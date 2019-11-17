/*
   MicroSocks - multithreaded, small, efficient SOCKS5 server.

   Copyright (C) 2017 rofl0r.

   This is the successor of "rocksocks5", and it was written with
   different goals in mind:

   - prefer usage of standard libc functions over homegrown ones
   - no artificial limits
   - do not aim for minimal binary size, but for minimal source code size,
     and maximal readability, reusability, and extensibility.

   as a result of that, ipv4, dns, and ipv6 is supported out of the box
   and can use the same code, while rocksocks5 has several compile time
   defines to bring down the size of the resulting binary to extreme values
   like 10 KB static linked when only ipv4 support is enabled.

   still, if optimized for size, *this* program when static linked against musl
   libc is not even 50 KB. that's easily usable even on the cheapest routers.

*/

#define _GNU_SOURCE
#include <unistd.h>
#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <sys/select.h>
#include <arpa/inet.h>
#include <errno.h>
#include <limits.h>
#include "server.h"
#include "sblist.h"

#ifndef MAX
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#endif

#if !defined(PTHREAD_STACK_MIN) || defined(__APPLE__)
/* MAC says its min is 8KB, but then crashes in our face. thx hunkOLard */
#undef PTHREAD_STACK_MIN
#define PTHREAD_STACK_MIN 64*1024
#elif defined(__GLIBC__)
#undef PTHREAD_STACK_MIN
#define PTHREAD_STACK_MIN 32*1024
#endif

#define MAX_BINDLISTENIPPORT 50

enum socksstate {
	SS_1_CONNECTED,
	SS_2_NEED_AUTH, /* skipped if NO_AUTH method supported */
	SS_3_AUTHED,
};

enum authmethod {
	AM_NO_AUTH = 0,
	AM_GSSAPI = 1,
	AM_USERNAME = 2,
	AM_INVALID = 0xFF
};

enum errorcode {
	EC_SUCCESS = 0,
	EC_GENERAL_FAILURE = 1,
	EC_NOT_ALLOWED = 2,
	EC_NET_UNREACHABLE = 3,
	EC_HOST_UNREACHABLE = 4,
	EC_CONN_REFUSED = 5,
	EC_TTL_EXPIRED = 6,
	EC_COMMAND_NOT_SUPPORTED = 7,
	EC_ADDRESSTYPE_NOT_SUPPORTED = 8,
};

struct serverthread
{
	pthread_t pt;
    struct server server;
    volatile int done;
};

struct clientthread
{
    pthread_t pt;
	struct client client;
	enum socksstate state;
    volatile int done;
};

static void *serverpthread(struct serverthread *serverthread);

#ifndef CONFIG_LOG
#define CONFIG_LOG 1
#endif
#if CONFIG_LOG
/* we log to stderr because it's not using line buffering, i.e. malloc which would need
   locking when called from different threads. for the same reason we use dprintf,
   which writes directly to an fd. */
#define dolog(...) dprintf(2, __VA_ARGS__)
#else
static void dolog(const char* fmt, ...) { }
#endif

static int connect_socks_target(unsigned char *buf, size_t n, struct client *client) {
	if(n < 5) return -EC_GENERAL_FAILURE;
	if(buf[0] != 5) return -EC_GENERAL_FAILURE;
	if(buf[1] != 1) return -EC_COMMAND_NOT_SUPPORTED; /* we support only CONNECT method */
	if(buf[2] != 0) return -EC_GENERAL_FAILURE; /* malformed packet */

	int af = AF_INET;
	size_t minlen = 4 + 4 + 2, l;
	char namebuf[256];
	struct addrinfo* remote;

	switch(buf[3]) {
		case 4: /* ipv6 */
			af = AF_INET6;
			minlen = 4 + 2 + 16;
			/* fall through */
		case 1: /* ipv4 */
			if(n < minlen) return -EC_GENERAL_FAILURE;
			if(namebuf != inet_ntop(af, buf+4, namebuf, sizeof namebuf))
				return -EC_GENERAL_FAILURE; /* malformed or too long addr */
			break;
		case 3: /* dns name */
			l = buf[4];
			minlen = 4 + 2 + l + 1;
			if(n < 4 + 2 + l + 1) return -EC_GENERAL_FAILURE;
			memcpy(namebuf, buf+4+1, l);
			namebuf[l] = 0;
			break;
		default:
			return -EC_ADDRESSTYPE_NOT_SUPPORTED;
	}
	unsigned short port;
	port = (buf[minlen-2] << 8) | buf[minlen-1];
	/* there's no suitable errorcode in rfc1928 for dns lookup failure */
	if(resolve(namebuf, port, &remote)) return -EC_GENERAL_FAILURE;
	int fd = socket(remote->ai_addr->sa_family, SOCK_STREAM, 0);
	if(fd == -1) {
		eval_errno:
		if(fd != -1) close(fd);
		freeaddrinfo(remote);
		switch(errno) {
			case ETIMEDOUT:
				return -EC_TTL_EXPIRED;
			case EPROTOTYPE:
			case EPROTONOSUPPORT:
			case EAFNOSUPPORT:
				return -EC_ADDRESSTYPE_NOT_SUPPORTED;
			case ECONNREFUSED:
				return -EC_CONN_REFUSED;
			case ENETDOWN:
			case ENETUNREACH:
				return -EC_NET_UNREACHABLE;
			case EHOSTUNREACH:
				return -EC_HOST_UNREACHABLE;
			case EBADF:
			default:
			perror("socket/connect");
			return -EC_GENERAL_FAILURE;
		}
	}
  if(SOCKADDR_UNION_AF(&client->server->bind_addr) != AF_UNSPEC &&
     bindtoip(fd, &client->server->bind_addr) == -1)
		goto eval_errno;
	if(connect(fd, remote->ai_addr, remote->ai_addrlen) == -1)
		goto eval_errno;

	freeaddrinfo(remote);
	if(CONFIG_LOG) {
		char clientname[256];
		af = SOCKADDR_UNION_AF(&client->addr);
		void *ipdata = SOCKADDR_UNION_ADDRESS(&client->addr);
		inet_ntop(af, ipdata, clientname, sizeof clientname);
		dolog("client[%d] %s: connected to %s:%d\n", client->fd, clientname, namebuf, port);
	}
	return fd;
}

static enum authmethod check_auth_method(unsigned char *buf, size_t n, struct client *client) {
	if(buf[0] != 5) return AM_INVALID;
	size_t idx = 1;
  if(idx >= n)
    return AM_INVALID;
	int n_methods = buf[idx];
	idx++;
	while(idx < n && n_methods > 0) {
		if(buf[idx] == AM_NO_AUTH) {
      return AM_NO_AUTH;
		} else if(buf[idx] == AM_USERNAME) {
		}
		idx++;
		n_methods--;
	}
	return AM_INVALID;
}

static void send_auth_response(int fd, int version, enum authmethod meth) {
	unsigned char buf[2];
	buf[0] = version;
	buf[1] = meth;
	write(fd, buf, 2);
}

static void send_error(int fd, enum errorcode ec) {
	/* position 4 contains ATYP, the address type, which is the same as used in the connect
	   request. we're lazy and return always IPV4 address type in errors. */
	char buf[10] = { 5, ec, 0, 1 /*AT_IPV4*/, 0,0,0,0, 0,0 };
	write(fd, buf, 10);
}

static void copyloop(int fd1, int fd2) {
	int maxfd = fd2;
	if(fd1 > fd2) maxfd = fd1;
	fd_set fdsc, fds;
	FD_ZERO(&fdsc);
	FD_SET(fd1, &fdsc);
	FD_SET(fd2, &fdsc);

	while(1) {
		memcpy(&fds, &fdsc, sizeof(fds));
		/* inactive connections are reaped after 15 min to free resources.
		   usually programs send keep-alive packets so this should only happen
		   when a connection is really unused. */
		struct timeval timeout = {.tv_sec = 60*15, .tv_usec = 0};
		switch(select(maxfd+1, &fds, 0, 0, &timeout)) {
			case 0:
				send_error(fd1, EC_TTL_EXPIRED);
				return;
			case -1:
				if(errno == EINTR) continue;
				else perror("select");
				return;
		}
		int infd = FD_ISSET(fd1, &fds) ? fd1 : fd2;
		int outfd = infd == fd2 ? fd1 : fd2;
		char buf[1024];
		ssize_t sent = 0, n = read(infd, buf, sizeof buf);
		if(n <= 0) return;
		while(sent < n) {
			ssize_t m = write(outfd, buf+sent, n-sent);
			if(m < 0) return;
			sent += m;
		}
	}
}

static void *clientpthread(void *data) {
  struct clientthread *thread = data;
  dolog("clientpthread %d\n", thread->client.fd);
  thread->state = SS_1_CONNECTED;
	unsigned char buf[1024];
	ssize_t n;
	int ret;
	int remotefd = -1;
	enum authmethod am;
  while((n = recv(thread->client.fd, buf, sizeof buf, 0)) > 0) {
    switch(thread->state) {
			case SS_1_CONNECTED:
      am = check_auth_method(buf, n, &thread->client);
      if(am == AM_NO_AUTH)
        thread->state = SS_3_AUTHED;
      else if(am == AM_USERNAME)
        goto breakloop;
      send_auth_response(thread->client.fd, 5, am);
				if(am == AM_INVALID) goto breakloop;
				break;
			case SS_3_AUTHED:
      dolog("connecting to %s\n", buf);
      ret = connect_socks_target(buf, n, &thread->client);
				if(ret < 0) {
        send_error(thread->client.fd, ret * -1);
					goto breakloop;
				}
      dolog("yay\n");
				remotefd = ret;
      send_error(thread->client.fd, EC_SUCCESS);
      copyloop(thread->client.fd, remotefd);
				goto breakloop;
		}
	}
breakloop:

  if(remotefd != -1) close(remotefd);

  close(thread->client.fd);
  thread->done = 1;

	return 0;
}

static void collect(sblist *threads) {
	size_t i;
  for(i = 0; i < sblist_getsize(threads);) {
    struct clientthread *thread = *((struct clientthread **)sblist_get(threads, i));
		if(thread->done) {
			pthread_join(thread->pt, 0);
			sblist_delete(threads, i);
			free(thread);
		} else
			i++;
	}
}

static int usage(void) {
	dprintf(2,
		"MicroSocks SOCKS5 Server\n"
		"------------------------\n"
          "usage: microsocks -1 -I bindaddr:listenip:port -u user -P password\n"
		"option -1 activates auth_once mode: once a specific ip address\n"
		"authed successfully with user/pass, it is added to a whitelist\n"
		"and may use the proxy without auth.\n"
		"this is handy for programs like firefox that don't support\n"
		"user/pass auth. for it to work you'd basically make one connection\n"
		"with another program that supports it, and then you can use firefox too.\n"
	);
	return 1;
}

/* prevent username and password from showing up in top. */
static void zero_arg(char *s) {
	size_t i, l = strlen(s);
	for(i=0;i<l;i++) s[i] = 0;
}

  int bindlistenipport_index = 0;

	int c;

  union sockaddr_union bind_addr[MAX_BINDLISTENIPPORT]; // = {.v4.sin_family = AF_UNSPEC};
  const char *listenip[MAX_BINDLISTENIPPORT];
  unsigned port[MAX_BINDLISTENIPPORT];

  while((c = getopt(argc, argv, "I:")) != -1) {
		switch(c) {
    case 'I': {
      const char *p0 = optarg;

      char *p1 = strchr(p0, ':');
      if(p1 == NULL) {
        dprintf(2, "error: IP and port should be separated by a colon\n");
        return 1;
      }
      *p1++ = '\0';

      char *p2 = strchr(p1 + 1, ':');
      if(p2 == NULL) {
        dprintf(2, "error: IP and port should be separated by a colon\n");
        return 1;
      }
      *p2++ = '\0';

      resolve_sa(p0, 0, &bind_addr[bindlistenipport_index]);
      listenip[bindlistenipport_index] = strdup(p1);
      port[bindlistenipport_index] = atoi(p2);
      bindlistenipport_index += 1;

      zero_arg(p1);
      zero_arg(p2);
				zero_arg(optarg);
				break;
    }
			case ':':
				dprintf(2, "error: option -%c requires an operand\n", optopt);
			case '?':
				return usage();
		}
	}

  for(int a = 1; a < argc; a++) {
    argv[a] = '\0';
	}

	signal(SIGPIPE, SIG_IGN);
  struct serverthread server_threads[MAX_BINDLISTENIPPORT];

  size_t stacksz = MAX(8192, PTHREAD_STACK_MIN); /* 4KB for us, 4KB for libc */

  for(int i = 0; i < bindlistenipport_index; i++) {
    server_threads[i].done = 0;
    server_threads[i].server.bind_addr = bind_addr[i];
    if(server_setup(&server_threads[i].server, listenip[i], port[i])) {
		perror("server_setup");
		return 1;
	}

    pthread_attr_t *a = 0, attr;
    if(pthread_attr_init(&attr) == 0) {
      a = &attr;
      pthread_attr_setstacksize(a, stacksz);
    }
    dolog("creating serverthread\n");
    if(pthread_create(&server_threads[i].pt, a, serverpthread, &server_threads[i]) != 0)
      dolog("pthread_create failed. OOM?\n");
    if(a) pthread_attr_destroy(&attr);
  }

  dolog("joining serverthreads\n");

  for(int i = 0; i < bindlistenipport_index; i++) {
    pthread_join(server_threads[i].pt, 0);
  }

  dolog("serverthreads closed\n");

  return 0;
}

static void *serverpthread(struct serverthread *serverthread) {
  dolog("serverthread %d\n", serverthread->server.fd);

  size_t stacksz = MAX(8192, PTHREAD_STACK_MIN); /* 4KB for us, 4KB for libc */

  sblist *threads = sblist_new(sizeof(struct clientthread *), 8);

	while(1) {
		collect(threads);
    struct clientthread *clientthread = malloc(sizeof(struct clientthread));
    if(!clientthread) goto oom;
    clientthread->done = 0;
    if(server_waitclient(&serverthread->server, &clientthread->client)) continue;
    if(!sblist_add(threads, &clientthread)) {
      close(clientthread->client.fd);
      free(clientthread);
			oom:
			dolog("rejecting connection due to OOM\n");
			usleep(16); /* prevent 100% CPU usage in OOM situation */
			continue;
		}
		pthread_attr_t *a = 0, attr;
		if(pthread_attr_init(&attr) == 0) {
			a = &attr;
			pthread_attr_setstacksize(a, stacksz);
		}
    clientthread->client.server = &serverthread->server;
    if(pthread_create(&clientthread->pt, a, clientpthread, clientthread) != 0)
			dolog("pthread_create failed. OOM?\n");
		if(a) pthread_attr_destroy(&attr);
	}

  serverthread->done = 1;

  return 0;
}
