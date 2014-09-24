#include <stdlib.h>
#include <curl/curl.h>
#include <ctype.h>
#include <stddef.h>
#include <string.h>
#include <syslog.h>

/* === added for curl multi socket action with libevent === */
#include <stdio.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <sys/poll.h>
#include <event2/event.h>
#include <event2/thread.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <errno.h>
#include <pthread.h>

#include "vrt.h"
#include "vsb.h"
#include "cache/cache.h"

#include "vcc_if.h"
#include "config.h"

#define EVLOOP_ONCE             0x01
#define EVLOOP_NONBLOCK         0x02
#define EVLOOP_NO_EXIT_ON_EMPTY 0x04

struct hdr {
	char *key;
	char *value;
	VTAILQ_ENTRY(hdr) list;
};

struct req_hdr {
	char *value;
	VTAILQ_ENTRY(req_hdr) list;
};

struct vmod_curl {
	unsigned	magic;
#define VMOD_CURL_MAGIC 0xBBB0C87C
	unsigned vxid;
	long		status;
	long		timeout_ms;
	long		connect_timeout_ms;
	char		flags;
#define VC_VERIFY_PEER (1 << 0)
#define VC_VERIFY_HOST (1 << 1)
	const char	*url;
	const char	*method;
	const char	*postfields;
	const char	*error;
	const char	*cafile;
	const char	*capath;
	VTAILQ_HEAD(, hdr) headers;
	VTAILQ_HEAD(, req_hdr) req_headers;
	const char 	*proxy;
	struct vsb	*body;
	CURL *curl_handle;
	CURLcode cr;
	pthread_mutex_t mtx;
	pthread_cond_t cond;
};

/* =========== curl-multi related handler defs ===========*/

#define MSG_OUT stdout  

static int nr_of_requests = 0;


 
 
/* Global information, common to all connections */ 
typedef struct _GlobalInfo
{
  unsigned magic;
#define GLOBAL_INFO_MAGIC 0x77feec11
  struct event_base *evbase;
  struct event *timer_event;
  CURLM *multi;
  int still_running;
  // global curl init result
  CURLcode global_init_result;
  struct vmod_curl *current;
  int run_dispatch;
} GlobalInfo;
 
 
/* Information associated with a specific easy handle */ 
typedef struct _ConnInfo
{
  CURL *easy;
  char *url;
  GlobalInfo *global;
  char error[CURL_ERROR_SIZE];
} ConnInfo;
 
 
/* Information associated with a specific socket */ 
typedef struct _SockInfo
{
  curl_socket_t sockfd;
  CURL *easy;
  int action;
  long timeout;
  struct event *ev;
  int evset;
  GlobalInfo *global;
} SockInfo;


/* CURLMOPT_SOCKETFUNCTION */ 
static int sock_cb(CURL *e, curl_socket_t s, int what, void *cbp, void *sockp);

/* Update the event timer after curl_multi library calls */ 
static int multi_timer_cb(CURLM *multi, long timeout_ms, GlobalInfo *g);

/* Called by libevent when our timeout expires */ 
static void timer_cb(int fd, short kind, void *userp);

/* curl-multi thread worker */
static void* cm_worker(void *priv);

/* error handler */
static void mcode_or_die(const char *where, CURLMcode code);

/* creates an easy handle and adds to multi session */
static void cm_perform_easy(struct vmod_curl *c);

/* turns the curl request into the 'wait for response' state */
static void cm_wait(struct vmod_curl *c);

static GlobalInfo *globalInfo;

/* ====EOF==== curl-multi related handler defs ===========*/

static int initialised = 0;

static struct vmod_curl **vmod_curl_list;
int vmod_curl_list_sz;
static pthread_mutex_t cl_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t gl_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t gl2_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t gl3_mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t gl_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t gl2_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t gl3_cond = PTHREAD_COND_INITIALIZER;
static void cm_clear(struct vmod_curl *c);

static GlobalInfo* new_vcl_priv();
static void free_vcl_priv(GlobalInfo *priv);

static void cm_init(struct vmod_curl *c) {
	c->magic = VMOD_CURL_MAGIC;
	VTAILQ_INIT(&c->headers);
	VTAILQ_INIT(&c->req_headers);
	c->body = VSB_new_auto();
	cm_clear(c);
	pthread_mutex_init(&c->mtx, NULL);
	pthread_cond_init(&c->cond, NULL);
}

static void cm_clear_body(struct vmod_curl *c) {

	CHECK_OBJ_NOTNULL(c, VMOD_CURL_MAGIC);

	VSB_clear(c->body);
}

static void cm_clear_headers(struct vmod_curl *c) {
	struct hdr *h, *h2;

	CHECK_OBJ_NOTNULL(c, VMOD_CURL_MAGIC);

	VTAILQ_FOREACH_SAFE(h, &c->headers, list, h2) {
		VTAILQ_REMOVE(&c->headers, h, list);
		free(h->key);
		free(h->value);
		free(h);
	}
}

static void cm_clear_req_headers(struct vmod_curl *c) {
	struct req_hdr *rh, *rh2;

	CHECK_OBJ_NOTNULL(c, VMOD_CURL_MAGIC);

	VTAILQ_FOREACH_SAFE(rh, &c->req_headers, list, rh2) {
		VTAILQ_REMOVE(&c->req_headers, rh, list);
		free(rh->value);
		free(rh);
	}
}

static void cm_clear_fetch_state(struct vmod_curl *c) {
	CHECK_OBJ_NOTNULL(c, VMOD_CURL_MAGIC);

	c->method = NULL;
	cm_clear_body(c);
	cm_clear_headers(c);
}

static void cm_clear(struct vmod_curl *c) {
	CHECK_OBJ_NOTNULL(c, VMOD_CURL_MAGIC);

	cm_clear_fetch_state(c);
	//cm_clear_req_headers(c);
	c->status = 0;
	c->timeout_ms = -1;
	c->connect_timeout_ms = -1;
	c->flags = 0;
	c->cafile = NULL;
	c->capath = NULL;
	c->error = NULL;
	c->vxid = 0;
	c->proxy = NULL;
	c->postfields = NULL;
	c->curl_handle = NULL;
}

static struct vmod_curl* cm_get(const struct vrt_ctx *ctx) {
	struct vmod_curl *cm;
	AZ(pthread_mutex_lock(&cl_mtx));

	while (vmod_curl_list_sz <= ctx->req->sp->fd) {
		int ns = vmod_curl_list_sz*2;
		/* resize array */
		vmod_curl_list = realloc(vmod_curl_list, ns * sizeof(struct vmod_curl *));
		for (; vmod_curl_list_sz < ns; vmod_curl_list_sz++) {
			vmod_curl_list[vmod_curl_list_sz] = malloc(sizeof(struct vmod_curl));
			cm_init(vmod_curl_list[vmod_curl_list_sz]);
		}
		assert(vmod_curl_list_sz == ns);
		AN(vmod_curl_list);
	}
	cm = vmod_curl_list[ctx->req->sp->fd];
	if (cm->vxid != ctx->req->sp->vxid) {
		cm_clear(cm);
		cm->vxid = ctx->req->sp->vxid;
	}
	AZ(pthread_mutex_unlock(&cl_mtx));
	cm_wait(cm);
	return cm;
}

/******************************************************************************
 * Init related functions
 *****************************************************************************/

 /* curl-multi thread worker */
static void* cm_worker(void *priv) {
	syslog(LOG_INFO, "Starting curl-multi worker...thread ID = %d", (int)pthread_self());
	GlobalInfo *g;
	int rc;
	struct timeval timeout;
	struct vmod_curl *req, *req2;
	struct timespec tim, tim2;

	tim.tv_sec  = 0;
	tim.tv_nsec = 50000000L;

	CAST_OBJ_NOTNULL(g, priv, GLOBAL_INFO_MAGIC);
 	g->global_init_result = curl_global_init(CURL_GLOBAL_ALL);
  	if (!g->global_init_result) {
    	g->multi = curl_multi_init();
		/* setup the generic multi interface options we want */ 
		curl_multi_setopt(g->multi, CURLMOPT_SOCKETFUNCTION, sock_cb);
  		curl_multi_setopt(g->multi, CURLMOPT_SOCKETDATA, g);
  		curl_multi_setopt(g->multi, CURLMOPT_TIMERFUNCTION, multi_timer_cb);
  		curl_multi_setopt(g->multi, CURLMOPT_TIMERDATA, g);

  		evthread_use_pthreads(); 
  		g->evbase = event_base_new();
  		evthread_make_base_notifiable(g->evbase);
  		g->timer_event = evtimer_new(g->evbase, timer_cb, g);

  		//event_base_dispatch(g->evbase);

  		timeout.tv_sec = 100;
  		timeout.tv_usec = 0;

  		do {
  			AZ(pthread_mutex_lock(&gl_mtx));
  			while (!g->current) {
  				pthread_cond_wait(&gl_cond, &gl_mtx);
  			}
  			pthread_mutex_unlock(&gl_mtx);
  			//AZ(pthread_mutex_lock(&gl2_mtx));
  			syslog(LOG_INFO, "Nr of REQUESTS = %d, g->current=%d", nr_of_requests++, (int)g->current);
  			cm_perform_easy(g->current);
  			//event_base_loop(g->evbase, EVLOOP_NONBLOCK);
  			g->current = NULL;
  			AZ(pthread_mutex_lock(&gl2_mtx));
  			pthread_cond_signal(&gl2_cond);
  			pthread_mutex_unlock(&gl2_mtx);
  			//pthread_mutex_unlock(&gl_mtx);
  			//AZ(pthread_mutex_lock(&gl_mtx));
  			//event_base_dispatch(g->evbase);
  			//pthread_cond_signal(&gl_cond);
  			//pthread_mutex_unlock(&gl2_mtx);
  		} while (1);


  	// 	evtimer_add(g->timer_event, &timeout);
	  //   rc = event_base_loop(g->evbase, EVLOOP_NO_EXIT_ON_EMPTY);
	  //   if (rc) {
 		// 	syslog(LOG_INFO, "Return code from event_base_loop() is %d", rc);
   //      	exit(1);
 		// }
 
  	} else {
  		syslog(LOG_INFO, "Return code from curl_global_init() is %d", rc);
        exit(1);
  	}
	syslog(LOG_INFO, "bla bla...");
	syslog(LOG_INFO, "Worker started");
}

/* event-base thread worker */
static void* cm_worker2(void *priv) {
	syslog(LOG_INFO, "Starting event-base worker...thread ID = %d", (int)pthread_self());
	GlobalInfo *g;
	int rc;
	struct timeval timeout;
	struct vmod_curl *req, *req2;
	struct timespec tim, tim2;

	tim.tv_sec  = 0;
	tim.tv_nsec = 10000000L;

	CAST_OBJ_NOTNULL(g, priv, GLOBAL_INFO_MAGIC);


	while(1) {
		AZ(pthread_mutex_lock(&gl3_mtx));
  		while (!globalInfo->run_dispatch) {
  			pthread_cond_wait(&gl3_cond, &gl3_mtx);
  		}
  		pthread_mutex_unlock(&gl3_mtx);
  		globalInfo->run_dispatch = 0;
  		event_base_dispatch(globalInfo->evbase);
  	}

	/*do {
		if (globalInfo->evbase) {
			event_base_dispatch(globalInfo->evbase);
		}
		nanosleep(&tim, &tim);
	} while(1);*/
}

static GlobalInfo *
new_vcl_priv()
{
	syslog(LOG_INFO, "new_vcl_priv CALLED");
	pthread_t thread0, thread1;
	int rc;
	GlobalInfo *g;
	ALLOC_OBJ(g, GLOBAL_INFO_MAGIC);
    AN(g);
    g->global_init_result = 0;
    g->still_running = 0;
    g->multi = NULL;
    g->evbase = NULL;
    g->timer_event = NULL;
    g->current = NULL;
    g->run_dispatch = 0;
  	
	/* start an event loop thread */
	syslog(LOG_INFO, "Starting event loop thread...");
	rc = pthread_create(&thread0, NULL, cm_worker, (void *)g); 
	if (rc) {
		syslog(LOG_INFO, "ERROR; return code from pthread_create() is %d", rc);
 		exit(-1);
    }

    rc = pthread_create(&thread1, NULL, cm_worker2, (void *)g); 
	if (rc) {
		syslog(LOG_INFO, "ERROR; return code from pthread_create() is %d", rc);
 		exit(-1);
    }     
    return g;
}

static void
free_vcl_priv(GlobalInfo *priv)
{
	CURLMsg *msg; /* for picking up messages with the transfer status */ 
	int msgs_left; /* how many messages are left */ 
	CURL *easy_handle; /* easy handle */
	syslog(LOG_INFO, "free_vcl_priv CALLED");

    if(!priv->global_init_result) {
    	if (priv->multi) {
    		while ((msg = curl_multi_info_read(priv->multi, &msgs_left))) {
    			// not sure if the msg pointers are still valid after 'curl_multi_remove_handle' call, so better assign.
    			easy_handle = msg->easy_handle;
    			curl_multi_remove_handle(priv->multi, easy_handle);
    			curl_easy_cleanup(easy_handle);
    		}
    	}
    	curl_global_cleanup();
    }
    syslog(LOG_INFO, "free_vcl_priv CALLED, cleanup complete");
    FREE_OBJ(priv);
}

int
init_function(struct vmod_priv *priv, const struct VCL_conf *conf)
{
	int i;
	GlobalInfo *priv_t;

	(void)priv;
	(void)conf;

	if (initialised)
	  return 0;

	initialised = 1;

	vmod_curl_list = NULL;
	vmod_curl_list_sz = 256;
	vmod_curl_list = malloc(sizeof(struct vmod_curl *) * 256);
	AN(vmod_curl_list);
	for (i = 0 ; i < vmod_curl_list_sz; i++) {
		vmod_curl_list[i] = malloc(sizeof(struct vmod_curl));
		cm_init(vmod_curl_list[i]);
	}
	if (priv->priv == NULL) {
		priv_t = new_vcl_priv();
        priv->priv = priv_t;
        //priv->free = (vmod_priv_free_f *)free_vcl_priv;
    }
    syslog(LOG_INFO, "init_function, cURL global result: %d, thread ID=%d", priv_t->global_init_result, (int)pthread_self());
    globalInfo = priv_t;
	return priv_t->global_init_result;
}

static size_t recv_data(void *ptr, size_t size, size_t nmemb, void *s)
{
	struct vmod_curl *vc;

	CAST_OBJ_NOTNULL(vc, s, VMOD_CURL_MAGIC);

	VSB_bcat(vc->body, ptr, size * nmemb);
	return size * nmemb;
}

static size_t recv_hdrs(void *ptr, size_t size, size_t nmemb, void *s)
{
	syslog(LOG_INFO, "recv_hdrs CALLED, thread ID = %d", (int)pthread_self());
	struct vmod_curl *vc;
	struct hdr *h;
	char *split;
	ptrdiff_t keylen, vallen;

	CAST_OBJ_NOTNULL(vc, s, VMOD_CURL_MAGIC);

	split = memchr(ptr, ':', size * nmemb);
	if (split == NULL)
		return (size * nmemb);

	keylen = split - (char *)ptr;
	assert(keylen >= 0);
	if (keylen == 0)
		return (size * nmemb);

	h = calloc(1, sizeof(struct hdr));
	AN(h);
	h->key = strndup(ptr, keylen);
	AN(h->key);

	vallen = size*nmemb - keylen;
	assert(vallen > 0);	/* Counts ':' so always larger than 0 */
	split++;		/* Drop ':' */
	vallen--;
	while (vallen > 0 && isspace(*split)) {
		split++;
		vallen--;
	}
	while (vallen > 0 && isspace(*(split + vallen - 1)))
		vallen--;
	h->value = strndup(split, vallen);
	AN(h->value);

	VTAILQ_INSERT_HEAD(&vc->headers, h, list);

	return (size * nmemb);
}

/* safely sets current vmod_curl instance, only if the current value is NULL 
 returns 0 if succesful, non-zero otherwise */
static int cm_set_current(struct vmod_curl *c) {
	int result;
	AZ(pthread_mutex_lock(&gl2_mtx));
	if (globalInfo->current) {
		result = 1;
	} else {
		globalInfo->current = c;
		result =0;
	}	
	pthread_mutex_unlock(&gl2_mtx);
	return result;
}

static void cm_perform(struct vmod_curl *c) {
	struct timespec tim;

	tim.tv_sec  = 0;
	tim.tv_nsec = 100000000L;
	AZ(pthread_mutex_lock(&gl2_mtx));
	while (globalInfo->current) {
		pthread_cond_wait(&gl2_cond, &gl2_mtx);
	}
	globalInfo->current = c;
	pthread_mutex_unlock(&gl2_mtx);
	//globalInfo->current = c;

	// try to set the 'c' as current in global info
	//while(cm_set_current(c)) {
		//nanosleep(&tim, &tim);
	//}

	//AZ(pthread_mutex_lock(&gl2_mtx));
	//if (globalInfo->current) {
	//	pthread_cond_wait(&gl_cond, &gl_mtx);
	//}
	//pthread_mutex_unlock(&gl_mtx);
	syslog(LOG_INFO, "Request thread ID = %d, url: %s", (int)pthread_self(), c->url);
	c->curl_handle = 1;
	AZ(pthread_mutex_lock(&gl_mtx));
	//globalInfo->current = c;
	pthread_cond_signal(&gl_cond);
	//event_base_dispatch(globalInfo->evbase);
	//AZ(pthread_mutex_lock(&gl_mtx));
	//c->curl_handle = 1;
	//globalInfo->current = c;
	//pthread_cond_signal(&gl_cond);
	pthread_mutex_unlock(&gl_mtx);
	//AZ(pthread_mutex_lock(&gl_mtx));
	//pthread_cond_wait(&gl_cond, &gl_mtx);
	//pthread_mutex_unlock(&gl_mtx);
	//pthread_mutex_unlock(&gl2_mtx);
}

static void cm_perform_easy(struct vmod_curl *c) {


	//CURL *curl_handle;
	CURLcode cr;
	struct curl_slist *req_headers = NULL;
	struct req_hdr *rh;

	c->curl_handle = curl_easy_init();
	AN(c->curl_handle);

	VTAILQ_FOREACH(rh, &c->req_headers, list) {
		req_headers = curl_slist_append(req_headers, rh->value);
	}

	if (c->method && strcmp(c->method, "POST") == 0) {
		curl_easy_setopt(c->curl_handle, CURLOPT_POST, 1L);
		curl_easy_setopt(c->curl_handle, CURLOPT_POSTFIELDS, c->postfields);

	}
	if (c->method && strcmp(c->method, "HEAD") == 0) {
		curl_easy_setopt(c->curl_handle, CURLOPT_NOBODY, 1L);

	}
	if (req_headers)
		curl_easy_setopt(c->curl_handle, CURLOPT_HTTPHEADER, req_headers);
	curl_easy_setopt(c->curl_handle, CURLOPT_URL, c->url);
	curl_easy_setopt(c->curl_handle, CURLOPT_NOSIGNAL , 1L);
	//curl_easy_setopt(curl_handle, CURLOPT_VERBOSE, 1L);
	curl_easy_setopt(c->curl_handle, CURLOPT_PRIVATE, c);
	curl_easy_setopt(c->curl_handle, CURLOPT_NOPROGRESS, 1L);
	curl_easy_setopt(c->curl_handle, CURLOPT_WRITEFUNCTION, recv_data);
	curl_easy_setopt(c->curl_handle, CURLOPT_WRITEDATA, c);
	curl_easy_setopt(c->curl_handle, CURLOPT_HEADERFUNCTION, recv_hdrs);
	curl_easy_setopt(c->curl_handle, CURLOPT_HEADERDATA, c);
	if(c->proxy) {
		curl_easy_setopt(c->curl_handle, CURLOPT_PROXY, c->proxy);
	}
	if (c->timeout_ms > 0) {
#ifdef CURL_TIMEOUTMS_WORKS
		curl_easy_setopt(c->curl_handle, CURLOPT_TIMEOUT_MS, c->timeout_ms);
#else
		curl_easy_setopt(c->curl_handle, CURLOPT_TIMEOUT, c->timeout_ms / 1000);
#endif
	}

	if (c->connect_timeout_ms > 0) {
#ifdef CURL_TIMEOUTMS_WORKS
		curl_easy_setopt(c->curl_handle, CURLOPT_CONNECTTIMEOUT_MS, c->connect_timeout_ms);
#else
		curl_easy_setopt(c->curl_handle, CURLOPT_CONNECTTIMEOUT, c->connect_timeout_ms / 1000);
#endif
	}

	if (c->flags & VC_VERIFY_PEER) {
		curl_easy_setopt(c->curl_handle, CURLOPT_SSL_VERIFYPEER, 1L);
	} else {
		curl_easy_setopt(c->curl_handle, CURLOPT_SSL_VERIFYPEER, 0L);
	}

	if (c->flags & VC_VERIFY_HOST) {
		curl_easy_setopt(c->curl_handle, CURLOPT_SSL_VERIFYHOST, 1L);
	} else {
		curl_easy_setopt(c->curl_handle, CURLOPT_SSL_VERIFYHOST, 0L);
	}

	if (c->cafile) {
		      curl_easy_setopt(c->curl_handle, CURLOPT_CAINFO, c->cafile);
	}

	if (c->capath) {
		      curl_easy_setopt(c->curl_handle, CURLOPT_CAPATH, c->capath);
	}

	syslog(LOG_INFO, "Adding easy to MULTI");
	c->cr = curl_multi_add_handle(globalInfo->multi, c->curl_handle);
	syslog(LOG_INFO, "Added easy to MULTI");
    mcode_or_die("new_conn: curl_multi_add_handle", c->cr);

	/* cr = curl_easy_perform(curl_handle); 

	if (cr != 0) {
		c->error = curl_easy_strerror(cr);
	}

	curl_easy_getinfo(curl_handle, CURLINFO_RESPONSE_CODE, &c->status);


	if (req_headers)
		curl_slist_free_all(req_headers);
	cm_clear_req_headers(c);
	curl_easy_cleanup(curl_handle);
	VSB_finish(c->body); */
}

VCL_VOID
vmod_fetch(const struct vrt_ctx *ctx, VCL_STRING url)
{
	vmod_get(ctx, url);
}

VCL_VOID
vmod_get(const struct vrt_ctx *ctx, VCL_STRING url)
{
	struct vmod_curl *c;
	c = cm_get(ctx);
	cm_clear_fetch_state(c);
	c->url = url;
	c->method = "GET";
	cm_perform(c);
}

VCL_VOID
vmod_head(const struct vrt_ctx *ctx, VCL_STRING url)
{
	struct vmod_curl *c;
	c = cm_get(ctx);
	cm_clear_fetch_state(c);
	c->url = url;
	c->method = "HEAD";
	cm_perform(c);
}

VCL_VOID
vmod_post(const struct vrt_ctx *ctx, VCL_STRING url, VCL_STRING postfields)
{
	struct vmod_curl *c;
	c = cm_get(ctx);
	cm_clear_fetch_state(c);
	c->url = url;
	c->method = "POST";
	c->postfields = postfields;
	cm_perform(c);
}

VCL_INT
vmod_status(const struct vrt_ctx *ctx)
{
	int r;
	struct vmod_curl *c;
	c = cm_get(ctx);
	cm_wait(c);
	r = c->status;
	return r;
}

VCL_VOID
vmod_free(const struct vrt_ctx *ctx)
{
	cm_clear(cm_get(ctx));
}

VCL_STRING
vmod_error(const struct vrt_ctx *ctx)
{
	struct vmod_curl *c;

	c = cm_get(ctx);
	cm_wait(c);
	if (c->status != 0)
		return(NULL);
	return(c->error);
}

VCL_STRING
vmod_header(const struct vrt_ctx *ctx, VCL_STRING header)
{
	struct hdr *h;
	const char *r = NULL;
	struct vmod_curl *c;

	c = cm_get(ctx);
	cm_wait(c);

	VTAILQ_FOREACH(h, &c->headers, list) {
		if (strcasecmp(h->key, header) == 0) {
			r = h->value;
			break;
		}
	}
	return r;
}

VCL_STRING
vmod_body(const struct vrt_ctx *ctx)
{
	struct vmod_curl *c;
	c = cm_get(ctx);
	cm_wait(c);
	return VSB_data(c->body);
}

VCL_VOID
vmod_set_timeout(const struct vrt_ctx *ctx, VCL_INT timeout)
{
	cm_get(ctx)->timeout_ms = timeout;
}

VCL_VOID
vmod_set_connect_timeout(const struct vrt_ctx *ctx, VCL_INT timeout)
{
	cm_get(ctx)->connect_timeout_ms = timeout;
}

VCL_VOID
vmod_set_ssl_verify_peer(const struct vrt_ctx *ctx, VCL_INT verify)
{
	if (verify) {
		cm_get(ctx)->flags |= VC_VERIFY_PEER;
	} else {
		cm_get(ctx)->flags &= ~VC_VERIFY_PEER;
	}
}

VCL_VOID
vmod_set_ssl_verify_host(const struct vrt_ctx *ctx, VCL_INT verify)
{
	if (verify) {
		cm_get(ctx)->flags |= VC_VERIFY_HOST;
	} else {
		cm_get(ctx)->flags &= ~VC_VERIFY_HOST;
	}
}

VCL_VOID
vmod_set_ssl_cafile(const struct vrt_ctx *ctx, VCL_STRING path)
{
	cm_get(ctx)->cafile = path;
}

VCL_VOID
vmod_set_ssl_capath(const struct vrt_ctx *ctx, VCL_STRING path)
{
	cm_get(ctx)->capath = path;
}

VCL_VOID
vmod_header_add(const struct vrt_ctx *ctx, VCL_STRING value)
{
	struct vmod_curl *c;
	struct req_hdr *rh;

	c = cm_get(ctx);

	rh = calloc(1, sizeof(struct req_hdr));
	AN(rh);
	rh->value = strdup(value);
	AN(rh->value);

	VTAILQ_INSERT_HEAD(&c->req_headers, rh, list);
}

VCL_VOID
vmod_header_remove(const struct vrt_ctx *ctx, VCL_STRING header)
{
	struct vmod_curl *c;
	struct req_hdr *rh;
	char *split, *s;

	c = cm_get(ctx);

	VTAILQ_FOREACH(rh, &c->req_headers, list) {
		s = strdup(rh->value);
		AN(s);
		if ((split = strchr(s, ':')) != NULL)
			*split = '\x0';
		if (strcasecmp(s, header) == 0) {
			VTAILQ_REMOVE(&c->req_headers, rh, list);
			free(rh->value);
			free(rh);
		}
		free(s);
	}
}

VCL_STRING
vmod_escape(const struct vrt_ctx *ctx, VCL_STRING str)
{
	char *esc, *r;

	CURL *curl_handle;

	curl_handle = curl_easy_init();
	AN(curl_handle);

	esc = curl_easy_escape(curl_handle, str, 0);
	AN(esc);
	r = WS_Copy(ctx->ws, esc, -1);
	curl_free(esc);
	curl_easy_cleanup(curl_handle);

	return r;
}

VCL_STRING
vmod_unescape(const struct vrt_ctx *ctx, VCL_STRING str)
{
	char *tmp, *r;

	CURL *curl_handle;

	curl_handle = curl_easy_init();
	AN(curl_handle);

	tmp = curl_easy_unescape(curl_handle, str, 0, NULL);
	AN(tmp);
	r = WS_Copy(ctx->ws, tmp, -1);
	curl_free(tmp);
	curl_easy_cleanup(curl_handle);

	return r;
}

VCL_VOID
vmod_proxy(const struct vrt_ctx *ctx, VCL_STRING proxy) {
	cm_get(ctx)->proxy = proxy;
}

/* =========== curl-multi handler ===========*/

static void cm_wait(struct vmod_curl *c) {
	// 'while' instead of 'if' because of possible spurious wakeups
	AZ(pthread_mutex_lock(&c->mtx));
	while (c->curl_handle) {
		syslog(LOG_INFO, "cm_wait - OK");
  		pthread_cond_wait(&c->cond, &c->mtx);
  	}
  	pthread_mutex_unlock(&c->mtx);
}
 
/* Update the event timer after curl_multi library calls */ 
static int multi_timer_cb(CURLM *multi, long timeout_ms, GlobalInfo *g)
{
  syslog(LOG_INFO, "multi_timer_cb thread ID = %d", (int)pthread_self());
  struct timeval timeout;
  (void)multi; /* unused */ 
 
  timeout.tv_sec = timeout_ms/1000;
  timeout.tv_usec = (timeout_ms%1000)*1000;
  //fprintf(MSG_OUT, "multi_timer_cb: Setting timeout to %ld ms\n", timeout_ms);
  evtimer_add(g->timer_event, &timeout);
  g->run_dispatch = 1;
  AZ(pthread_mutex_lock(&gl3_mtx));
  pthread_cond_signal(&gl3_cond);
  pthread_mutex_unlock(&gl3_mtx);
  //event_base_dispatch(g->evbase);
  //event_base_loopbreak(g->evbase);
  return 0;
}
 
/* Die if we get a bad CURLMcode somewhere */ 
static void mcode_or_die(const char *where, CURLMcode code)
{
  if ( CURLM_OK != code ) {
    const char *s;
    switch (code) {
      case     CURLM_BAD_HANDLE:         s="CURLM_BAD_HANDLE";         break;
      case     CURLM_BAD_EASY_HANDLE:    s="CURLM_BAD_EASY_HANDLE";    break;
      case     CURLM_OUT_OF_MEMORY:      s="CURLM_OUT_OF_MEMORY";      break;
      case     CURLM_INTERNAL_ERROR:     s="CURLM_INTERNAL_ERROR";     break;
      case     CURLM_UNKNOWN_OPTION:     s="CURLM_UNKNOWN_OPTION";     break;
      case     CURLM_LAST:               s="CURLM_LAST";               break;
      default: s="CURLM_unknown";
        break;
    case     CURLM_BAD_SOCKET:         s="CURLM_BAD_SOCKET";
      fprintf(MSG_OUT, "ERROR: %s returns %s\n", where, s);
      /* ignore this error */ 
      return;
    }
    fprintf(MSG_OUT, "ERROR: %s returns %s\n", where, s);
    exit(code);
  }
}
 
 
/* Check for completed transfers, and remove their easy handles */ 
static void check_multi_info(GlobalInfo *g)
{
   //fprintf(MSG_OUT, "Called check_multi_info...");
  char *eff_url;
  CURLMsg *msg;
  int msgs_left;
  struct vmod_curl *c;
  CURL *easy;
  CURLcode res;
 
  fprintf(MSG_OUT, "REMAINING: %d\n", g->still_running);
  while ((msg = curl_multi_info_read(g->multi, &msgs_left))) {
    if (msg->msg == CURLMSG_DONE) {
      easy = msg->easy_handle;
      res = msg->data.result;
      curl_easy_getinfo(easy, CURLINFO_PRIVATE, &c);
      curl_easy_getinfo(easy, CURLINFO_RESPONSE_CODE, &c->status);
      //curl_easy_getinfo(easy, CURLINFO_EFFECTIVE_URL, &eff_url);
      //fprintf(MSG_OUT, "DONE: %s => (%d) %s\n", eff_url, res, conn->error);
      curl_multi_remove_handle(g->multi, easy);
      //free(conn->url);
      curl_easy_cleanup(easy);
      cm_clear_req_headers(c);
      // unlock the request
      //AZ(pthread_mutex_lock(&c->mtx));
      c->curl_handle = NULL;
      //pthread_mutex_unlock(&c->mtx);
      AZ(pthread_mutex_lock(&c->mtx));
	  pthread_cond_signal(&c->cond);
	  pthread_mutex_unlock(&c->mtx);
      //free(conn);
      fprintf(MSG_OUT, "DONE: easy :) message left: %d\n", msgs_left);
    }
  }
}
 
 
 
/* Called by libevent when we get action on a multi socket */ 
static void event_cb(int fd, short kind, void *userp)
{
  //fprintf(MSG_OUT, "Called event_cb...");
  GlobalInfo *g = (GlobalInfo*) userp;
  CURLMcode rc;
 
  int action =
    (kind & EV_READ ? CURL_CSELECT_IN : 0) |
    (kind & EV_WRITE ? CURL_CSELECT_OUT : 0);
 
  rc = curl_multi_socket_action(g->multi, fd, action, &g->still_running);
  mcode_or_die("event_cb: curl_multi_socket_action", rc);
 
  check_multi_info(g);
  if ( g->still_running <= 0 ) {
    fprintf(MSG_OUT, "last transfer done, kill timeout\n");
    if (evtimer_pending(g->timer_event, NULL)) {
      evtimer_del(g->timer_event);
    }
  }
}
 
 
 
/* Called by libevent when our timeout expires */ 
static void timer_cb(int fd, short kind, void *userp)
{
  fprintf(MSG_OUT, "Called timer_cb...");
  GlobalInfo *g = (GlobalInfo *)userp;
  CURLMcode rc;
  (void)fd;
  (void)kind;
 
  rc = curl_multi_socket_action(g->multi,
                                  CURL_SOCKET_TIMEOUT, 0, &g->still_running);
  mcode_or_die("timer_cb: curl_multi_socket_action", rc);
  check_multi_info(g);
}
 
 
 
/* Clean up the SockInfo structure */ 
static void remsock(SockInfo *f)
{
  if (f) {
    if (f->evset)
      event_free(f->ev);
    free(f);
  }
}
 
 
 
/* Assign information to a SockInfo structure */ 
static void setsock(SockInfo*f, curl_socket_t s, CURL*e, int act, GlobalInfo*g)
{
  int kind =
     (act&CURL_POLL_IN?EV_READ:0)|(act&CURL_POLL_OUT?EV_WRITE:0)|EV_PERSIST;
 
  f->sockfd = s;
  f->action = act;
  f->easy = e;
  if (f->evset)
    event_free(f->ev);
  f->ev = event_new(g->evbase, f->sockfd, kind, event_cb, g);
  f->evset = 1;
  event_add(f->ev, NULL);
}
 
 
 
/* Initialize a new SockInfo structure */ 
static void addsock(curl_socket_t s, CURL *easy, int action, GlobalInfo *g)
{
  SockInfo *fdp = calloc(sizeof(SockInfo), 1);
 
  fdp->global = g;
  setsock(fdp, s, easy, action, g);
  curl_multi_assign(g->multi, s, fdp);
}
 
/* CURLMOPT_SOCKETFUNCTION */ 
static int sock_cb(CURL *e, curl_socket_t s, int what, void *cbp, void *sockp)
{
  GlobalInfo *g = (GlobalInfo*) cbp;
  SockInfo *fdp = (SockInfo*) sockp;
  const char *whatstr[]={ "none", "IN", "OUT", "INOUT", "REMOVE" };
 
  //fprintf(MSG_OUT,
          //"socket callback: s=%d e=%p what=%s ", s, e, whatstr[what]);
  if (what == CURL_POLL_REMOVE) {
    //fprintf(MSG_OUT, "\n");
    remsock(fdp);
  }
  else {
    if (!fdp) {
      //fprintf(MSG_OUT, "Adding data: %s\n", whatstr[what]);
      addsock(s, e, what, g);
    }
    else {
      // fprintf(MSG_OUT,
      //         "Changing action from %s to %s\n",
      //         whatstr[fdp->action], whatstr[what]);
      setsock(fdp, s, e, what, g);
    }
  }
  return 0;
}
 
 
/* CURLOPT_WRITEFUNCTION */ 
static size_t write_cb(void *ptr, size_t size, size_t nmemb, void *data)
{
  size_t realsize = size * nmemb;
  ConnInfo *conn = (ConnInfo*) data;
  (void)ptr;
  (void)conn;
  return realsize;
}
