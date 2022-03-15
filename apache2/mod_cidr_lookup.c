/* Licensed to KLab Inc. <http://www.klab.org/> (KLab) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * KLab licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * mod_cidr_lookup.c -- lookup CIDR blocks and set CDIR name to
 *                      request header and environment variable.
 *
 * please refer to our project site for overview, installation,
 * configuration and more.
 *
 * http://sourceforge.net/projects/modcidrlookup/
 *
 */

#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "httpd.h"
#include "http_config.h"
#include "http_protocol.h"
#include "http_request.h"
#include "http_log.h"
#include "ap_config.h"
#include "apr_strings.h"
#include "apr_fnmatch.h"

#ifndef CIDR_TABLE_BITS
#  define CIDR_TABLE_BITS 8   /* 8 or 16: 16 is bit faster but use mooooooore memory. */
#endif
#define CIDR_TABLE_SIZE (1 << CIDR_TABLE_BITS)

#define LINE_SIZE 256

typedef struct CIDR_TRIE {
  const char       *name;
  uint32_t          bits;
  struct CIDR_TRIE *child[CIDR_TABLE_SIZE];
} CIDR_TRIE;

/* borrow from server/config.c */
typedef struct {
  char *fname;
} fnames;

static int fname_alphasort(const void *fn1, const void *fn2)
{
  const fnames *f1 = fn1;
  const fnames *f2 = fn2;

  return strcmp(f1->fname,f2->fname);
}


module AP_MODULE_DECLARE_DATA cidr_lookup_module;

#ifdef DEBUG
  #define _dprint(s)         ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, s)
  #define _dprintf(f,s)      ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r, f, s)
  #define _dprintp(f,s)      ap_log_perror(APLOG_MARK, APLOG_ERR, 0, p, f, s)
  #define _dprintpx(p,f,...) ap_log_perror(APLOG_MARK, APLOG_ERR, 0, p, f, __VA_ARGS__)
#else
  #define _dprint(s)
  #define _dprintf(f,s)
  #define _dprintp(f,s)
  #define _dprintpx(f,s,...)
#endif

static int itonetmask(int n, uint32_t *netmask)
{
  uint32_t m;

  if (n < 0 || 32 < n) return 0;

  m = 1UL << (32 - n);
  --m;
  *netmask = ~m;
  return 1;
}

static int is_leaf(const CIDR_TRIE *pt) {
  return pt->child[0] == pt;
}

static CIDR_TRIE *new_trie_node(apr_pool_t *pool) {
  int i;
  CIDR_TRIE *pt = apr_palloc(pool, sizeof(CIDR_TRIE));

  pt->name = 0;
  pt->bits = 0;
  for (i = 0; i < CIDR_TABLE_SIZE; ++i)
    pt->child[i] = pt;
  return pt;
}

static void init_root(apr_pool_t *pool, CIDR_TRIE *trie_root)
{
  int i;
  CIDR_TRIE *nullnode;

  nullnode = new_trie_node(pool);
  for (i = 0; i < CIDR_TABLE_SIZE; ++i)
    trie_root->child[i] = nullnode;
}

static CIDR_TRIE* digg_trie(apr_pool_t *pool, CIDR_TRIE *child) {
  int i;
  CIDR_TRIE *parent = new_trie_node(pool);

  for (i = 0; i < CIDR_TABLE_SIZE; ++i)
    parent->child[i] = child;
  return parent;
}

static int update_leaf(CIDR_TRIE *pt, CIDR_TRIE *leaf)
{
  int used = 0;
  int i;

  for (i = 0; i < CIDR_TABLE_SIZE; ++i) {
    CIDR_TRIE *next = pt->child[i];
    if (is_leaf(next)) {
      if (next->bits < leaf->bits) {
        pt->child[i] = leaf;
        used = 1;
      }
    }
    else {
      used |= update_leaf(next, leaf);
    }
  }
  return used;
}

static char *get_cidr_name(const char *name)
{
  char *base;
  char  path[PATH_MAX];

  strcpy(path, name);
  base = basename(path);

  return strdup(base);
}

static int read_cidr_file(apr_pool_t *pool, const char *filename, CIDR_TRIE *trie_root)
{
  size_t    len;
  char      line[LINE_SIZE];
  char     *p  = line;
  char     *type;
  uint32_t  ad;
  uint32_t  nm = 0xffffffff;
  char      ip[64];
  FILE     *f;

  f = fopen(filename, "r");
  if (f == NULL) {
    ap_log_perror(APLOG_MARK, APLOG_ERR, errno, pool, "cannot open file: %s", filename);
    return -1;
  }

  type = get_cidr_name(filename);

  while (fgets(line, LINE_SIZE, f)) {
    if (*p == '#' || *p == '\r' || *p == '\n')
      continue;

    for (len = strlen(line) - 1; len > 0; len--) {
      if (strchr(" \t\r\n", line[len]) != NULL) {
        // strip whitespace
        line[len] = '\0';
      } else if (line[len] == '/') {
        // for sscanf
        line[len] = ' ';
        break;
      }
    }

    len = 32;
    if (sscanf(line, "%s%ld", ip, &len) < 1) {
      ap_log_perror(APLOG_MARK, APLOG_WARNING, errno, pool,
                    "read error: %s(%s/%ld)\n", line, ip, len);
    } else {
      if (!inet_aton(ip, (struct in_addr *)&ad)) {
        ap_log_perror(APLOG_MARK, APLOG_WARNING, errno, pool,
                      "ip addr error: %s\n", line);
      }
      if (!itonetmask(len,&nm)) {
        ap_log_perror(APLOG_MARK, APLOG_WARNING, errno, pool,
                      "netmask error: %s\n", line);
      }

      ad = ntohl(ad);
      ad &= nm;

      {
        CIDR_TRIE *pt     = trie_root;
        CIDR_TRIE *p_leaf = new_trie_node(pool);

        p_leaf->name = type;
        p_leaf->bits = len;

        while (len > CIDR_TABLE_BITS) {
          int b = ad >> (32 - CIDR_TABLE_BITS);
          CIDR_TRIE *next = pt->child[b];
          if (is_leaf(next)) {
            pt->child[b] = next = digg_trie(pool, next);
          }
          pt = next;
          ad <<= CIDR_TABLE_BITS;
          len -= CIDR_TABLE_BITS;
        }
        {
          int i;
          const int bmin = ad >> (32 - CIDR_TABLE_BITS);
          const int bmax = bmin + (1 << (CIDR_TABLE_BITS - len));
          int used = 0; // delete p_leaf if it is not used.
          for (i = bmin; i < bmax; ++i) {
            CIDR_TRIE *target = pt->child[i];
            if (is_leaf(target)) {
              if (target->bits < p_leaf->bits) {
                pt->child[i] = p_leaf;
                used = 1;
              }
            }
            else {
              int j;
              for (j = 0; j < CIDR_TABLE_SIZE; ++j) {
                used |= update_leaf(target, p_leaf);
              }
            }
          }
        }
      } /* CIDR_TRIE */

    }
  } /* while */

  fclose(f);

  return 0;
}

static int process_cidr_file(cmd_parms *cmd, const char *filename, CIDR_TRIE *trie_root)
{

  _dprintpx(cmd->temp_pool, "%s", "process cidr files");
  /* borrow from server/config.c */
  if (!apr_fnmatch_test(filename)) {
    _dprintpx(cmd->temp_pool, "  [_] %s", filename);
    return read_cidr_file(cmd->pool, filename, trie_root);
  } else {
    apr_dir_t *dirp;
    apr_finfo_t dirent;
    apr_array_header_t *candidates = NULL;
    fnames *fnew;
    apr_status_t rv;
    char *path = apr_pstrdup(cmd->temp_pool, filename);
    char *pattern = NULL;

    pattern = ap_strrchr(path, '/');
    AP_DEBUG_ASSERT(pattern != NULL); /* path must be absolute. */
    *pattern++ = '\0';

    if (apr_fnmatch_test(path)) {
      ap_log_perror(APLOG_MARK, APLOG_ERR, errno, cmd->temp_pool, "Wildcard patterns not pallowed in Include %s", filename);
      return -1;
    }

    if (!ap_is_directory(cmd->temp_pool, path)){
      ap_log_perror(APLOG_MARK, APLOG_ERR, errno, cmd->temp_pool, "Include directory '%s' not found", path);
      return -1;
    }

    if (!apr_fnmatch_test(pattern)) {
      ap_log_perror(APLOG_MARK, APLOG_ERR, errno, cmd->temp_pool, "Must include a wildcard pattern for Include %s", filename);
      return -1;
    }

    /*
     * first course of business is to grok all the directory
     * entries here and store 'em away. Recall we need full pathnames
     * for this.
     */
    rv = apr_dir_open(&dirp, path, cmd->temp_pool);
    if (rv != APR_SUCCESS) {
      char errmsg[120];
      ap_log_perror(APLOG_MARK, APLOG_ERR, errno, cmd->temp_pool, "Could not open config directory %s: %s", path, apr_strerror(rv, errmsg, sizeof errmsg));
      return -1;
    }

    candidates = apr_array_make(cmd->temp_pool, 1, sizeof(filename));
    while (apr_dir_read(&dirent, APR_FINFO_DIRENT, dirp) == APR_SUCCESS) {
      /* strip out '.' and '..' */
      if (strcmp(dirent.name, ".")
          && strcmp(dirent.name, "..")
          && (apr_fnmatch(pattern, dirent.name,
                          APR_FNM_PERIOD) == APR_SUCCESS)) {
        fnew = (fnames *) apr_array_push(candidates);
        fnew->fname = ap_make_full_path(cmd->temp_pool, path, dirent.name);
      }
    }

    apr_dir_close(dirp);
    if (candidates->nelts != 0) {
      int r, current;

      qsort((void *) candidates->elts, candidates->nelts,
            sizeof(fnames), fname_alphasort);

      /*
       * Now recurse these... we handle errors and subdirectories
       * via the recursion, which is nice
       */
      for (current = 0; current < candidates->nelts; ++current) {
        fnew = &((fnames *) candidates->elts)[current];
        _dprintpx(cmd->temp_pool, "  [%d] %s", current, fnew->fname);
        if (ap_is_directory(cmd->temp_pool, fnew->fname)) {
          _dprintpx(cmd->temp_pool, "    %s", "SKIP because directory");
          continue;
        }
        r = read_cidr_file(cmd->pool, fnew->fname, trie_root);
        if (r == -1) {
          return -1;
        }
      }
    }
  }

  return 0;
}

static const char *read_cidr(cmd_parms *cmd, void *trie_root_,
                             const char *filename)
{
  int rv;
  CIDR_TRIE *trie_root = trie_root_;

  trie_root->name = "R"; /* mark indicate trie_root has CIDRFile directive */

  rv = process_cidr_file(cmd, filename, trie_root);
  if (rv == -1) {
    return "failed to read cidr data";
  }

  return NULL;
}

static const char *lookup_cidr(request_rec *r, CIDR_TRIE *pt)
{
  apr_sockaddr_t *sockaddr;
  uint8_t        *addr;

#if AP_SERVER_MINORVERSION_NUMBER >= 4
  sockaddr = r->useragent_addr;
#else
  sockaddr = r->connection->remote_addr;
#endif

#if APR_HAVE_IPV6
  if (sockaddr->family == AF_INET6 &&
      IN6_IS_ADDR_V4MAPPED(&sockaddr->sa.sin6.sin6_addr)) {
    addr = (uint8_t *)&((uint32_t *)sockaddr->ipaddr_ptr)[3];
  } else
#endif
    {
      addr = sockaddr->ipaddr_ptr;
    }

#if CIDR_TABLE_BITS == 8
  pt = pt->child[*addr++];
  pt = pt->child[*addr++];
  pt = pt->child[*addr++];
  pt = pt->child[*addr++];
#elif CIDR_TABLE_BITS == 16
  pt = pt->child[addr[0] * 256 + addr[1]];
  pt = pt->child[addr[2] * 256 + addr[3]];
#else
#error CIDR_TABLE_BITS must be 8 or 16.
#endif

  return pt->name;
}

static void *create_cidr_config(apr_pool_t *p)
{
  CIDR_TRIE *pt = new_trie_node(p);

  init_root(p, pt);
  return pt;
}

static void *create_cidr_config_dir(apr_pool_t *p, char *dummy)
{

  return create_cidr_config(p);
}

static const command_rec cidr_module_cmds[] =
  {
    AP_INIT_TAKE1("CIDRFile", read_cidr,
                  NULL,
                  ACCESS_CONF | RSRC_CONF,
                  "path to CIDR data file"),
    { NULL },
  };

static int fixup_cidr_info(request_rec *r)
{
  const char *type;
  CIDR_TRIE *trie_root = ap_get_module_config(r->per_dir_config,
                                              &cidr_lookup_module);

  if (trie_root->name == NULL)
    return DECLINED;

  type = lookup_cidr(r, trie_root);

  apr_table_setn(r->subprocess_env, "X_CLIENT_TYPE", type);
  apr_table_setn(r->headers_in,     "X-Client-Type", type);

  return OK;
}

static void cidr_register_hooks(apr_pool_t *p)
{
  static const char * const suc[] = { "mod_setenvif.c", NULL };

  ap_hook_post_read_request(fixup_cidr_info, NULL, suc, APR_HOOK_MIDDLE);
  ap_hook_header_parser(fixup_cidr_info, NULL, suc, APR_HOOK_MIDDLE);
}

module AP_MODULE_DECLARE_DATA cidr_lookup_module = {
  STANDARD20_MODULE_STUFF,
  create_cidr_config_dir,  /* create per-dir    config structures */
  NULL,                    /* merge  per-dir    config structures */
  NULL,                    /* create per-server config structures */
  NULL,                    /* merge  per-server config structures */
  cidr_module_cmds,        /* table of config file commands       */
  cidr_register_hooks      /* register hooks                      */
};

