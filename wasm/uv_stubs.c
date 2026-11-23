// The Lean runtime's io.cpp still calls a handful of libuv filesystem functions on
// Emscripten (upstream links a patched libuv for that). In the browser there is no
// filesystem worth talking to, so these fail with UV_ENOSYS: the corresponding Lean
// IO actions (stat/lstat, link, unlink, temp files/dirs) return an IO error.
// Upstream: open PR leanprover/lean4#13298 guards the temp-file calls (uv_os_tmpdir,
// uv_fs_mkstemp/mkdtemp, uv_fs_req_cleanup) under LEAN_EMSCRIPTEN; as of 2026-11-23 it
// does not cover uv_fs_stat/lstat/link/unlink, so these stubs stay until upstream does.
#include <uv.h>

int uv_fs_stat(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { (void)l; (void)r; (void)p; (void)cb; return UV_ENOSYS; }
int uv_fs_lstat(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { (void)l; (void)r; (void)p; (void)cb; return UV_ENOSYS; }
int uv_fs_link(uv_loop_t *l, uv_fs_t *r, const char *p, const char *n, uv_fs_cb cb) { (void)l; (void)r; (void)p; (void)n; (void)cb; return UV_ENOSYS; }
int uv_fs_unlink(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { (void)l; (void)r; (void)p; (void)cb; return UV_ENOSYS; }
int uv_fs_mkdtemp(uv_loop_t *l, uv_fs_t *r, const char *t, uv_fs_cb cb) { (void)l; (void)r; (void)t; (void)cb; return UV_ENOSYS; }
int uv_fs_mkstemp(uv_loop_t *l, uv_fs_t *r, const char *t, uv_fs_cb cb) { (void)l; (void)r; (void)t; (void)cb; return UV_ENOSYS; }
void uv_fs_req_cleanup(uv_fs_t *r) { (void)r; }
int uv_os_tmpdir(char *buf, size_t *size) { (void)buf; (void)size; return UV_ENOSYS; }
