  ;; Imports of the filesystem servers (store, static): `method` and wasi:filesystem. build.sh
  ;; puts them before common.wat (imports come first in a module).
  (import "wasi:http/types@0.2.12" "[method]incoming-request.method"
    (func $req_method (param i32 i32)))
  (import "wasi:filesystem/preopens@0.2.12" "get-directories" (func $get_dirs (param i32)))
  (import "wasi:filesystem/types@0.2.12" "[method]descriptor.open-at"
    (func $open_at (param i32 i32 i32 i32 i32 i32 i32)))
  (import "wasi:filesystem/types@0.2.12" "[method]descriptor.read"
    (func $fd_read (param i32 i64 i64 i32)))
  (import "wasi:filesystem/types@0.2.12" "[method]descriptor.write"
    (func $fd_write (param i32 i32 i32 i64 i32)))
  (import "wasi:filesystem/types@0.2.12" "[method]descriptor.unlink-file-at"
    (func $unlink_at (param i32 i32 i32 i32)))

