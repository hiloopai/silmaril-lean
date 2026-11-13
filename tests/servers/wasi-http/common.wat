  ;; Shared part of the example servers (Silmaril.Servers.WasiExamples): imports, memory,
  ;; allocator and `answer`. build.sh wraps it with one server's part in a module.
  (import "wasi:http/types@0.2.12" "[constructor]fields" (func $fields (result i32)))
  (import "wasi:http/types@0.2.12" "[method]fields.append"
    (func $fields_append (param i32 i32 i32 i32 i32 i32)))
  (import "wasi:http/types@0.2.12" "[constructor]outgoing-response"
    (func $new_resp (param i32) (result i32)))
  (import "wasi:http/types@0.2.12" "[method]outgoing-response.set-status-code"
    (func $set_status (param i32 i32) (result i32)))
  (import "wasi:http/types@0.2.12" "[method]outgoing-response.body"
    (func $resp_body (param i32 i32)))
  (import "wasi:http/types@0.2.12" "[static]response-outparam.set"
    (func $out_set (param i32 i32 i32 i32 i64 i32 i32 i32 i32)))
  (import "wasi:http/types@0.2.12" "[method]outgoing-body.write"
    (func $body_write (param i32 i32)))
  (import "wasi:http/types@0.2.12" "[static]outgoing-body.finish"
    (func $body_finish (param i32 i32 i32 i32)))
  (import "wasi:http/types@0.2.12" "[method]incoming-request.path-with-query"
    (func $req_path (param i32 i32)))
  (import "wasi:http/types@0.2.12" "[method]incoming-request.consume"
    (func $req_consume (param i32 i32)))
  (import "wasi:http/types@0.2.12" "[method]incoming-body.stream"
    (func $in_stream (param i32 i32)))
  (import "wasi:http/types@0.2.12" "[method]incoming-request.headers"
    (func $req_headers (param i32) (result i32)))
  (import "wasi:http/types@0.2.12" "[method]fields.get"
    (func $fields_get (param i32 i32 i32 i32)))
  (import "wasi:io/streams@0.2.12" "[method]output-stream.blocking-write-and-flush"
    (func $stream_write (param i32 i32 i32 i32)))
  (import "wasi:io/streams@0.2.12" "[resource-drop]output-stream"
    (func $stream_drop (param i32)))
  (import "wasi:io/streams@0.2.12" "[method]input-stream.blocking-read"
    (func $in_read (param i32 i64 i32)))

  ;; 0x10: return area (16 bytes). 0x100: constant strings. 0x10000: echo's buffer (1 MiB).
  ;; 0x120000: heap for cabi_realloc (bump allocation, never freed: an instance serves one
  ;; request).
  (memory (export "memory") 19)
  (global $heap (mut i32) (i32.const 0x120000))
  (global $ret i32 (i32.const 0x10))

  (func (export "cabi_realloc") (param $old i32) (param $osize i32) (param $align i32)
      (param $size i32) (result i32)
    (local $p i32) (local $end i32)
    (local.set $p (i32.and (i32.add (global.get $heap) (i32.sub (local.get $align) (i32.const 1)))
      (i32.sub (i32.const 0) (local.get $align))))
    (local.set $end (i32.add (local.get $p) (local.get $size)))
    (if (i32.gt_u (local.get $end) (i32.shl (memory.size) (i32.const 16)))
      (then (if (i32.eq (memory.grow (i32.shr_u (i32.add (i32.sub (local.get $end)
          (i32.shl (memory.size) (i32.const 16))) (i32.const 0xffff)) (i32.const 16)))
          (i32.const -1)) (then unreachable))))
    (if (local.get $osize) (then (memory.copy (local.get $p) (local.get $old) (local.get $osize))))
    (global.set $heap (local.get $end))
    (local.get $p))

  ;; `hOf` of a `result<own<_>>` in the return area: the handle if `ok`, else 0.
  (func $ok_handle (result i32)
    (if (result i32) (i32.load8_u (global.get $ret))
      (then (i32.const 0)) (else (i32.load (i32.add (global.get $ret) (i32.const 4))))))

  ;; `answer o resp` with status `status`, the `nh` header lines at `hdrs` (each four i32s:
  ;; name pointer and length, value pointer and length; `addFields`) and content at `ptr`,
  ;; `len`.
  (func $answer (param $o i32) (param $status i32) (param $hdrs i32) (param $nh i32)
      (param $ptr i32) (param $len i32)
    (local $n1 i32) (local $n2 i32) (local $n4 i32) (local $n6 i32)
    (local.set $n1 (call $fields))
    (block $done
      (loop $l
        (br_if $done (i32.eqz (local.get $nh)))
        (call $fields_append (local.get $n1)
          (i32.load (local.get $hdrs)) (i32.load offset=4 (local.get $hdrs))
          (i32.load offset=8 (local.get $hdrs)) (i32.load offset=12 (local.get $hdrs))
          (global.get $ret))
        (local.set $hdrs (i32.add (local.get $hdrs) (i32.const 16)))
        (local.set $nh (i32.sub (local.get $nh) (i32.const 1)))
        (br $l)))
    (local.set $n2 (call $new_resp (local.get $n1)))
    (drop (call $set_status (local.get $n2) (local.get $status)))
    (call $resp_body (local.get $n2) (global.get $ret))
    (local.set $n4 (call $ok_handle))
    (call $out_set (local.get $o) (i32.const 0) (local.get $n2) (i32.const 0) (i64.const 0)
      (i32.const 0) (i32.const 0) (i32.const 0) (i32.const 0))
    (call $body_write (local.get $n4) (global.get $ret))
    (local.set $n6 (call $ok_handle))
    (call $stream_write (local.get $n6) (local.get $ptr) (local.get $len) (global.get $ret))
    (call $stream_drop (local.get $n6))
    (call $body_finish (local.get $n4) (i32.const 0) (i32.const 0) (global.get $ret)))
