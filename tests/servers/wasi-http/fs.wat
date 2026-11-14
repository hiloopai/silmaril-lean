  ;; Shared functions of the filesystem servers (store, static). build.sh puts them after
  ;; common.wat and before one server's part.

  ;; `failResp`: `500` without content.
  (func $fail (param $o i32)
    (call $answer (local.get $o) (i32.const 500) (i32.const 0) (i32.const 0) (i32.const 0)
      (i32.const 0)))

  ;; `answer` without header fields or content.
  (func $status (param $o i32) (param $s i32)
    (call $answer (local.get $o) (local.get $s) (i32.const 0) (i32.const 0) (i32.const 0)
      (i32.const 0)))

  ;; `preOf`: the descriptor of the first preopen (0 when there is none).
  (func $pre (result i32)
    (call $get_dirs (global.get $ret))
    (if (result i32) (i32.load offset=4 (global.get $ret))
      (then (i32.load (i32.load (global.get $ret))))
      (else (i32.const 0))))

  ;; `open-at(d, {}, name, {create, truncate}?, {read, write?})`; `openFd` of the answer: the
  ;; descriptor, or -1 with the error code at `ret + 4`.
  (func $open (param $d i32) (param $p i32) (param $n i32) (param $create i32) (result i32)
    (call $open_at (local.get $d) (i32.const 0) (local.get $p) (local.get $n)
      (select (i32.const 9) (i32.const 0) (local.get $create))
      (select (i32.const 3) (i32.const 1) (local.get $create))
      (global.get $ret))
    (if (result i32) (i32.load8_u (global.get $ret))
      (then (i32.const -1))
      (else (i32.load offset=4 (global.get $ret)))))

  ;; `isNoEntry`: the error code at `ret + off` is `no-entry` (20).
  (func $no_entry (param $off i32) (result i32)
    (i32.eq (i32.load8_u (i32.add (global.get $ret) (local.get $off))) (i32.const 20)))
