  ;; The static file server of Silmaril.Servers.State.OwnedFs (`staticAnswer (docRoot root)`)
  ;; over the first preopen: `GET` answers `200` with the file the target's path names, or
  ;; `404`; `HEAD` the same without content; other methods `405` with `Allow: GET, HEAD`.
  ;; `docRoot`: the path before `?`, without empty and `.` components; a `..` component, or no
  ;; component at all, names no file. A name that cannot be opened or read is `404` too.

  (data (i32.const 0x100) "Allow")
  (data (i32.const 0x108) "GET, HEAD")
  ;; 0x140: the header line of `allowGetHead` (`addFields`: name and value, pointers, lengths).
  (data (i32.const 0x140) "\00\01\00\00\05\00\00\00\08\01\00\00\09\00\00\00")

  ;; 0x110000: the relative path (at most 0x10000 bytes).
  (global $name i32 (i32.const 0x110000))

  ;; `docRoot` of the request `r` at `$name`, components joined by `/`; its length, or -1
  ;; when it names no file.
  (func $doc_root (param $r i32) (result i32)
    (local $p i32) (local $end i32) (local $s i32) (local $k i32) (local $q i32)
    (call $req_path (local.get $r) (global.get $ret))
    (if (i32.eqz (i32.load8_u (global.get $ret))) (then (return (i32.const -1))))
    (local.set $p (i32.load offset=4 (global.get $ret)))
    (local.set $end (i32.add (local.get $p) (i32.load offset=8 (global.get $ret))))
    (if (i32.gt_u (i32.load offset=8 (global.get $ret)) (i32.const 0xffff))
      (then (return (i32.const -1))))
    (local.set $q (global.get $name))
    (block $done
      (loop $comp
        ;; skip `/`; stop at the end or at `?`
        (block $start
          (loop $skip
            (br_if $done (i32.ge_u (local.get $p) (local.get $end)))
            (br_if $done (i32.eq (i32.load8_u (local.get $p)) (i32.const 0x3f)))
            (br_if $start (i32.ne (i32.load8_u (local.get $p)) (i32.const 0x2f)))
            (local.set $p (i32.add (local.get $p) (i32.const 1)))
            (br $skip)))
        ;; one component, from `$s`, `$k` octets
        (local.set $s (local.get $p))
        (block $stop
          (loop $in
            (br_if $stop (i32.ge_u (local.get $p) (local.get $end)))
            (br_if $stop (i32.eq (i32.load8_u (local.get $p)) (i32.const 0x2f)))
            (br_if $stop (i32.eq (i32.load8_u (local.get $p)) (i32.const 0x3f)))
            (local.set $p (i32.add (local.get $p) (i32.const 1)))
            (br $in)))
        (local.set $k (i32.sub (local.get $p) (local.get $s)))
        ;; `.` is dropped, `..` names no file
        (if (i32.and (i32.eq (local.get $k) (i32.const 1))
              (i32.eq (i32.load8_u (local.get $s)) (i32.const 0x2e)))
          (then (br $comp)))
        (if (i32.and (i32.eq (local.get $k) (i32.const 2))
              (i32.eq (i32.load16_u (local.get $s)) (i32.const 0x2e2e)))
          (then (return (i32.const -1))))
        (if (i32.ne (local.get $q) (global.get $name))
          (then (i32.store8 (local.get $q) (i32.const 0x2f))
            (local.set $q (i32.add (local.get $q) (i32.const 1)))))
        (memory.copy (local.get $q) (local.get $s) (local.get $k))
        (local.set $q (i32.add (local.get $q) (local.get $k)))
        (br $comp)))
    (if (i32.eq (local.get $q) (global.get $name)) (then (return (i32.const -1))))
    (i32.sub (local.get $q) (global.get $name)))

  ;; `getAnswer` of the file at `$name`, `n` octets (no content for `HEAD`).
  (func $get (param $o i32) (param $n i32) (param $head i32)
    (local $fd i32)
    (if (i32.eq (local.get $n) (i32.const -1))
      (then (return (call $status (local.get $o) (i32.const 404)))))
    (local.set $fd (call $open (call $pre) (global.get $name) (local.get $n) (i32.const 0)))
    (if (i32.eq (local.get $fd) (i32.const -1))
      (then (return (call $status (local.get $o) (i32.const 404)))))
    (call $fd_read (local.get $fd) (i64.const -1) (i64.const 0) (global.get $ret))
    (if (i32.load8_u (global.get $ret))
      (then (return (call $status (local.get $o) (i32.const 404)))))
    (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
      (i32.load offset=4 (global.get $ret))
      (select (i32.const 0) (i32.load offset=8 (global.get $ret)) (local.get $head))))

  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (local $m i32)
    (call $req_method (local.get $r) (global.get $ret))
    (local.set $m (i32.load8_u (global.get $ret)))
    (if (i32.eqz (local.get $m))
      (then (return (call $get (local.get $o) (call $doc_root (local.get $r)) (i32.const 0)))))
    (if (i32.eq (local.get $m) (i32.const 1))
      (then (return (call $get (local.get $o) (call $doc_root (local.get $r)) (i32.const 1)))))
    (call $answer (local.get $o) (i32.const 405) (i32.const 0x140) (i32.const 1) (i32.const 0)
      (i32.const 0)))
