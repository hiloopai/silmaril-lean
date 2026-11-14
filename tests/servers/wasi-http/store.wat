  ;; `storeBody` (Silmaril.Servers.WasiFs): a file-backed key-value store over the first
  ;; preopen. The representation of a target is the file `keyName` of its path-with-query
  ;; (`k` and the octets in lowercase hexadecimal, `n` for none).

  ;; 0x110000: the file name (at most 0x10000 bytes, else 500).
  (global $name i32 (i32.const 0x110000))

  ;; `keyName (pathOf np)` at `$name`; its length, or -1 when it does not fit.
  (func $key_name (param $r i32) (result i32)
    (local $p i32) (local $n i32) (local $q i32) (local $b i32) (local $d i32)
    (call $req_path (local.get $r) (global.get $ret))
    (if (i32.eqz (i32.load8_u (global.get $ret)))
      (then (i32.store8 (global.get $name) (i32.const 0x6e)) (return (i32.const 1))))
    (local.set $p (i32.load offset=4 (global.get $ret)))
    (local.set $n (i32.load offset=8 (global.get $ret)))
    (if (i32.gt_u (local.get $n) (i32.const 0x7fff)) (then (return (i32.const -1))))
    (i32.store8 (global.get $name) (i32.const 0x6b))
    (local.set $q (i32.add (global.get $name) (i32.const 1)))
    (block $done
      (loop $l
        (br_if $done (i32.eqz (local.get $n)))
        (local.set $b (i32.load8_u (local.get $p)))
        ;; hexDigit d = '0' + d for d < 10, else 'a' + (d - 10)
        (local.set $d (i32.shr_u (local.get $b) (i32.const 4)))
        (i32.store8 (local.get $q) (i32.add (local.get $d)
          (select (i32.const 48) (i32.const 87) (i32.lt_u (local.get $d) (i32.const 10)))))
        (local.set $d (i32.and (local.get $b) (i32.const 15)))
        (i32.store8 offset=1 (local.get $q) (i32.add (local.get $d)
          (select (i32.const 48) (i32.const 87) (i32.lt_u (local.get $d) (i32.const 10)))))
        (local.set $q (i32.add (local.get $q) (i32.const 2)))
        (local.set $p (i32.add (local.get $p) (i32.const 1)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $l)))
    (i32.sub (local.get $q) (global.get $name)))

  ;; `getPath`: open the file and read it whole: `200` with its contents (none for `HEAD`),
  ;; `404` for `error(no-entry)`, else `500`.
  (func $get (param $o i32) (param $n i32) (param $head i32)
    (local $fd i32)
    (local.set $fd (call $open (call $pre) (global.get $name) (local.get $n) (i32.const 0)))
    (if (i32.eq (local.get $fd) (i32.const -1))
      (then
        (if (call $no_entry (i32.const 4))
          (then (return (call $status (local.get $o) (i32.const 404)))))
        (return (call $fail (local.get $o)))))
    (call $fd_read (local.get $fd) (i64.const -1) (i64.const 0) (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
      (i32.load offset=4 (global.get $ret))
      (select (i32.const 0) (i32.load offset=8 (global.get $ret)) (local.get $head))))

  ;; `putFile` of the `len` octets at 0x10000: does the file exist? Create (and truncate) it,
  ;; write the contents: `204` if it existed, `201` if not.
  (func $put_file (param $o i32) (param $n i32) (param $len i32)
    (local $d i32) (local $old i32) (local $fd i32)
    (local.set $d (call $pre))
    (local.set $old (call $open (local.get $d) (global.get $name) (local.get $n) (i32.const 0)))
    (local.set $fd (call $open (local.get $d) (global.get $name) (local.get $n) (i32.const 1)))
    (if (i32.eq (local.get $fd) (i32.const -1)) (then (return (call $fail (local.get $o)))))
    (call $fd_write (local.get $fd) (i32.const 0x10000) (local.get $len) (i64.const 0)
      (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (call $status (local.get $o)
      (select (i32.const 201) (i32.const 204) (i32.eq (local.get $old) (i32.const -1)))))

  ;; `putPath`: read the request body as echo does (at most 16 reads of 65536 octets), then
  ;; `putFile`.
  (func $put (param $o i32) (param $r i32) (param $n i32)
    (local $s i32) (local $fuel i32) (local $acc i32) (local $k i32)
    (call $req_consume (local.get $r) (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (call $in_stream (i32.load offset=4 (global.get $ret)) (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (local.set $s (i32.load offset=4 (global.get $ret)))
    (local.set $fuel (i32.const 16))
    (loop $l
      (if (i32.eqz (local.get $fuel)) (then (return (call $fail (local.get $o)))))
      (local.set $fuel (i32.sub (local.get $fuel) (i32.const 1)))
      (call $in_read (local.get $s) (i64.const 65536) (global.get $ret))
      (if (i32.eqz (i32.load8_u (global.get $ret)))
        (then
          (local.set $k (i32.load offset=8 (global.get $ret)))
          (memory.copy (i32.add (i32.const 0x10000) (local.get $acc))
            (i32.load offset=4 (global.get $ret)) (local.get $k))
          (local.set $acc (i32.add (local.get $acc) (local.get $k)))
          (br $l)))
      (if (i32.eq (i32.load8_u offset=4 (global.get $ret)) (i32.const 1))
        (then (return (call $put_file (local.get $o) (local.get $n) (local.get $acc))))))
    (call $fail (local.get $o)))

  ;; `delPath`: unlink the file: `204`, `404` for `error(no-entry)`, else `500`.
  (func $delete (param $o i32) (param $n i32)
    (call $unlink_at (call $pre) (global.get $name) (local.get $n) (global.get $ret))
    (if (i32.eqz (i32.load8_u (global.get $ret)))
      (then (return (call $status (local.get $o) (i32.const 204)))))
    (if (call $no_entry (i32.const 1)) (then (return (call $status (local.get $o) (i32.const 404)))))
    (call $fail (local.get $o)))

  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (local $m i32) (local $n i32)
    (call $req_method (local.get $r) (global.get $ret))
    (local.set $m (i32.load8_u (global.get $ret)))
    (local.set $n (call $key_name (local.get $r)))
    (if (i32.eq (local.get $n) (i32.const -1)) (then (return (call $fail (local.get $o)))))
    (block $other (block $options (block $na (block $delete (block $put (block $head (block $get
      (br_table $get $head $na $put $delete $na $options $na $na $other (local.get $m)))
      (return (call $get (local.get $o) (local.get $n) (i32.const 0))))
      (return (call $get (local.get $o) (local.get $n) (i32.const 1))))
      (return (call $put (local.get $o) (local.get $r) (local.get $n))))
      (return (call $delete (local.get $o) (local.get $n))))
      (return (call $status (local.get $o) (i32.const 405))))
      (return (call $status (local.get $o) (i32.const 204))))
    (call $status (local.get $o) (i32.const 501)))
