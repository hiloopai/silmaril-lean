  ;; Shared part of the dice servers (Silmaril.Servers.Examples.Dice), after common.wat and
  ;; before dice.wat or dice-buggy.wat, which define the faces:
  ;; * `$roll_face`: the face of `/roll`, from one `get-random-u64`;
  ;; * `$pair_face`: the face of one component of `/pair`, from one `get-random-u64`.
  ;; Routing on the path-with-query, compared octet by octet (a query makes it another path):
  ;; * `/roll` -> 200, content: the decimal digit of `$roll_face`;
  ;; * `/pair` -> 200, content: `<a> <b>`, `a` from the first draw, `b` from the second;
  ;; * any other path-with-query, or none -> 404, content `not found`.
  (data (i32.const 0x100) "/roll")
  (data (i32.const 0x108) "/pair")
  (data (i32.const 0x110) "not found")
  ;; 0x200: the response content (at most three octets).

  ;; The bytes at `p`, `n` are the bytes at `q`, `m` (as in ../wasi-http/route.wat).
  (func $eq (param $p i32) (param $n i32) (param $q i32) (param $m i32) (result i32)
    (if (i32.ne (local.get $n) (local.get $m)) (then (return (i32.const 0))))
    (loop $l
      (if (i32.eqz (local.get $n)) (then (return (i32.const 1))))
      (if (i32.ne (i32.load8_u (local.get $p)) (i32.load8_u (local.get $q)))
        (then (return (i32.const 0))))
      (local.set $p (i32.add (local.get $p) (i32.const 1)))
      (local.set $q (i32.add (local.get $q) (i32.const 1)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br $l))
    (i32.const 0))

  ;; `(x % sides) + 1` of one draw `x`, read as an unsigned u64 (the faces are single digits).
  (func $face (param $sides i64) (result i32)
    (i32.wrap_i64 (i64.add (i64.rem_u (call $random_u64) (local.get $sides)) (i64.const 1))))

  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (local $p i32) (local $n i32)
    (call $req_path (local.get $r) (global.get $ret))
    (if (i32.load8_u (global.get $ret))
      (then
        (local.set $p (i32.load (i32.add (global.get $ret) (i32.const 4))))
        (local.set $n (i32.load (i32.add (global.get $ret) (i32.const 8))))
        (if (call $eq (local.get $p) (local.get $n) (i32.const 0x100) (i32.const 5))
          (then
            (i32.store8 (i32.const 0x200) (i32.add (i32.const 48) (call $roll_face)))
            (return (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
              (i32.const 0x200) (i32.const 1)))))
        (if (call $eq (local.get $p) (local.get $n) (i32.const 0x108) (i32.const 5))
          (then
            ;; the two draws in order: `a` first, then `b`
            (i32.store8 (i32.const 0x200) (i32.add (i32.const 48) (call $pair_face)))
            (i32.store8 (i32.const 0x201) (i32.const 32))
            (i32.store8 (i32.const 0x202) (i32.add (i32.const 48) (call $pair_face)))
            (return (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
              (i32.const 0x200) (i32.const 3)))))))
    (call $answer (local.get $o) (i32.const 404) (i32.const 0) (i32.const 0)
      (i32.const 0x110) (i32.const 9)))
