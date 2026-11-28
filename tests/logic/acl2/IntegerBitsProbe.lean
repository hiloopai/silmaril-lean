module

import Silmaril.Logic.ACL2.Standard.IntegerBits.Defs
meta import Silmaril.Logic.ACL2.Standard.IntegerBits.Defs
meta import Silmaril.Logic.ACL2.Standard.Objects.Defs
meta import Mathlib.Data.Int.Bitwise
meta import Mathlib.Data.Nat.Bits
meta import Batteries.Data.Int

open Silmaril.Logic.ACL2.Standard

private def expect (actual expected : Object) : Object := .integer (if actual = expected then 1 else 0)

private def asBit (actual : Object) : IO Object :=
  if actual = .truth then pure (.integer 1)
  else if actual = .nil then pure (.integer 0)
  else throw (IO.userError s!"Expected T or NIL, got {repr actual}")

public def main : IO Unit := do
  let i := Object.integer
  let ratio := Object.rational (Rat.divInt 3 2)
  let complex := Object.ofParts 3 1
  let atom := Object.symbol ((Symbol.ofName? ⟨"ACL2", "A"⟩).get (by decide))
  let wide := i (2 ^ 128)
  let rows : List (String × Object) := [
    ("and-sign", Object.logand [i (-13), i 10]),
    ("and-negative-pair", Object.logand [i (-13), i (-10)]),
    ("and-minus-one", Object.logand [i (-1), i (-13)]),
    ("and-noninteger-left", Object.logand [ratio, i (-1)]),
    ("and-noninteger-right", Object.logand [i (-1), complex]),
    ("and-empty", Object.logand []),
    ("and-single", expect (Object.logand [ratio]) ratio),
    ("and-three", Object.logand [i (-1), i (-13), i 10]),
    ("or-sign", Object.logior [i (-13), i 10]),
    ("or-negative-pair", Object.logior [i (-13), i (-10)]),
    ("or-noninteger-left", Object.logior [atom, i (-13)]),
    ("or-noninteger-right", Object.logior [i 13, ratio]),
    ("or-empty", Object.logior []),
    ("or-single", expect (Object.logior [atom]) atom),
    ("or-three", Object.logior [i 1, i 4, i 16]),
    ("xor-sign", Object.logxor [i (-13), i 10]),
    ("xor-negative-pair", Object.logxor [i (-13), i (-10)]),
    ("xor-noninteger-left", Object.logxor [complex, i (-13)]),
    ("xor-noninteger-right", Object.logxor [i 13, .cons (i 1) (i 2)]),
    ("xor-empty", Object.logxor []),
    ("xor-single", expect (Object.logxor [complex]) complex),
    ("xor-three", Object.logxor [i (-1), i (-13), i 10]),
    ("not-negative", (i (-13)).lognot),
    ("not-noninteger", ratio.lognot),
    ("not-zero", (i 0).lognot),
    ("ash-left", (i (-13)).ash (i 5)),
    ("ash-right-negative", (i (-13)).ash (i (-2))),
    ("ash-right-positive", (i 13).ash (i (-2))),
    ("ash-noninteger-data", complex.ash (i 16)),
    ("ash-noninteger-count", (i (-13)).ash (.rational (Rat.divInt (-3) 2))),
    ("ash-nonnumber-count", (i 13).ash (.string [98, 97, 100])),
    ("ash-wide-left", (i (-1)).ash (i 129)),
    ("ash-wide-right", (i (-13)).ash (i (-129))),
    ("bitp-negative-index", ← asBit ((i (-1)).logbitp (i 3))),
    ("bitp-noninteger-index", ← asBit (ratio.logbitp (i (-13)))),
    ("bitp-noninteger-data", ← asBit ((i 4).logbitp complex)),
    ("bitp-negative-sign", ← asBit ((i 129).logbitp (i (-13)))),
    ("bitp-negative-hole", ← asBit ((i 2).logbitp (i (-13)))),
    ("bitp-wide-positive", ← asBit ((i 128).logbitp wide)),
    ("length-negative", (i (-257)).integerLength),
    ("length-negative-power", (i (-256)).integerLength),
    ("length-minus-one", (i (-1)).integerLength),
    ("length-zero", (i 0).integerLength),
    ("length-noninteger", ratio.integerLength),
    ("length-wide", wide.integerLength)]
  for (label, value) in rows do
    let some result := value.integerValue? | throw (IO.userError s!"{label}: expected integer")
    IO.println s!"BIT {label} {result}"
