module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Slots
public import Silmaril.Proofs.Wasm.Examples.Farkas.Arith

@[expose] public section

/-!
# The Farkas checker: the machine steps

`rowM`, `entryM`: what `row` and `entry` do to the machine state, written as the `i64`/`i32`
operations of the bodies (`Silmaril.Proofs.Wasm.Examples.Farkas.Bodies` shows the bodies compute
them).
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Numerics

/-- Signed `x < v`, as the module computes it. -/
abbrev ltS (x : BitVec 64) (v : Int) : BitVec 32 := intRelOp .i64 (.lt .signed) x (BitVec.ofInt 64 v)
/-- Signed `x > v`, as the module computes it. -/
abbrev gtS (x : BitVec 64) (v : Int) : BitVec 32 := intRelOp .i64 (.gt .signed) x (BitVec.ofInt 64 v)

/-- **`row(y, b)`** on the machine state. -/
def rowM (m : Mach) (y b : BitVec 64) : Mach where
  bad := m.bad ||| ltS y 0 ||| gtS y cB ||| ltS b (-cB) ||| gtS b cB ||| ltS (m.vb + y * b) (-aB) |||
    gtS (m.vb + y * b) aB
  hr := 1
  y := y
  vb := m.vb + y * b
  mem := m.mem

/-- **`entry(j, a)`** on the machine state: slot `j mod nVars` gets `acc + y a`. -/
def entryM (m : Mach) (j : BitVec 32) (a : BitVec 64) : Mach where
  bad := m.bad ||| intTestOp .i32 .eqz m.hr ||| intRelOp .i32 (.ge .unsigned) j (BitVec.ofNat 32 nVars) ||| ltS a (-cB) |||
    gtS a cB ||| ltS (slot m.mem (j.toNat % nVars) + m.y * a) (-aB) |||
    gtS (slot m.mem (j.toNat % nVars) + m.y * a) aB
  hr := m.hr
  y := m.y
  vb := m.vb
  mem := setSlot m.mem (j.toNat % nVars) (slot m.mem (j.toNat % nVars) + m.y * a)

end Silmaril.Wasm.Examples.Farkas
