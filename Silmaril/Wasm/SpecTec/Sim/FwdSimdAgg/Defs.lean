module

public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs

/-!
# SpecTec ↔ Core 3.0, round 3 track `fwd-simd-agg`: primitives for `B`

The bitwise SIMD instructions (`v128.not`, `v128.and`, `v128.andnot`, `v128.or`, `v128.xor`,
`v128.bitselect`) reduce in SpecTec through `$vvunop_`, `$vvbinop_`, `$vvternop_`, whose clauses
call the integer primitives at width `$vsizenn(V128) = 128`. `$iand_`, `$ior_`, `$ixor_` are
already answered at every width by family N's `IntNumeric.intCall`; the other three, `$inot_`,
`$iandnot_` and `$ibitselect_`, are declared `hint(builtin)` without clauses
(`3.1-numerics.scalar.spectec:203-214`) and were in no `B`. `vvCall` interprets them by
`Silmaril.Wasm.Numerics` at every width.

`$sx(storagetype) : sx?` (`Original.d418`) has the clauses `$sx(consttype) = ε` and
`$sx(packtype) = S`. Since the typing track's fix (`Sem.argSubOk`) a clause pattern
`consttype <: storagetype` admits only `I32`, `I64`, `F32`, `F64`, `V128`, so `$sx` has **no clause
at a reference type**: `array.copy-le`/`-gt` (`sx? = $sx(zt_2)`) cannot fire on an array of
references, although Core copies it (finding of this track; upstream item U4 in
`docs/projects/spectec/README.md`). `callDef` consults `B` exactly where every clause definitely fails, so
`vvCall` answers `$sx` there with `ε`, the value the specification means for every value type.

`VVB B` says `B` extends `vvCall`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.ExecBuiltins (asBits? binBits unBits)

/-- A ternary integer primitive, read through the value bridge. -/
def ternBits (N : Nat) (f : BitVec N → BitVec N → BitVec N → BitVec N) (a b c : Value) :
    Option Value :=
  match asBits? N a, asBits? N b, asBits? N c with
  | some x, some y, some z => some (bvV (f x y z))
  | _, _, _ => none

/-- `$inot_`, `$iandnot_`, `$ibitselect_`, at the argument shapes the pinned declarations give
them (`N` first, then the operands), and `$sx` where its clauses fail (`ε`). -/
noncomputable def vvCall : IL.Id → List ArgV → Option Value
  | "inot_", [.val (.num (.natN N)), .val a] => unBits N (Silmaril.Wasm.Numerics.inot_ N) a
  | "iandnot_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.iandnot_ N) a b
  | "ibitselect_", [.val (.num (.natN N)), .val a, .val b, .val c] =>
      ternBits N (Silmaril.Wasm.Numerics.ibitselect_ N) a b c
  | "sx", [.val _] => some (.opt none)
  | _, _ => none

/-- `B` extends `vvCall`. -/
def VVB (B : Builtins) : Prop := ∀ x ws v, vvCall x ws = some v → B.call x ws = some v

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
