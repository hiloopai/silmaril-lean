module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.ConvSem

/-!
# Float track: the conversion primitives on encoded arguments

What `floatCall P` returns for `$wrap__`, `$extend__`, `$trunc__`, `$trunc_sat__`, `$convert__`,
`$promote__`, `$demote__` and `$reinterpret__` at the arguments `$cvtop__`'s clauses pass them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

variable {P : Profile}

theorem asBits?_pctV {N : Nat} (x : BitVec N) : Equiv.ExecBuiltins.asBits? N (pctV x.toNat) = some x :=
  Equiv.ExecBuiltins.asBits?_bvV x

/-- `$wrap__(N, N', i)` is the low `N'` bits, at every width. -/
theorem floatCall_wrap (P : Profile) (N N' : Nat) (x : BitVec N) :
    floatCall P "wrap__" [.val (natV N), .val (natV N'), .val (pctV x.toNat)] =
      some (bvV (x.setWidth N')) := by
  rw [floatCall_eq (by simp [floatNames])]
  show wrapBits N N' (pctV x.toNat) = _
  simp only [wrapBits, asBits?_pctV, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- `$extend__(N, N', sx, i)` is the sign or zero extension, at every width. -/
theorem floatCall_extend (P : Profile) (N N' : Nat) (s : Signedness) (x : BitVec N) :
    floatCall P "extend__" [.val (natV N), .val (natV N'), .val (sxV s), .val (pctV x.toNat)] =
      some (bvV (match s with | .signed => x.signExtend N' | .unsigned => x.setWidth N')) := by
  rw [floatCall_eq (by simp [floatNames])]
  show extendBits N N' (sxV s) (pctV x.toNat) = _
  simp only [extendBits, asBits?_pctV, asSx?_sxV, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem convOpt_numV (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) :
    convOpt P op (numV ⟨op.source, x⟩) =
      some (.opt ((convRes P op x).map fun z => numV ⟨op.target, z⟩)) := by
  simp [convOpt, decNum_numV]

theorem convOne_numV (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) :
    convOne P op (numV ⟨op.source, x⟩) = (convRes P op x).map fun z => numV ⟨op.target, z⟩ := by
  cases hc : convRes P op x <;> simp [convOne, decNum_numV, hc]

theorem convList_numV (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) :
    convList P op (numV ⟨op.source, x⟩) = some (.list ((bitsWhere op.target.width
      (fun z => convertP P op x (.ok z))).map fun z => numV ⟨op.target, z⟩)) := by
  simp [convList, decNum_numV]

/-- `$trunc__(N, N', sx, f)`. -/
theorem floatCall_trunc (P : Profile) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    floatCall P "trunc__" [.val (natV f.width), .val (natV i.width), .val (sxV s),
      .val (floatV f x)] =
      some (.opt ((convRes P (.trunc f i s) x).map fun z => numV ⟨.int i, z⟩)) := by
  rw [floatCall_eq (by simp [floatNames])]
  show (do let t ← floatOfWidth f.width; let i' ← intOfWidth i.width
           let sx ← IntNumeric.asSx? (sxV s); convOpt P (.trunc t i' sx) (floatV f x)) = _
  simp only [floatOfWidth_width, intOfWidth_width, asSx?_sxV, Option.bind_eq_bind,
    Option.bind_some]
  exact convOpt_numV P (.trunc f i s) x

/-- `$trunc_sat__(N, N', sx, f)`. -/
theorem floatCall_truncSat (P : Profile) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    floatCall P "trunc_sat__" [.val (natV f.width), .val (natV i.width), .val (sxV s),
      .val (floatV f x)] =
      some (.opt ((convRes P (.truncSat f i s) x).map fun z => numV ⟨.int i, z⟩)) := by
  rw [floatCall_eq (by simp [floatNames])]
  show (do let t ← floatOfWidth f.width; let i' ← intOfWidth i.width
           let sx ← IntNumeric.asSx? (sxV s); convOpt P (.truncSat t i' sx) (floatV f x)) = _
  simp only [floatOfWidth_width, intOfWidth_width, asSx?_sxV, Option.bind_eq_bind,
    Option.bind_some]
  exact convOpt_numV P (.truncSat f i s) x

/-- `$convert__(N, N', sx, i)`. -/
theorem floatCall_convert (P : Profile) (i : IntType) (f : FloatType) (s : Signedness)
    (x : BitVec i.width) :
    floatCall P "convert__" [.val (natV i.width), .val (natV f.width), .val (sxV s),
      .val (pctV x.toNat)] =
      (convRes P (.convert i f s) x).map fun z => numV ⟨.float f, z⟩ := by
  rw [floatCall_eq (by simp [floatNames])]
  show (do let i' ← intOfWidth i.width; let t ← floatOfWidth f.width
           let sx ← IntNumeric.asSx? (sxV s); convOne P (.convert i' t sx) (pctV x.toNat)) = _
  simp only [floatOfWidth_width, intOfWidth_width, asSx?_sxV, Option.bind_eq_bind,
    Option.bind_some]
  exact convOne_numV P (.convert i f s) x

/-- `$promote__(32, 64, f)`. -/
theorem floatCall_promote (P : Profile) (x : BitVec 32) :
    floatCall P "promote__" [.val (natV 32), .val (natV 64), .val (floatV .f32 x)] =
      some (.list ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => numV ⟨.float .f64, z⟩)) := by
  rw [floatCall_eq (by simp [floatNames])]
  exact convList_numV P .promote x

/-- `$demote__(64, 32, f)`. -/
theorem floatCall_demote (P : Profile) (x : BitVec 64) :
    floatCall P "demote__" [.val (natV 64), .val (natV 32), .val (floatV .f64 x)] =
      some (.list ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => numV ⟨.float .f32, z⟩)) := by
  rw [floatCall_eq (by simp [floatNames])]
  exact convList_numV P .demote x

/-- `$reinterpret__(nt_1, nt_2, c)`, at a reinterpretation. -/
theorem floatCall_reinterpret (P : Profile) {op : ConvertOp}
    (hop : reinterpOp? op.source op.target = some op) (x : BitVec op.source.width) :
    floatCall P "reinterpret__" [.val (Vec.numTypeV op.source), .val (Vec.numTypeV op.target),
      .val (numV ⟨op.source, x⟩)] = (convRes P op x).map fun z => numV ⟨op.target, z⟩ := by
  rw [floatCall_eq (by simp [floatNames])]
  show (do let t₁ ← decNumType (Vec.numTypeV op.source); let t₂ ← decNumType (Vec.numTypeV op.target)
           let op' ← reinterpOp? t₁ t₂; convOne P op' (numV ⟨op.source, x⟩)) = _
  simp only [decNumType_numTypeV, hop, Option.bind_eq_bind, Option.bind_some]
  exact convOne_numV P op x

end Silmaril.Wasm.SpecTec.Sim.Floats
