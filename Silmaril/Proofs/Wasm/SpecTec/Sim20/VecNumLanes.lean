module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumB

/-!
# What `vecNB P` answers, lane by lane

`vecNB P` answers `$vunop_(Fnn X M, op, c)` with every result V2 permits
(`VecFloatUnOpResult P s op c`). This module shows that this set is the one the script's clause
describes when its `if` premises are read as binding: draw each lane from the scalar results
(`Numerics.floatUnOpP P t op`, the answers 's `$fabs_` … under `Floats.FloatB P`), take
the set product, and put the lanes back with `$inv_lanes_` (`vecFloatUnOpResult_lanes`). Both NaN
policies of the profile are covered. So the answers of `vecNB P` are not chosen to fit: they are
the lane-wise reading of `3-numerics.spectec:464-491`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

theorem forall₂_eq_map_iff {α β : Type} (f : α → β) :
    ∀ (xs : List α) (zs : List β), List.Forall₂ (fun x z => z = f x) xs zs ↔ zs = xs.map f
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, z :: zs => by
    rw [List.forall₂_cons, forall₂_eq_map_iff f xs zs]
    simp

/-- **V2's float `vunop` results are the set product of the lane-wise scalar results**, put back
with `$inv_lanes_`. -/
theorem vecFloatUnOpResult_lanes (P : Profile) (s : FloatShape) (op : FloatUnOp) (c r : BitVec 128) :
    VecFloatUnOpResult P s op c r ↔ ∃ zs, List.Forall₂ (Numerics.floatUnOpP P s.floatType op)
      (s.lanesOf c) zs ∧ r = s.invLanes zs := by
  simp only [VecFloatUnOpResult, Numerics.VecFloatUnOpRel]
  cases hP : P.nan with
  | spec =>
    have hR : Numerics.floatUnOpP P s.floatType op = Numerics.floatUnOpRel s.floatType op := by
      funext x z
      simp [Numerics.floatUnOpP, hP]
    simp only [hR, Numerics.vunopFloatRel, Numerics.invLanesSet, Numerics.lanesRel1,
      FloatShape.invLanes]
  | canonical =>
    have hR : Numerics.floatUnOpP P s.floatType op =
        fun x z => z = Numerics.floatUnOp s.floatType op x := by
      funext x z
      simp [Numerics.floatUnOpP, hP]
    simp only [hR, forall₂_eq_map_iff, Numerics.vunopFloat]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨zs, hz, h⟩ => hz ▸ h⟩

end Silmaril.Wasm.SpecTec.Sim20.VecNum
