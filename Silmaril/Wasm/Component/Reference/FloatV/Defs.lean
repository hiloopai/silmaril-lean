module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs

/-!
# Floats in variant payloads: definitions

`Reference.Sound.Defs` states the float soundness theorems for floats anywhere except inside
variant payloads (`floatOk`). This header extends the NaN relation and the canonicalisation
through variant payloads, at every type:

* `FloatRelAt R t v v'`: `v'` has the shape of `v` at type `t`, its floats related by `R`;
* `NanAtV prof t v v'` (`FloatRelAt (NanLower prof)`): `v'` is an admissible lowering of `v`
  at type `t` under the component choice profile `prof`: the same shape and discriminants,
  every float (at any depth, including inside variant payloads) related by `NanLower prof`,
  everything else equal. A float in a
  variant payload is lowered by one or two C7 choices (`lowerFloat`, then `encodeFloat` when its
  joined slot is an integer); `NanLower prof` is transitive at every profile, so one step
  covers both;
* `canonAtV t w`: `w` with all its floats canonicalised, including in variant payloads;
* `IRObsFV`, `NanCallsV`, `canonCallsV`, `canonResultsV`, `SeqIRObsFV`: `IRObsF`, `NanCalls`,
  `canonCalls`, `canonResults`, `SeqIRObsF` with these relations.

No restriction on the types is needed: the statements hold for every type.

Litmus: `Litmus.floatVariantS` exports `tag-plus-bits(v: variant { c(f32), cx(u32) }) -> u32`
over the adder core module `binMod .add`: the `f32` payload shares the `i32` joined slot with
the `u32` payload (`joinType f32 i32 = i32`), so lowering an `f32` NaN payload issues two C7
choices.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType)
open Silmaril.Wasm.Component (ValTy)

local notation "IVal" => Silmaril.Wasm.Component.Val

mutual
/-- `w` is related to `v` at type `t` by `R` on the floats (at any depth, variant payloads
included): the same shape and discriminants, everything other than floats equal. -/
def FloatRelAt (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    ValTy → IVal → IVal → Prop
  | .f32, v, w => ∃ x y, v = .f32 x ∧ w = .f32 y ∧ R .f32 x y
  | .f64, v, w => ∃ x y, v = .f64 x ∧ w = .f64 y ∧ R .f64 x y
  | .record ts, v, w => ∃ vs ws, v = .record vs ∧ w = .record ws ∧ FloatRelAtList R ts vs ws
  | .variant cs, v, w => ∃ i p p', v = .variant i p ∧ w = .variant i p' ∧
      FloatRelAtCase R cs i p p'
  | .bool, v, w | .s8, v, w | .u8, v, w | .s16, v, w | .u16, v, w | .s32, v, w | .u32, v, w
  | .s64, v, w | .u64, v, w | .char, v, w => v = w

/-- `FloatRelAt` on lists. -/
def FloatRelAtList (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    List ValTy → List IVal → List IVal → Prop
  | [], vs, ws => vs = [] ∧ ws = []
  | t :: ts, vs, ws => ∃ v vs' w ws', vs = v :: vs' ∧ ws = w :: ws' ∧ FloatRelAt R t v w ∧
      FloatRelAtList R ts vs' ws'

/-- `FloatRelAt` on the payload of case `i`. -/
def FloatRelAtCase (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    List (Option ValTy) → Nat → Option IVal → Option IVal → Prop
  | [], _, p, p' => p = p'
  | c :: _, 0, p, p' => FloatRelAtOpt R c p p'
  | _ :: cs, i + 1, p, p' => FloatRelAtCase R cs i p p'

/-- `FloatRelAt` on an optional payload. -/
def FloatRelAtOpt (R : (f : FloatType) → BitVec f.width → BitVec f.width → Prop) :
    Option ValTy → Option IVal → Option IVal → Prop
  | none, p, p' => p = none ∧ p' = none
  | some t, p, p' => ∃ v w, p = some v ∧ p' = some w ∧ FloatRelAt R t v w
end

/-- `v'` is an admissible lowering of `v` at type `t` under the profile `prof`: the floats
related by `NanLower prof` at any depth (variant payloads included), everything else equal. -/
abbrev NanAtV (prof : ProfileKind) : ValTy → IVal → IVal → Prop := FloatRelAt (NanLower prof)

/-- `NanAtV` on lists. -/
abbrev NanAtVList (prof : ProfileKind) : List ValTy → List IVal → List IVal → Prop :=
  FloatRelAtList (NanLower prof)

mutual
/-- The canonicalisation of all floats of a value of type `t`, variant payloads included. -/
def canonAtV : ValTy → IVal → IVal
  | .f32, .f32 x => .f32 (canonicalizeNaN .f32 x)
  | .f64, .f64 x => .f64 (canonicalizeNaN .f64 x)
  | .record ts, .record vs => .record (canonAtVList ts vs)
  | .variant cs, .variant i p => .variant i (canonAtVCase cs i p)
  | _, v => v

/-- `canonAtV` on lists. -/
def canonAtVList : List ValTy → List IVal → List IVal
  | t :: ts, v :: vs => canonAtV t v :: canonAtVList ts vs
  | _, vs => vs

/-- `canonAtV` on the payload of case `i`. -/
def canonAtVCase : List (Option ValTy) → Nat → Option IVal → Option IVal
  | c :: _, 0, p => canonAtVOpt c p
  | _ :: cs, i + 1, p => canonAtVCase cs i p
  | [], _, p => p

/-- `canonAtV` on an optional payload. -/
def canonAtVOpt : Option ValTy → Option IVal → Option IVal
  | some t, some v => some (canonAtV t v)
  | _, p => p
end

/-- `IRObsF` with floats in variant payloads: the play of the call on the arguments `vs'`, with
returned values reported canonicalised by `canonAtVList`. -/
def IRObsFV {k : Nat} (σ : Silmaril.Games.Strategy (Silmaril.Wasm.Component.sigN 0)
    (Silmaril.Wasm.Component.sigN k)) (j : Fin k) (rts : List ValTy)
    (vs' : List IVal) : Silmaril.Wasm.Component.Reference.Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = (canonAtVList rts ws).map toRefVal ∧
      [.inr (.ask (j, .vals vs')), .inr (.ans (j, .vals vs') (some (.vals ws)))] ∈ σ
  | .traps => [.inr (.ask (j, .vals vs')), .inr (.ans (j, .vals vs') none)] ∈ σ
  | _ => True

/-- `NanCalls` with `NanAtVList`. -/
def NanCallsV (prof : ProfileKind) (c : Simple) :
    List (Fin c.exports.length × List IVal) → List (Fin c.exports.length × List IVal) → Prop :=
  List.Forall₂ fun q q' => q'.1 = q.1 ∧ NanAtVList prof c.exports[q.1].ty.params q.2 q'.2

/-- `canonCalls` with `canonAtVList`. -/
def canonCallsV (c : Simple) (calls : List (Fin c.exports.length × List IVal)) :
    List (Fin c.exports.length × List IVal) :=
  calls.map fun q => (q.1, canonAtVList c.exports[q.1].ty.params q.2)

/-- `canonResults` with `canonAtVList`. -/
def canonResultsV (c : Simple) :
    List (Fin c.exports.length × List IVal) → List (List IVal) → List (List Value.Val)
  | q :: cs, ws :: wss =>
    (canonAtVList c.exports[q.1].ty.results ws).map toRefVal :: canonResultsV c cs wss
  | _, _ => []

/-- `SeqIRObsF` with `canonAtVList`. -/
def SeqIRObsFV (c : Simple)
    (σ : Silmaril.Games.Strategy (Silmaril.Wasm.Component.sigN 0)
      (Silmaril.Wasm.Component.sigN c.toComp.exports.length))
    (calls : List (Fin c.exports.length × List IVal))
    (wss : List (List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) : Outcome → Prop
  | .returns (some rs) => ∃ ws, rs = (canonAtVList c.exports[j].ty.results ws).map toRefVal ∧
      seqMoves c (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ σ
  | .traps => seqMoves c calls wss ++
      [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈ σ
  | _ => True

/-- `tag-plus-bits(v: variant { c(f32), cx(u32) }) -> u32` over the adder core module: the
discriminant plus the bits of the payload slot (an `f32` payload is held in the `i32` joined
slot). -/
def Litmus.floatVariantS : Simple :=
  ⟨Litmus.binMod .add, [⟨"tag-plus-bits", ⟨[.variant [some .f32, some .u32]], [.u32]⟩, 0⟩]⟩

end Silmaril.Wasm.Component.Reference
