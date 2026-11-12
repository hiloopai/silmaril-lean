module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPure2

/-!
# What the two pure fragments leave out of V2's `PureStep`

`pureStep_cover`: every V2 `PureStep` is in `PureFrag20` (pass 1), in `PureFrag20B` (this pass),
or in `PureRest20`, which names exactly what is left:

* a vector operator in the code (`vecOp20`, as in `Task.wholeStepBwdW`). The vector rules use
  `$lanes_` and the other lane primitives, which no builtins here answer for the operators;
* an integer unary operator that is not valid at its type (`¬ op.valid t`), and a conversion that
  V2's `toShared` does not define. Both are excluded by validation;
* `br`, `return` and `trap-vals` with administrative code after the redex. The 2.0 script
  quantifies that code as `instr*`, so those rules cannot fire there. V2 reduces the leftmost
  redex, so this does not occur in runs from plain code, but it is not proved here.

V2's three trap rules that can never fire (`unop-trap`, integer and float, and the float
`binop-trap`) are discharged by the totality lemmas (`IntUnOpResult_nonempty`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

/-- `rest` is plain code. -/
def PlainTail (rest : List Admin) : Prop := ∃ is : List V2.Instr, rest = expression is

/-- **The pure steps neither fragment covers.** -/
inductive PureRest20 : List Admin → Prop where
  | vec {is : List Admin} {i : V2.Instr} (hm : .plain i ∈ is) (hv : vecOp20 i = true) :
      PureRest20 is
  | unOpInvalid {t : IntType} {op : IntUnOp} {x : BitVec t.width} (h : ¬ op.valid t) :
      PureRest20 [.plain (.intConst t x), .plain (.intUnOp t op)]
  | cvtUndefined {target source : NumType} {op : V2.CvtOp} {x : BitVec source.width}
      (h : V2.CvtOp.toShared target source op = none) :
      PureRest20 [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]
  | brTail {n : Nat} {cont : List V2.Instr} {us : List Val} {l : LabelIdx} {rest : List Admin}
      (h : ¬ PlainTail rest) :
      PureRest20 [.label n cont (vals us ++ [.plain (.br l)] ++ rest)]
  | returnFrameTail {n : Nat} {fr : Frame} {us : List Val} {rest : List Admin}
      (h : ¬ PlainTail rest) :
      PureRest20 [.frame n fr (vals us ++ [.plain .return_] ++ rest)]
  | returnLabelTail {n : Nat} {cont : List V2.Instr} {us : List Val} {rest : List Admin}
      (h : ¬ PlainTail rest) :
      PureRest20 [.label n cont (vals us ++ [.plain .return_] ++ rest)]
  | trapTail {vs : List Val} {rest : List Admin} (h : ¬ PlainTail rest) :
      PureRest20 (vals vs ++ [.trap] ++ rest)

/-- A vector operator at the end of a code sequence. -/
theorem pureRest_vecLast {is : List Admin} {i : V2.Instr} (hl : is.getLast? = some (.plain i))
    (hv : vecOp20 i = true) : PureRest20 is :=
  .vec (List.mem_of_getLast? hl) hv

/-- `br-zero`, split on its tail. -/
theorem cover_brZero {P : Profile} {n : Nat} {cont : List V2.Instr} {vs' vs : List Val}
    {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n) :
    PureFrag20B P [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ expression cont) ∨
      PureRest20 [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)] := by
  by_cases hp : PlainTail rest
  · obtain ⟨is, rfl⟩ := hp
    exact .inl (.brZero hl hn)
  · rw [← vals_append]
    exact .inr (.brTail hp)

/-- `br-succ`, split on its tail. -/
theorem cover_brSucc {P : Profile} {n : Nat} {cont : List V2.Instr} {vs : List Val}
    {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat) :
    PureFrag20B P [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ [.plain (.br (labelPred l))]) ∨
      PureRest20 [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)] := by
  by_cases hp : PlainTail rest
  · obtain ⟨is, rfl⟩ := hp
    exact .inl (.brSucc hl)
  · exact .inr (.brTail hp)

/-- `return-frame`, split on its tail. -/
theorem cover_returnFrame {P : Profile} {n : Nat} {fr : Frame} {vs' vs : List Val}
    {rest : List Admin} (hn : vs.length = n) :
    PureFrag20B P [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] (vals vs) ∨
      PureRest20 [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] := by
  by_cases hp : PlainTail rest
  · obtain ⟨is, rfl⟩ := hp
    exact .inl (.returnFrame hn)
  · rw [← vals_append]
    exact .inr (.returnFrameTail hp)

/-- `return-label`, split on its tail. -/
theorem cover_returnLabel {P : Profile} {n : Nat} {cont : List V2.Instr} {vs : List Val}
    {rest : List Admin} :
    PureFrag20B P [.label n cont (vals vs ++ [.plain .return_] ++ rest)]
        (vals vs ++ [.plain .return_]) ∨
      PureRest20 [.label n cont (vals vs ++ [.plain .return_] ++ rest)] := by
  by_cases hp : PlainTail rest
  · obtain ⟨is, rfl⟩ := hp
    exact .inl .returnLabel
  · exact .inr (.returnLabelTail hp)

/-- `trap-vals`, split on its tail. -/
theorem cover_trapVals {P : Profile} {vs : List Val} {rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) :
    PureFrag20B P (vals vs ++ [.trap] ++ rest) [.trap] ∨ PureRest20 (vals vs ++ [.trap] ++ rest) := by
  by_cases hp : PlainTail rest
  · obtain ⟨is, rfl⟩ := hp
    exact .inl (.trapVals hne)
  · exact .inr (.trapTail hp)

/-- A disjunction of the second fragment and the rest, as the cover's last two cases. -/
theorem cover_of {P : Profile} {is is' : List Admin} (h : PureFrag20B P is is' ∨ PureRest20 is) :
    PureFrag20 P is is' ∨ PureFrag20B P is is' ∨ PureRest20 is :=
  .inr h

/-- **Every V2 pure step is covered**: by one of the two forward fragments, or by `PureRest20`. -/
theorem pureStep_cover {P : Profile} {is is' : List Admin} (h : PureStep P is is') :
    PureFrag20 P is is' ∨ PureFrag20B P is is' ∨ PureRest20 is := by
  cases h with
  | unreachable => exact .inl .unreachable
  | nop => exact .inl .nop
  | drop v => exact .inl (.drop v)
  | selectTrue hc => exact .inr (.inl (.selectTrue hc))
  | selectFalse v₁ v₂ ts => exact .inr (.inl (.selectFalse v₁ v₂ ts))
  | ifTrue hc => exact .inr (.inl (.ifTrue hc))
  | ifFalse => exact .inr (.inl .ifFalse)
  | labelVals => exact .inl .labelVals
  | brZero hl hn => exact cover_of (cover_brZero hl hn)
  | brSucc hl => exact cover_of (cover_brSucc hl)
  | brIfTrue hc => exact .inr (.inl (.brIfTrue hc))
  | brIfFalse => exact .inr (.inl .brIfFalse)
  | brTableLt hi => exact .inr (.inl (.brTableLt hi))
  | brTableGe hi => exact .inr (.inl (.brTableGe hi))
  | frameVals hn => exact .inl (.frameVals hn)
  | returnFrame hn => exact cover_of (cover_returnFrame hn)
  | returnLabel => exact cover_of cover_returnLabel
  | trapVals hne => exact cover_of (cover_trapVals hne)
  | trapLabel => exact .inl .trapLabel
  | trapFrame => exact .inl .trapFrame
  | @intUnOp t op x z h =>
    by_cases hop : op.valid t
    · exact .inl (.intUnOp hop h)
    · exact .inr (.inr (.unOpInvalid hop))
  | floatUnOp h => exact .inl (.floatUnOp h)
  | @intUnOpTrap t op x h => exact absurd (IntUnOpResult_nonempty t op x) (fun ⟨z, hz⟩ => h z hz)
  | @floatUnOpTrap t op x h =>
    exact absurd (FloatUnOpResult_nonempty P t op x) (fun ⟨z, hz⟩ => h z hz)
  | intBinOp h => exact .inl (.intBinOp h)
  | floatBinOp h => exact .inl (.floatBinOp h)
  | intBinOpTrap h => exact .inl (.intBinOpTrap h)
  | @floatBinOpTrap t op x y h =>
    exact absurd (FloatBinOpResult_nonempty P t op x y) (fun ⟨z, hz⟩ => h z hz)
  | testOp => exact .inl .testOp
  | intRelOp => exact .inl .intRelOp
  | floatRelOp => exact .inl .floatRelOp
  | @cvtOp target source op x z h =>
    cases hop : V2.CvtOp.toShared target source op with
    | none => exact .inr (.inr (.cvtUndefined hop))
    | some _ => exact .inr (.inl (.cvtOp (by simp [hop]) h))
  | @cvtOpTrap target source op x h =>
    cases hop : V2.CvtOp.toShared target source op with
    | none => exact .inr (.inr (.cvtUndefined hop))
    | some _ => exact .inr (.inl (.cvtOpTrap (by simp [hop]) h))
  | refIsNullTrue => exact .inr (.inl .refIsNullTrue)
  | refIsNullFalse h => exact .inr (.inl (.refIsNullFalse h))
  | localTee => exact .inr (.inl .localTee)
  | _ => exact .inr (.inr (pureRest_vecLast rfl rfl))

end Silmaril.Wasm.SpecTec.Sim20.Whole
