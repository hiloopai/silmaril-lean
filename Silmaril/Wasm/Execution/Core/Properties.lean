module

public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-! # Structural properties of Core reduction

Context lifting of `Steps` and `Diverges`, profile refinement (the deterministic
profile is a sub-relation of the spec with `$ND = false`), and the determinism
of pure non-numeric rules. Statements only (U16).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Reduction preserves the current frame's module instance, including while
executing initialization and the start function. -/
theorem Step.frame_module {c c' : Config H} (h : Step P host c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

/-- Any finite reduction retains the module instance of its initial frame. -/
theorem Steps.frame_module {c c' : Config H} (h : Steps P host c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact step.frame_module.trans ih

theorem Step.steps {a b : Config H} (h : Step P host a b) : Steps P host a b :=
  Relation.ReflTransGen.single h

theorem Steps.ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ :=
  Relation.ReflTransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩
      rcases b with ⟨sb, fb, ib⟩
      by_cases hne : vs ≠ [] ∨ rest ≠ []
      · exact Step.ctxtInstrs hs hne
      · simp only [ne_eq, not_or, not_not] at hne
        obtain ⟨rfl, rfl⟩ := hne
        simpa [vals] using hs) _ _ h

theorem Steps.label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ :=
  Relation.ReflTransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Step.ctxtLabel hs) _ _ h

theorem Steps.handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ :=
  Relation.ReflTransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Step.ctxtHandler hs) _ _ h

theorem Steps.frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (h : Steps P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Steps P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ :=
  Relation.ReflTransGen.lift
    (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Step.ctxtFrame hs) _ _ h

theorem Diverges.frame {s : Store H} {f fi : Frame} {n : Nat} {is : List Admin}
    (h : Diverges P host ⟨s, fi, is⟩) : Diverges P host ⟨s, f, [.frame n fi is]⟩ :=
  InfiniteTrace.map (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Step.ctxtFrame hs) h

theorem Diverges.label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {is : List Admin}
    (h : Diverges P host ⟨s, f, is⟩) : Diverges P host ⟨s, f, [.label n cont is]⟩ :=
  InfiniteTrace.map (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact Step.ctxtLabel hs) h

/-- Every rule is monotone in the host relation; the empty host is the least.
(Graft from design A, `Step.noHost_mono`.) -/
theorem Step.of_noHost {P : Profile} (host : HostSemantics H) {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') : Step P host c c' := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h
  | vector h => exact .vector h
  | «variable» h => exact .«variable» h
  | table h => exact .table h
  | memory h => exact .memory h
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtHandler _ ih => exact .ctxtHandler ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-! ## Refinement of the deterministic profile -/

section Refines

variable {o : GrowKind → Nat → Nat → Nat → Bool}

theorem NumericStep.deterministic_refines {is is' : List Admin}
    (h : NumericStep (Profile.deterministic o) is is') :
    NumericStep (Profile.spec false {}) is is' := by
  cases h with
  | intUnOp => exact .intUnOp
  | floatUnOp h =>
    exact .floatUnOp (by
      have := floatUnOpP_canonical_spec (P := Profile.deterministic o) rfl h
      simpa [floatUnOpP, Profile.spec, Profile.deterministic] using this)
  | intBinOp h => exact .intBinOp h
  | intBinOpTrap h => exact .intBinOpTrap h
  | floatBinOp h =>
    exact .floatBinOp (by
      have := floatBinOpP_canonical_spec (P := Profile.deterministic o) rfl h
      simpa [floatBinOpP, Profile.spec, Profile.deterministic] using this)
  | intTestOp => exact .intTestOp
  | intRelOp => exact .intRelOp
  | floatRelOp => exact .floatRelOp
  | convert h =>
    exact .convert (by
      have := convertP_canonical_spec (P := Profile.deterministic o) rfl h
      simpa [convertP, Profile.spec, Profile.deterministic] using this)
  | convertTrap h =>
    exact .convertTrap (by
      have := convertP_canonical_spec (P := Profile.deterministic o) rfl h
      simpa [convertP, Profile.spec, Profile.deterministic] using this)

theorem lanesRel3_zipWith3 {α β : Type} {R : α → α → α → β → Prop} {g : α → α → α → β}
    (hg : ∀ x y z, R x y z (g x y z)) :
    ∀ xs ys zs : List α, lanesRel3 R xs ys zs (List.zipWith3 g xs ys zs)
  | [], _, _ => by simp [lanesRel3, List.zipWith3]
  | _ :: _, [], _ => by simp [lanesRel3, List.zipWith3]
  | _ :: _, _ :: _, [] => by simp [lanesRel3, List.zipWith3]
  | x :: xs, y :: ys, z :: zs => by
    have := lanesRel3_zipWith3 hg xs ys zs
    simp only [lanesRel3, List.zipWith3, List.zip_cons_cons] at this ⊢
    exact .cons (hg x y z) this

theorem vrelaxedMaddRel_fmaddCanon (p : RelaxedParams) (sh : FloatShape) (op : VecFloatTernOp)
    (a b c : V128) :
    vrelaxedMaddRel false p sh op a b c (sh.invLanes (List.zipWith3
      (fmaddCanon sh.floatType op) (sh.lanesOf a) (sh.lanesOf b) (sh.lanesOf c))) := by
  refine ⟨_, ?_, rfl⟩
  cases op
  · exact lanesRel3_zipWith3 (fun x y z =>
      ⟨_, floatBinOpRel_self _ _ _ _, floatBinOpRel_self _ _ _ _⟩) _ _ _
  · exact lanesRel3_zipWith3 (fun x y z =>
      ⟨_, floatBinOpRel_self _ _ _ _, floatBinOpRel_self _ _ _ _⟩) _ _ _

theorem VectorStep.deterministic_refines {is is' : List Admin}
    (h : VectorStep (Profile.deterministic o) is is') :
    VectorStep (Profile.spec false {}) is is' := by
  cases h with
  | vecUnOp op a => exact .vecUnOp op a
  | vecBinOp op a b => exact .vecBinOp op a b
  | vecTernOp op a b c => exact .vecTernOp op a b c
  | vecTestOp op a => exact .vecTestOp op a
  | vecIntUnOp sh op a => exact .vecIntUnOp sh op a
  | vecFloatUnOp h =>
    refine .vecFloatUnOp ?_
    have h' : _ = _ := h
    subst h'
    exact vunopFloatRel_self _ _ _
  | vecFloatUnOpTrap h => exact absurd rfl (h _)
  | vecIntBinOp sh op a b => exact .vecIntBinOp sh op a b
  | vecFloatBinOp h =>
    rename_i sh op a b r
    refine .vecFloatBinOp ?_
    show vbinopFloatRelaxedRel false {} sh op a b r
    cases op with
    | relaxedMin =>
      rw [vbinopFloatRelaxedRel_false_min]; exact vbinopFloatRel_self _ _ _ _ _ h
    | relaxedMax =>
      rw [vbinopFloatRelaxedRel_false_max]; exact vbinopFloatRel_self _ _ _ _ _ h
    | _ => exact vbinopFloatRel_self _ _ _ _ _ h
  | vecFloatBinOpTrap h =>
    rename_i sh op a b
    exfalso
    cases op <;> exact h _ rfl
  | vecIntTernOp sh op a b c => exact .vecIntTernOp sh op a b c
  | vecFloatTernOp h =>
    refine .vecFloatTernOp ?_
    have h' : _ = _ := h
    subst h'
    exact vrelaxedMaddRel_fmaddCanon _ _ _ _ _ _
  | vecFloatTernOpTrap h => exact absurd rfl (h _)
  | vecAllTrue sh a => exact .vecAllTrue sh a
  | vecIntRelOp sh op a b => exact .vecIntRelOp sh op a b
  | vecFloatRelOp sh op a b => exact .vecFloatRelOp sh op a b
  | vecShiftOp sh op a n => exact .vecShiftOp sh op a n
  | vecBitmask sh a => exact .vecBitmask sh a
  | vecSwizzle a s => exact .vecSwizzle a s
  | vecRelaxedSwizzle a s => exact .vecRelaxedSwizzle a s
  | vecShuffle idx a b hidx => exact .vecShuffle idx a b hidx
  | vecSplat sh x => exact .vecSplat sh x
  | vecExtractLane sh sx i a hi => exact .vecExtractLane sh sx i a hi
  | vecReplaceLane sh i a x hi => exact .vecReplaceLane sh i a x hi
  | vecExtUnOp h => exact .vecExtUnOp h
  | vecExtBinOp h => exact .vecExtBinOp h
  | vecExtTernOp h => exact .vecExtTernOp h
  | vecNarrow h => exact .vecNarrow h
  | vecConvert h =>
    rename_i sh₁ sh₂ op a r
    refine .vecConvert ?_
    cases op with
    | relaxedTrunc sx z => exact h
    | _ => exact vcvtopRel_self _ _ _ _ _ h

theorem MemoryStep.deterministic_refines {c c' : Config H}
    (h : MemoryStep (Profile.deterministic o) c c') :
    MemoryStep (Profile.spec false {}) c c' := by
  cases h
  all_goals (constructor <;> first | assumption |
    (simp [Profile.growMaySucceed, Profile.growMayFail, Profile.spec]))

theorem TableStep.deterministic_refines {c c' : Config H}
    (h : TableStep (Profile.deterministic o) c c') :
    TableStep (Profile.spec false {}) c c' := by
  cases h
  all_goals (constructor <;> first | assumption |
    (simp [Profile.growMaySucceed, Profile.growMayFail, Profile.spec]))

end Refines

/-- The deterministic profile refines the spec semantics with `$ND = false`. -/
theorem Step.deterministic_refines {o : GrowKind → Nat → Nat → Nat → Bool} {a b : Config H}
    (h : Step (Profile.deterministic o) host a b) : Step (Profile.spec false {}) host a b := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h.deterministic_refines
  | vector h => exact .vector h.deterministic_refines
  | «variable» h => exact .«variable» h
  | table h => exact .table h.deterministic_refines
  | memory h => exact .memory h.deterministic_refines
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtHandler _ ih => exact .ctxtHandler ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hhost => exact .callRefHost hc hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost => exact .callRefHostDiv hc hf he hn hcode hhost
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-! ## Values do not reduce -/

/-- Is an administrative instruction a value? -/
def Admin.isVal (a : Admin) : Bool := a.val?.isSome

@[simp] theorem Admin.isVal_toAdmin (v : Val) : v.toAdmin.isVal = true := by
  simp [Admin.isVal]

@[simp] theorem all_isVal_vals (vs : List Val) : (vals vs).all Admin.isVal = true := by
  simp [vals, List.all_map, Function.comp_def]

theorem Admin.eq_of_val? {c : Admin} {v : Val} (h : c.val? = some v) : c = v.toAdmin := by
  unfold Admin.val? at h
  split at h <;> (try cases h) <;> rfl

theorem Admin.val?_of_isCallRef {c : Admin} (h : c.IsCallRef) : c.val? = none := by
  cases hv : c.val? with
  | none => rfl
  | some v =>
    obtain rfl := Admin.eq_of_val? hv
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> exact h.elim

theorem Admin.val?_of_isReturnCallRef {c : Admin} (h : c.IsReturnCallRef) : c.val? = none := by
  cases hv : c.val? with
  | none => rfl
  | some v =>
    obtain rfl := Admin.eq_of_val? hv
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> exact h.elim

/-- Every left-hand side of a reduction contains a non-value. -/
theorem Step.not_all_isVal {c c' : Config H} (h : Step P host c c') :
    c.code.all Admin.isVal = false := by
  induction h
  all_goals first
    | (simp_all [List.all_append]; done)
    | (simp [Admin.isVal, Admin.val?, constI32, Val.i32, Val.toAdmin, List.all_append,
        *]; done)
    | simp [List.all_append, Admin.isVal, Admin.val?_of_isCallRef (by assumption)]
    | (rename_i hf;cases hf <;> simp [Admin.isVal, Admin.val?, constI32, Val.i32, Val.toAdmin,
        vconst, aconst, List.all_append, *])

/-- Values do not reduce. -/
theorem Step.not_vals {s : Store H} {f : Frame} {vs : List Val} {c : Config H} :
    ¬ Step P host ⟨s, f, vals vs⟩ c := fun h => by
  have := h.not_all_isVal
  simp at this

end Silmaril.Wasm.Execution.Core
