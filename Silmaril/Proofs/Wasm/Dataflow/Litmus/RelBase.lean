module

public import Silmaril.Wasm.Dataflow.Litmus.Defs
public import Silmaril.Wasm.Dataflow.Fused.Thms
public import Silmaril.Wasm.Dataflow.LocalDce.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

/-!
# Litmus: the fused DCE simulation needs admissible label continuations

`RelBase.not_step_sim_relBase`: the step simulation of the fused transform is false for
`RelBase`. The target `codeA` reaches only `codeB`, `codeC` and `[]` (`reach`), and none of
them, nor `codeA` itself, is the transform `codeX` of the source's next code `codeB`.

The source inverted the label step at the head level (`head_label_inv`, a 32-line case
split); here it is `Step.label_split` (silmaril-lean's `Sim.Step.split_head` and
`Sim.Closure.Step.label_inv`).
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow.Litmus.RelBase

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

theorem dce_codeA : dceAdminSeq [] ⊥ codeA = codeA := by rfl

theorem dce_codeB : dceAdminSeq [] ⊥ codeB = codeX := by rfl

theorem frag_codeA : fragAdminSeq codeA = true := by rfl

section
variable (s : Store H) (f : Frame)

/-- The source step `codeA ↪ codeB`. -/
theorem stepAB : Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ := by
  have hh : Head prof s f [] (.label 1 [eqzI] [.plain (.intConst .i32 0), .plain br0])
      ⟨s, f, vals [Val.i32 0] ++ expression [eqzI]⟩ :=
    Head.brLabelZero (vs' := []) (vs := [Val.i32 0]) (l := ⟨0⟩) (rest := []) rfl rfl rfl
  exact lift_instrs [] [.plain .drop] _ _ hh.toStep

theorem headB : Head prof s f [Val.i32 0] (.plain eqzI)
    ⟨s, f, [constI32 (Numerics.intTestOp .i32 .eqz 0)]⟩ :=
  Head.numeric NumericStep.intTestOp

theorem headC : Head prof s f [Val.i32 (Numerics.intTestOp .i32 .eqz 0)] (.plain .drop)
    ⟨s, f, []⟩ :=
  Head.parametric (ParametricStep.drop _)

/-- The label body `i32.const 0; br 0` does not step on its own. -/
theorem body_stuck {c : Config H}
    (h : Step prof noHost ⟨s, f, [.plain (.intConst .i32 0), .plain br0]⟩ c) : False := by
  have h' : Step prof noHost ⟨s, f, vals [Val.i32 0] ++ .plain br0 :: []⟩ c := h
  obtain ⟨_, _, _, _, hh, _⟩ := Step.head_inv h' rfl (by intro h; cases h) (by intro h; cases h)
  exact hh.good.not_blocked (.inl ⟨_, rfl⟩)

/-- The branch to the label in the body `i32.const 0; br 0` carries `i32.const 0`. -/
theorem body_brZero {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (hn : vs.length = 1)
    (hb : [.plain (.intConst .i32 0), .plain br0] =
      vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) :
    vs' = [] ∧ vs = [Val.i32 0] := by
  have h' : vals [Val.i32 0] ++ .plain br0 :: [] = vals (vs' ++ vs) ++ .plain (.br l) :: rest := by
    rw [vals_append]
    exact hb.trans (by simp)
  have h3 : [Val.i32 0] = vs' ++ vs := (vals_append_cons_inj h' rfl rfl).1
  have hlen : 1 = vs'.length + vs.length := by simpa using congrArg List.length h3
  have hvs' : vs' = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨hvs', by simpa [hvs'] using h3.symm⟩

/-- The label redexes of the body `i32.const 0; br 0`: only the branch to the label. -/
theorem labelRed_inv {s' : Store H} {f' : Frame} {out : List Admin}
    (h : Sim.Closure.LabelRed prof noHost s f 1 [eqzI] [.plain (.intConst .i32 0), .plain br0]
      s' f' out) :
    s' = s ∧ f' = f ∧ out = vals [Val.i32 0] ++ expression [eqzI] := by
  generalize hb : [Admin.plain (.intConst .i32 0), .plain br0] = body at h
  have hb' : vals [Val.i32 0] ++ .plain br0 :: [] = body := hb
  cases h with
  | ctxt hstep => exact (body_stuck s f (hb ▸ hstep)).elim
  | values vs =>
    exact (mem_vals (hb' ▸ List.mem_append_right _ (List.mem_singleton_self _)) rfl).elim
  | brZero hl hn =>
    obtain ⟨rfl, rfl⟩ := body_brZero hn hb
    exact ⟨rfl, rfl, rfl⟩
  | @brSucc vs l rest hl =>
    have h' : vals [Val.i32 0] ++ .plain br0 :: [] = vals vs ++ .plain (.br l) :: rest := by
      rw [hb']; simp
    have hl' : br0 = .br l := Admin.plain.inj (vals_append_cons_inj h' rfl rfl).2.1
    cases hl'
    exact absurd hl (Nat.lt_irrefl 0)
  | @returnCallRef vs c rest hc =>
    have h' : vals [Val.i32 0] ++ .plain br0 :: [] = vals vs ++ c :: rest := by rw [hb']; simp
    have hc' : Admin.plain br0 = c :=
      (vals_append_cons_inj h' rfl (IsReturnCallRef.val_none hc)).2.1
    exact absurd (hc' ▸ hc) (by simp [Admin.IsReturnCallRef])
  | @return_ vs rest =>
    have h' : vals [Val.i32 0] ++ .plain br0 :: [] = vals vs ++ .plain .return_ :: rest := by
      rw [hb']; simp
    exact absurd (vals_append_cons_inj h' rfl rfl).2.1 (by simp)
  | throwRef a => exact absurd hb (by simp [throwing])
  | trap => exact absurd hb (by simp)

theorem stepA_inv {c : Config H} (h : Step prof noHost ⟨s, f, codeA⟩ c) : c = ⟨s, f, codeB⟩ := by
  obtain ⟨s', f', es'⟩ := c
  have h' : Step prof noHost ⟨s, f, vals [] ++
      .label 1 [eqzI] [.plain (.intConst .i32 0), .plain br0] :: [.plain .drop]⟩ ⟨s', f', es'⟩ := h
  obtain ⟨ws, us, out, hwu, hred, rfl⟩ := Step.label_split h'
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hwu.symm
  obtain ⟨rfl, rfl, rfl⟩ := labelRed_inv s f hred
  rfl

theorem stepB_inv {c : Config H} (h : Step prof noHost ⟨s, f, codeB⟩ c) : c = ⟨s, f, codeC⟩ := by
  have h' : Step prof noHost ⟨s, f, vals [Val.i32 0] ++ .plain eqzI :: [.plain .drop]⟩ c := h
  obtain ⟨pre, args, c₀, hpa, hh, rfl⟩ :=
    Step.head_inv h' rfl (by intro h; cases h) (by intro h; cases h)
  obtain ⟨rfl, rfl⟩ := Head.det_fam (by decide) (headB s f) hh hpa
  rfl

theorem stepC_inv {c : Config H} (h : Step prof noHost ⟨s, f, codeC⟩ c) : c = ⟨s, f, []⟩ := by
  have h' : Step prof noHost ⟨s, f, vals [Val.i32 (Numerics.intTestOp .i32 .eqz 0)] ++
      .plain .drop :: []⟩ c := h
  obtain ⟨pre, args, c₀, hpa, hh, rfl⟩ :=
    Step.head_inv h' rfl (by intro h; cases h) (by intro h; cases h)
  obtain ⟨rfl, rfl⟩ := Head.det_fam (by decide) (headC s f) hh hpa
  rfl

/-- Everything the target reaches from `codeA`. -/
theorem reach {c : Config H} (h : Relation.TransGen (Step prof noHost) ⟨s, f, codeA⟩ c) :
    c = ⟨s, f, codeB⟩ ∨ c = ⟨s, f, codeC⟩ ∨ c = ⟨s, f, []⟩ := by
  induction h with
  | single h => exact .inl (stepA_inv s f h)
  | tail _ h ih =>
      rcases ih with rfl | rfl | rfl
      · exact .inr (.inl (stepB_inv s f h))
      · exact .inr (.inr (stepC_inv s f h))
      · exact (not_step_vals (W := []) h).elim

theorem codeB_ne : codeB ≠ codeX := by simp [codeB, codeX]

theorem codeC_ne : codeC ≠ codeX := fun h =>
  absurd (congrArg (List.map Admin.val?) h) (by decide)

/-- **Counterexample.** From any store and frame, `codeA` steps to `codeB`, the target
`codeA` is `RelBase`-related to it, and no target configuration matches the step. -/
theorem counterexample :
    Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ ∧
    Dataflow.RelBase [] ⊥ (⟨s, f, codeA⟩ : Config H) ⟨s, f, codeA⟩ ∧
    ¬ ∃ d₂, Dataflow.RelBase [] ⊥ (⟨s, f, codeB⟩ : Config H) d₂ ∧
      (Relation.TransGen (Step prof noHost) ⟨s, f, codeA⟩ d₂ ∨
        (d₂ = ⟨s, f, codeA⟩ ∧ codeSize codeB < codeSize codeA)) := by
  refine ⟨stepAB s f, ⟨rfl, FrameRel.refl _ _, frag_codeA, dce_codeA.symm⟩, ?_⟩
  rintro ⟨d₂, hr, hm⟩
  have hc : d₂.code = codeX := hr.code.trans dce_codeB
  rcases hm with ht | ⟨rfl, -⟩
  · rcases reach s f ht with rfl | rfl | rfl
    · exact codeB_ne hc
    · exact codeC_ne hc
    · simp [codeX] at hc
  · simp [codeA, codeX] at hc

end

/-- The fused step simulation is false for `RelBase`. -/
theorem not_step_sim_relBase (s : Store H) (f : Frame) :
    ¬ ∀ c₁ c₂ d₁ : Config H, Step prof noHost c₁ c₂ → Dataflow.RelBase [] ⊥ c₁ d₁ →
      ∃ d₂, Dataflow.RelBase [] ⊥ c₂ d₂ ∧
        (Relation.TransGen (Step prof noHost) d₁ d₂ ∨
          (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code)) := fun hall =>
  (counterexample s f).2.2 (hall _ _ _ (counterexample s f).1 (counterexample s f).2.1)

end Silmaril.Wasm.Dataflow.Litmus.RelBase
