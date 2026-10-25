module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

@[expose] public section

/-! # A diverging block body: `block (loop (br 0))`

`loop (br 0)` has no free label, no `return`, nothing outside the analysed
fragment, and is typed; but it diverges, so running it inside the block and
outside it never reaches a common configuration: every configuration reachable
from the block keeps the block's label, and none reachable from the bare loop
has it. This refutes `block_unwrap` as first stated (without excluding loops and
calls), see `Pass/Vacuum.lean`.

The reachable configurations are characterised by inverting host-free steps with
`Step.head_inv` (first non-value) and the `Head` relation.
-/

namespace Silmaril.Wasm.Binaryen.LoopCex

open Silmaril.Wasm.Binaryen Execution.Core Numerics Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

/-- Label `0`. -/
abbrev l0 : LabelIdx := ⟨⟨0, by decide⟩⟩

/-- `loop (br 0)` as a Core instruction. -/
abbrev loopI : Instr := .loop .empty [.br l0]

/-- `block (loop (br 0))` as a Core instruction. -/
abbrev blockI : Instr := .block .empty [loopI]

/-- The diverging body, on layer D. -/
def body : List BExpr := [.loop .empty [.op (.br l0) []]]

theorem body_lower : BExpr.lowerList body = [loopI] := rfl

theorem body_labels : BExpr.labelsList body = [] := by
  simp [BExpr.labelsList, body_lower, instrsLabels, instrLabels, unbind, Idx.toNat]

theorem body_any : (effectsList body).any = false := by decide

theorem body_branchesOut : (effectsList body).branchesOut = false := by decide

theorem body_typed : SeqOk {} [.block .empty body] (.plain [] []) := by
  show InstrsOk {} [blockI] _
  have hbr : InstrsOk ((({} : Context).withLabel []).withLabel []) [.br l0] (.plain [] []) :=
    .instr (.br (ts := []) (t₁ := []) (t₂ := []) rfl ⟨by simp [ResultOk], by simp [ResultOk],
      by simp⟩)
  have hloop : InstrsOk (({} : Context).withLabel []) [loopI] (.plain [] []) :=
    .instr (.loop .empty hbr)
  exact .instr (.block .empty hloop)

variable {P : Profile} {H : Type}

/-! ## Inverting the steps -/

theorem single_vals_inv {a x : Admin} (ha : a.val? = none) {vs : List Val} {rest : List Admin}
    (h : [a] = vals vs ++ x :: rest) : vs = [] ∧ x = a ∧ rest = [] := by
  cases vs with
  | nil =>
    simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  | cons v vs =>
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ ha) (toAdmin_val?_ne_none v)

theorem single_ne_vals {a : Admin} (ha : a.val? = none) {vs : List Val} (h : [a] = vals vs) :
    False := by
  cases vs with
  | nil => simp [vals] at h
  | cons v vs =>
    simp only [vals, List.map_cons, List.cons.injEq] at h
    exact absurd (h.1 ▸ ha) (toAdmin_val?_ne_none v)

theorem blockType?_empty (m : ModuleInst) : m.blockType? .empty = some ([], []) := rfl

/-- First non-value is the single admin. -/
theorem head_single {s : Store H} {f : Frame} {e : Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, [e]⟩ c) (he : e.val? = none) (ht : e ≠ .trap)
    (hthr : e ≠ .plain .throwRef) :
    ∃ c₀, Head P s f [] e c₀ ∧ c = ⟨c₀.store, c₀.frame, c₀.code⟩ := by
  obtain ⟨pre, args, c₀, hw, hh, rfl⟩ := Step.head_inv (ws := []) (e := e) (rest := [])
    (by simpa [vals] using h) he ht hthr
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw.symm
  exact ⟨c₀, hh, by simp [vals]⟩

/-- A family step does not apply to a single control instruction. -/
theorem fam_single_absurd {k : Fam} {x : Admin} (h : FamShape k [x]) (hk : famOf x = .control)
    (hne : k ≠ .control) : False := by
  obtain ⟨args, e, heq, -, hfe⟩ := h
  cases args with
  | nil =>
    simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, and_true] at heq
    rw [← heq, hk] at hfe
    exact hne hfe.symm
  | cons v vs =>
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at heq
    have := congrArg List.length heq.2
    simp at this

/-- Closes the family and `call_ref` heads on a single control instruction. -/
macro "fam_absurd" : tactic => `(tactic| first
  | exact (fam_single_absurd (ParametricStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (NumericStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (VectorStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (VariableStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (TableStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (MemoryStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (RefStep.shape ‹_›) rfl (by decide)).elim
  | exact (fam_single_absurd (AggregateStep.shape ‹_›) rfl (by decide)).elim
  | (simp_all [Admin.IsCallRef]; done))

/-- The only step of the bare loop. -/
theorem step_loop {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.plain loopI]⟩ c) :
    c = ⟨s, f, [.label 0 [loopI] [.plain (.br l0)]]⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := head_single h rfl (by simp) (by simp)
  cases hh with
  | loop hbt hm =>
    rw [blockType?_empty] at hbt
    simp only [Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt
    simp [vals, expression]
  | _ => fam_absurd

/-- The only step of the block. -/
theorem step_block {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.plain blockI]⟩ c) :
    c = ⟨s, f, [.label 0 [] [.plain loopI]]⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := head_single h rfl (by simp) (by simp)
  cases hh with
  | block hbt hm =>
    rw [blockType?_empty] at hbt
    simp only [Option.some.injEq, Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt
    simp [vals, expression]
  | _ => fam_absurd

/-- A bare branch does not step. -/
theorem no_step_br {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.plain (.br l0)]⟩ c) : False :=
  not_step_blocked h (W := []) (e := .plain (.br l0)) (rest := []) (by simp) (.inl ⟨l0, rfl⟩)

theorem vals_vals_br {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} :
    vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
      vals (vs' ++ vs) ++ Admin.plain (.br l) :: rest := by
  simp

theorem vals_one {vs : List Val} {x : Admin} {rest : List Admin} :
    vals vs ++ [x] ++ rest = vals vs ++ x :: rest := by
  simp

/-- Inverting a step of a label around a one-instruction body that is not a value. -/
theorem step_label_single {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Admin}
    {c : Config H} (h : Step P noHost ⟨s, f, [.label n cont [a]]⟩ c) (ha : a.val? = none)
    (hnt : a ≠ .trap) (hnb : ∀ l, a ≠ .plain (.br l)) (hnr : a ≠ .plain .return_)
    (hnrc : ¬ a.IsReturnCallRef) :
    ∃ s' f' is', Step P noHost ⟨s, f, [a]⟩ ⟨s', f', is'⟩ ∧ c = ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := head_single h rfl (by simp) (by simp)
  cases hh with
  | ctxtLabel h' => exact ⟨_, _, _, h', rfl⟩
  | labelVals hb => exact (single_ne_vals ha hb).elim
  | brLabelZero hb hl hn =>
    rw [vals_vals_br] at hb
    exact absurd (single_vals_inv ha hb).2.1.symm (hnb _)
  | brLabelSucc hb hl =>
    rw [vals_one] at hb
    exact absurd (single_vals_inv ha hb).2.1.symm (hnb _)
  | returnCallRefLabel hb hc =>
    rw [vals_one] at hb
    exact absurd ((single_vals_inv ha hb).2.1 ▸ hc) hnrc
  | returnLabel hb =>
    rw [vals_one] at hb
    exact absurd (single_vals_inv ha hb).2.1.symm hnr
  | trapLabel => exact absurd rfl hnt
  | _ => fam_absurd

/-- The inner loop label steps only back to the loop. -/
theorem step_loop_label {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.label 0 [loopI] [.plain (.br l0)]]⟩ c) :
    c = ⟨s, f, [.plain loopI]⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := head_single h rfl (by simp) (by simp)
  cases hh with
  | ctxtLabel h' => exact (no_step_br h').elim
  | labelVals hb => exact (single_ne_vals rfl hb).elim
  | brLabelZero hb hl hn =>
    rw [List.eq_nil_of_length_eq_zero hn]
    simp [vals, expression]
  | brLabelSucc hb hl =>
    rw [vals_one] at hb
    obtain ⟨-, e, -⟩ := single_vals_inv rfl hb
    simp only [Admin.plain.injEq, Instr.br.injEq] at e
    subst e
    simp [Idx.toNat] at hl
  | returnCallRefLabel hb hc =>
    rw [vals_one] at hb
    obtain ⟨-, e, -⟩ := single_vals_inv rfl hb
    subst e
    simp [Admin.IsReturnCallRef] at hc
  | returnLabel hb =>
    rw [vals_one] at hb
    obtain ⟨-, e, -⟩ := single_vals_inv rfl hb
    simp at e
  | _ => fam_absurd

/-- The block label around the bare loop steps only by stepping the loop. -/
theorem step_block_label₁ {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.label 0 [] [.plain loopI]]⟩ c) :
    c = ⟨s, f, [.label 0 [] [.label 0 [loopI] [.plain (.br l0)]]]⟩ := by
  obtain ⟨s', f', is', h', rfl⟩ := step_label_single h rfl (by simp) (by simp) (by simp)
    (by simp [Admin.IsReturnCallRef])
  have := step_loop h'
  simp only [Config.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

/-- The block label around the loop label steps only by stepping the loop label. -/
theorem step_block_label₂ {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.label 0 [] [.label 0 [loopI] [.plain (.br l0)]]]⟩ c) :
    c = ⟨s, f, [.label 0 [] [.plain loopI]]⟩ := by
  obtain ⟨s', f', is', h', rfl⟩ := step_label_single h rfl (by simp) (by simp) (by simp)
    (by simp [Admin.IsReturnCallRef])
  have := step_loop_label h'
  simp only [Config.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

/-! ## Reachable configurations -/

/-- Configurations reachable from the block. -/
def RA (s : Store H) (f : Frame) (c : Config H) : Prop :=
  c = ⟨s, f, [.plain blockI]⟩ ∨ c = ⟨s, f, [.label 0 [] [.plain loopI]]⟩ ∨
    c = ⟨s, f, [.label 0 [] [.label 0 [loopI] [.plain (.br l0)]]]⟩

/-- Configurations reachable from the bare loop. -/
def RB (s : Store H) (f : Frame) (c : Config H) : Prop :=
  c = ⟨s, f, [.plain loopI]⟩ ∨ c = ⟨s, f, [.label 0 [loopI] [.plain (.br l0)]]⟩

theorem RA.steps {s : Store H} {f : Frame} {c c' : Config H} (hc : RA s f c)
    (h : Steps P noHost c c') : RA s f c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih =>
    rcases ih with rfl | rfl | rfl
    · exact .inr (.inl (step_block hs))
    · exact .inr (.inr (step_block_label₁ hs))
    · exact .inr (.inl (step_block_label₂ hs))

theorem RB.steps {s : Store H} {f : Frame} {c c' : Config H} (hc : RB s f c)
    (h : Steps P noHost c c') : RB s f c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih =>
    rcases ih with rfl | rfl
    · exact .inr (step_loop hs)
    · exact .inl (step_loop_label hs)

theorem RA_RB_disjoint {s : Store H} {f : Frame} {c : Config H} (ha : RA s f c) (hb : RB s f c) :
    False := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with h | h <;> simp at h

/-! ## A fitting configuration -/

/-- The empty store is valid. -/
theorem storeOk_empty : StoreOk ({} : Store H) := by
  constructor <;> simp

/-- The empty frame fits the empty context. -/
theorem frameOk_empty : FrameOk ({} : Store H) ({} : Frame)
    ({ ({} : Context) with labels := [], return_ := none }) := by
  refine ⟨{
      types := [], recs := [], tags := [], globals := [], mems := [], tables := [], funcs := [],
      datas := [], elems := [], refs := List.range 0 }, [], ?_, .nil, rfl⟩
  exact ModuleInstOk.mk (k := 0) (by simp) .nil .nil .nil .nil .nil (by simp) .nil (by simp)
    (by simp) (by simp) (Nat.le_refl _)

theorem fits_empty : Fits ({} : Context) (.plain [] []) ({} : Store H) ({} : Frame) [] :=
  ⟨storeOk_empty, frameOk_empty, .nil⟩

/-- **The block and the bare loop never meet.** -/
theorem not_joinable : ¬ Joinable P {} (.plain [] []) [.block .empty body] body := by
  intro h
  obtain ⟨c, hA, hB⟩ := h (H := Empty) {} {} [] fits_empty
  have hA0 : RA ({} : Store Empty) {} (codeConfig {} {} [] [.block .empty body]) := .inl rfl
  have hB0 : RB ({} : Store Empty) {} (codeConfig {} {} [] body) := .inl rfl
  exact RA_RB_disjoint (hA0.steps hA) (hB0.steps hB)

end Silmaril.Wasm.Binaryen.LoopCex
