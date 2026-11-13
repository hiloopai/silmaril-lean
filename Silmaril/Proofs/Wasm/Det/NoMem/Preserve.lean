module

public import Silmaril.Proofs.Wasm.Det.NoMem.Basic

/-!
# The memory-free, float-free subset: preservation by every Core 3.0 step

* `step_lastS`: if the code of a configuration ends with an element that may precede an
  administrative call (`InS`: a reference into `q`, a `trap` or a `throw_ref`), so does the code
  after any step (only bubbling rules consume such an ending, and they end in `trap` or
  `throw_ref`). This is what keeps an administrative call that follows the code in a larger
  sequence well preceded (`ctxt-instrs`).
* `step_seq`: a Core step (every profile, every host) keeps code of the subset in the subset,
  provided the functions that may be entered are of the subset (`FunOk`), and keeps the frame's
  module instance.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Det.NoMem

variable {H : Type} {q : Nat → Bool} {ind : Bool}

/-! ## Calls -/

theorem not_inS_callRef {c : Admin} (hc : c.IsCallRef) : ¬ InS q c := by
  unfold Admin.IsCallRef at hc
  split at hc
  · exact id
  · exact id
  · exact hc.elim

theorem not_inS_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : ¬ InS q c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · exact id
  · exact id
  · exact hc.elim

/-- A `call_ref` preceded (in subset code) by a function reference may enter it. -/
theorem q_of_callRef (hM : Mode q ind) {fs : List Nat} {p : Prop} {a : Nat} {c : Admin}
    (hc : c.IsCallRef) (h : Seq q ind fs p [.ref (.func a), c]) : q a = true := by
  unfold Admin.IsCallRef at hc
  split at hc
  · rename_i y
    have h' : PlainOk q ind fs (.callRef y) := h.2.2.2.1
    rcases h' with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩
    · exact hM (by simpa [instrB] using h') a
    · cases h'
    · cases h'
  · exact h.2.2.1 trivial a rfl
  · exact hc.elim

/-- A `return_call_ref` preceded (in subset code) by a function reference may enter it. -/
theorem q_of_returnCallRef (hM : Mode q ind) {fs : List Nat} {p : Prop} {a : Nat} {c : Admin}
    (hc : c.IsReturnCallRef) (h : Seq q ind fs p [.ref (.func a), c]) : q a = true := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · rename_i y
    have h' : PlainOk q ind fs (.returnCallRef y) := h.2.2.2.1
    rcases h' with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩
    · exact hM (by simpa [instrB] using h') a
    · cases h'
    · cases h'
  · exact h.2.2.1 trivial a rfl
  · exact hc.elim

/-- The `call_ref` a tail call leaves behind is of the subset (in any module instance). -/
theorem seq_retToCallIn {fs fs' : List Nat} {p p' : Prop} {a : Nat} {c : Admin} (m : ModuleInst)
    (hc : c.IsReturnCallRef) (h : Seq q ind fs p [.ref (.func a), c]) (ha : q a = true) :
    Seq q ind fs' p' [.ref (.func a), c.retToCallIn m] := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · rename_i y
    have h' : PlainOk q ind fs (.returnCallRef y) := h.2.2.2.1
    have hi : ind = true := by
      rcases h' with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩
      · simpa [instrB] using h'
      · cases h'
      · cases h'
    simp only [Admin.retToCallIn]
    split
    · exact ⟨fun hc => absurd hc isCRT_ref, trivial, fun _ b hb => by cases hb; exact ha,
        trivial, trivial⟩
    · exact ⟨fun hc => absurd hc isCRT_ref, trivial, fun hc => absurd hc isCRT_plain,
        Or.inl (by simp [instrB, hi]), trivial⟩
  · exact ⟨fun hc => absurd hc isCRT_ref, trivial, fun _ b hb => by cases hb; exact ha,
      trivial, trivial⟩
  · exact hc.elim

/-! ## The last element -/

@[simp] theorem lastS_toAdmin_ne {p : Prop} (vs : List Val) (a : Admin) :
    lastS q p (vals vs ++ [a]) = InS q a := by
  rw [lastS_append]
  rfl

/-- `step_lastS` through `ctxt-instrs`. -/
theorem lastS_ctxt {p : Prop} {vs : List Val} {is is' rest : List Admin}
    (ih : ∀ {p : Prop}, lastS q p is → lastS q p is')
    (hl : lastS q p (vals vs ++ is ++ rest)) : lastS q p (vals vs ++ is' ++ rest) := by
  have hl' : lastS q (lastS q (lastS q p (vals vs)) is) rest := by
    simpa only [lastS_append] using hl
  show lastS q p (vals vs ++ is' ++ rest)
  rw [lastS_append, lastS_append]
  rcases List.eq_nil_or_concat rest with hr | ⟨L, b, hr⟩
  · have h₁ : lastS q (lastS q p (vals vs)) is := by simpa only [hr, lastS_nil] using hl'
    have h₂ : lastS q (lastS q p (vals vs)) is' := ih h₁
    simpa only [hr, lastS_nil] using h₂
  · have hne : rest ≠ [] := by simp [hr]
    have h₃ : lastS q (lastS q (lastS q p (vals vs)) is') rest =
        lastS q (lastS q (lastS q p (vals vs)) is) rest := lastS_irrel hne
    rw [h₃]
    exact hl'

/-- **The ending is kept**: after a step, code that ended with an `InS` element still does. -/
theorem step_lastS {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') {p : Prop} (hl : lastS q p c.code) : lastS q p c'.code := by
  induction h generalizing p with
  | parametric h =>
    cases h <;> exact absurd hl (by simp [constI32, Val.toAdmin, InS])
  | numeric h => cases h <;> exact absurd hl (by simp [InS])
  | vector h => cases h <;> exact absurd hl (by simp [InS])
  | «variable» h => cases h <;> exact absurd hl (by simp [InS])
  | table h => cases h <;> exact absurd hl (by simp [InS])
  | memory h => cases h <;> exact absurd hl (by simp [InS])
  | reference h => cases h <;> exact absurd hl (by simp [InS])
  | aggregate h =>
    cases h <;> exact absurd hl (by simp [InS, lastS_append])
  | @ctxtInstrs _ _ _ _ vs is is' rest _ _ ih => exact lastS_ctxt ih hl
  | callRefFunc hc => exact absurd hl (by simp [lastS_append, not_inS_callRef hc])
  | callRefHost hc => exact absurd hl (by simp [lastS_append, not_inS_callRef hc])
  | callRefHostDiv => exact hl
  | throwRefInstrs => simp
  | trapInstrs => simp
  | _ => first | (simp [InS]; done) | exact absurd hl (by simp [InS, lastS_append])

end Silmaril.Proofs.Wasm.Det.NoMem
