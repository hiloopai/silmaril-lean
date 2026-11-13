module

public import Silmaril.Wasm.Dataflow.Litmus.Defs
public import Silmaril.Wasm.Dataflow.DropElim.Thms
public import Mathlib.Data.List.Chain

/-!
# Litmus: An earlier step needs exception absorption

`ThrowRef.not_erase_step_sim`: an earlier step simulation is false for `OldERel`, the
relation whose erasure lets a trap but not a pending exception absorb its suffix.
`ThrowRef.repaired_counterexample`, `repaired_label`: `ERel` (with `Erase`) closes the
same step, also under a label.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow.Litmus.ThrowRef

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

theorem OldErase.cons {a a' : List Admin} {b : Admin} {bs bs' : List Admin}
    (h : OldErase [b] a) (hs : OldErase bs bs') (ha : a' = a ++ bs') : OldErase (b :: bs) a' := by
  subst ha
  exact OldErase.append (a := [b]) h hs

/-- Code made of values, `THROW_REF` and `drop`, with no removable producer directly before
a `drop`, is only erased to itself. -/
theorem OldErase.eq_of_unpaired {c d : List Admin} (h : OldErase c d)
    (hc : ∀ a ∈ c, a.val? ≠ none ∨ a = .plain .throwRef ∨ a = .plain .drop)
    (hp : c.IsChain fun x y => y = .plain .drop → adminPureArity? x = none) : d = c := by
  induction h with
  | nil => rfl
  | append _ _ ih₁ ih₂ =>
      rw [ih₁ (fun a ha => hc a (List.mem_append_left _ ha)) hp.left_of_append,
        ih₂ (fun a ha => hc a (List.mem_append_right _ ha)) hp.right_of_append]
  | keep => rfl
  | pure h => exact absurd ((List.isChain_cons_cons.mp hp).1 rfl ▸ h) (by simp)
  | block bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [Admin.val?])
  | loop bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [Admin.val?])
  | if_ bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [Admin.val?])
  | label n => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [Admin.val?])
  | trap => exact absurd (hc .trap (by simp)) (by simp [Admin.val?])

theorem erase_codeA : OldErase codeA codeT :=
  OldErase.cons (.keep _) (OldErase.cons (.keep _) (OldErase.pure (n := 0) rfl) rfl) rfl

theorem erase_codeB {d : List Admin} (h : OldErase codeB d) : d = codeB :=
  OldErase.eq_of_unpaired h (by simp [codeB, Admin.val?])
    (by simp [codeB, adminPureArity?, pureArity?])

/-- The source step `codeA ↪ codeB`. -/
theorem stepAB (s : Store H) (f : Frame) : Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ := by
  have h1 : Step prof noHost ⟨s, f, vals [] ++ throwing 0 ++ [.ref .null]⟩ ⟨s, f, throwing 0⟩ :=
    .throwRefInstrs (.inr (List.cons_ne_nil _ _))
  exact .ctxtInstrs (vs := []) (rest := [.plain .drop]) h1 (.inr (List.cons_ne_nil _ _))

/-- **Counterexample.** From any store and frame, `codeA` steps to `codeB`, the target
`codeT` is `OldERel`-related to `codeA`, and no target configuration matches the step. -/
theorem counterexample (s : Store H) (f : Frame) :
    Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ ∧
    OldERel (⟨s, f, codeA⟩ : Config H) ⟨s, f, codeT⟩ ∧
    ¬ ∃ d₂, OldERel (⟨s, f, codeB⟩ : Config H) d₂ ∧
      (Relation.TransGen (Step prof noHost) ⟨s, f, codeT⟩ d₂ ∨
        (d₂ = ⟨s, f, codeT⟩ ∧ codeSize codeB < codeSize codeA)) := by
  refine ⟨stepAB s f, ⟨rfl, rfl, erase_codeA⟩, ?_⟩
  rintro ⟨d₂, hr, hm⟩
  rcases hm with ht | ⟨rfl, -⟩
  · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp ht
    exact not_step_throwing hc
  · have hc : codeT = codeB := erase_codeB hr.code
    simp [codeT, codeB] at hc

/-- The `OldErase`-based simulation is false: it fails on `codeA`. -/
theorem not_erase_step_sim (s : Store H) (f : Frame) :
    ¬ ∀ c₁ c₂ d₁ : Config H, Step prof noHost c₁ c₂ → OldERel c₁ d₁ →
      ∃ d₂, OldERel c₂ d₂ ∧
        (Relation.TransGen (Step prof noHost) d₁ d₂ ∨
          (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code)) := fun hall =>
  (counterexample s f).2.2 (hall _ _ _ (counterexample s f).1 (counterexample s f).2.1)

/-- The repaired relation closes the step that refutes `OldERel`. -/
theorem repaired_counterexample (s : Store H) (f : Frame) :
    ERel (⟨s, f, codeA⟩ : Config H) ⟨s, f, codeT⟩ ∧
    ERel (⟨s, f, codeB⟩ : Config H) ⟨s, f, codeT⟩ ∧
    codeSize codeB < codeSize codeA :=
  ⟨⟨rfl, rfl, Erase.throwRef 0 [.ref .null, .plain .drop]⟩,
    ⟨rfl, rfl, Erase.throwRef 0 [.plain .drop]⟩,
    by decide⟩

/-- The same partial throw discard under a label is matched by a stutter. -/
theorem repaired_label (s : Store H) (f : Frame) (n : Nat) (cont : List Instr) :
    Step prof noHost ⟨s, f, [.label n cont codeA]⟩ ⟨s, f, [.label n cont codeB]⟩ ∧
    ERel (⟨s, f, [.label n cont codeB]⟩ : Config H) ⟨s, f, [.label n cont codeT]⟩ ∧
    codeSize [.label n cont codeB] < codeSize [.label n cont codeA] := by
  refine ⟨.ctxtLabel (stepAB s f),
    ⟨rfl, rfl, .label n (Erase.refl _) (Erase.throwRef 0 [.plain .drop])⟩, ?_⟩
  change 1 + codeSize codeB + 0 < 1 + codeSize codeA + 0
  have := (repaired_counterexample s f).2.2
  omega

end Silmaril.Wasm.Dataflow.Litmus.ThrowRef
