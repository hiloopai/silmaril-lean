module

public import Silmaril.Wasm.Binaryen.InlDrive
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

@[expose] public section

/-! # Determinism of classified runs

Under the deterministic profile, runs whose configurations are all classified
(`Classif`: host-free steps, or a diverging host call staying put) have a unique result
(`nf_unique_classif`) and a terminating run excludes divergence (`term_not_div`). Both
come from the one-step diamond of host-free steps (`Det.DStep.join'`) and the shrinking
of diverging host-free steps (`Det.DStep.shrink`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

theorem steps_noHost_of_classif {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hcl : ∀ x, Steps P host c x → Classif P host x) :
    Relation.ReflTransGen (Step P Det.noHost) c c' := by
  induction h with
  | refl => exact .refl
  | @tail x x' hx hst ih =>
    rcases hcl x hx x' hst with hn | ⟨hxx, -⟩
    · exact ih.tail hn
    · rw [hxx]; exact ih

theorem terminal_no_step {P : Numerics.Profile} {host : HostSemantics H} {c : Config H}
    (h : c.Terminal) (c' : Config H) : ¬ Step P host c c' := fun hs => by
  apply Step.not_quiet hs
  obtain ⟨r, hr⟩ := h
  rw [hr]
  cases r with
  | values vs => exact quiet_vals vs
  | trap => exact quiet_trap
  | throw a => exact quiet_throwing a

/-- **Unique results.** -/
theorem nf_unique_classif {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}
    {host : HostSemantics H} {c x y : Config H}
    (hx : Steps (Numerics.Profile.deterministic o) host c x)
    (hy : Steps (Numerics.Profile.deterministic o) host c y) (hxT : x.Terminal) (hyT : y.Terminal)
    (hcl : ∀ z, Steps (Numerics.Profile.deterministic o) host c z →
      Classif (Numerics.Profile.deterministic o) host z) : x = y :=
  nf_unique_of_join (fun ha hb => Det.DStep.join' ha hb) (steps_noHost_of_classif hx hcl)
    (steps_noHost_of_classif hy hcl) (terminal_no_step hxT) (terminal_no_step hyT)

/-- **Termination excludes divergence.** -/
theorem term_not_div {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} {host : HostSemantics H}
    {c x : Config H} (hx : Steps (Numerics.Profile.deterministic o) host c x) (hxT : x.Terminal)
    (hcl : ∀ z, Steps (Numerics.Profile.deterministic o) host c z →
      Classif (Numerics.Profile.deterministic o) host z) :
    ¬ Diverges (Numerics.Profile.deterministic o) host c := by
  have hnf : ∀ z, ¬ Det.DStep o x z := terminal_no_step hxT
  have hj : ∀ {a b d : Config H}, Det.DStep o a b → Det.DStep o a d → Det.Join (Det.DStep o) b d :=
    fun ha hb => Det.DStep.join' ha hb
  obtain ⟨k₀, hk₀⟩ := NSteps.of_rtg (steps_noHost_of_classif hx hcl)
  have aux : ∀ (k m : Nat) (y : Config H), sizeOf y.code = m →
      Steps (Numerics.Profile.deterministic o) host c y → NSteps (Det.DStep o) k y x →
      ¬ Diverges (Numerics.Profile.deterministic o) host y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro y hm hy hk hdiv
    obtain ⟨y₁, hst, hdiv₁⟩ := InfiniteTrace.unfold hdiv
    rcases hcl y hy y₁ hst with hn | ⟨-, E, a, hh, args, hd, -⟩
    · cases hk with
      | refl => exact hnf _ hn
      | @head _ a' _ j h₁ hrest =>
        obtain ⟨ys, yf, ycode⟩ := y
        rcases Det.DStep.shrink _ ys yf ycode a' y₁ rfl h₁ hn with heq | ⟨-, -, -, hlt⟩
        · subst heq
          exact ihk j (by omega) _ _ rfl (hy.tail hst) hrest hdiv₁
        · obtain ⟨m', hm', hpath⟩ := NSteps.of_step_join hj hnf (.head h₁ hrest) hn
          rcases Nat.lt_or_eq_of_le hm' with hlt' | rfl
          · exact ihk m' hlt' _ _ rfl (hy.tail hst) hpath hdiv₁
          · exact ihm _ (by simp only at hm; omega) _ rfl (hy.tail hst) hpath hdiv₁
    · cases hk with
      | refl =>
        rw [decompose?_terminal hxT] at hd
        cases hd
      | head h₁ _ =>
        rw [decompose?_none_of_noRedex (Step.noRedex h₁)] at hd
        cases hd
  exact aux k₀ _ c rfl .refl hk₀

end Silmaril.Wasm.Binaryen.InlR
