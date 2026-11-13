module

public import Silmaril.Compiler.Contract.Defs
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-! # Mir-to-Mir passes

A Mir-to-Mir pass (`Mir.Pass`) is a function on Mir units bundled with its proof of the
frozen contract `Contract.mirPass` (backward refinement on the independent Mir semantics
`Contract.MirSem` at the identity convention, with the output's entry state). A proof may go
through a proved checker: run the transformation, check it, and fall back to the input when
the check fails.

`Pass.runAll ps` runs a list of passes in order; it proves `Contract.mirPass` because the
contract holds for the identity (`Pass.mirPass_id`) and is closed under composition
(`Pass.mirPass_comp`). A link that proves `Contract.link`, run after a pass, still proves it
(`Pass.link_comp`), so the passes compose with the validated link stage. `link` is stated
forward, so `link_comp` turns the backward clause around with `MirSem` determinism: every
state has exactly one behaviour (`MirSem.Behaves.unique`, `MirSem.Behaves.exists`). -/

@[expose] public section

namespace Silmaril.Compile.Contract.MirSem

open Silmaril.Machine Relation

/-- `MirSem` steps by a function, so it is deterministic. -/
theorem step_rightUnique (us : Array Mir.Unit) (P : Placement) :
    Relator.RightUnique (Step us P) :=
  RightUnique.of_injective (step us P) Result.running fun _ _ h => Result.running.inj h

/-- The final `step` result of a finite behaviour. -/
private def final? : Lir.Behavior → Option Result
  | .returned vs m => some (.returned vs m)
  | .trapped m => some (.trapped m)
  | .stuck => some .stuck
  | .diverges => none

private theorem final?_injective {b₁ b₂ : Lir.Behavior} {r : Result} (h₁ : final? b₁ = some r)
    (h₂ : final? b₂ = some r) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp only [final?, Option.some.injEq, reduceCtorEq] at h₁ h₂ <;>
    subst h₁ <;> simp_all

/-- A finite behaviour ends in a reachable state that does not step. -/
private theorem Behaves.final {us : Array Mir.Unit} {P : Placement} {s : State} {b : Lir.Behavior}
    (h : Behaves us P s b) (hd : b ≠ .diverges) :
    ∃ t r, ReflTransGen (Step us P) s t ∧ step us P t = r ∧ final? b = some r ∧
      ∀ x, ¬ Step us P t x := by
  cases b with
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t, _, ht, hf, rfl, fun x hx => by simp [Step, hf] at hx⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t, _, ht, hf, rfl, fun x hx => by simp [Step, hf] at hx⟩
  | stuck =>
    obtain ⟨t, ht, hf⟩ := h
    exact ⟨t, _, ht, hf, rfl, fun x hx => by simp [Step, hf] at hx⟩
  | diverges => exact absurd rfl hd

/-- A `MirSem` state has at most one behaviour. -/
theorem Behaves.unique {us : Array Mir.Unit} {P : Placement} {s : State} {b₁ b₂ : Lir.Behavior}
    (h₁ : Behaves us P s b₁) (h₂ : Behaves us P s b₂) : b₁ = b₂ := by
  have hR := step_rightUnique us P
  by_cases d₁ : b₁ = .diverges <;> by_cases d₂ : b₂ = .diverges
  · rw [d₁, d₂]
  · obtain ⟨t, -, ht, -, -, ft⟩ := h₂.final d₂
    subst d₁
    exact absurd h₁ (RightUnique.not_infinite_of_final hR ht ft)
  · obtain ⟨t, -, ht, -, -, ft⟩ := h₁.final d₁
    subst d₂
    exact absurd h₂ (RightUnique.not_infinite_of_final hR ht ft)
  · obtain ⟨t₁, r₁, ht₁, hs₁, hr₁, ft₁⟩ := h₁.final d₁
    obtain ⟨t₂, r₂, ht₂, hs₂, hr₂, ft₂⟩ := h₂.final d₂
    obtain rfl := RightUnique.reach_final_eq hR ht₁ ht₂ ft₁ ft₂
    obtain rfl := hs₁.symm.trans hs₂
    exact final?_injective hr₁ hr₂

/-- Every `MirSem` state has a behaviour (classically). -/
theorem Behaves.exists (us : Array Mir.Unit) (P : Placement) (s : State) :
    ∃ b, Behaves us P s b := by
  classical
  by_cases fin : ∃ t, ReflTransGen (Step us P) s t ∧ ∀ x, step us P t ≠ .running x
  · obtain ⟨t, ht, final⟩ := fin
    cases hr : step us P t with
    | running x => exact absurd hr (final x)
    | returned vs m => exact ⟨.returned vs m, t, ht, hr⟩
    | trapped m => exact ⟨.trapped m, t, ht, hr⟩
    | stuck => exact ⟨.stuck, t, ht, hr⟩
  · refine ⟨.diverges, ?_⟩
    apply InfiniteTrace.coinduct (fun t => ReflTransGen (Step us P) s t) ?_ ReflTransGen.refl
    intro t ht
    have : ∃ x, step us P t = .running x := by
      by_contra hno
      exact fin ⟨t, ht, fun x hx => hno ⟨x, hx⟩⟩
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, ht.tail hx⟩

end Silmaril.Compile.Contract.MirSem

namespace Silmaril.Compile.Mir

open Silmaril.Compile.Contract

/-- A Mir-to-Mir pass with its proof (or its proved checker's). -/
structure Pass where
  /-- The name of the pass (`ccomp` reports, the registry row). -/
  name : String
  /-- The transformation, as the driver runs it. -/
  run : Array Mir.Unit → Array Mir.Unit
  /-- It refines its input on `Contract.MirSem`. -/
  correct : mirPass run

namespace Pass

/-- The identity refines its input. -/
theorem mirPass_id : mirPass id := by
  refine fun _ => ⟨fun _ => le_rfl, fun _ _ P' hP' => ⟨P', hP', fun s hs => ⟨⟨s, hs⟩, ?_⟩⟩⟩
  intro t ht b hb
  obtain rfl : s = t := Option.some.inj (hs.symm.trans ht)
  exact ⟨b, hb, .inr rfl⟩

/-- Running `f`, then `g`, refines the input when each does. -/
theorem mirPass_comp {f g : Array Mir.Unit → Array Mir.Unit} (hg : mirPass g)
    (hf : mirPass f) : mirPass (g ∘ f) := by
  intro us
  obtain ⟨hnf, hf⟩ := hf us
  obtain ⟨hng, hg⟩ := hg (f us)
  refine ⟨fun base => (hng base).trans (hnf base), fun memSize hm P'' hP'' => ?_⟩
  obtain ⟨P', hP', hsim'⟩ := hg memSize hm P'' hP''
  obtain ⟨P, hP, hsim⟩ := hf memSize hm P' hP'
  refine ⟨P, hP, fun s hs => ?_⟩
  obtain ⟨⟨t, ht⟩, hback⟩ := hsim s hs
  obtain ⟨hstart, hback'⟩ := hsim' t ht
  refine ⟨hstart, fun u hu b hb => ?_⟩
  obtain ⟨b'', hb'', h''⟩ := hback' u hu b hb
  obtain ⟨b', hb', h'⟩ := hback t ht b'' hb''
  refine ⟨b', hb', ?_⟩
  rcases h' with h' | rfl
  · exact .inl h'
  · exact h''

/-- A link that refines `MirSem`, run after a pass that refines it, refines it. The
input's non-stuck behaviour is its only one, so the output's behaviour, which the input
matches, is the same. -/
theorem link_comp {L : Array Mir.Unit → Except String Mir.Linked}
    {f : Array Mir.Unit → Array Mir.Unit} (hL : Contract.link L) (hf : mirPass f) :
    Contract.link (fun us => L (f us)) := by
  intro us l hl memSize hneed hm
  obtain ⟨hn, hsim⟩ := hf us
  obtain ⟨P', hP', hlink⟩ := hL (f us) l hl memSize ((hn _).trans hneed) hm
  obtain ⟨P, hP, hsim⟩ := hsim memSize hm P' hP'
  refine ⟨P, hP, fun s hs b hb hstuck => ?_⟩
  obtain ⟨⟨t, ht⟩, hback⟩ := hsim s hs
  obtain ⟨bo, hbo⟩ := MirSem.Behaves.exists (f us) P' t
  obtain ⟨b', hb', hb'o⟩ := hback t ht bo hbo
  obtain rfl := MirSem.Behaves.unique hb hb'
  rcases hb'o with h | rfl
  · exact absurd h hstuck
  · exact hlink t ht b hbo hstuck

/-- Run the passes in order, the first first. -/
def runAll : List Pass → Array Mir.Unit → Array Mir.Unit
  | [] => id
  | p :: ps => runAll ps ∘ p.run

/-- Running proved passes in order refines the input. -/
theorem runAll_correct : ∀ ps : List Pass, mirPass (runAll ps)
  | [] => mirPass_id
  | p :: ps => mirPass_comp (runAll_correct ps) p.correct

end Pass

end Silmaril.Compile.Mir
