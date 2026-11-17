module

public import Silmaril.Wasm.Abstract.HostDet.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

/-!
# Proofs: deterministic hosts and logged Core runs

* `lstep_toStep`, `step_toLStep`: `LStep` projects to `Step`, and every `Step` lifts to an `LStep`
  from any log (`Step.split_host`: a step is host-free or a host call at the `decompose?` callout).
* `lstep_nf_iff`: a pair is `LStep`-normal exactly when its configuration is `Step`-normal.
* `step_join`, `step_shrink`: at `profile o` with a deterministic host, two steps of one
  configuration join in at most one step each, and they are equal or the first has strictly
  smaller code. Host-free steps: `Det.DStep.join'` and `Det.DStep.shrink`. A host-free step has
  no callout (`Step.noRedex`, `decompose?_none_of_noRedex`), so it never competes with a host
  call. Two host calls are at the same callout and the host has one outcome (`HostDet`), so they
  are equal.
* `lstep_join`, `lstep_shrink`: the same for `LStep` (a host-free step keeps the log, so the
  joining steps keep both logs equal).
* `nsteps_normal_not_infinite`, `nsteps_of_steps`: the abstract termination argument (restated
  from `Silmaril.Proofs.Project.Shapes.WasmWast`, another topic).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostDet

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

theorem lstep_toStep {x y : Config H × HostLog H} (h : LStep P host x y) :
    Step P host x.1 y.1 := by
  cases h with
  | free h => exact Step.of_noHost host h
  | call hd hr =>
    obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    rename_i c _ _ _ _ _ _ _
    rcases c with ⟨s, f, code⟩
    simp only at hcode hf hr ⊢
    subst hcode
    exact Ctx.step_fill _ (fun g => Step.callRefHost hyy hf he hn hc hr) _
  | div hd hr =>
    obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    rename_i c _ _ _ _ _
    rcases c with ⟨s, f, code⟩
    simp only at hcode hf hr ⊢
    subst hcode
    exact Ctx.step_fill _ (fun g => Step.callRefHostDiv hyy hf he hn hc hr) _

theorem step_toLStep {c c' : Config H} (h : Step P host c c') (l : HostLog H) :
    ∃ l', LStep P host (c, l) (c', l') := by
  rcases Step.split_host h with h | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact ⟨l, .free h⟩
  · exact ⟨_, .call hd hr⟩
  · exact ⟨l, .div hd hdiv⟩

theorem lsteps_toSteps {x y : Config H × HostLog H} (h : LSteps P host x y) :
    Steps P host x.1 y.1 := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (lstep_toStep h)

theorem steps_toLSteps {c c' : Config H} (h : Steps P host c c') (l : HostLog H) :
    ∃ l', LSteps P host (c, l) (c', l') := by
  induction h with
  | refl => exact ⟨l, .refl⟩
  | tail _ h ih =>
    obtain ⟨l₁, h₁⟩ := ih
    obtain ⟨l₂, h₂⟩ := step_toLStep h l₁
    exact ⟨l₂, .tail h₁ h₂⟩

theorem lstep_nf_iff {c : Config H} {l : HostLog H} :
    (∀ y, ¬ LStep P host (c, l) y) ↔ ∀ c', ¬ Step P host c c' := by
  constructor
  · intro h c' hs
    obtain ⟨l', hl⟩ := step_toLStep hs l
    exact h _ hl
  · intro h y hl
    exact h _ (lstep_toStep hl)

/-- A host-free step has no callout. -/
theorem decompose?_none_of_free {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') : decompose? c.store c.code = none :=
  decompose?_none_of_noRedex (Step.noRedex h)

variable {o : GrowOracle}

theorem step_join (hd : HostDet host) {c c₁ c₂ : Config H} (h₁ : Step (profile o) host c c₁)
    (h₂ : Step (profile o) host c c₂) : Det.Join (Step (profile o) host) c₁ c₂ := by
  rcases Step.split_host h₁ with f₁ | ⟨E, a, hh, args, hd₁, k₁⟩
  · rcases Step.split_host h₂ with f₂ | ⟨E', a', hh', args', hd₂, -⟩
    · exact Det.Join.map' id (fun a b h => Step.of_noHost host h) (Det.DStep.join' f₁ f₂)
    · rw [decompose?_none_of_free f₁] at hd₂; cases hd₂
  · rcases Step.split_host h₂ with f₂ | ⟨E', a', hh', args', hd₂, k₂⟩
    · rw [decompose?_none_of_free f₂] at hd₁; cases hd₁
    · rw [hd₁] at hd₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
      rcases k₁ with ⟨s₁, r₁, hr₁, rfl⟩ | ⟨hv₁, rfl⟩ <;>
        rcases k₂ with ⟨s₂, r₂, hr₂, rfl⟩ | ⟨hv₂, rfl⟩
      · cases hd _ _ _ _ _ hr₁ hr₂
        exact Det.Join.rfl'
      · cases hd _ _ _ _ _ hr₁ hv₂
      · cases hd _ _ _ _ _ hv₁ hr₂
      · exact Det.Join.rfl'

theorem step_shrink (hd : HostDet host) {c c₁ c₂ : Config H} (h₁ : Step (profile o) host c c₁)
    (h₂ : Step (profile o) host c c₂) : c₁ = c₂ ∨ sizeOf c₁.code < sizeOf c.code := by
  rcases Step.split_host h₁ with f₁ | ⟨E, a, hh, args, hd₁, k₁⟩
  · rcases Step.split_host h₂ with f₂ | ⟨E', a', hh', args', hd₂, -⟩
    · rcases c with ⟨s, f, code⟩
      rcases Det.DStep.shrink _ s f code c₁ c₂ rfl f₁ f₂ with h | ⟨-, -, hl, -⟩
      · exact .inl h
      · exact .inr hl
    · rw [decompose?_none_of_free f₁] at hd₂; cases hd₂
  · rcases Step.split_host h₂ with f₂ | ⟨E', a', hh', args', hd₂, k₂⟩
    · rw [decompose?_none_of_free f₂] at hd₁; cases hd₁
    · rw [hd₁] at hd₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
      left
      rcases k₁ with ⟨s₁, r₁, hr₁, rfl⟩ | ⟨hv₁, rfl⟩ <;>
        rcases k₂ with ⟨s₂, r₂, hr₂, rfl⟩ | ⟨hv₂, rfl⟩
      · cases hd _ _ _ _ _ hr₁ hr₂; rfl
      · cases hd _ _ _ _ _ hr₁ hv₂
      · cases hd _ _ _ _ _ hv₁ hr₂
      · rfl

/-- Two logged steps of one pair: both host-free, or both the same host call. -/
theorem lstep_cases (hd : HostDet host) {x a b : Config H × HostLog H}
    (ha : LStep (profile o) host x a) (hb : LStep (profile o) host x b) :
    a = b ∨ (∃ c₁ c₂, a = (c₁, x.2) ∧ b = (c₂, x.2) ∧
      Step (profile o) (fun _ _ _ _ => False) x.1 c₁ ∧
      Step (profile o) (fun _ _ _ _ => False) x.1 c₂) := by
  cases ha with
  | free f₁ =>
    cases hb with
    | free f₂ => exact .inr ⟨_, _, rfl, rfl, f₁, f₂⟩
    | call hd₂ _ => rw [decompose?_none_of_free f₁] at hd₂; cases hd₂
    | div hd₂ _ => rw [decompose?_none_of_free f₁] at hd₂; cases hd₂
  | call hd₁ hr₁ =>
    cases hb with
    | free f₂ => rw [decompose?_none_of_free f₂] at hd₁; cases hd₁
    | call hd₂ hr₂ =>
      rw [hd₁] at hd₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
      cases hd _ _ _ _ _ hr₁ hr₂
      exact .inl rfl
    | div hd₂ hv₂ =>
      rw [hd₁] at hd₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
      cases hd _ _ _ _ _ hr₁ hv₂
  | div hd₁ hv₁ =>
    cases hb with
    | free f₂ => rw [decompose?_none_of_free f₂] at hd₁; cases hd₁
    | call hd₂ hr₂ =>
      rw [hd₁] at hd₂
      simp only [Option.some.injEq, Prod.mk.injEq] at hd₂
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd₂
      cases hd _ _ _ _ _ hv₁ hr₂
    | div _ _ => exact .inl rfl

theorem lstep_join (hd : HostDet host) {x a b : Config H × HostLog H}
    (ha : LStep (profile o) host x a) (hb : LStep (profile o) host x b) :
    Det.Join (LStep (profile o) host) a b := by
  rcases lstep_cases hd ha hb with rfl | ⟨c₁, c₂, rfl, rfl, f₁, f₂⟩
  · exact Det.Join.rfl'
  · exact Det.Join.map' (fun c => (c, x.2)) (fun _ _ h => LStep.free h) (Det.DStep.join' f₁ f₂)

theorem lstep_shrink (hd : HostDet host) {x a b : Config H × HostLog H}
    (ha : LStep (profile o) host x a) (hb : LStep (profile o) host x b) :
    a = b ∨ sizeOf a.1.code < sizeOf x.1.code := by
  rcases lstep_cases hd ha hb with rfl | ⟨c₁, c₂, rfl, rfl, f₁, f₂⟩
  · exact .inl rfl
  · rcases x with ⟨⟨s, f, code⟩, l⟩
    rcases Det.DStep.shrink _ s f code c₁ c₂ rfl f₁ f₂ with h | ⟨-, -, hl, -⟩
    · exact .inl (by rw [h])
    · exact .inr hl

/-! ## The abstract termination argument -/

theorem nsteps_normal_not_infinite {α : Type _} {R : α → α → Prop} (μ : α → Nat)
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b)
    (hs : ∀ {x a b : α}, R x a → R x b → a = b ∨ μ a < μ x)
    {y : α} (hy : ∀ z, ¬ R y z) :
    ∀ (k : Nat) (x : α), NSteps R k x y → ¬ InfiniteTrace R x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  suffices h : ∀ (n : Nat) (x : α), μ x = n → NSteps R k x y → ¬ InfiniteTrace R x from
    fun x => h _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro x hn hpath hinf
  obtain ⟨x₁, hx₁, hinf₁⟩ := hinf.unfold
  obtain ⟨m, hm, hpath₁⟩ := NSteps.of_step_join hj hy hpath hx₁
  cases hpath with
  | refl => exact hy _ hx₁
  | @head _ a _ k' hxa hrest =>
    rcases hs hx₁ hxa with heq | hlt
    · exact ihk k' (Nat.lt_succ_self k') _ (heq ▸ hrest) hinf₁
    · rcases Nat.lt_or_ge m (k' + 1) with hlt' | hge
      · exact ihk m hlt' x₁ hpath₁ hinf₁
      · have hmk : m = k' + 1 := le_antisymm hm hge
        exact ihn (μ x₁) (by omega) x₁ rfl (hmk ▸ hpath₁) hinf₁

theorem nsteps_of_steps {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b) {y : α} (hy : ∀ z, ¬ R y z)
    {k : Nat} {x x' : α} (hk : NSteps R k x y) (h : Relation.ReflTransGen R x x') :
    ∃ m, NSteps R m x' y := by
  induction h with
  | refl => exact ⟨k, hk⟩
  | tail _ hs ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m', -, hm'⟩ := NSteps.of_step_join hj hy hm hs
    exact ⟨m', hm'⟩

theorem nsteps_to_rtg {α : Type _} {R : α → α → Prop} {k : Nat} {x y : α}
    (h : NSteps R k x y) : Relation.ReflTransGen R x y := by
  induction h with
  | refl => exact .refl
  | head hxy _ ih => exact .head hxy ih

theorem steps_always (hd : HostDet host) {c₀ c : Config H} (h : Steps (profile o) host c₀ c)
    (hn : ∀ x, ¬ Step (profile o) host c x) :
    ¬ Diverges (profile o) host c₀ ∧
      ∀ c', Steps (profile o) host c₀ c' → Steps (profile o) host c' c := by
  obtain ⟨k, hk⟩ := NSteps.of_rtg h
  refine ⟨nsteps_normal_not_infinite (fun c : Config H => sizeOf c.code)
    (fun ha hb => step_join hd ha hb) (fun ha hb => step_shrink hd ha hb) hn k _ hk,
    fun c' hc' => ?_⟩
  obtain ⟨m, hm⟩ := nsteps_of_steps (fun ha hb => step_join hd ha hb) hn hk hc'
  exact nsteps_to_rtg hm

end Silmaril.Proofs.Wasm.Abstract.HostDet

end
