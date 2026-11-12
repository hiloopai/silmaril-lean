module

public import Silmaril.Wasm.Jco.Bridge.StateFix.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Strategy.Thms

/-!
# The stateful component bridge, restated: proofs

* `compLTS_eq`: `compLTS md m` is the answering machine of `compAns md m`.
* `compAnsS_eq`: on modules whose returned calls always lift, `compAnsS` is `compAns`.
* `mem_ans_iff`: the play of questions `qs` answered by `rs` is in the strategy of an
  answering machine exactly when `rs` are the machine's answers (the argument of
  `Bridge.State.mem_sem_iff`, for machines over `sigU`).
* `bump_answers`, `bump_answersS`, `bump_differs`: on `bumpMod` the two machines answer two
  calls of `f` differently (`[none, none]` against `[none, some 7]`), so their strategies differ.

New proofs.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Bridge.StateFix

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Bridge
open Silmaril.Wasm.Jco (PTy PVal Meta)

variable {σ : Type}

/-! ## `compLTS` is an answering machine -/

theorem compStep_eq (md : Meta) (m : SMod σ) : CompStep md m = AnsStep (compAns md m) := by
  funext x l y
  apply propext
  constructor
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q
  · intro h
    cases h with
    | ask s q => exact .ask s q
    | ret s q => exact .ret s q

theorem compLTS_eq (md : Meta) (m : SMod σ) : compLTS md m = ansLTS (compAns md m) m.init := by
  unfold compLTS ansLTS
  rw [compStep_eq]

/-- On modules whose returned calls always lift, the two answers agree. -/
theorem compAnsS_eq (md : Meta) (m : SMod σ) (h : LiftTotal md m) :
    compAnsS md m = compAns md m := by
  funext q st
  obtain ⟨i, p⟩ := q
  cases p with
  | flat xs => rfl
  | vals vs =>
    simp only [compAnsS, compAns, stateCall]
    rcases hs : md.world[i]? with _ | s
    · rfl
    · have hmem : s ∈ md.world := List.mem_of_getElem? hs
      rcases hcl : checkLower (s.params.map PTy.toVal) vs with _ | xs
      · simp only [hcl, Option.bind_none]
      · rcases hc : m.callN s.name xs st with _ | ⟨ys, st'⟩
        · simp only [hcl, hc, Option.bind_some, Option.bind_none]
        · have hl := h s hmem xs st ys st' hc
          rcases hr : liftRes s.result ys with _ | r
          · rw [hr] at hl
            cases hl
          · simp only [hcl, hc, hr, Option.bind_some, Option.map_some]

/-! ## Plays of an answering machine -/

variable (f : sigU.Op → σ → Option Payload × σ)

theorem run_nil {s₀ : σ} {x y : (ansLTS f s₀).State} (h : (ansLTS f s₀).Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hs => cases hs

theorem run_plays {s₀ : σ} : ∀ (qs : List sigU.Op) (rs : List (Option Payload)) (s : σ)
    (y : (ansLTS f s₀).State),
    (ansLTS f s₀).Run (s, none) (ansPlays qs rs) y → rs.length = qs.length →
      rs = (ansList f s qs).1
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | q :: qs, r :: rs, s, y, hrun, hlen => by
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hrun
    have e₁ : x₁ = (s, none) := run_nil f h₁
    subst e₁
    have e₂ : x₂ = (s, some q) := by cases h₂; rfl
    subst e₂
    obtain ⟨y₁, y₂, g₁, g₂, g₃⟩ := LTS.Run.cons_inv h₃
    have e₃ : y₁ = (s, some q) := run_nil f g₁
    subst e₃
    have e₄ : r = (f q s).1 ∧ y₂ = ((f q s).2, none) := by
      cases g₂
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := e₄
    have ih := run_plays qs rs (f q s).2 y g₃ (by simpa using hlen)
    simp only [ansList, ih]

theorem run_answers {s₀ : σ} : ∀ (qs : List sigU.Op) (s : σ),
    (ansLTS f s₀).Run (s, none) (ansPlays qs (ansList f s qs).1) ((ansList f s qs).2, none)
  | [], _ => .nil _
  | q :: qs, s => by
    have h₁ : (ansLTS f s₀).step (s, none) (some (.inr (.ask q))) (s, some q) := AnsStep.ask s q
    have h₂ : (ansLTS f s₀).step (s, some q) (some (.inr (.ans q (f q s).1)))
        ((f q s).2, none) := AnsStep.ret s q
    exact .vis h₁ (.vis h₂ (run_answers qs (f q s).2))

theorem path_plays : ∀ (qs : List sigU.Op) (rs : List (Option Payload)),
    Path .idle (ansPlays qs rs) .idle
  | [], _ => .nil _
  | _ :: _, [] => .nil _
  | q :: qs, r :: rs => .cons (.ask q) (.cons (.ret q r) (path_plays qs rs))

theorem getLast_plays : ∀ (qs : List sigU.Op) (rs : List (Option Payload)),
    (ansPlays qs rs).getLast? = none ∨
      ∃ q r, (ansPlays qs rs).getLast? = some (.inr (.ans q r))
  | [], _ => .inl rfl
  | _ :: _, [] => .inl rfl
  | q :: qs, r :: rs => by
    rcases getLast_plays qs rs with h | ⟨q', r', h⟩
    · have e : ansPlays qs rs = [] := List.getLast?_eq_none_iff.1 h
      refine .inr ⟨q, r, ?_⟩
      simp [ansPlays, e]
    · refine .inr ⟨q', r', ?_⟩
      have hne : ansPlays qs rs ≠ [] := fun he => by simp [he] at h
      rw [ansPlays, List.getLast?_cons_cons, List.getLast?_cons, h]
      cases hp : ansPlays qs rs with
      | nil => exact absurd hp hne
      | cons a l => rfl

theorem plays_last (qs : List sigU.Op) (rs : List (Option Payload)) (p₀ : List (Move sigU sigU))
    (o : Move sigU sigU) (h : ansPlays qs rs = p₀ ++ [o]) : ¬ o.IsO := by
  have hl : (ansPlays qs rs).getLast? = some o := by rw [h]; simp
  rcases getLast_plays qs rs with h' | ⟨q, r, h'⟩
  · rw [h'] at hl
    cases hl
  · rw [h'] at hl
    cases hl
    simp [Move.IsO]

/-- **The strategy of an answering machine contains exactly the plays it answers.** -/
theorem mem_ans_iff (s₀ : σ) (qs : List sigU.Op) (rs : List (Option Payload))
    (hlen : rs.length = qs.length) :
    ansPlays qs rs ∈ Strategy.ofLTS (ansLTS f s₀) ↔ rs = (ansList f s₀ qs).1 := by
  constructor
  · intro hp
    obtain ⟨-, t, ht, hpre⟩ := Strategy.mem_generate.1 hp
    rcases hpre with hpre | ⟨p₀, o, he, -, ho⟩
    · have htr : ansPlays qs rs ∈ (ansLTS f s₀).Traces := by
        rcases ht with rfl | ⟨ht, -⟩
        · have e : ansPlays qs rs = [] := List.prefix_nil.1 hpre
          rw [e]
          exact ⟨_, .nil _⟩
        · exact LTS.traces_of_prefix ht hpre
      obtain ⟨y, hy⟩ := htr
      exact run_plays f qs rs s₀ y hy hlen
    · exact absurd ho (plays_last qs rs p₀ o he)
  · intro h
    subst h
    exact Strategy.mem_ofLTS_of_mem_traces ⟨_, run_answers f qs s₀⟩ ⟨_, path_plays qs _⟩

/-! ## The counterexample -/

theorem bump_answers : (ansList (compAns bumpMeta bumpMod) false [bumpQ, bumpQ]).1 = [none, none] :=
  rfl

theorem bump_answersS :
    (ansList (compAnsS bumpMeta bumpMod) false [bumpQ, bumpQ]).1 =
      [none, some (.vals [.u32 7])] :=
  rfl

/-- **On `bumpMod` the two machines have different strategies.** -/
theorem bump_differs :
    Strategy.ofLTS (compLTS bumpMeta bumpMod) ≠ Strategy.ofLTS (compLTSS bumpMeta bumpMod) := by
  intro heq
  have hp : ansPlays [bumpQ, bumpQ] [none, some (.vals [.u32 7])] ∈
      Strategy.ofLTS (compLTSS bumpMeta bumpMod) :=
    (mem_ans_iff _ false _ _ rfl).2 bump_answersS.symm
  rw [← heq, compLTS_eq] at hp
  have h := (mem_ans_iff _ false _ _ rfl).1 hp
  rw [bump_answers] at h
  simp at h

end Silmaril.Proofs.Wasm.Jco.Bridge.StateFix
