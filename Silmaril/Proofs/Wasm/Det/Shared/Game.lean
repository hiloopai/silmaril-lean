module

public import Silmaril.Proofs.Wasm.Det.Shared.Basic
public import Silmaril.Wasm.Game.Shared.Thms
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# Determinism of the store-passing instance strategy

Two runs of the store-passing transition system `I.shLts P` (`Silmaril.Wasm.Game.Shared`) along the
same play are related by `ShTwin`: both idle, or the threads of one export call `f` reached from
the invocation in the store of the question by store-writing runs (`RunsS`) with the same trace,
read off the play (import calls, answers and returned stores). Silent steps of either side keep
the relation (`twin_tau_left`/`twin_tau_right`), a common admissible non-trapping move keeps it
(`twin_vis`), and from twin running threads the next Proponent moves agree modulo traps
(`twin_p`): an import question carries the current store and an export answer the final store,
and `DetCfgS` compares outputs and stores. Hence `detModOn_shStrategy`.

New proofs (the structure follows `Silmaril.Proofs.Wasm.Det.Game.Instance`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game Silmaril.Wasm.Det.Shared
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile} {A : Store Nat → Store Nat → Prop}
  {S : Store Nat → Prop}

theorem config_store' (s : Store Nat) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

theorem ifaceOp?_eq {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.1.val = h ∧ e.2.1 = args := by
  unfold ifaceOp? at he
  split at he
  · split at he
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  · cases he

/-- The invocation of an export question, in the store it carries. -/
abbrev shInv (I : ScalarInstance) (f : I.shF.Op) : Config Nat :=
  invoke f.2.1 (I.addr f.1) f.2.2.1

/-- Two hidden states of the store-passing system reached along the same play. -/
inductive ShTwin (P : Profile) (I : ScalarInstance) (A : Store Nat → Store Nat → Prop)
    (S : Store Nat → Prop) : I.ShState → I.ShState → Prop where
  | idle : ShTwin P I A S .idle .idle
  | running {f : I.shF.Op} {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall}
      (hS : S f.2.1) (r₁ : RunsS P A (shInv I f) tr (t₁.config s₁))
      (r₂ : RunsS P A (shInv I f) tr (t₂.config s₂)) :
      ShTwin P I A S (.running f s₁ t₁) (.running f s₂ t₂)
  | waiting {f : I.shF.Op} {s : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} {e : I.shE.Op}
      {h : Nat} {args : List Val} (hS : S f.2.1) (r₁ : RunsS P A (shInv I f) tr (t₁.config s))
      (r₂ : RunsS P A (shInv I f) tr (t₂.config s)) (he : e.2.1 = s)
      (c₁ : CalloutAt s t₁ h args) (c₂ : CalloutAt s t₂ h args) :
      ShTwin P I A S (.waiting f s t₁ e) (.waiting f s t₂ e)

theorem steps_of_internal {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
    Steps P Det.noHost (t.config s) (t'.config s') :=
  Reach.steps (host := Det.noHost) (Relation.ReflTransGen.single h)

theorem twin_tau_left {x₁ x₁' x₂ : I.ShState} (ht : ShTwin P I A S x₁ x₂)
    (h : I.ShTrans P x₁ none x₁') : ShTwin P I A S x₁' x₂ := by
  cases ht with
  | idle => cases h
  | waiting => cases h
  | running hS r₁ r₂ =>
    cases h with
    | tau hi => exact .running hS (runsS_steps r₁ (steps_of_internal hi)) r₂

theorem twin_tau_right {x₁ x₂ x₂' : I.ShState} (ht : ShTwin P I A S x₁ x₂)
    (h : I.ShTrans P x₂ none x₂') : ShTwin P I A S x₁ x₂' := by
  cases ht with
  | idle => cases h
  | waiting => cases h
  | running hS r₁ r₂ =>
    cases h with
    | tau hi => exact .running hS r₁ (runsS_steps r₂ (steps_of_internal hi))

theorem twin_taus_left {x₁ y₁ : (I.shLts P).State} {x₂ : I.ShState} {l : List (Move I.shE I.shF)}
    (h : (I.shLts P).Run x₁ l y₁) (hl : l = []) (ht : ShTwin P I A S x₁ x₂) :
    ShTwin P I A S y₁ x₂ := by
  induction h with
  | nil => exact ht
  | tau hs _ ih => exact ih hl (twin_tau_left ht hs)
  | vis => cases hl

theorem twin_taus_right {x₁ : I.ShState} {x₂ y₂ : (I.shLts P).State} {l : List (Move I.shE I.shF)}
    (h : (I.shLts P).Run x₂ l y₂) (hl : l = []) (ht : ShTwin P I A S x₁ x₂) :
    ShTwin P I A S x₁ y₂ := by
  induction h with
  | nil => exact ht
  | tau hs _ ih => exact ih hl (twin_tau_right ht hs)
  | vis => cases hl

/-- The output of a running thread's Proponent move: an import question in the current store,
or an export answer with the final store. -/
theorem p_out {f : I.shF.Op} {s : Store Nat} {t : Thread} {m : Move I.shE I.shF}
    {q' : I.ShState} (h : I.ShTrans P (.running f s t) (some m) q') :
    (∃ hh args e, CalloutAt s t hh args ∧ I.importOp? hh args = some e ∧
        m = .inl (.ask (shOp s e)) ∧ q' = .waiting f s t (shOp s e)) ∨
      (∃ r v, ResultAt s t r ∧ Answer.ofResult? (I.exports.get f.1) r = some v ∧
        m = .inr (.ans f (s, v)) ∧ q' = .idle) := by
  cases h with
  | ucall callout op => exact .inl ⟨_, _, _, callout, op, rfl, rfl⟩
  | oret final answer => exact .inr ⟨_, _, final, answer, rfl, rfl⟩

theorem out_of_callout' {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hc : CalloutAt s t h args) : OutAt (t.config s) (.call h args) := by
  obtain ⟨E, a, hd⟩ := hc
  exact .call (E := E) (a := a) (by rw [config_store']; exact hd)

theorem ofResult?_trap' {ft : FnType} {v : Answer ft} (h : Answer.ofResult? ft .trap = some v) :
    v = .trap := by
  simp only [Answer.ofResult?, Option.some.injEq] at h
  exact h.symm

/-- The move a Core output of export call `f` in the store `s` is played as. -/
def ShMoveOf (I : ScalarInstance) (f : I.shF.Op) (s : Store Nat) : Out → Move I.shE I.shF → Prop
  | .call hh args, m => ∃ e, I.importOp? hh args = some e ∧ m = .inl (.ask (shOp s e))
  | .ret r, m => ∃ v, Answer.ofResult? (I.exports.get f.1) r = some v ∧ m = .inr (.ans f (s, v))

theorem shMoveOf_fun {f : I.shF.Op} {s : Store Nat} {o : Out} {m₁ m₂ : Move I.shE I.shF}
    (h₁ : ShMoveOf I f s o m₁) (h₂ : ShMoveOf I f s o m₂) : m₁ = m₂ := by
  cases o with
  | call hh args =>
    obtain ⟨e₁, he₁, rfl⟩ := h₁
    obtain ⟨e₂, he₂, rfl⟩ := h₂
    have he : e₁ = e₂ := Option.some.inj (he₁.symm.trans he₂)
    rw [he]
  | ret r =>
    obtain ⟨v₁, hv₁, rfl⟩ := h₁
    obtain ⟨v₂, hv₂, rfl⟩ := h₂
    have hv : v₁ = v₂ := Option.some.inj (hv₁.symm.trans hv₂)
    rw [hv]

/-- A Proponent move of a running thread is a trap, or plays a non-trapping output. -/
theorem p_move {f : I.shF.Op} {s : Store Nat} {t : Thread} {m : Move I.shE I.shF}
    {q' : I.ShState} (h : I.ShTrans P (.running f s t) (some m) q') :
    PTrap (shTraps I.exports) m ∨ ∃ o, OutAt (t.config s) o ∧ ShMoveOf I f s o m := by
  rcases p_out h with ⟨hh, args, e, hc, he, rfl, -⟩ | ⟨r, v, hr, hv, rfl, -⟩
  · exact .inr ⟨_, out_of_callout' hc, e, he, rfl⟩
  · by_cases ht : r = .trap
    · subst ht
      exact .inl (ofResult?_trap' hv)
    · exact .inr ⟨_, .ret ht hr, v, hv, rfl⟩

/-- Twin running threads: the next Proponent moves agree modulo traps. -/
theorem running_p (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f)) {f : I.shF.Op}
    {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} (hS : S f.2.1)
    (r₁ : RunsS P A (shInv I f) tr (t₁.config s₁)) (r₂ : RunsS P A (shInv I f) tr (t₂.config s₂))
    {q₁' q₂' : I.ShState} {m₁ m₂ : Move I.shE I.shF}
    (h₁ : I.ShTrans P (.running f s₁ t₁) (some m₁) q₁')
    (h₂ : I.ShTrans P (.running f s₂ t₂) (some m₂) q₂') :
    m₁ = m₂ ∨ PTrap (shTraps I.exports) m₁ ∨ PTrap (shTraps I.exports) m₂ := by
  rcases p_move h₁ with ht₁ | ⟨o₁, ho₁, hm₁⟩
  · exact .inr (.inl ht₁)
  rcases p_move h₂ with ht₂ | ⟨o₂, ho₂, hm₂⟩
  · exact .inr (.inr ht₂)
  have hd : o₁ = o₂ ∧ (t₁.config s₁).store = (t₂.config s₂).store := hD _ hS _ _ _ _ _ r₁ r₂ ho₁ ho₂
  have hs : s₁ = s₂ := by rw [← config_store' s₁ t₁, ← config_store' s₂ t₂]; exact hd.2
  have hm₂' : ShMoveOf I f s₁ o₁ m₂ := by rw [hd.1, hs]; exact hm₂
  exact .inl (shMoveOf_fun hm₁ hm₂')

/-- **Twin states make the same next Proponent move, modulo traps.** -/
theorem twin_p (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f))
    {q₁ q₂ q₁' q₂' : I.ShState} {m₁ m₂ : Move I.shE I.shF} (ht : ShTwin P I A S q₁ q₂)
    (h₁ : I.ShTrans P q₁ (some m₁) q₁') (h₂ : I.ShTrans P q₂ (some m₂) q₂') (hm₁ : m₁.IsP) :
    m₁ = m₂ ∨ PTrap (shTraps I.exports) m₁ ∨ PTrap (shTraps I.exports) m₂ := by
  cases ht with
  | idle =>
    cases h₁
    exact hm₁.elim
  | waiting =>
    cases h₁
    exact hm₁.elim
  | running hS r₁ r₂ => exact running_p hD hS r₁ r₂ h₁ h₂

theorem config_resume {s s' : Store Nat} {t : Thread} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    (resumeResult s t r).config s' = resumeIn (t.config s) E r s' := by
  simp only [resumeResult, hd, resumeIn]
  rfl

/-- A twin waiting thread resumed with an admissible answer. -/
theorem resume_run {f : I.shF.Op} {s s' : Store Nat} {t : Thread} {tr : List SCall} {hh : Nat}
    {args : List Val} (r : RunsS P A (shInv I f) tr (t.config s)) (c : CalloutAt s t hh args)
    (res : Result) (hA : A s s') :
    RunsS P A (shInv I f) (tr ++ [⟨hh, args, res, s'⟩]) ((resumeResult s t res).config s') := by
  obtain ⟨E, a, hd⟩ := c
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [config_store']
    exact hd
  have hA' : A (t.config s).store s' := by
    rw [config_store']
    exact hA
  rw [config_resume hd]
  exact runsS_snoc r hd' res hA'

/-- Twin running threads after a common non-trapping Proponent move. -/
theorem running_vis (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f)) {f : I.shF.Op}
    {s₁ s₂ : Store Nat} {t₁ t₂ : Thread} {tr : List SCall} (hS : S f.2.1)
    (r₁ : RunsS P A (shInv I f) tr (t₁.config s₁)) (r₂ : RunsS P A (shInv I f) tr (t₂.config s₂))
    {q₁' q₂' : I.ShState} {m : Move I.shE I.shF}
    (h₁ : I.ShTrans P (.running f s₁ t₁) (some m) q₁')
    (h₂ : I.ShTrans P (.running f s₂ t₂) (some m) q₂') : ShTwin P I A S q₁' q₂' := by
  rcases p_out h₁ with ⟨hh, args, e, hc₁, he₁, rfl, rfl⟩ | ⟨r, v, hr₁, hv₁, rfl, rfl⟩
  · rcases p_out h₂ with ⟨hh', args', e', hc₂, he₂, hm', rfl⟩ | ⟨_, _, _, _, hm', _⟩
    · obtain ⟨ho, hs⟩ := hD _ hS _ _ _ _ _ r₁ r₂ (out_of_callout' hc₁) (out_of_callout' hc₂)
      rw [config_store', config_store'] at hs
      subst hs
      cases ho
      rw [he₁] at he₂
      cases he₂
      exact .waiting hS r₁ r₂ rfl hc₁ hc₂
    · cases hm'
  · rcases p_out h₂ with ⟨_, _, _, _, _, hm', _⟩ | ⟨r', v', hr₂, hv₂, hm', rfl⟩
    · cases hm'
    · exact .idle

/-- **Twin states stay twins along a common admissible non-trapping move.** -/
theorem twin_vis {q₁ q₂ q₁' q₂' : I.ShState} {m : Move I.shE I.shF}
    (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f)) (ht : ShTwin P I A S q₁ q₂)
    (h₁ : I.ShTrans P q₁ (some m) q₁') (h₂ : I.ShTrans P q₂ (some m) q₂')
    (hok : ShOk I A S m) : ShTwin P I A S q₁' q₂' := by
  cases ht with
  | idle =>
    cases h₁
    cases h₂
    exact .running hok (.stop .refl) (.stop .refl)
  | @waiting f s t₁ t₂ tr e hh args hS r₁ r₂ he c₁ c₂ =>
    cases h₁ with
    | uret s' v =>
      cases h₂
      have hA : A s s' := he ▸ hok
      exact .running hS (resume_run r₁ c₁ _ hA) (resume_run r₂ c₂ _ hA)
  | running hS r₁ r₂ => exact running_vis hD hS r₁ r₂ h₁ h₂

/-- **Along the same admissible trap-free play, twin states stay twins.** -/
theorem twin_run (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f))
    {x₁ y₁ : (I.shLts P).State} {p : List (Move I.shE I.shF)} (h₁ : (I.shLts P).Run x₁ p y₁) :
    ∀ {x₂ y₂ : (I.shLts P).State}, (I.shLts P).Run x₂ p y₂ → ShTwin P I A S x₁ x₂ →
      (∀ m ∈ p, ¬ PTrap (shTraps I.exports) m ∧ ShOk I A S m) → ShTwin P I A S y₁ y₂ := by
  induction h₁ with
  | nil => exact fun h₂ ht _ => twin_taus_right h₂ rfl ht
  | tau hs _ ih => exact fun h₂ ht hp => ih h₂ (twin_tau_left ht hs) hp
  | vis hs _ ih =>
    intro x₂ y₂ h₂ ht hp
    obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ := LTS.Run.cons_inv h₂
    have ht' := twin_taus_right hz₁ rfl ht
    have hm := hp _ List.mem_cons_self
    exact ih hz (twin_vis hD ht' hs hz₂ hm.2) (fun m hm' => hp m (List.mem_cons_of_mem _ hm'))

/-- **Determinism of the store-passing strategy on admissible plays.** -/
theorem detModOn_shStrategy (hD : ∀ f : I.shF.Op, S f.2.1 → DetCfgS P A (shInv I f)) :
    DetModOn (ShOk I A S) (shTraps I.exports) (I.shStrategy P) := by
  intro c m₁ m₂ h₁ h₂ hm₁ _ hc hok
  obtain ⟨y₁, hy₁⟩ := ScalarInstance.mem_shStrategy_iff.1 h₁
  obtain ⟨y₂, hy₂⟩ := ScalarInstance.mem_shStrategy_iff.1 h₂
  obtain ⟨z₁, hc₁, hl₁⟩ := LTS.Run.of_append hy₁
  obtain ⟨z₂, hc₂, hl₂⟩ := LTS.Run.of_append hy₂
  have ht : ShTwin P I A S z₁ z₂ :=
    twin_run hD hc₁ hc₂ .idle fun m hm => ⟨hc m hm, hok m hm⟩
  obtain ⟨w₁, w₁', hw₁, hs₁, -⟩ := LTS.Run.cons_inv hl₁
  obtain ⟨w₂, w₂', hw₂, hs₂, -⟩ := LTS.Run.cons_inv hl₂
  exact twin_p hD (twin_taus_right hw₂ rfl (twin_taus_left hw₁ rfl ht)) hs₁ hs₂ hm₁

end Silmaril.Proofs.Wasm.Det.Shared
