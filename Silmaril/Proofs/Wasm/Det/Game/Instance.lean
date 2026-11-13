module

public import Silmaril.Wasm.Det.Game.Instance.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Proofs.Wasm.Det.Game.Trapped

/-!
# Determinism of instance strategies

Two runs of the hidden-state transition system of an instance along the same play are related
by `Twin`: idle stores related by a relation `S` on call states, or the threads of one export
call reached from `S`-related call states by Core runs (`Silmaril.Wasm.Det.Core.Runs`) with the
same import calls and answers, read off the play. If `S` makes export calls agree on their
outputs and is preserved by non-trapping returns (`CallRel`), Proponent's next moves agree
modulo traps (`twin_agree`). `S` is equality of reachable call states for determinism and any
pair of reachable call states for statelessness.

Strictness (`strict_strategy`): a thread resumed with a trap holds trapped code, which never
calls an import and finishes only with a trap (`Silmaril.Proofs.Wasm.Det.Game.reach_trapped`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

/-! ## Core facts -/

theorem config_store (s : Store Nat) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

theorem ifaceOp?_spec {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.1.val = h ∧ e.2.1 = args := by
  unfold ifaceOp? at he
  split at he
  · split at he
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  · cases he

theorem importOp?_inj {h₁ h₂ : Nat} {a₁ a₂ : List Val} {e : I.E.Op}
    (h₁' : I.importOp? h₁ a₁ = some e) (h₂' : I.importOp? h₂ a₂ = some e) : h₁ = h₂ ∧ a₁ = a₂ := by
  obtain ⟨rfl, rfl⟩ := ifaceOp?_spec h₁'
  obtain ⟨h, a⟩ := ifaceOp?_spec h₂'
  exact ⟨h, a⟩

theorem ofResult?_trap {ft : FnType} {v : Answer ft} (h : Answer.ofResult? ft .trap = some v) :
    v = .trap := by
  simp only [Answer.ofResult?, Option.some.injEq] at h
  exact h.symm

theorem result_ne_trap {ft : FnType} {r : Result} {v : Answer ft}
    (h : Answer.ofResult? ft r = some v) (hv : v ≠ .trap) : r ≠ .trap := by
  rintro rfl
  exact hv (ofResult?_trap h)

theorem invokeOk_of_typed {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {ft : FnType}
    {vs : List Val} (hfi : s.funcs[a]? = some fi) (hE : Expand fi.type ft.toComp)
    (hv : List.Forall₂ ScalarType.HasVal ft.params vs) : InvokeOk s a vs := by
  refine ⟨fi, _, _, hfi, hE, ?_⟩
  rw [Ty.toList_ofList]
  rw [List.forall₂_map_right_iff]
  clear hfi hE
  generalize ft.params = ps at hv
  induction hv with
  | nil => exact .nil
  | cons h _ ih => exact .cons ((ScalarType.hasVal_iff_valOk s _ _).1 h) ih

/-- Export calls of the game are typed invocations at every call state. -/
theorem invokeOk_callReach {s₀ s : Store Nat} (ht : ExportsTyped I s₀)
    (hs : CallReach P (entry I) s₀ s) (f : I.F.Op) : InvokeOk s (I.addr f.1) f.2.1 := by
  obtain ⟨fi, hfi, hE⟩ := ht f.1
  rw [← CallReach.funcs_eq hs] at hfi
  exact invokeOk_of_typed hfi hE f.2.2

/-- Extend a run by host-free steps. -/
theorem runs_steps {c d d' : Config Nat} {tr : List Call} (hr : Runs P c tr d)
    (hs : Steps P Det.noHost d d') : Runs P c tr d' := by
  induction hr with
  | stop h => exact .stop (h.trans hs)
  | call h hd _ ih => exact .call h hd (ih hs)

/-- Extend a run by an answered import call. -/
theorem runs_snoc {c d : Config Nat} {tr : List Call} {E : Ctx} {a h : Nat} {args : List Val}
    (hr : Runs P c tr d) (hd : decompose? d.store d.code = some (E, a, h, args)) (r : Result) :
    Runs P c (tr ++ [⟨h, args, r⟩]) (resumeAt d E r) := by
  induction hr with
  | stop hs => exact .call hs hd (.stop .refl)
  | call hs hd' _ ih => exact .call hs hd' (ih hd)

/-- A run of the machine is a host-free Core run. -/
theorem steps_of_reach {s s' : Store Nat} {t t' : Thread} (h : Reach P (s, t) (s', t')) :
    Steps P Det.noHost (t.config s) (t'.config s') :=
  Reach.steps (host := Det.noHost) h

/-- The callout of a thread, as a Core redex. -/
theorem decompose_of_callout {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hc : CalloutAt s t h args) :
    ∃ E a, decompose? (t.config s).store (t.config s).code = some (E, a, h, args) ∧
      ∀ r, (resumeResult s t r).config s = resumeAt (t.config s) E r := by
  obtain ⟨E, a, hd⟩ := hc
  refine ⟨E, a, by rw [config_store]; exact hd, fun r => ?_⟩
  simp only [resumeResult, hd, resumeAt, config_store]
  rfl

/-! ## Twin runs -/

/-- What a relation between call states must give: agreeing outputs of export calls, and
related stores after equal non-trapping returns. -/
structure CallRel (P : Profile) (I : ScalarInstance) (S : Store Nat → Store Nat → Prop) :
    Prop where
  agree : ∀ u₁ u₂ (f : I.F.Op), S u₁ u₂ →
    ObsAgree P (invoke u₁ (I.addr f.1) f.2.1) (invoke u₂ (I.addr f.1) f.2.1)
  next : ∀ u₁ u₂ (f : I.F.Op) tr (d₁ d₂ : Config Nat) (r : Result), S u₁ u₂ →
    Runs P (invoke u₁ (I.addr f.1) f.2.1) tr d₁ → Runs P (invoke u₂ (I.addr f.1) f.2.1) tr d₂ →
    d₁.code = r.toAdmin → d₂.code = r.toAdmin → r ≠ .trap → S d₁.store d₂.store

/-- Two hidden states reached along the same play. -/
inductive Twin (P : Profile) (I : ScalarInstance) (S : Store Nat → Store Nat → Prop) :
    I.HState → I.HState → Prop where
  | idle {s₁ s₂ : Store Nat} (hS : S s₁ s₂) : Twin P I S (.idle s₁) (.idle s₂)
  | running {f : I.F.Op} {s₁ s₂ u₁ u₂ : Store Nat} {t₁ t₂ : Thread} {tr : List Call}
      (hS : S u₁ u₂) (r₁ : Runs P (invoke u₁ (I.addr f.1) f.2.1) tr (t₁.config s₁))
      (r₂ : Runs P (invoke u₂ (I.addr f.1) f.2.1) tr (t₂.config s₂)) :
      Twin P I S (.running f s₁ t₁) (.running f s₂ t₂)
  | waiting {f : I.F.Op} {s₁ s₂ u₁ u₂ : Store Nat} {t₁ t₂ : Thread} {tr : List Call}
      {e : I.E.Op} {h : Nat} {args : List Val}
      (hS : S u₁ u₂) (r₁ : Runs P (invoke u₁ (I.addr f.1) f.2.1) tr (t₁.config s₁))
      (r₂ : Runs P (invoke u₂ (I.addr f.1) f.2.1) tr (t₂.config s₂))
      (c₁ : CalloutAt s₁ t₁ h args) (c₂ : CalloutAt s₂ t₂ h args) :
      Twin P I S (.waiting f s₁ t₁ e) (.waiting f s₂ t₂ e)

/-- The output reached by a Proponent move of a running thread. -/
theorem p_out {f : I.F.Op} {s u : Store Nat} {t : Thread} {tr : List Call} {m : Move I.E I.F}
    {q' : I.HState} (hr : Runs P (invoke u (I.addr f.1) f.2.1) tr (t.config s))
    (h : I.Trans P (.running f s t) m q') :
    (∃ e hh args d s' t', m = .inl (.ask e) ∧ q' = .waiting f s' t' e ∧
        Runs P (invoke u (I.addr f.1) f.2.1) tr d ∧ d = t'.config s' ∧
        CalloutAt s' t' hh args ∧ I.importOp? hh args = some e ∧ OutAt d (.call hh args)) ∨
      (∃ v d r s', m = .inr (.ans f v) ∧ q' = .idle s' ∧
        Runs P (invoke u (I.addr f.1) f.2.1) tr d ∧ d.store = s' ∧ d.code = r.toAdmin ∧
        Answer.ofResult? (I.exports.get f.1) r = some v) := by
  cases h with
  | @ucall _ _ s' _ t' hh args e run callout op =>
    obtain ⟨E, a, hd, -⟩ := decompose_of_callout callout
    exact .inl ⟨e, hh, args, _, s', t', rfl, rfl, runs_steps hr (steps_of_reach run), rfl,
      callout, op, .call hd⟩
  | @oret _ _ s' _ t' r v run final answer =>
    exact .inr ⟨v, _, r, s', rfl, rfl, runs_steps hr (steps_of_reach run), config_store _ _,
      final, answer⟩

/-- The move a Core output of export call `f` is played as. -/
def MoveOf (I : ScalarInstance) (f : I.F.Op) : Out → Move I.E I.F → Prop
  | .call h args, m => ∃ e, I.importOp? h args = some e ∧ m = .inl (.ask e)
  | .ret r, m => ∃ v, Answer.ofResult? (I.exports.get f.1) r = some v ∧ m = .inr (.ans f v)

theorem moveOf_fun {f : I.F.Op} {o : Out} {m₁ m₂ : Move I.E I.F} (h₁ : MoveOf I f o m₁)
    (h₂ : MoveOf I f o m₂) : m₁ = m₂ := by
  cases o with
  | call h args =>
    obtain ⟨e₁, he₁, rfl⟩ := h₁
    obtain ⟨e₂, he₂, rfl⟩ := h₂
    rw [he₁] at he₂
    cases he₂
    rfl
  | ret r =>
    obtain ⟨v₁, hv₁, rfl⟩ := h₁
    obtain ⟨v₂, hv₂, rfl⟩ := h₂
    rw [hv₁] at hv₂
    cases hv₂
    rfl

/-- A Proponent move of a running thread is a trap, or plays a non-trapping output. -/
theorem p_move {f : I.F.Op} {s u : Store Nat} {t : Thread} {tr : List Call}
    {m : Move I.E I.F} {q' : I.HState} (hr : Runs P (invoke u (I.addr f.1) f.2.1) tr (t.config s))
    (h : I.Trans P (.running f s t) m q') :
    PTrap (wasmTraps I.exports) m ∨
      ∃ d o, Runs P (invoke u (I.addr f.1) f.2.1) tr d ∧ OutAt d o ∧ MoveOf I f o m := by
  rcases p_out hr h with ⟨e, _, _, d, -, -, rfl, -, hd, -, -, he, ho⟩ |
    ⟨v, d, r, -, rfl, -, hd, -, hc, hv⟩
  · exact .inr ⟨d, _, hd, ho, e, he, rfl⟩
  · by_cases ht : r = .trap
    · exact .inl (ofResult?_trap (ht ▸ hv))
    · exact .inr ⟨d, _, hd, .ret ht hc, v, hv, rfl⟩

/-- **Twin runs make the same next Proponent move, modulo traps.** -/
theorem twin_p {S : Store Nat → Store Nat → Prop} (hS : CallRel P I S) {q₁ q₂ q₁' q₂' : I.HState}
    {m₁ m₂ : Move I.E I.F} (ht : Twin P I S q₁ q₂) (h₁ : I.Trans P q₁ m₁ q₁')
    (h₂ : I.Trans P q₂ m₂ q₂') (hm₁ : m₁.IsP) :
    m₁ = m₂ ∨ PTrap (wasmTraps I.exports) m₁ ∨ PTrap (wasmTraps I.exports) m₂ := by
  cases ht with
  | idle =>
    cases h₁
    exact hm₁.elim
  | waiting =>
    cases h₁
    exact hm₁.elim
  | running hu r₁ r₂ =>
    rcases p_move r₁ h₁ with ht₁ | ⟨d₁, o₁, hd₁, ho₁, hmo₁⟩
    · exact .inr (.inl ht₁)
    rcases p_move r₂ h₂ with ht₂ | ⟨d₂, o₂, hd₂, ho₂, hmo₂⟩
    · exact .inr (.inr ht₂)
    have ho : o₁ = o₂ := hS.agree _ _ _ hu _ _ _ _ _ hd₁ hd₂ ho₁ ho₂
    exact .inl (moveOf_fun hmo₁ (ho ▸ hmo₂))

theorem out_of_callout {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hc : CalloutAt s t h args) : OutAt (t.config s) (.call h args) := by
  obtain ⟨E, a, hd⟩ := hc
  exact .call (E := E) (a := a) (by rw [config_store]; exact hd)

/-- Twin threads answering the export call with the same non-trapping answer leave related
call states. -/
theorem twin_ret {S : Store Nat → Store Nat → Prop} (hS : CallRel P I S) {f : I.F.Op}
    {s₁ s₂ u₁ u₂ : Store Nat} {t₁ t₂ : Thread} {tr : List Call} {r₁ r₂ : Result}
    {v : I.F.Ar f} (hu : S u₁ u₂)
    (hag : ObsAgree P (invoke u₁ (I.addr f.1) f.2.1) (invoke u₂ (I.addr f.1) f.2.1))
    (r₁' : Runs P (invoke u₁ (I.addr f.1) f.2.1) tr (t₁.config s₁))
    (r₂' : Runs P (invoke u₂ (I.addr f.1) f.2.1) tr (t₂.config s₂))
    (final₁ : ResultAt s₁ t₁ r₁) (final₂ : ResultAt s₂ t₂ r₂)
    (answer₁ : Answer.ofResult? (I.exports.get f.1) r₁ = some v)
    (answer₂ : Answer.ofResult? (I.exports.get f.1) r₂ = some v)
    (hm : ¬ PTrap (wasmTraps I.exports) (.inr (.ans f v) : Move I.E I.F)) :
    Twin P I S (.idle s₁) (.idle s₂) := by
  have hne : v ≠ .trap := hm
  have hr₁ : r₁ ≠ .trap := result_ne_trap answer₁ hne
  have hr₂ : r₂ ≠ .trap := result_ne_trap answer₂ hne
  have heq : Out.ret r₁ = Out.ret r₂ := hag _ _ _ _ _ r₁' r₂' (.ret hr₁ final₁) (.ret hr₂ final₂)
  have hrr : r₁ = r₂ := Out.ret.inj heq
  have hS' : S (t₁.config s₁).store (t₂.config s₂).store :=
    hS.next _ _ _ _ _ _ _ hu r₁' r₂' final₁ (hrr ▸ final₂) hr₁
  rw [config_store, config_store] at hS'
  exact .idle hS'

/-- Twin running threads stay twins along a non-trapping Proponent move. -/
theorem twin_running {S : Store Nat → Store Nat → Prop} (hS : CallRel P I S) {f : I.F.Op}
    {s₁ s₂ u₁ u₂ : Store Nat} {t₁ t₂ : Thread} {tr : List Call} {m : Move I.E I.F}
    {q₁' q₂' : I.HState} (hu : S u₁ u₂) (r₁ : Runs P (invoke u₁ (I.addr f.1) f.2.1) tr (t₁.config s₁))
    (r₂ : Runs P (invoke u₂ (I.addr f.1) f.2.1) tr (t₂.config s₂))
    (h₁ : I.Trans P (.running f s₁ t₁) m q₁') (h₂ : I.Trans P (.running f s₂ t₂) m q₂')
    (hm : ¬ PTrap (wasmTraps I.exports) m) : Twin P I S q₁' q₂' := by
  have hag : ObsAgree P (invoke u₁ (I.addr f.1) f.2.1) (invoke u₂ (I.addr f.1) f.2.1) :=
    hS.agree u₁ u₂ f hu
  cases h₁ with
  | ucall run₁ callout₁ _ =>
    cases h₂ with
    | ucall run₂ callout₂ _ =>
      have hd₁ := runs_steps r₁ (steps_of_reach run₁)
      have hd₂ := runs_steps r₂ (steps_of_reach run₂)
      have heq := hag _ _ _ _ _ hd₁ hd₂ (out_of_callout callout₁) (out_of_callout callout₂)
      obtain ⟨rfl, rfl⟩ := Out.call.inj heq
      exact .waiting hu hd₁ hd₂ callout₁ callout₂
  | oret run₁ final₁ answer₁ =>
    cases h₂ with
    | oret run₂ final₂ answer₂ =>
      exact twin_ret hS hu hag (runs_steps r₁ (steps_of_reach run₁))
        (runs_steps r₂ (steps_of_reach run₂)) final₁ final₂ answer₁ answer₂ hm

/-- **Twin runs stay twins along a non-trapping move.** -/
theorem twin_step {S : Store Nat → Store Nat → Prop} (hS : CallRel P I S)
    {q₁ q₂ q₁' q₂' : I.HState} {m : Move I.E I.F} (ht : Twin P I S q₁ q₂)
    (h₁ : I.Trans P q₁ m q₁') (h₂ : I.Trans P q₂ m q₂') (hm : ¬ PTrap (wasmTraps I.exports) m) :
    Twin P I S q₁' q₂' := by
  cases ht with
  | idle hu =>
    cases h₁
    cases h₂
    exact .running hu (.stop .refl) (.stop .refl)
  | waiting hu r₁ r₂ c₁ c₂ =>
    cases h₁
    cases h₂
    obtain ⟨E₁, _a₁, hd₁, hres₁⟩ := decompose_of_callout c₁
    obtain ⟨E₂, _a₂, hd₂, hres₂⟩ := decompose_of_callout c₂
    exact .running hu ((hres₁ _).symm ▸ runs_snoc r₁ hd₁ _) ((hres₂ _).symm ▸ runs_snoc r₂ hd₂ _)
  | running hu r₁ r₂ => exact twin_running hS hu r₁ r₂ h₁ h₂ hm

/-- **Along the same trap-free play, twin runs agree on the next Proponent move modulo
traps.** -/
theorem twin_agree {S : Store Nat → Store Nat → Prop} (hS : CallRel P I S) :
    ∀ (c : List (Move I.E I.F)) {q₁ q₂ q₁' q₂' : I.HState} {m₁ m₂ : Move I.E I.F},
      Twin P I S q₁ q₂ → I.Path P q₁ (c ++ [m₁]) q₁' → I.Path P q₂ (c ++ [m₂]) q₂' →
      m₁.IsP → TrapFree (wasmTraps I.exports) c →
      m₁ = m₂ ∨ PTrap (wasmTraps I.exports) m₁ ∨ PTrap (wasmTraps I.exports) m₂
  | [], _, _, _, _, _, _, ht, h₁, h₂, hm, _ => by
    cases h₁ with
    | cons t₁ p₁ =>
      cases h₂ with
      | cons t₂ p₂ => exact twin_p hS ht t₁ t₂ hm
  | x :: c, _, _, _, _, _, _, ht, h₁, h₂, hm, hc => by
    cases h₁ with
    | cons t₁ p₁ =>
      cases h₂ with
      | cons t₂ p₂ =>
        exact twin_agree hS c (twin_step hS ht t₁ t₂ (hc x (by simp))) p₁ p₂ hm
          (fun y hy => hc y (by simp [hy]))

end Silmaril.Proofs.Wasm.Det.Game

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

/-! ## Paths of the transition system -/

theorem path_append {q q'' : I.HState} {a b : List (Move I.E I.F)}
    (h : I.Path P q (a ++ b) q'') : ∃ q', I.Path P q a q' ∧ I.Path P q' b q'' := by
  induction a generalizing q with
  | nil => exact ⟨q, .nil q, h⟩
  | cons x a ih =>
    cases h with
    | cons t p =>
      obtain ⟨q', h₁, h₂⟩ := ih p
      exact ⟨q', .cons t h₁, h₂⟩

theorem trans_pos {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q') :
    Silmaril.Games.Step q.pos m q'.pos := by
  cases h <;> constructor

theorem path_pos {q q' : I.HState} {p : List (Move I.E I.F)} (h : I.Path P q p q') :
    Silmaril.Games.Path q.pos p q'.pos := by
  induction h with
  | nil => exact .nil _
  | cons t _ ih => exact .cons (trans_pos t) ih

/-- A waiting state is at a callout. -/
theorem trans_waiting {q : I.HState} {m : Move I.E I.F} {f : I.F.Op} {s : Store Nat}
    {t : Thread} {e : I.E.Op} (h : I.Trans P q m (.waiting f s t e)) :
    ∃ hh args, CalloutAt s t hh args := by
  cases h with
  | ucall _ callout _ => exact ⟨_, _, callout⟩

theorem path_waiting {s₀ : Store Nat} {p : List (Move I.E I.F)} {f : I.F.Op} {s : Store Nat}
    {t : Thread} {e : I.E.Op} (h : I.Path P (.idle s₀) p (.waiting f s t e)) :
    ∃ hh args, CalloutAt s t hh args := by
  suffices ∀ q q', I.Path P q p q' → (∀ f s t e, q = .waiting f s t e →
      ∃ hh args, CalloutAt s t hh args) → ∀ f s t e, q' = .waiting f s t e →
        ∃ hh args, CalloutAt s t hh args from
    this _ _ h (fun _ _ _ _ h => nomatch h) _ _ _ _ rfl
  intro q q' hp
  clear h
  induction hp with
  | nil => exact id
  | cons t _ ih =>
    intro _
    apply ih
    rintro f s t' e rfl
    exact trans_waiting t

/-! ## Reachable states -/

/-- The hidden states reachable from `idle s₀`: call states reachable by finished export calls,
and threads of export calls run from them. -/
inductive One (P : Profile) (I : ScalarInstance) (s₀ : Store Nat) : I.HState → Prop where
  | idle {s : Store Nat} (hs : CallReach P (entry I) s₀ s) : One P I s₀ (.idle s)
  | running {f : I.F.Op} {s u : Store Nat} {t : Thread} {tr : List Call}
      (hu : CallReach P (entry I) s₀ u) (hr : Runs P (invoke u (I.addr f.1) f.2.1) tr (t.config s)) :
      One P I s₀ (.running f s t)
  | waiting {f : I.F.Op} {s u : Store Nat} {t : Thread} {tr : List Call} {e : I.E.Op} {hh : Nat}
      {args : List Val} (hu : CallReach P (entry I) s₀ u)
      (hr : Runs P (invoke u (I.addr f.1) f.2.1) tr (t.config s)) (hc : CalloutAt s t hh args) :
      One P I s₀ (.waiting f s t e)

theorem one_step {s₀ : Store Nat} (ht : ExportsTyped I s₀) {q q' : I.HState}
    {m : Move I.E I.F} (ho : One P I s₀ q) (h : I.Trans P q m q') : One P I s₀ q' := by
  cases ho with
  | idle hs =>
    cases h
    exact .running hs (.stop .refl)
  | running hu hr =>
    rename_i f _ _ _ _
    rcases p_out hr h with ⟨_, _, _, d, s', t', -, rfl, hd, rfl, hc, -, -⟩ |
      ⟨-, d, r, s', -, rfl, hd, hs, hc, -⟩
    · exact .waiting hu hd hc
    · rw [← hs]
      exact .idle (.call hu ⟨f.1, rfl⟩ (invokeOk_callReach ht hu f) hd hc)
  | waiting hu hr hc =>
    cases h
    obtain ⟨E, _a, hd, hres⟩ := decompose_of_callout hc
    exact .running hu ((hres _).symm ▸ runs_snoc hr hd _)

theorem one_path {s₀ : Store Nat} (ht : ExportsTyped I s₀) {q q' : I.HState}
    {p : List (Move I.E I.F)} (ho : One P I s₀ q) (h : I.Path P q p q') : One P I s₀ q' := by
  induction h with
  | nil => exact ho
  | cons t _ ih => exact ih (one_step ht ho t)

/-- After a play ending idle, the hidden state is a reachable call state. -/
theorem idle_reach {s₀ : Store Nat} (ht : ExportsTyped I s₀) {p : List (Move I.E I.F)}
    {q : I.HState} (hp : I.Path P (.idle s₀) p q) (hpos : Silmaril.Games.Path .idle p .idle) :
    ∃ s, q = .idle s ∧ CallReach P (entry I) s₀ s := by
  have hq : q.pos = .idle := Silmaril.Games.Path.det (path_pos hp) hpos
  cases one_path ht (.idle .init) hp with
  | idle hs => exact ⟨_, rfl, hs⟩
  | running => cases hq
  | waiting => cases hq

/-! ## Determinism, statelessness and strictness of instance strategies -/

/-- **A deterministic module has a deterministic strategy, modulo traps.** -/
theorem detMod_strategy {s₀ : Store Nat} (hD : DetModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : DetMod (wasmTraps I.exports) (I.strategy P s₀) := by
  have hS : CallRel P I (fun u₁ u₂ => u₁ = u₂ ∧ CallReach P (entry I) s₀ u₁) :=
    { agree := by
        rintro u _ f ⟨rfl, hu⟩
        exact DetCfg.obsAgree (hD u hu _ ⟨f.1, rfl⟩ _ (invokeOk_callReach ht hu f))
      next := by
        rintro u _ f tr d₁ d₂ r ⟨rfl, hu⟩ h₁ h₂ hc₁ hc₂ hr
        have hd := hD u hu _ ⟨f.1, rfl⟩ _ (invokeOk_callReach ht hu f) tr d₁ d₂ _ _ h₁ h₂
          (.ret hr hc₁) (.ret hr hc₂)
        exact ⟨hd.2, .call hu ⟨f.1, rfl⟩ (invokeOk_callReach ht hu f) h₁ hc₁⟩ }
  intro c m₁ m₂ h₁ h₂ hm₁ _ hc
  obtain ⟨q₁, hp₁⟩ := ScalarInstance.mem_strategy_iff.1 h₁
  obtain ⟨q₂, hp₂⟩ := ScalarInstance.mem_strategy_iff.1 h₂
  exact twin_agree hS c (.idle ⟨rfl, .init⟩) hp₁ hp₂ hm₁ hc

/-- **A stateless module has a stateless strategy, modulo traps.** -/
theorem statelessMod_strategy {s₀ : Store Nat} (hD : StatelessModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : StatelessMod (wasmTraps I.exports) (I.strategy P s₀) := by
  have hS : CallRel P I (fun u₁ u₂ => CallReach P (entry I) s₀ u₁ ∧ CallReach P (entry I) s₀ u₂) :=
    { agree := by
        rintro u₁ u₂ f ⟨h₁, h₂⟩
        exact hD _ ⟨f.1, rfl⟩ u₁ u₂ f.2.1 h₁ h₂ (invokeOk_callReach ht h₁ f)
          (invokeOk_callReach ht h₂ f)
      next := by
        rintro u₁ u₂ f tr d₁ d₂ r ⟨hu₁, hu₂⟩ h₁ h₂ hc₁ hc₂ -
        exact ⟨.call hu₁ ⟨f.1, rfl⟩ (invokeOk_callReach ht hu₁ f) h₁ hc₁,
          .call hu₂ ⟨f.1, rfl⟩ (invokeOk_callReach ht hu₂ f) h₂ hc₂⟩ }
  intro h₁ h₂ _ _ hP₁ hP₂ c m₁ m₂ hc₁ hc₂ hm₁ _ hc
  obtain ⟨q₁, hp₁⟩ := ScalarInstance.mem_strategy_iff.1 hc₁
  obtain ⟨q₂, hp₂⟩ := ScalarInstance.mem_strategy_iff.1 hc₂
  rw [List.append_assoc] at hp₁ hp₂
  obtain ⟨r₁, hr₁, hp₁'⟩ := path_append hp₁
  obtain ⟨r₂, hr₂, hp₂'⟩ := path_append hp₂
  obtain ⟨s₁, rfl, hs₁⟩ := idle_reach ht hr₁ hP₁
  obtain ⟨s₂, rfl, hs₂⟩ := idle_reach ht hr₂ hP₂
  exact twin_agree hS c (.idle ⟨hs₁, hs₂⟩) hp₁' hp₂' hm₁ hc

/-- Resuming a callout with a trap gives trapped code. -/
theorem resume_trap {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val}
    (hc : CalloutAt s t hh args) : ∃ (E : Ctx) (F : Frame), resumeResult s t .trap = .active F (E.fill [.trap]) := by
  obtain ⟨E, a, hd⟩ := hc
  exact ⟨E, (t.config s).frame, by simp [resumeResult, hd, Result.toAdmin]⟩

/-- A Proponent move from trapped code is a trap answer. -/
theorem trapped_move {f : I.F.Op} {s : Store Nat} {t : Thread} {E : Ctx} {F : Frame}
    {b : Move I.E I.F} {q : I.HState} (hE : t = .active F (E.fill [.trap]))
    (h : I.Trans P (.running f s t) b q) : PTrap (wasmTraps I.exports) b := by
  subst hE
  cases h with
  | ucall run callout _ =>
    obtain ⟨E', hE'⟩ := reach_trapped run
    obtain ⟨E₀, a₀, hd⟩ := callout
    rw [hE', Ctx.decompose?_fill_trap] at hd
    cases hd
  | oret run final answer =>
    obtain ⟨E', hE'⟩ := reach_trapped run
    have hr := fill_trap_toAdmin (hE'.symm.trans final)
    subst hr
    exact ofResult?_trap answer

/-- **Instance strategies are strict**: after an import answers with a trap, the export call
answers with a trap. -/
theorem strict_strategy (s₀ : Store Nat) :
    Strict (wasmTraps I.imports) (wasmTraps I.exports) (I.strategy P s₀) := by
  intro p e v b hm hv
  obtain ⟨q, hq⟩ := ScalarInstance.mem_strategy_iff.1 hm
  obtain ⟨q₀, hp₀, hrest⟩ := path_append hq
  cases hrest with
  | cons t₁ hrest' =>
    cases hrest' with
    | cons t₂ _ =>
      cases t₁
      obtain ⟨hh, args, hc⟩ := path_waiting hp₀
      have hv' : v = .trap := hv
      subst hv'
      obtain ⟨E, F, hE⟩ := resume_trap hc
      exact trapped_move hE t₂

end Silmaril.Proofs.Wasm.Det.Game

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

/-! ## From Core runs to plays -/

/-- A host-free Core run from a thread is a run of the machine to a thread denoting its end. -/
theorem reach_of_steps {s : Store Nat} {t : Thread} {d : Config Nat}
    (h : Steps P Det.noHost (t.config s) d) :
    ∃ t', Reach P (s, t) (d.store, t') ∧ t'.config d.store = d := by
  induction h with
  | refl => exact ⟨t, by rw [config_store], by rw [config_store]⟩
  | @tail e d' _ hst ih =>
    obtain ⟨t', hr, hc⟩ := ih
    refine ⟨.active d'.frame d'.code, hr.tail ⟨d'.frame, d'.code, rfl, ?_⟩, rfl⟩
    rw [hc]
    exact hst

/-- The plays of a typed trace: each call is played as an import question and its answer. -/
inductive PlayOf (I : ScalarInstance) : List Call → List (Move I.E I.F) → Prop where
  | nil : PlayOf I [] []
  | cons {h : Nat} {args : List Val} {tr : List Call} {p : List (Move I.E I.F)} {e : I.E.Op}
      {r : Result} (v : I.E.Ar e) (he : I.importOp? h args = some e) (hr : v.toResult = r)
      (hp : PlayOf I tr p) :
      PlayOf I (⟨h, args, r⟩ :: tr) (.inl (.ask e) :: .inl (.ans e v) :: p)

theorem playOf_fun {tr : List Call} {p₁ p₂ : List (Move I.E I.F)} (h₁ : PlayOf I tr p₁)
    (h₂ : PlayOf I tr p₂) : p₁ = p₂ := by
  induction h₁ generalizing p₂ with
  | nil => cases h₂; rfl
  | cons v he hr _ ih =>
    cases h₂ with
    | cons v' he' hr' hp' =>
      rw [he] at he'
      cases he'
      have hv : v = v' := Answer.toResult_injective (hr.trans hr'.symm)
      rw [hv, ih hp']

theorem playOf_trapFree {tr : List Call} {p : List (Move I.E I.F)} (h : PlayOf I tr p) :
    TrapFree (wasmTraps I.exports) p := by
  induction h with
  | nil => exact fun _ hm => absurd hm (by simp)
  | cons v he _ _ ih =>
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact id
    rcases List.mem_cons.1 hm with rfl | hm
    · exact id
    · exact ih m hm

/-- One answered import call of a Core run is an import question and its answer. -/
theorem play_call {f : I.F.Op} {c₀ d₀ e₀ : Config Nat} {E : Ctx} {a h : Nat} {args : List Val}
    {r : Result} {tr' : List Call} (hs : Steps P Det.noHost c₀ d₀)
    (hd : decompose? d₀.store d₀.code = some (E, a, h, args))
    (ih : ∀ {s : Store Nat} {t : Thread}, t.config s = resumeAt d₀ E r → TypedTrace I tr' →
      ∃ p s' t', PlayOf I tr' p ∧ I.Path P (.running f s t) p (.running f s' t') ∧
        Steps P Det.noHost (t'.config s') e₀)
    {s : Store Nat} {t : Thread} (ht : t.config s = c₀) (htr : TypedTrace I (⟨h, args, r⟩ :: tr')) :
    ∃ p s' t', PlayOf I (⟨h, args, r⟩ :: tr') p ∧ I.Path P (.running f s t) p (.running f s' t') ∧
      Steps P Det.noHost (t'.config s') e₀ := by
  obtain ⟨e, v, he, hv⟩ := htr _ (List.mem_cons_self ..)
  have hv' : r = v.toResult := hv
  obtain ⟨t₀, hr₀, hc₀⟩ := reach_of_steps (ht ▸ hs)
  have hco : CalloutAt d₀.store t₀ h args := ⟨E, a, by rw [hc₀]; exact hd⟩
  obtain ⟨E', a', hd', hres⟩ := decompose_of_callout hco
  have hd'' : decompose? d₀.store d₀.code = some (E', a', h, args) := by rw [← hc₀]; exact hd'
  have hE : E' = E := by
    rw [hd] at hd''
    cases hd''
    rfl
  have hcfg : (resumeResult d₀.store t₀ v.toResult).config d₀.store = resumeAt d₀ E r := by
    rw [hres, hc₀, hE, ← hv']
  obtain ⟨p, s', t', hp, hpath, hst⟩ := ih hcfg (fun x hx => htr x (List.mem_cons_of_mem _ hx))
  exact ⟨_, s', t', .cons v he hv'.symm hp, .cons (.ucall hr₀ hco he) (.cons (.uret v) hpath),
    hst⟩

/-- **A Core run with a typed trace is a play** of a running export call. -/
theorem play_of_runs {f : I.F.Op} {c d : Config Nat} {tr : List Call} (hr : Runs P c tr d) :
    ∀ {s : Store Nat} {t : Thread}, t.config s = c → TypedTrace I tr →
      ∃ p s' t', PlayOf I tr p ∧ I.Path P (.running f s t) p (.running f s' t') ∧
        Steps P Det.noHost (t'.config s') d := by
  induction hr with
  | stop hs => exact fun ht _ => ⟨[], _, _, .nil, .nil _, ht ▸ hs⟩
  | call hs hd _ ih => exact fun ht htr => play_call hs hd ih ht htr

/-- The last move of a play read off a Core run. -/
theorem last_move {f : I.F.Op} {s : Store Nat} {t : Thread} {d : Config Nat} {o : Out}
    (hs : Steps P Det.noHost (t.config s) d) (ho : OutAt d o) (hg : GameOut I f o) :
    ∃ m q, I.Trans P (.running f s t) m q ∧ MoveOf I f o m := by
  obtain ⟨t', hr, hc⟩ := reach_of_steps hs
  cases ho with
  | ret hne hcode =>
    obtain ⟨v, hv⟩ := hg
    exact ⟨_, _, .oret hr (by show (t'.config d.store).code = _; rw [hc]; exact hcode) hv, v, hv, rfl⟩
  | call hd =>
    obtain ⟨e, he⟩ := hg
    exact ⟨_, _, .ucall hr ⟨_, _, by rw [hc]; exact hd⟩ he, e, he, rfl⟩

theorem moveOf_inj {f : I.F.Op} {o₁ o₂ : Out} {m : Move I.E I.F} (h₁ : MoveOf I f o₁ m)
    (h₂ : MoveOf I f o₂ m) : o₁ = o₂ := by
  cases o₁ with
  | call h₁' a₁ =>
    cases o₂ with
    | call h₂' a₂ =>
      obtain ⟨e₁, he₁, rfl⟩ := h₁
      obtain ⟨e₂, he₂, he⟩ := h₂
      cases he
      obtain ⟨rfl, rfl⟩ := importOp?_inj he₁ he₂
      rfl
    | ret r => obtain ⟨_, _, rfl⟩ := h₁; obtain ⟨_, _, h⟩ := h₂; cases h
  | ret r₁ =>
    cases o₂ with
    | call _ _ => obtain ⟨_, _, rfl⟩ := h₁; obtain ⟨_, _, h⟩ := h₂; cases h
    | ret r₂ =>
      obtain ⟨v₁, hv₁, rfl⟩ := h₁
      obtain ⟨v₂, hv₂, he⟩ := h₂
      cases he
      rw [← Answer.toResult_of_ofResult? hv₁, ← Answer.toResult_of_ofResult? hv₂]

/-- A non-trapping output is not played as a trap. -/
theorem moveOf_not_trap {f : I.F.Op} {d : Config Nat} {o : Out} {m : Move I.E I.F}
    (ho : OutAt d o) (hm : MoveOf I f o m) : ¬ PTrap (wasmTraps I.exports) m := by
  cases ho with
  | ret hne _ =>
    obtain ⟨v, hv, rfl⟩ := hm
    intro ht
    have ht' : v = .trap := ht
    subst ht'
    exact hne (Answer.toResult_of_ofResult? hv).symm
  | call _ =>
    obtain ⟨e, -, rfl⟩ := hm
    exact id

theorem path_snoc {q q' q'' : I.HState} {p : List (Move I.E I.F)} {m : Move I.E I.F}
    (h : I.Path P q p q') (ht : I.Trans P q' m q'') : I.Path P q (p ++ [m]) q'' := by
  induction h with
  | nil => exact .cons ht (.nil _)
  | cons t _ ih => exact .cons t (ih ht)

theorem trans_isP {f : I.F.Op} {s : Store Nat} {t : Thread} {m : Move I.E I.F} {q : I.HState}
    (h : I.Trans P (.running f s t) m q) : m.IsP := by
  cases h <;> trivial

/-- **A deterministic strategy gives output agreement of the first export call**, against
every trace a game environment can produce. -/
theorem obsAgree_of_detMod {s₀ : Store Nat} (hD : DetMod (wasmTraps I.exports) (I.strategy P s₀))
    (f : I.F.Op) {tr : List Call} {d₁ d₂ : Config Nat} {o₁ o₂ : Out} (htr : TypedTrace I tr)
    (h₁ : Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₁)
    (h₂ : Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₂) (ho₁ : OutAt d₁ o₁) (ho₂ : OutAt d₂ o₂)
    (hg₁ : GameOut I f o₁) (hg₂ : GameOut I f o₂) : o₁ = o₂ := by
  obtain ⟨p₁, s₁, t₁, hp₁, hpath₁, hs₁⟩ := play_of_runs (f := f) (t := I.initThread f) h₁ rfl htr
  obtain ⟨p₂, s₂, t₂, hp₂, hpath₂, hs₂⟩ := play_of_runs (f := f) (t := I.initThread f) h₂ rfl htr
  have hpp : p₂ = p₁ := playOf_fun hp₂ hp₁
  subst hpp
  obtain ⟨m₁, q₁, ht₁, hm₁⟩ := last_move hs₁ ho₁ hg₁
  obtain ⟨m₂, q₂, ht₂, hm₂⟩ := last_move hs₂ ho₂ hg₂
  have hmem₁ : (.inr (.ask f) :: p₂) ++ [m₁] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2 ⟨q₁, .cons (.call s₀ f) (path_snoc hpath₁ ht₁)⟩
  have hmem₂ : (.inr (.ask f) :: p₂) ++ [m₂] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2 ⟨q₂, .cons (.call s₀ f) (path_snoc hpath₂ ht₂)⟩
  have hfree : TrapFree (wasmTraps I.exports) (.inr (.ask f) :: p₂) := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact id
    · exact playOf_trapFree hp₂ m hm
  rcases hD _ m₁ m₂ hmem₁ hmem₂ (trans_isP ht₁) (trans_isP ht₂) hfree with h | h | h
  · exact moveOf_inj hm₁ (h ▸ hm₂)
  · exact (moveOf_not_trap ho₁ hm₁ h).elim
  · exact (moveOf_not_trap ho₂ hm₂ h).elim

end Silmaril.Proofs.Wasm.Det.Game
