module

public import Silmaril.Proofs.Wasm.Game.Adequacy.RunTyping
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Closed-world runs and plays of the composite

The bridge between Core reduction under a strategy-definable host (`hostOf`)
and plays of the closed program `I.closedWith P s K = K.strategy ≫ I.strategy P s`:

* `run_of_answer` (game to operations): an answer of the composite comes from
  a finite Core run to a result;
* `answer_of_run` (operations to game): a finite Core run to a result is
  answered by the composite;
* `activation_of_run`: the store left by the closed-world run is the store the
  strategy persists (the run is a complete activation whose environment moves
  agree with `K`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-- Prepending a host-free step to a nonempty run of the strategy from a running state. -/
theorem Path.internal_head {P : Profile} {f : I.F.Op} {s s₁ : Store Nat} {t t₁ : Thread}
    {p : List (Move I.E I.F)} {q : I.HState} (hne : p ≠ [])
    (hi : InternalP P (s, t) (s₁, t₁)) (hp : I.Path P (.running f s₁ t₁) p q) :
    I.Path P (.running f s t) p q := by
  cases hp with
  | nil => exact absurd rfl hne
  | cons htr hrest =>
    cases htr with
    | ucall run callout op =>
      exact .cons (.ucall (Relation.ReflTransGen.head hi run) callout op) hrest
    | oret run final answer =>
      exact .cons (.oret (Relation.ReflTransGen.head hi run) final answer) hrest

/-- From an idle state, a path with no upper move is empty. -/
theorem Path.nil_of_idle {P : Profile} {s : Store Nat} {p : List (Move I.E I.F)}
    {q : I.HState} (hp : I.Path P (.idle s) p q) (hu : upper p = []) : p = [] ∧ q = .idle s := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons ht _ => cases ht; simp at hu

/-- A host-free run to a callout answered as `K` answers it is a Core run under `hostOf`
to the resumed thread. -/
private theorem callout_answer_steps {P : Profile} {K : Silmaril.Wasm.Game.Env I.E}
    {s s' : Store Nat} {th t' : Thread} {h : Nat} {args : List Val} {e : I.E.Op}
    {v : I.E.Ar e} (run : Reach P (s, th) (s', t')) (callout : CalloutAt s' t' h args)
    (op : I.importOp? h args = some e) (hans : K.Answers e v) :
    Steps P (hostOf I.imports K) (th.config s)
      ((resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v)).config s') :=
  (Reach.steps (host := hostOf I.imports K) run).tail
    (calloutAt_step (P := P) (host := hostOf I.imports K) callout ⟨_, op, Or.inl ⟨_, hans, rfl⟩⟩)

/-- Game to operations, from a running state: a run of the strategy whose upper part is the
answer `w` and whose lower part agrees with `K` is a Core run under `hostOf` to a result
read as `w`. -/
theorem steps_of_path {P : Profile} {K : Silmaril.Wasm.Game.Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} : ∀ (n : Nat) (p : List (Move I.E I.F)) (s : Store Nat) (t : Thread)
      (q : I.HState), p.length ≤ n → I.Path P (.running f s t) p q →
      upper p = [.ans f w] → K.Agrees (lower p) →
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (t.config s) c' ∧ c'.code = r.toAdmin ∧
          Answer.ofResult? (I.exports.get f.1) r = some w ∧ q = .idle c'.store := by
  intro n
  induction n with
  | zero =>
    intro p s t q hn _ hu _
    exact absurd hu (by simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)])
  | succ n ih =>
    intro p s t q hn hp hu hK
    rcases hp with _ | ⟨_ | ⟨run, callout, op⟩ | _ | ⟨run, final, answer⟩, hrest⟩
    · exact absurd hu (by simp)
    · rcases hrest with _ | ⟨_ | _ | ⟨v⟩ | _, hrest'⟩
      · exact absurd hu (by simp)
      · obtain _ | _ | ⟨hans, hK'⟩ := hK
        obtain ⟨c', r, hsteps, hfinal, hans', hq⟩ :=
          ih _ _ _ _ (Nat.le_of_succ_le (Nat.le_of_succ_le_succ hn)) hrest' hu hK'
        exact ⟨c', r, (callout_answer_steps run callout op hans).trans hsteps, hfinal, hans', hq⟩
    · obtain ⟨hw, hu'⟩ := List.cons.inj hu
      cases hw
      obtain ⟨-, hq⟩ := Path.nil_of_idle hrest hu'
      exact ⟨_, _, Reach.steps run, final, answer, by rw [hq, Thread.config_store]⟩

/-- A callout at the head of a thread, answered with `w'`, in front of a run of the resumed
thread. -/
private theorem Path.callout_head {P : Profile} {f : I.F.Op} {s : Store Nat} {t : Thread}
    {E : Ctx} {a hh : Nat} {args : List Val} {e : I.E.Op} {w' : I.E.Ar e}
    {p : List (Move I.E I.F)} {q : I.HState}
    (hd : decompose? s (t.config s).code = some (E, a, hh, args))
    (he : I.importOp? hh args = some e)
    (hp : I.Path P (.running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w')))
      p q) :
    I.Path P (.running f s t) (.inl (.ask e) :: .inl (.ans e w') :: p) q :=
  .cons (.ucall Relation.ReflTransGen.refl ⟨E, a, hd⟩ he) (.cons (.uret w') hp)

/-- Operations to game, from a thread: a Core run under `hostOf` to a result read as `w` is
a run of the strategy to the answer `w` whose environment moves agree with `K`. -/
theorem path_of_steps {P : Profile} {K : Silmaril.Wasm.Game.Env I.E} {f : I.F.Op}
    {w : I.F.Ar f} {r : Result} (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    {c c' : Config Nat} (run : Steps P (hostOf I.imports K) c c')
    (final : c'.code = r.toAdmin) :
    ∀ (s : Store Nat) (t : Thread), c = t.config s →
      ∃ l : List (Ev I.E), K.Agrees l ∧
        I.Path P (.running f s t) (l.map .inl ++ [.inr (.ans f w)]) (.idle c'.store) := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s t hc
    have hfinal : (t.config s).code = r.toAdmin := hc ▸ final
    have hstore : c'.store = s := by rw [hc, Thread.config_store]
    refine ⟨[], .nil, ?_⟩
    rw [hstore]
    exact .cons (.oret Relation.ReflTransGen.refl hfinal hr) (.nil _)
  | @head c₀ b hstep _ ih =>
    show ∀ (s : Store Nat) (t : Thread), c₀ = t.config s → ∃ l : List (Ev I.E), K.Agrees l ∧
      I.Path P (.running f s t) (l.map .inl ++ [.inr (.ans f w)]) (.idle c'.store)
    intro s t hc
    rcases (stepP_iff P _ s t _).mp (hc ▸ hstep) with
      ⟨s₁, f₁, code₁, hb, hi⟩ | ⟨E, a, hh, args, hd, ⟨s₁, r₁, hr₁, hb⟩ | ⟨-, hb⟩⟩
    · obtain ⟨l, h3, hp⟩ := ih s₁ (.active f₁ code₁) hb
      exact ⟨l, h3, Path.internal_head (by simp) hi hp⟩
    · obtain ⟨e, he, ⟨w', hans, hout⟩ | ⟨-, hout⟩⟩ := hr₁
      · obtain ⟨rfl, rfl⟩ : s = s₁ ∧ r₁ = Answer.toResult w' := by simpa [eq_comm] using hout
        obtain ⟨l, h3, hp⟩ := ih s (resumeResult s t (Answer.toResult w')) hb
        exact ⟨.ask e :: .ans e w' :: l, .answered hans h3, Path.callout_head hd he hp⟩
      · cases hout
    · exact ih s t hb

/-- **Game to operations.** An answer of the composite comes from a finite Core run (under
the induced host) to a result. -/
theorem run_of_answer {P : Profile} {s : Store Nat} {K : Silmaril.Wasm.Game.Env I.E}
    {f : I.F.Op} {w : I.F.Ar f} (h : Responds (I.closedWith P s K) f w) :
    ∃ (c' : Config Nat) (r : Result),
      Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c' ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w := by
  obtain ⟨p, hp, henv, hx⟩ := Env.mem_comp_iff.1 h
  obtain ⟨q, hpath⟩ := mem_strategy_iff.1 hp
  cases hpath with
  | nil => simp at hx
  | cons htr hrest =>
    cases htr with
    | call s f' =>
      simp only [upper_cons_inr, List.map_cons, List.cons.injEq, Sum.inr.injEq] at hx
      obtain ⟨hf, hx⟩ := hx
      cases hf
      have hu : upper _ = [Ev.ans f w] :=
        List.map_injective_iff.2 Sum.inr_injective hx.symm
      simp only [lower_cons_inr] at henv
      obtain ⟨c', r, hs, hf, ha, -⟩ := steps_of_path _ _ _ _ _ (Nat.le_refl _) hrest hu henv
      exact ⟨c', r, hs, hf, ha⟩

/-- **Operations to game.** A finite Core run to a result is answered by the composite. -/
theorem answer_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) :
    ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w ∧ Responds (I.closedWith P s K) f w := by
  obtain ⟨w, hw'⟩ := result_typed hw hK run final
  refine ⟨w, hw', ?_⟩
  obtain ⟨l, henv, hp⟩ := path_of_steps hw' run final s (I.initThread f) rfl
  refine Env.mem_comp_iff.2 ⟨.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)]),
    mem_strategy_iff.2 ⟨_, .cons (.call s f) hp⟩, by simpa using henv, by simp⟩

/-- **Later calls.** A closed-world run of the export call `f` to a result is a complete
activation of the instance (environment moves agreeing with `K`) ending in exactly the
store the run leaves. -/
theorem activation_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {K : Silmaril.Wasm.Game.Env I.E} (hK : ThrowsBelow K s.exns.length) {f : I.F.Op}
    {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) c')
    (final : c'.code = r.toAdmin) :
    ∃ (l : List (Ev I.E)) (w : I.F.Ar f),
      Answer.ofResult? (I.exports.get f.1) r = some w ∧ K.Agrees l ∧
      I.Activation P s (.inr (.ask f) :: (l.map .inl ++ [.inr (.ans f w)])) c'.store := by
  obtain ⟨w, hw'⟩ := result_typed hw hK run final
  obtain ⟨l, henv, hp⟩ := path_of_steps hw' run final s (I.initThread f) rfl
  exact ⟨l, w, hw', henv, .cons (.call s f) hp⟩

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
