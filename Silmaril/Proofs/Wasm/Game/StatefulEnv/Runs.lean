module

public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Strategy
public import Silmaril.Proofs.Wasm.Game.Adequacy.Runs
public import Silmaril.Proofs.Wasm.Game.Adequacy.Progress

/-!
# Product runs against a stateful host and plays of the closed program

* `SStep.core_step`, `core_step_sstep`: a product step is a Core step against
  the stateless host `L.hostAt q` of the current host state, and conversely.
* `good_sstep`, `good_sprogress`: the typing invariant `Good` of the
  stateless proof is preserved by product steps, and a configuration
  satisfying it is final or has a product step. Each answer step is a Core
  step against the stateless environment answering exactly that call
  (`singleEnv`), so the per-step typing and progress lemmas of
  `Silmaril.Proofs.Wasm.Game.Adequacy.Progress` apply step by step.
* `ssteps_of_path` (game to operations) and `path_of_ssteps` (operations to
  game): runs of the instance strategy whose import events agree with `L`
  are product runs, with the host-state run read off the events.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### The environment answering one call -/

open Classical in
/-- The stateless environment answering exactly the question `e`, with `w`. -/
noncomputable def singleEnv {E : Sig.{0}} (e : E.Op) (w : E.Ar e) : Silmaril.Wasm.Game.Env E :=
  fun e' => if h : e' = e then some (h ▸ w) else none

theorem singleEnv_answers {E : Sig.{0}} (e : E.Op) (w : E.Ar e) :
    (singleEnv e w).Answers e w := by
  simp [singleEnv, Silmaril.Wasm.Game.Env.Answers]

theorem singleEnv_throwsBelow {ts : List FnType} {e : (ifaceSig ts).Op}
    {w : (ifaceSig ts).Ar e} {n : Nat} (hw : Answer.ThrowsBelow (ft := ts.get e.1) n w) :
    ThrowsBelow (singleEnv e w) n := by
  intro e' w' h
  unfold Silmaril.Wasm.Game.Env.Answers singleEnv at h
  split at h
  · rename_i he
    subst he
    cases h
    exact hw
  · cases h

theorem silent_not_answers {E : Sig.{0}} {e : E.Op} {w : E.Ar e} :
    ¬ (Silmaril.Wasm.Game.Env.silent E).Answers e w := by
  simp [Silmaril.Wasm.Game.Env.Answers, Silmaril.Wasm.Game.Env.silent]

/-! ### Product steps are Core steps -/

section Core

variable {ts : List FnType} {P : Profile} {L : Silmaril.Wasm.Game.SEnv (ifaceSig ts)}

/-- **A product step is a Core step** against the host of the current host state. -/
theorem SStep.core_step {c c' : Config Nat} {q q' : L.S} (h : SStep P L (c, q) (c', q')) :
    Execution.Core.Step P (L.hostAt q) c c' := by
  cases h with
  | internal h0 => exact Step.of_noHost _ h0
  | answer hd op ans =>
    exact ScalarInstance.step_of_callout_returned hd ⟨_, op, Or.inl ⟨_, _, ans, rfl⟩⟩
  | silent hd op hs => exact ScalarInstance.step_of_callout_diverged hd ⟨_, op, Or.inr ⟨hs, rfl⟩⟩

/-- **A Core step against the host of the current state is a product step**, for some next
host state. -/
theorem core_step_sstep {c c' : Config Nat} {q : L.S}
    (h : Execution.Core.Step P (L.hostAt q) c c') : ∃ q', SStep P L (c, q) (c', q') := by
  rcases Step.split_host h with h0 | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact ⟨q, .internal h0⟩
  · obtain ⟨e, op, ⟨w, q', hans, hout⟩ | ⟨-, hout⟩⟩ := hr
    · obtain ⟨rfl, rfl⟩ : s' = c.store ∧ r = Answer.toResult (ft := ts.get e.1) w := by
        simpa [eq_comm] using hout
      exact ⟨q', .answer hd op hans⟩
    · cases hout
  · obtain ⟨e, op, ⟨w, q', -, hout⟩ | ⟨hs, -⟩⟩ := hdiv
    · cases hout
    · exact ⟨q, .silent hd op hs⟩

end Core

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ### Typing and progress along product runs -/

/-- Product steps preserve the run invariant. -/
theorem good_sstep {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {ts : List CValType}
    {x y : Config Nat × L.S} (hg : Good s ts x.1) (h : SStep P L x y) : Good s ts y.1 := by
  cases h with
  | internal h0 =>
    exact good_step hw (throwsBelow_silent I.imports s.exns.length) hg (Step.of_noHost _ h0)
  | @answer c E a hh args e w q q' hd op ans =>
    have hr : hostOf I.imports (singleEnv e w) hh c.store args
        (.returned c.store (Answer.toResult (ft := I.imports.get e.1) w)) :=
      ⟨e, op, Or.inl ⟨w, singleEnv_answers e w, rfl⟩⟩
    exact good_step (P := P) hw (singleEnv_throwsBelow (hL _ _ _ _ ans)) hg
      (step_of_callout_returned hd hr)
  | silent => exact hg

/-- Product runs preserve the run invariant. -/
theorem good_ssteps {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {ts : List CValType}
    {x y : Config Nat × L.S} (hg : Good s ts x.1) (h : SSteps P L x y) : Good s ts y.1 := by
  induction h with
  | refl => exact hg
  | tail _ hst ih => exact good_sstep hw hL ih hst

/-- **Progress against a stateful host.** A configuration satisfying the run invariant is
final or has a product step, from every host state. -/
theorem good_sprogress {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} {ts : List CValType} {c : Config Nat} (q : L.S)
    (hg : Good s ts c) : (∃ r : Result, c.code = r.toAdmin) ∨ ∃ y, SStep P L (c, q) y := by
  rcases good_progress (P := P) hw (throwsBelow_silent I.imports s.exns.length) hg with
    hr | ⟨c', hc'⟩
  · exact Or.inl hr
  · right
    rcases Step.split_host hc' with h0 | ⟨E, a, hh, args, hd, ⟨s', r, hr, -⟩ | ⟨hdiv, -⟩⟩
    · exact ⟨_, .internal h0⟩
    · obtain ⟨e, -, ⟨w, hans, -⟩ | ⟨-, hout⟩⟩ := hr
      · exact absurd hans silent_not_answers
      · cases hout
    · obtain ⟨e, op, -⟩ := hdiv
      by_cases hA : ∃ w q', L.Ans q e w q'
      · obtain ⟨w, q', hans⟩ := hA
        exact ⟨_, .answer hd op hans⟩
      · exact ⟨_, .silent hd op (Or.inr fun w q' h => hA ⟨w, q', h⟩)⟩

/-- The invariant at an export invocation, with the declared result types. -/
theorem good_invoke_results {s : Store Nat} (hw : I.WellFormed s) (f : I.F.Op) :
    Good s ((I.exports.get f.1).results.map ScalarType.toC) (invoke s (I.addr f.1) f.2.1) := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type f.1
  have hinv : InvokeOk s (I.addr f.1) f.2.1 := by
    refine ⟨fi, Ty.ofList ((I.exports.get f.1).params.map ScalarType.toC),
      Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC), hfi, hexp, ?_⟩
    rw [Ty.toList_ofList]
    exact Silmaril.Proofs.Wasm.Game.forall₂_valOk_of_hasVal s f.2.2
  obtain ⟨fi', ps, rs, hfi', hexp', hok⟩ := invoke_ok hw.storeOk hinv
  obtain rfl : fi' = fi := (Option.some.inj (hfi.symm.trans hfi')).symm
  have hrs : rs = Ty.ofList ((I.exports.get f.1).results.map ScalarType.toC) := by
    have hboth := Expand.func_eq hexp' hexp
    simp only [FnType.toComp, Ty.func.injEq] at hboth
    exact hboth.2
  have hok' : ConfigOk (invoke s (I.addr f.1) f.2.1)
      ((I.exports.get f.1).results.map ScalarType.toC) := by
    simpa only [hrs, Ty.toList_ofList] using hok
  exact ⟨hok', ⟨rfl, Nat.le_refl _⟩⟩

/-- **Typed results against a stateful host.** -/
theorem sresult_typed {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : Silmaril.Wasm.Game.SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {f : I.F.Op} {q q' : L.S}
    {c' : Config Nat} {r : Result}
    (run : SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) : ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w := by
  cases r with
  | trap => exact ⟨_, rfl⟩
  | throw a => exact ⟨_, rfl⟩
  | values vs =>
    show ∃ w, Answer.ofResult? (I.exports.get f.1) (.values vs) = some w
    have hend : Good s ((I.exports.get f.1).results.map ScalarType.toC) c' :=
      good_ssteps hw hL (good_invoke_results hw f) run
    have htyped : List.Forall₂ ScalarType.HasVal (I.exports.get f.1).results vs :=
      hasVal_of_configOk hend.ok final
    exact ⟨.values ⟨vs, htyped⟩, by simp only [Answer.ofResult?, htyped, dite_true]⟩

/-! ### Runs of the strategy and product runs -/

/-- A host-free run is a product run with the host state unchanged. -/
theorem reach_ssteps {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {x y : Store Nat × Thread}
    (q : L.S) (h : Reach P x y) : SSteps P L (x.2.config x.1, q) (y.2.config y.1, q) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (.internal (InternalP.toStep P _ hst))

/-- A callout answered by the host is one product step to the resumed thread. -/
theorem callout_sstep {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {s : Store Nat} {t : Thread}
    {hh : Nat} {args : List Val} {e : I.E.Op} {v : I.E.Ar e} {q q' : L.S}
    (callout : CalloutAt s t hh args) (op : I.importOp? hh args = some e)
    (hans : L.Ans q e v q') :
    SStep P L (t.config s, q)
      ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s, q') := by
  obtain ⟨E, a, hd⟩ := callout
  have hst : (t.config s).store = s := Thread.config_store s t
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [hst]
    exact hd
  have hstep := SStep.answer (P := P) (L := L) (q := q) hd' op hans
  have hres : (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s =
      ⟨(t.config s).store, (t.config s).frame,
        E.fill (Answer.toResult (ft := I.imports.get e.1) v).toAdmin⟩ := by
    rw [resumeResult_config hd, hst]
  rw [hres]
  exact hstep

/-- The run `t` from thread `th` at store `s` splits at the answer `w` of `f`, with the host
driven from `h`: the conclusion of `ssplit_at_answer`. -/
private def SSplitsAt (P : Profile) (L : Silmaril.Wasm.Game.SEnv I.E) (f : I.F.Op)
    (w : I.F.Ar f) (s : Store Nat) (th : Thread) (q : I.HState) (u : List (Ev I.F)) (h : L.S)
    (t : List (Move I.E I.F)) : Prop :=
  ∃ (t₁ t₂ : List (Move I.E I.F)) (c' : Config Nat) (h' : L.S) (r : Result),
    t = t₁ ++ t₂ ∧ SSteps P L (th.config s, h) (c', h') ∧ c'.code = r.toAdmin ∧
    Answer.ofResult? (I.exports.get f.1) r = some w ∧
    I.Path P (.idle c'.store) t₂ q ∧ upper t₂ = u ∧
    L.Drive h (lower t₁) h' ∧ L.Agrees h' (lower t₂)

/-- A split after an import call answered by the host is a split with that call in front. -/
private theorem SSplitsAt.answered {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {f : I.F.Op}
    {w : I.F.Ar f} {s s₁ : Store Nat} {th t₁ : Thread} {q : I.HState} {u : List (Ev I.F)}
    {h h₁ : L.S} {rest : List (Move I.E I.F)} {hh : Nat} {args : List Val} {e : I.E.Op}
    {v : I.E.Ar e} (run : Reach P (s, th) (s₁, t₁)) (callout : CalloutAt s₁ t₁ hh args)
    (op : I.importOp? hh args = some e) (hans : L.Ans h e v h₁)
    (hs : SSplitsAt P L f w s₁ (resumeResult s₁ t₁ (Answer.toResult (ft := I.imports.get e.1) v))
      q u h₁ rest) :
    SSplitsAt P L f w s th q u h (.inl (.ask e) :: .inl (.ans e v) :: rest) := by
  obtain ⟨p₁, p₂, c', h', r, ht, hsteps, hfinal, hans', hp₂, hu₂, hd₁, ha₂⟩ := hs
  have hpre : SSteps P L (th.config s, h)
      ((resumeResult s₁ t₁ (Answer.toResult (ft := I.imports.get e.1) v)).config s₁, h₁) :=
    (reach_ssteps h run).tail (callout_sstep callout op hans)
  have hd : L.Drive h (lower ((.inl (.ask e) :: .inl (.ans e v) :: p₁ : List (Move I.E I.F))))
      h' := by
    simpa using Silmaril.Wasm.Game.SEnv.Drive.cons hans hd₁
  exact ⟨_ :: _ :: p₁, p₂, c', h', r, by rw [ht]; rfl, hpre.trans hsteps, hfinal, hans', hp₂,
    hu₂, hd, ha₂⟩

/-- The answer itself splits the run. -/
private theorem SSplitsAt.final {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {f : I.F.Op}
    {w : I.F.Ar f} {s s₁ : Store Nat} {th t₁ : Thread} {q : I.HState} {u : List (Ev I.F)}
    {h : L.S} {rest : List (Move I.E I.F)} {r : Result} (run : Reach P (s, th) (s₁, t₁))
    (final : ResultAt s₁ t₁ r) (answer : Answer.ofResult? (I.exports.get f.1) r = some w)
    (hrest : I.Path P (.idle s₁) rest q) (hu : upper rest = u) (hL : L.Agrees h (lower rest)) :
    SSplitsAt P L f w s th q u h (.inr (.ans f w) :: rest) := by
  have hp₂ : I.Path P (.idle (t₁.config s₁).store) rest q := by
    rw [Thread.config_store]
    exact hrest
  exact ⟨[.inr (.ans f w)], rest, _, h, r, rfl, reach_ssteps h run, final, answer, hp₂, hu,
    by simpa using Silmaril.Wasm.Game.SEnv.Drive.nil h, hL⟩

/-- **Game to operations, stateful host.** A run of the strategy from a running state whose
upper part starts with the answer `w` and whose lower part agrees with `L` from `h` splits at
that answer: its first part is a product run to a result read as `w`, driving the host from
`h` to some `h'`, and the rest is a run from the idle store left by it, agreeing with `L` from
`h'`. -/
theorem ssplit_at_answer {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {f : I.F.Op}
    {w : I.F.Ar f} : ∀ (n : Nat) (t : List (Move I.E I.F)) (s : Store Nat) (th : Thread)
      (q : I.HState) (u : List (Ev I.F)) (h : L.S), t.length ≤ n →
      I.Path P (.running f s th) t q → upper t = .ans f w :: u → L.Agrees h (lower t) →
      ∃ (t₁ t₂ : List (Move I.E I.F)) (c' : Config Nat) (h' : L.S) (r : Result),
        t = t₁ ++ t₂ ∧ SSteps P L (th.config s, h) (c', h') ∧ c'.code = r.toAdmin ∧
        Answer.ofResult? (I.exports.get f.1) r = some w ∧
        I.Path P (.idle c'.store) t₂ q ∧ upper t₂ = u ∧
        L.Drive h (lower t₁) h' ∧ L.Agrees h' (lower t₂) := by
  intro n
  induction n with
  | zero =>
    intro t s th q u h hn _ hu _
    exact absurd hu (by simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)])
  | succ n ih =>
    intro t s th q u h hn hp hu hL
    rcases hp with _ | ⟨_ | ⟨run, callout, op⟩ | _ | ⟨run, final, answer⟩, hrest⟩
    · exact absurd hu (by simp)
    · rcases hrest with _ | ⟨_ | _ | ⟨v⟩ | _, hrest'⟩
      · exact absurd hu (by simp)
      · obtain _ | _ | ⟨hans, hL'⟩ := hL
        exact SSplitsAt.answered run callout op hans
          (ih _ _ _ _ _ _ (Nat.le_of_succ_le (Nat.le_of_succ_le_succ hn)) hrest' hu hL')
    · obtain ⟨hw, hu'⟩ := List.cons.inj hu
      cases hw
      exact SSplitsAt.final run final answer hrest hu' (by simpa using hL)

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

/-- One product step from a thread configuration, read on threads. -/
private theorem sstep_thread {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {s : Store Nat}
    {t : Thread} {q : L.S} {y : Config Nat × L.S} (hstep : SStep P L (t.config s, q) y) :
    (∃ s₁ f₁ code₁, y = ((Thread.active f₁ code₁).config s₁, q) ∧
        InternalP P (s, t) (s₁, .active f₁ code₁)) ∨
      (∃ E a hh args e w q', decompose? s (t.config s).code = some (E, a, hh, args) ∧
        I.importOp? hh args = some e ∧ L.Ans q e w q' ∧
        y = ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s, q')) ∨
      y = (t.config s, q) := by
  have hst : (t.config s).store = s := Thread.config_store s t
  cases hstep with
  | internal h0 =>
    rcases (stepP_iff P _ s t _).mp h0 with ⟨s₁, f₁, code₁, rfl, hi⟩ | ⟨-, -, -, -, -, hb⟩
    · exact Or.inl ⟨s₁, f₁, code₁, rfl, hi⟩
    · rcases hb with ⟨-, -, hf, -⟩ | ⟨hf, -⟩ <;> exact hf.elim
  | @answer _ E a hh args e w _ q' hd op ans =>
    have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by
      simpa only [hst] using hd
    refine Or.inr (Or.inl ⟨E, a, hh, args, e, w, q', hd', op, ans, ?_⟩)
    rw [resumeResult_config hd', hst]
  | silent => exact Or.inr (Or.inr rfl)

/-- **Operations to game, stateful host.** A product run from a thread to a result read as
`w` is a run of the strategy to the answer `w` whose environment moves are driven by `L`
from `q` to the final host state. -/
theorem path_of_ssteps {P : Profile} {L : Silmaril.Wasm.Game.SEnv I.E} {f : I.F.Op}
    {w : I.F.Ar f} {r : Result} (hr : Answer.ofResult? (I.exports.get f.1) r = some w)
    {x y : Config Nat × L.S} (run : SSteps P L x y) (final : y.1.code = r.toAdmin) :
    ∀ (s : Store Nat) (t : Thread), x = (t.config s, x.2) →
      ∃ l : List (Ev I.E), L.Drive x.2 l y.2 ∧
        I.Path P (.running f s t) (l.map .inl ++ [.inr (.ans f w)]) (.idle y.1.store) := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s t hc
    have hfinal : (t.config s).code = r.toAdmin := by rw [← final, hc]
    have hstore : y.1.store = s := by rw [hc, Thread.config_store]
    refine ⟨[], .nil _, ?_⟩
    rw [hstore]
    exact .cons (.oret Relation.ReflTransGen.refl hfinal hr) (.nil _)
  | @head x₀ b hstep _ ih =>
    show ∀ (s : Store Nat) (t : Thread), x₀ = (t.config s, x₀.2) → ∃ l : List (Ev I.E),
      L.Drive x₀.2 l y.2 ∧
      I.Path P (.running f s t) (l.map .inl ++ [.inr (.ans f w)]) (.idle y.1.store)
    intro s t hc
    have hstep' : SStep P L (t.config s, x₀.2) b := hc ▸ hstep
    rcases sstep_thread hstep' with ⟨s₁, f₁, code₁, rfl, hi⟩ |
      ⟨E, a, hh, args, e, w', q', hd, he, hans, rfl⟩ | rfl
    · obtain ⟨l, hl, hp⟩ := ih s₁ (.active f₁ code₁) rfl
      exact ⟨l, hl, Path.internal_head (by simp) hi hp⟩
    · obtain ⟨l, hl, hp⟩ := ih s _ rfl
      exact ⟨.ask e :: .ans e w' :: l, .cons hans hl, Path.callout_head hd he hp⟩
    · exact ih s t rfl

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
