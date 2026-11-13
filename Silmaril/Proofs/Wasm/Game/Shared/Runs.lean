module

public import Silmaril.Proofs.Wasm.Game.Shared.Strategy
public import Silmaril.Proofs.Wasm.Game.Shared.Typing

/-!
# Product runs with a store-changing host and runs of the composite system

The product semantics `ShStep P L` and the composite system
`ShCmp I P L q = (L.dlts q).comp (I.shLts P)` correspond through `ShRel f`: a
product configuration `(t.config s, q)` is related to the composite state with
the environment idle in `q` and the instance running `t` in the store `s`, or,
at a callout, waiting for the import question made in `s`.

* `cmp_run_of_shSteps` and `shSteps_of_cmp_run`: the finite runs correspond (a
  host-free step is a silent instance step, an answer the hidden exchange of
  question and answer, the new store being carried by the answer move).
* `responds_iff_run`: **an answer `(s', w)` of the closed program to the export
  question `f` is exactly a finite product run of the export call to a result
  read as `w`, in the final store `s'`.**
* `mem_div_closedShD_iff`: the closed divergence-observing program may diverge
  right after `[ask f]` exactly when the export call has an infinite product run
  (as `Silmaril.Proofs.Wasm.Game.StatefulEnv.Div`, store in the moves).
* `shAdequacy_div`, `shAdequacy`: hence the behaviours.

New proofs; the divergence part follows `Silmaril.Proofs.Wasm.Game.StatefulEnv.Div`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile} {L : SEnv I.shE} {q₀ : L.S}

open Silmaril.Wasm.Game.ScalarInstance

/-! ### Product steps from threads -/

/-- One product step from a thread configuration, read on threads. -/
theorem shStep_cases {s : Store Nat} {t : Thread} {q : L.S} {y : Config Nat × L.S}
    (hstep : ShStep P L (t.config s, q) y) :
    (∃ s₁ t₁, y = (t₁.config s₁, q) ∧ InternalP P (s, t) (s₁, t₁)) ∨
      (∃ hh args e, CalloutAt s t hh args ∧ I.importOp? hh args = some e ∧
        ((∃ s' w q', L.Ans q (shOp s e) (s', w) q' ∧
          y = ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s', q')) ∨
        (L.Silent q (shOp s e) ∧ y = (t.config s, q)))) := by
  have hst : (t.config s).store = s := Thread.config_store s t
  cases hstep with
  | internal h0 =>
    rcases (stepP_iff P _ s t _).mp h0 with ⟨s₁, f₁, code₁, rfl, hi⟩ | ⟨-, -, -, -, -, hb⟩
    · exact .inl ⟨s₁, .active f₁ code₁, rfl, hi⟩
    · rcases hb with ⟨-, -, hf, -⟩ | ⟨hf, -⟩ <;> exact hf.elim
  | @answer _ E a hh args e s' w _ q' hd op ans =>
    have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by
      simpa only [hst] using hd
    have ans' : L.Ans q (shOp s e) (s', w) q' := by
      rw [hst] at ans
      exact ans
    refine .inr ⟨hh, args, e, ⟨E, a, hd'⟩, op, .inl ⟨s', w, q', ans', ?_⟩⟩
    rw [resumeResult_config hd']
  | @silent _ E a hh args e _ hd op hs =>
    have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by
      simpa only [hst] using hd
    have hs' : L.Silent q (shOp s e) := by
      rw [hst] at hs
      exact hs
    exact .inr ⟨hh, args, e, ⟨E, a, hd'⟩, op, .inr ⟨hs', rfl⟩⟩

/-- A callout answered by the host is one product step to the resumed thread, in the store
of the answer. -/
theorem callout_shStep {s s' : Store Nat} {t : Thread} {hh : Nat} {args : List Val} {e : I.E.Op}
    {w : Answer (I.imports.get e.1)} {q q' : L.S} (callout : CalloutAt s t hh args)
    (op : I.importOp? hh args = some e) (hans : L.Ans q (shOp s e) (s', w) q') :
    ShStep P L (t.config s, q) ((resumeResult s t w.toResult).config s', q') := by
  obtain ⟨E, a, hd⟩ := callout
  have hst : (t.config s).store = s := Thread.config_store s t
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [hst]
    exact hd
  have hans' : L.Ans q (shOp (t.config s).store e) (s', w) q' := by rw [hst]; exact hans
  rw [resumeResult_config hd]
  exact ShStep.answer hd' op hans'

/-- A callout on which the host may stay silent is a product self-loop. -/
theorem silent_shStep {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val} {e : I.E.Op}
    {q : L.S} (callout : CalloutAt s t hh args) (op : I.importOp? hh args = some e)
    (hs : L.Silent q (shOp s e)) : ShStep P L (t.config s, q) (t.config s, q) := by
  obtain ⟨E, a, hd⟩ := callout
  have hst : (t.config s).store = s := Thread.config_store s t
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [hst]
    exact hd
  have hs' : L.Silent q (shOp (t.config s).store e) := by rw [hst]; exact hs
  exact ShStep.silent hd' op hs'

/-! ### Finite runs: operations to game -/

/-- An answered callout is two hidden exchanges of the composite system. -/
theorem cmp_run_answer (f : I.shF.Op) {s s' : Store Nat} {t : Thread} {hh : Nat}
    {args : List Val} {e : I.E.Op} {w : Answer (I.imports.get e.1)} {q q' : L.S}
    (callout : CalloutAt s t hh args) (op : I.importOp? hh args = some e)
    (hans : L.Ans q (shOp s e) (s', w) q') :
    (ShCmp I P L q₀).Run ((q, none), .running f s t) []
      ((q', none), .running f s' (resumeResult s t w.toResult)) :=
  .tau (.sync (Ev.ask (shOp s e)) (SEnv.DTrans.ask q _) (ShTrans.ucall callout op))
    (.tau (.sync (Ev.ans (shOp s e) (s', w)) (SEnv.DTrans.ans hans)
      (ShTrans.uret (P := P) (f := f) (s := s) (t := t) (e := shOp s e) s' w))
      (.nil _))

/-- **One product step is a silent run of the composite system.** -/
theorem cmp_run_of_shStep (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {z : Config Nat × L.S} (hstep : ShStep P L (t.config s, q) z) :
    ∃ s' t', (ShCmp I P L q₀).Run ((q, none), .running f s t) []
      ((z.2, none), .running f s' t') ∧ z.1 = t'.config s' := by
  rcases shStep_cases hstep with ⟨s₁, t₁, rfl, hi⟩ | ⟨hh, args, e, hco, hop, hcase⟩
  · exact ⟨s₁, t₁, .tau (.tau₂ (ShTrans.tau hi)) (.nil _), rfl⟩
  · rcases hcase with ⟨s', w, q', hans, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨s', _, cmp_run_answer f hco hop hans, rfl⟩
    · exact ⟨s, t, .nil _, rfl⟩

/-- **A product run is a silent run of the composite system.** -/
theorem cmp_run_of_shSteps (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {y : Config Nat × L.S} (run : ShSteps P L (t.config s, q) y) :
    ∃ s' t', (ShCmp I P L q₀).Run ((q, none), .running f s t) []
      ((y.2, none), .running f s' t') ∧ y.1 = t'.config s' := by
  induction run with
  | refl => exact ⟨s, t, .nil _, rfl⟩
  | @tail y z _ hst ih =>
    obtain ⟨s₁, t₁, hr₁, hy⟩ := ih
    have hst' : ShStep P L (t₁.config s₁, y.2) z := by
      rw [← hy]
      exact hst
    obtain ⟨s₂, t₂, hr₂, hz⟩ := cmp_run_of_shStep (q₀ := q₀) f hst'
    exact ⟨s₂, t₂, hr₁.append hr₂, hz⟩

/-- A product run of an export call to a result read as `w` is a run of the composite system
answering `(c'.store, w)` and returning to the idle state in the final host state. -/
theorem cmp_run_of_run (f : I.shF.Op) {q q' : L.S} {c' : Config Nat} {r : Result}
    {w : Answer (I.exports.get f.1)}
    (run : ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) (hw : Answer.ofResult? (I.exports.get f.1) r = some w) :
    (ShCmp I P L q).Run (ShCmp I P L q).init [.inr (.ask f), .inr (.ans f (c'.store, w))]
      ((q', none), .idle) := by
  obtain ⟨s', t', hrun, hc₀⟩ := cmp_run_of_shSteps (q₀ := q) f (t := I.shInit f) run
  have hc : c' = t'.config s' := hc₀
  have hfinal : ResultAt s' t' r := by
    show (t'.config s').code = r.toAdmin
    rw [← hc]
    exact final
  have hstore : c'.store = s' := by rw [hc, Thread.config_store]
  rw [hstore]
  have hcall : (ShCmp I P L q).step (ShCmp I P L q).init (some (.inr (.ask f)))
      ((q, none), .running f f.2.1 (I.shInit f)) := .right (Ev.ask f) (ShTrans.call f)
  have hans : (ShCmp I P L q).step ((q', none), .running f s' t') (some (.inr (.ans f (s', w))))
      ((q', none), .idle) := .right (Ev.ans f (s', w)) (ShTrans.oret hfinal hw)
  exact .vis hcall (hrun.append (.vis hans (.nil _)))

/-- **Operations to game.** A product run of an export call to a result read as `w` is an
answer `(c'.store, w)` of the closed program. -/
theorem responds_of_run (f : I.shF.Op) {q q' : L.S} {c' : Config Nat} {r : Result}
    {w : Answer (I.exports.get f.1)}
    (run : ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) (hw : Answer.ofResult? (I.exports.get f.1) r = some w) :
    Responds (I.closedSh P L q) f (c'.store, w) :=
  responds_iff.2 ⟨_, cmp_run_of_run f run final hw⟩

/-! ### Finite runs: game to operations -/

/-- The relation between product configurations and states of the composite system during the
export call `f`. -/
def ShRel (f : I.shF.Op) (cq : Config Nat × L.S) (x : (ShCmp I P L q₀).State) : Prop :=
  (∃ (s : Store Nat) (t : Thread), x = ((cq.2, none), .running f s t) ∧ cq.1 = t.config s) ∨
  (∃ (s : Store Nat) (t : Thread) (e : I.E.Op) (h : Nat) (args : List Val),
    x = ((cq.2, some (shOp s e)), .waiting f s t (shOp s e)) ∧ cq.1 = t.config s ∧
      CalloutAt s t h args ∧ I.importOp? h args = some e)

/-- A silent step of the composite from a running state is matched by product steps. -/
theorem shSteps_of_silent_running (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {x' : (ShCmp I P L q₀).State} (hs : (ShCmp I P L q₀).step ((q, none), .running f s t) none x') :
    ∃ cq', ShSteps P L (t.config s, q) cq' ∧ ShRel (q₀ := q₀) f cq' x' := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi =>
    cases hi with
    | tau hint =>
      exact ⟨_, .single (.internal (InternalP.toStep P _ hint)), .inl ⟨_, _, rfl, rfl⟩⟩
  | sync g hk hi =>
    cases hk with
    | ask q e =>
      cases hi with
      | ucall hco hop => exact ⟨_, .refl, .inr ⟨s, t, _, _, _, rfl, rfl, hco, hop⟩⟩

/-- A silent step of the composite from a waiting state is matched by product steps. -/
theorem shSteps_of_silent_waiting (f : I.shF.Op) {s : Store Nat} {t : Thread} {e : I.E.Op}
    {h : Nat} {args : List Val} {q : L.S} (hco : CalloutAt s t h args)
    (hop : I.importOp? h args = some e) {x' : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step ((q, some (shOp s e)), .waiting f s t (shOp s e)) none x') :
    ∃ cq', ShSteps P L (t.config s, q) cq' ∧ ShRel (q₀ := q₀) f cq' x' := by
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop _ => exact ⟨_, .refl, .inr ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hans =>
      cases hi with
      | uret s' w =>
        exact ⟨_, .single (callout_shStep hco hop hans), .inl ⟨_, _, rfl, rfl⟩⟩

/-- **A silent step of the composite is matched by product steps.** -/
theorem shSteps_of_silent (f : I.shF.Op) {cq : Config Nat × L.S}
    {x x' : (ShCmp I P L q₀).State} (hc : ShRel f cq x) (hs : (ShCmp I P L q₀).step x none x') :
    ∃ cq', ShSteps P L cq cq' ∧ ShRel f cq' x' := by
  obtain ⟨c, q⟩ := cq
  rcases hc with ⟨s, t, rfl, hct⟩ | ⟨s, t, e, h, args, rfl, hct, hco, hop⟩
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact shSteps_of_silent_running f hs
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact shSteps_of_silent_waiting f hco hop hs

/-- **A silent run of the composite is matched by a product run.** -/
theorem shSteps_of_run_nil (f : I.shF.Op) {x y : (ShCmp I P L q₀).State}
    {p : List (Move Sig.empty I.shF)} (h : (ShCmp I P L q₀).Run x p y) (hp : p = []) :
    ∀ cq, ShRel f cq x → ∃ cq', ShSteps P L cq cq' ∧ ShRel f cq' y := by
  induction h with
  | nil x => exact fun cq hc => ⟨cq, .refl, hc⟩
  | tau hs _ ih =>
    intro cq hc
    obtain ⟨cq₁, hr₁, hc₁⟩ := shSteps_of_silent f hc hs
    obtain ⟨cq₂, hr₂, hc₂⟩ := ih hp cq₁ hc₁
    exact ⟨cq₂, hr₁.trans hr₂, hc₂⟩
  | vis _ _ _ => cases hp

/-- The initial state of the composite takes no silent step. -/
theorem init_no_silent {x : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step (ShCmp I P L q₀).init none x) : False := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ask q e => cases hi

/-- Silent runs from the initial state stay there. -/
theorem init_run_nil {x y : (ShCmp I P L q₀).State} {p : List (Move Sig.empty I.shF)}
    (h : (ShCmp I P L q₀).Run x p y) (hp : p = []) (hx : x = (ShCmp I P L q₀).init) :
    y = (ShCmp I P L q₀).init := by
  cases h with
  | nil => exact hx
  | tau hs _ => exact (init_no_silent (hx ▸ hs)).elim
  | vis _ _ => cases hp

/-- Reading the export question from the initial state. -/
theorem step_ask_inv {f : I.shF.Op} {x : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step (ShCmp I P L q₀).init (some (.inr (.ask f))) x) :
    x = ((q₀, none), .running f f.2.1 (I.shInit f)) := by
  cases hs with
  | right g hi =>
    cases hi with
    | call f' => rfl

/-- The answer move from a running state: the thread is finished. -/
theorem final_running (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S} {a : I.shF.Ar f}
    {x' : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step ((q, none), .running f s t) (some (.inr (.ans f a))) x') :
    ∃ r, (t.config s).code = r.toAdmin ∧ (t.config s).store = a.1 ∧
      Answer.ofResult? (I.exports.get f.1) r = some a.2 := by
  cases hs with
  | right g hi =>
    cases hi with
    | @oret _ _ _ r v final answer => exact ⟨r, final, Thread.config_store s t, answer⟩

/-- A waiting state does not answer the export question. -/
theorem not_ans_waiting (f : I.shF.Op) {s : Store Nat} {t : Thread} {e : I.shE.Op}
    {q : Option I.shE.Op × L.S} {a : I.shF.Ar f} {x' : (ShCmp I P L q₀).State}
    (hs : (ShCmp I P L q₀).step ((q.2, q.1), .waiting f s t e) (some (.inr (.ans f a))) x') :
    False := by
  cases hs with
  | right g hi => cases hi

/-- The answer move from a related state is a final configuration. -/
theorem final_of_step_ans (f : I.shF.Op) {cq : Config Nat × L.S} {a : I.shF.Ar f}
    {x x' : (ShCmp I P L q₀).State} (hc : ShRel f cq x)
    (hs : (ShCmp I P L q₀).step x (some (.inr (.ans f a))) x') :
    ∃ r, cq.1.code = r.toAdmin ∧ cq.1.store = a.1 ∧
      Answer.ofResult? (I.exports.get f.1) r = some a.2 := by
  rcases hc with ⟨s, t, hx, hct⟩ | ⟨s, t, e, h, args, hx, -, -, -⟩
  · rw [hx] at hs
    rw [hct]
    exact final_running f hs
  · rw [hx] at hs
    exact (not_ans_waiting (q := (some (shOp s e), cq.2)) f hs).elim

/-- **Game to operations.** An answer `(s', w)` of the closed program is a product run of the
export call to a result read as `w`, in the final store `s'`. -/
theorem run_of_responds {f : I.shF.Op} {q : L.S} {a : I.shF.Ar f}
    (h : Responds (I.closedSh P L q) f a) :
    ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
        c'.store = a.1 ∧ Answer.ofResult? (I.exports.get f.1) r = some a.2 := by
  obtain ⟨y, hy⟩ := responds_iff.1 h
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv hy
  have hx₁ : x₁ = (ShCmp I P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.2.1 (I.shInit f)) := step_ask_inv (hx₁ ▸ hs₁)
  have hc₂ : ShRel (q₀ := q) f (invoke f.2.1 (I.addr f.1) f.2.2.1, q) x₂ :=
    .inl ⟨f.2.1, I.shInit f, hx₂, rfl⟩
  obtain ⟨x₃, x₄, hr₃, hs₃, -⟩ := LTS.Run.cons_inv hr₂
  obtain ⟨⟨c', q'⟩, hrun, hc₃⟩ := shSteps_of_run_nil f hr₃ rfl _ hc₂
  obtain ⟨r, hfinal, hstore, hans⟩ := final_of_step_ans f hc₃ hs₃
  exact ⟨c', q', r, hrun, hfinal, hstore, hans⟩

/-- **Answers of the closed program are finite product runs**, with the final store. -/
theorem responds_iff_run {f : I.shF.Op} {q : L.S} {s' : Store Nat}
    {w : Answer (I.exports.get f.1)} :
    Responds (I.closedSh P L q) f (s', w) ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
          c'.store = s' ∧ Answer.ofResult? (I.exports.get f.1) r = some w := by
  constructor
  · exact run_of_responds
  · rintro ⟨c', q', r, run, final, rfl, hw⟩
    exact responds_of_run f run final hw

/-! ### Divergence -/

/-- From a waiting state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem cmp_step_waiting (f : I.shF.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hinf : InfiniteTrace (ShStep P L) (t.config s, q)) :
    ∃ y, (ShCmp I P L q₀).step ((q, some (shOp s e)), .waiting f s t (shOp s e)) none y ∧
      ∃ cq, ShRel f cq y ∧ InfiniteTrace (ShStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases shStep_cases hst with ⟨s₁, t₁, -, hi⟩ | ⟨h', args', e', hco', hop', hcase⟩
  · exact absurd hi (calloutAt_no_internal hco _)
  · obtain ⟨rfl, rfl⟩ := calloutAt_unique hco' hco
    obtain rfl : e' = e := Option.some.inj (hop'.symm.trans hop)
    rcases hcase with ⟨s', w, q', hans, rfl⟩ | ⟨hs, rfl⟩
    · exact ⟨_, .sync (Ev.ans _ (s', w)) (SEnv.DTrans.ans hans) (ShTrans.uret s' w),
        _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
    · exact ⟨_, .tau₁ (SEnv.DTrans.loop hs), _,
        .inr ⟨s, t, e', h', args', rfl, rfl, hco, hop⟩, hinf₁⟩

/-- From a running state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem cmp_step_running (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hinf : InfiniteTrace (ShStep P L) (t.config s, q)) :
    ∃ y, (ShCmp I P L q₀).step ((q, none), .running f s t) none y ∧
      ∃ cq, ShRel f cq y ∧ InfiniteTrace (ShStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases shStep_cases hst with ⟨s₁, t₁, rfl, hi⟩ | ⟨h, args, e, hco, hop, -⟩
  · exact ⟨_, .tau₂ (ShTrans.tau hi), _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
  · exact ⟨_, .sync (Ev.ask _) (SEnv.DTrans.ask q _) (ShTrans.ucall hco hop),
      _, .inr ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hinf⟩

/-- **An infinite product run is divergence of the composite.** -/
theorem cmp_diverges_of_inf (f : I.shF.Op) {cq : Config Nat × L.S}
    {x : (ShCmp I P L q₀).State} (hc : ShRel f cq x) (hinf : InfiniteTrace (ShStep P L) cq) :
    (ShCmp I P L q₀).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ cq, ShRel f cq x ∧ InfiniteTrace (ShStep P L) cq) ?_ ⟨cq, hc, hinf⟩
  rintro x ⟨⟨c, q⟩, ⟨s, t, rfl, hct⟩ | ⟨s, t, e, h, args, rfl, hct, hco, hop⟩, hinf⟩
  · have hinf' : InfiniteTrace (ShStep P L) (t.config s, q) := hct ▸ hinf
    exact cmp_step_running f hinf'
  · have hinf' : InfiniteTrace (ShStep P L) (t.config s, q) := hct ▸ hinf
    exact cmp_step_waiting f hco hop hinf'

/-- A diverging waiting state related to a configuration gives a product step to a related,
diverging state. -/
theorem shStep_waiting (f : I.shF.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hd : (ShCmp I P L q₀).Diverges ((q, some (shOp s e)), .waiting f s t (shOp s e))) :
    ∃ cq₁, ShStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, ShRel f cq₁ x₁ ∧ (ShCmp I P L q₀).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop hsil =>
      exact ⟨_, silent_shStep hco hop hsil, _, .inr ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hd₁⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hans =>
      cases hi with
      | uret s' w => exact ⟨_, callout_shStep hco hop hans, _, .inl ⟨_, _, rfl, rfl⟩, hd₁⟩

/-- A diverging running state related to a configuration gives a product step to a related,
diverging state. -/
theorem shStep_running (f : I.shF.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hd : (ShCmp I P L q₀).Diverges ((q, none), .running f s t)) :
    ∃ cq₁, ShStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, ShRel f cq₁ x₁ ∧ (ShCmp I P L q₀).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi =>
    cases hi with
    | tau hint =>
      exact ⟨_, .internal (InternalP.toStep P _ hint), _, .inl ⟨_, _, rfl, rfl⟩, hd₁⟩
  | sync g hk hi =>
    cases hk with
    | ask q e =>
      cases hi with
      | ucall hco hop => exact shStep_waiting f hco hop hd₁

/-- **Divergence of the composite is an infinite product run.** -/
theorem inf_of_cmp_diverges (f : I.shF.Op) {cq : Config Nat × L.S}
    {x : (ShCmp I P L q₀).State} (hc : ShRel f cq x) (hd : (ShCmp I P L q₀).Diverges x) :
    InfiniteTrace (ShStep P L) cq := by
  refine InfiniteTrace.coinduct
    (fun cq => ∃ x, ShRel (P := P) (q₀ := q₀) f cq x ∧ (ShCmp I P L q₀).Diverges x)
    ?_ ⟨x, hc, hd⟩
  rintro ⟨c, q⟩ ⟨x, ⟨s, t, rfl, hct⟩ | ⟨s, t, e, h, args, rfl, hct, hco, hop⟩, hd⟩
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact shStep_running f hd
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact shStep_waiting f hco hop hd

/-- The runs of the composite reading the export question from its initial state. -/
theorem run_ask_inv {q : L.S} {f : I.shF.Op} {y : (ShCmp I P L q).State}
    (h : (ShCmp I P L q).Run (ShCmp I P L q).init [.inr (.ask f)] y) :
    Relation.ReflTransGen (ShCmp I P L q).Silent ((q, none), .running f f.2.1 (I.shInit f)) y := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (ShCmp I P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.2.1 (I.shInit f)) := step_ask_inv (hx₁ ▸ hs₁)
  exact hx₂ ▸ Silmaril.Proofs.Wasm.Game.ScalarInstance.silent_of_run_nil hr₂ rfl

/-- **The divergent plays of the closed program after the export question.** -/
theorem mem_div_closedShD_iff {q : L.S} (f : I.shF.Op) :
    [.inr (.ask f)] ∈ (I.closedShD P L q).div ↔
      InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q) := by
  rw [closedShD_eq_ofLTS]
  refine (DStrategy.mem_div_ofLTS (L := ShCmp I P L q)).trans ?_
  have hc : ShRel (P := P) (q₀ := q) f (invoke f.2.1 (I.addr f.1) f.2.2.1, q)
      ((q, none), .running f f.2.1 (I.shInit f)) := .inl ⟨f.2.1, I.shInit f, rfl, rfl⟩
  constructor
  · rintro ⟨⟨y, hy, hdiv⟩, -⟩
    exact inf_of_cmp_diverges f hc (InfiniteTrace.of_steps (run_ask_inv hy) hdiv)
  · intro hinf
    have hrun : (ShCmp I P L q).Run (ShCmp I P L q).init [.inr (.ask f)]
        ((q, none), .running f f.2.1 (I.shInit f)) :=
      .vis (LTS.CompStep.right (Ev.ask f) (ShTrans.call f)) (.nil _)
    exact ⟨⟨_, hrun, cmp_diverges_of_inf f hc hinf⟩, f, .cons (.ask f) (.nil _)⟩

/-! ### Adequacy -/

/-- **Typed results against a store-changing host.** -/
theorem shResult_typed {f : I.shF.Op} (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L)
    {q q' : L.S} {c' : Config Nat} {r : Result}
    (run : ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) : ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w :=
  shGood_result (shGood_shSteps (x := (_, q)) hL (shGood_invoke hw) run) final

/-- The terminating behaviours are the answers. -/
theorem mem_finite_iff {f : I.shF.Op} (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L)
    (q : L.S) (b : Behaviour Val) :
    (∃ (c' : Config Nat) (q' : L.S) (r : Result),
      ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
        b = r.toBehaviour) ↔
    ∃ (s' : Store Nat) (w : Answer (I.exports.get f.1)),
      Responds (I.closedSh P L q) f (s', w) ∧ b = w.toBehaviour := by
  constructor
  · rintro ⟨c', q', r, run, final, rfl⟩
    obtain ⟨w, hw'⟩ := shResult_typed hw hL run final
    refine ⟨c'.store, w, responds_of_run f run final hw', ?_⟩
    rw [Answer.toBehaviour, Answer.toResult_of_ofResult? hw']
  · rintro ⟨s', w, hr, rfl⟩
    obtain ⟨c', q', r, run, final, -, hw'⟩ := responds_iff_run.1 hr
    exact ⟨c', q', r, run, final, by rw [Answer.toBehaviour, Answer.toResult_of_ofResult? hw']⟩

/-- **M2 against store-changing hosts, divergence read off the game, every profile.** -/
theorem shAdequacy_div {f : I.shF.Op} (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L)
    (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      shDCompositeObs (I.closedShD P L q) f := by
  have hforget : (I.closedShD P L q).toStrategy = I.closedSh P L q := forget_closedShD P L q
  ext b
  show (_ ∨ _) ↔ (_ ∨ _)
  rw [hforget]
  exact or_congr (mem_finite_iff hw hL q b)
    (and_congr_right fun _ => (mem_div_closedShD_iff f).symm)

/-- **No answer is divergence.** -/
theorem shDiverges_of_no_answer {f : I.shF.Op} (hw : I.WellFormed f.2.1)
    (hL : I.ShEnvOk f.2.1 L) {q : L.S} (hno : ∀ s' w, ¬ Responds (I.closedSh P L q) f (s', w)) :
    InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q) := by
  refine InfiniteTrace.coinduct
    (fun y => ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) y) ?_ Relation.ReflTransGen.refl
  intro y run
  have hg := shGood_shSteps (x := (_, q)) hL (shGood_invoke hw) run
  rcases shGood_progress (P := P) (L := L) y.2 hg with ⟨r, hr⟩ | ⟨y', hy'⟩
  · obtain ⟨w, hw'⟩ := shResult_typed hw hL run hr
    exact absurd (responds_of_run f run hr hw') (hno _ w)
  · exact ⟨y', hy', run.tail hy'⟩

/-- **M2 against store-changing hosts, plain strategies, every profile**: observations of
the closed program together with may-divergence. -/
theorem shAdequacy {f : I.shF.Op} (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L)
    (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      shCompositeObs (I.closedSh P L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q)} := by
  ext b
  show (_ ∨ _) ↔ ((_ ∨ _) ∨ _)
  have hfin := mem_finite_iff (P := P) hw hL q b
  constructor
  · rintro (h | h)
    · exact .inl (.inl (hfin.1 h))
    · exact .inr h
  · rintro ((h | ⟨hb, hno⟩) | h)
    · exact .inl (hfin.2 h)
    · exact .inr ⟨hb, shDiverges_of_no_answer hw hL hno⟩
    · exact .inr h

end Silmaril.Proofs.Wasm.Game.Shared
