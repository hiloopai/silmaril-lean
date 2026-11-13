module

public import Silmaril.Proofs.Wasm.Game.Untyped.Strategy

/-!
# Untyped product runs and runs of the composite system

The product semantics `UStep P L` and the composite system
`Cmp U P L q = (L.dlts q).comp (U.lts P)` correspond through `URel f`: a product
configuration `(t.config s, q)` is related to the composite state with the environment
idle in `q` and the instance running `t` in `s`, or, at a callout, waiting for the raw
call made in `s`.

* `responds_iff_run`: **an answer `⟨s', r⟩` of the closed program to the export question
  `f` is exactly a finite product run of the export call to the result `r` in the final
  store `s'`.**
* `mem_div_closedD_iff`: the divergence-observing closed program may diverge right after
  `[ask f]` exactly when the export call has an infinite product run.
* `uAdequacy_div`: hence the behaviours are the observations of the composite strategy,
  for **every** environment and question: no typing is involved, since replies carry
  raw results.

New proofs, copied from `Silmaril.Proofs.Wasm.Game.Shared.Runs` with the moves untyped (the
result-typing step of the typed game disappears).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {U : UInstance} {P : Profile} {L : SEnv UImp} {q₀ : L.S}

open Silmaril.Wasm.Game.UInstance

/-! ### Product steps from threads -/

/-- One product step from a thread configuration, read on threads. -/
theorem uStep_cases {s : Store Nat} {t : Thread} {q : L.S} {y : Config Nat × L.S}
    (hstep : UStep P L (t.config s, q) y) :
    (∃ s₁ t₁, y = (t₁.config s₁, q) ∧ InternalP P (s, t) (s₁, t₁)) ∨
      (∃ hh args, CalloutAt s t hh args ∧
        ((∃ a q', L.Ans q ⟨hh, s, args⟩ a q' ∧
          y = ((resumeResult s t a.result).config a.store, q')) ∨
        (L.Silent q ⟨hh, s, args⟩ ∧ y = (t.config s, q)))) := by
  have hst : (t.config s).store = s := Thread.config_store s t
  cases hstep with
  | internal h0 =>
    rcases (stepP_iff P _ s t _).mp h0 with ⟨s₁, f₁, code₁, rfl, hi⟩ | ⟨-, -, -, -, -, hb⟩
    · exact .inl ⟨s₁, .active f₁ code₁, rfl, hi⟩
    · rcases hb with ⟨-, -, hf, -⟩ | ⟨hf, -⟩ <;> exact hf.elim
  | @answer _ E fa hh args a _ q' hd ans =>
    have hd' : decompose? s (t.config s).code = some (E, fa, hh, args) := by
      simpa only [hst] using hd
    have ans' : L.Ans q ⟨hh, s, args⟩ a q' := by
      rw [hst] at ans
      exact ans
    refine .inr ⟨hh, args, ⟨E, fa, hd'⟩, .inl ⟨a, q', ans', ?_⟩⟩
    rw [resumeResult_config hd']
  | @silent _ E fa hh args _ hd hs =>
    have hd' : decompose? s (t.config s).code = some (E, fa, hh, args) := by
      simpa only [hst] using hd
    have hs' : L.Silent q ⟨hh, s, args⟩ := by
      rw [hst] at hs
      exact hs
    exact .inr ⟨hh, args, ⟨E, fa, hd'⟩, .inr ⟨hs', rfl⟩⟩

/-- A callout answered by the host is one product step to the resumed thread, in the store
of the answer. -/
theorem callout_uStep {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val} {a : UReply}
    {q q' : L.S} (callout : CalloutAt s t hh args) (hans : L.Ans q ⟨hh, s, args⟩ a q') :
    UStep P L (t.config s, q) ((resumeResult s t a.result).config a.store, q') := by
  obtain ⟨E, fa, hd⟩ := callout
  have hst : (t.config s).store = s := Thread.config_store s t
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, fa, hh, args) := by
    rw [hst]
    exact hd
  have hans' : L.Ans q ⟨hh, (t.config s).store, args⟩ a q' := by rw [hst]; exact hans
  rw [resumeResult_config hd]
  exact UStep.answer hd' hans'

/-- A callout on which the host may stay silent is a product self-loop. -/
theorem silent_uStep {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val} {q : L.S}
    (callout : CalloutAt s t hh args) (hs : L.Silent q ⟨hh, s, args⟩) :
    UStep P L (t.config s, q) (t.config s, q) := by
  obtain ⟨E, fa, hd⟩ := callout
  have hst : (t.config s).store = s := Thread.config_store s t
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, fa, hh, args) := by
    rw [hst]
    exact hd
  have hs' : L.Silent q ⟨hh, (t.config s).store, args⟩ := by rw [hst]; exact hs
  exact UStep.silent hd' hs'

/-! ### Finite runs: operations to game -/

/-- An answered callout is two hidden exchanges of the composite system. -/
theorem cmp_run_answer (f : U.F.Op) {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val}
    {a : UReply} {q q' : L.S} (callout : CalloutAt s t hh args)
    (hans : L.Ans q ⟨hh, s, args⟩ a q') :
    (Cmp U P L q₀).Run ((q, none), .running f s t) []
      ((q', none), .running f a.store (resumeResult s t a.result)) :=
  .tau (.sync (Ev.ask (⟨hh, s, args⟩ : UCall Nat)) (SEnv.DTrans.ask q _) (Trans.ucall callout))
    (.tau (.sync (Ev.ans (⟨hh, s, args⟩ : UCall Nat) a) (SEnv.DTrans.ans hans)
      (Trans.uret (P := P) (f := f) (s := s) (t := t) (e := ⟨hh, s, args⟩) a))
      (.nil _))

/-- **One product step is a silent run of the composite system.** -/
theorem cmp_run_of_uStep (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {z : Config Nat × L.S} (hstep : UStep P L (t.config s, q) z) :
    ∃ s' t', (Cmp U P L q₀).Run ((q, none), .running f s t) []
      ((z.2, none), .running f s' t') ∧ z.1 = t'.config s' := by
  rcases uStep_cases hstep with ⟨s₁, t₁, rfl, hi⟩ | ⟨hh, args, hco, hcase⟩
  · exact ⟨s₁, t₁, .tau (.tau₂ (Trans.tau hi)) (.nil _), rfl⟩
  · rcases hcase with ⟨a, q', hans, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨a.store, _, cmp_run_answer f hco hans, rfl⟩
    · exact ⟨s, t, .nil _, rfl⟩

/-- **A product run is a silent run of the composite system.** -/
theorem cmp_run_of_uSteps (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {y : Config Nat × L.S} (run : USteps P L (t.config s, q) y) :
    ∃ s' t', (Cmp U P L q₀).Run ((q, none), .running f s t) []
      ((y.2, none), .running f s' t') ∧ y.1 = t'.config s' := by
  induction run with
  | refl => exact ⟨s, t, .nil _, rfl⟩
  | @tail y z _ hst ih =>
    obtain ⟨s₁, t₁, hr₁, hy⟩ := ih
    have hst' : UStep P L (t₁.config s₁, y.2) z := by
      rw [← hy]
      exact hst
    obtain ⟨s₂, t₂, hr₂, hz⟩ := cmp_run_of_uStep (q₀ := q₀) f hst'
    exact ⟨s₂, t₂, hr₁.append hr₂, hz⟩

/-- A product run of an export call to the result `r` is a run of the composite system
answering `⟨c'.store, r⟩` and returning to the idle state in the final host state. -/
theorem cmp_run_of_run (f : U.F.Op) {q q' : L.S} {c' : Config Nat} {r : Result}
    (run : USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q'))
    (final : c'.code = r.toAdmin) :
    (Cmp U P L q).Run (Cmp U P L q).init [.inr (.ask f), .inr (.ans f ⟨c'.store, r⟩)]
      ((q', none), .idle) := by
  obtain ⟨s', t', hrun, hc₀⟩ := cmp_run_of_uSteps (q₀ := q) f (t := U.init f) run
  have hc : c' = t'.config s' := hc₀
  have hfinal : ResultAt s' t' r := by
    show (t'.config s').code = r.toAdmin
    rw [← hc]
    exact final
  have hstore : c'.store = s' := by rw [hc, Thread.config_store]
  rw [hstore]
  have hcall : (Cmp U P L q).step (Cmp U P L q).init (some (.inr (.ask f)))
      ((q, none), .running f f.store (U.init f)) := .right (Ev.ask f) (Trans.call f)
  have hans : (Cmp U P L q).step ((q', none), .running f s' t') (some (.inr (.ans f ⟨s', r⟩)))
      ((q', none), .idle) := .right (Ev.ans f ⟨s', r⟩) (Trans.oret hfinal)
  exact .vis hcall (hrun.append (.vis hans (.nil _)))

/-- **Operations to game.** A product run of an export call to the result `r` is an answer
`⟨c'.store, r⟩` of the closed program. -/
theorem responds_of_run (f : U.F.Op) {q q' : L.S} {c' : Config Nat} {r : Result}
    (run : USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q'))
    (final : c'.code = r.toAdmin) : Responds (U.closed P L q) f ⟨c'.store, r⟩ :=
  responds_iff.2 ⟨_, cmp_run_of_run f run final⟩

/-! ### Finite runs: game to operations -/

/-- The relation between product configurations and states of the composite system during the
export call `f`. -/
def URel (f : U.F.Op) (cq : Config Nat × L.S) (x : (Cmp U P L q₀).State) : Prop :=
  (∃ (s : Store Nat) (t : Thread), x = ((cq.2, none), .running f s t) ∧ cq.1 = t.config s) ∨
  (∃ (s : Store Nat) (t : Thread) (h : Nat) (args : List Val),
    x = ((cq.2, some ⟨h, s, args⟩), .waiting f s t ⟨h, s, args⟩) ∧ cq.1 = t.config s ∧
      CalloutAt s t h args)

/-- A silent step of the composite from a running state is matched by product steps. -/
theorem uSteps_of_silent_running (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    {x' : (Cmp U P L q₀).State} (hs : (Cmp U P L q₀).step ((q, none), .running f s t) none x') :
    ∃ cq', USteps P L (t.config s, q) cq' ∧ URel (q₀ := q₀) f cq' x' := by
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
      | ucall hco => exact ⟨_, .refl, .inr ⟨s, t, _, _, rfl, rfl, hco⟩⟩

/-- A silent step of the composite from a waiting state is matched by product steps. -/
theorem uSteps_of_silent_waiting (f : U.F.Op) {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args) {x' : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step ((q, some ⟨h, s, args⟩), .waiting f s t ⟨h, s, args⟩) none x') :
    ∃ cq', USteps P L (t.config s, q) cq' ∧ URel (q₀ := q₀) f cq' x' := by
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop _ => exact ⟨_, .refl, .inr ⟨s, t, h, args, rfl, rfl, hco⟩⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hans =>
      cases hi with
      | uret a => exact ⟨_, .single (callout_uStep hco hans), .inl ⟨_, _, rfl, rfl⟩⟩

/-- **A silent step of the composite is matched by product steps.** -/
theorem uSteps_of_silent (f : U.F.Op) {cq : Config Nat × L.S}
    {x x' : (Cmp U P L q₀).State} (hc : URel f cq x) (hs : (Cmp U P L q₀).step x none x') :
    ∃ cq', USteps P L cq cq' ∧ URel f cq' x' := by
  obtain ⟨c, q⟩ := cq
  rcases hc with ⟨s, t, rfl, hct⟩ | ⟨s, t, h, args, rfl, hct, hco⟩
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact uSteps_of_silent_running f hs
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact uSteps_of_silent_waiting f hco hs

/-- **A silent run of the composite is matched by a product run.** -/
theorem uSteps_of_run_nil (f : U.F.Op) {x y : (Cmp U P L q₀).State}
    {p : List (Move Sig.empty U.F)} (h : (Cmp U P L q₀).Run x p y) (hp : p = []) :
    ∀ cq, URel f cq x → ∃ cq', USteps P L cq cq' ∧ URel f cq' y := by
  induction h with
  | nil x => exact fun cq hc => ⟨cq, .refl, hc⟩
  | tau hs _ ih =>
    intro cq hc
    obtain ⟨cq₁, hr₁, hc₁⟩ := uSteps_of_silent f hc hs
    obtain ⟨cq₂, hr₂, hc₂⟩ := ih hp cq₁ hc₁
    exact ⟨cq₂, hr₁.trans hr₂, hc₂⟩
  | vis _ _ _ => cases hp

/-- The initial state of the composite takes no silent step. -/
theorem init_no_silent {x : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step (Cmp U P L q₀).init none x) : False := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ask q e => cases hi

/-- Silent runs from the initial state stay there. -/
theorem init_run_nil {x y : (Cmp U P L q₀).State} {p : List (Move Sig.empty U.F)}
    (h : (Cmp U P L q₀).Run x p y) (hp : p = []) (hx : x = (Cmp U P L q₀).init) :
    y = (Cmp U P L q₀).init := by
  cases h with
  | nil => exact hx
  | tau hs _ => exact (init_no_silent (hx ▸ hs)).elim
  | vis _ _ => cases hp

/-- Reading the export question from the initial state. -/
theorem step_ask_inv {f : U.F.Op} {x : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step (Cmp U P L q₀).init (some (.inr (.ask f))) x) :
    x = ((q₀, none), .running f f.store (U.init f)) := by
  cases hs with
  | right g hi =>
    cases hi with
    | call f' => rfl

/-- The answer move from a running state: the thread is finished. -/
theorem final_running (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S} {a : UReply}
    {x' : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step ((q, none), .running f s t) (some (.inr (.ans f a))) x') :
    (t.config s).code = a.result.toAdmin ∧ (t.config s).store = a.store := by
  cases hs with
  | right g hi =>
    cases hi with
    | oret final => exact ⟨final, Thread.config_store s t⟩

/-- A waiting state does not answer the export question. -/
theorem not_ans_waiting (f : U.F.Op) {s : Store Nat} {t : Thread} {e : U.E.Op}
    {q : Option U.E.Op × L.S} {a : UReply} {x' : (Cmp U P L q₀).State}
    (hs : (Cmp U P L q₀).step ((q.2, q.1), .waiting f s t e) (some (.inr (.ans f a))) x') :
    False := by
  cases hs with
  | right g hi => cases hi

/-- The answer move from a related state is a final configuration. -/
theorem final_of_step_ans (f : U.F.Op) {cq : Config Nat × L.S} {a : UReply}
    {x x' : (Cmp U P L q₀).State} (hc : URel f cq x)
    (hs : (Cmp U P L q₀).step x (some (.inr (.ans f a))) x') :
    cq.1.code = a.result.toAdmin ∧ cq.1.store = a.store := by
  rcases hc with ⟨s, t, hx, hct⟩ | ⟨s, t, h, args, hx, -, -⟩
  · rw [hx] at hs
    rw [hct]
    exact final_running f hs
  · rw [hx] at hs
    exact (not_ans_waiting (q := (some ⟨h, s, args⟩, cq.2)) f hs).elim

/-- **Game to operations.** An answer `a` of the closed program is a product run of the
export call to the result `a.result`, in the final store `a.store`. -/
theorem run_of_responds {f : U.F.Op} {q : L.S} {a : UReply} (h : Responds (U.closed P L q) f a) :
    ∃ (c' : Config Nat) (q' : L.S),
      USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
        c'.code = a.result.toAdmin ∧ c'.store = a.store := by
  obtain ⟨y, hy⟩ := responds_iff.1 h
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv hy
  have hx₁ : x₁ = (Cmp U P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.store (U.init f)) := step_ask_inv (hx₁ ▸ hs₁)
  have hc₂ : URel (q₀ := q) f (invoke f.store (U.addr f.target) f.args, q) x₂ :=
    .inl ⟨f.store, U.init f, hx₂, rfl⟩
  obtain ⟨x₃, x₄, hr₃, hs₃, -⟩ := LTS.Run.cons_inv hr₂
  obtain ⟨⟨c', q'⟩, hrun, hc₃⟩ := uSteps_of_run_nil f hr₃ rfl _ hc₂
  obtain ⟨hfinal, hstore⟩ := final_of_step_ans f hc₃ hs₃
  exact ⟨c', q', hrun, hfinal, hstore⟩

/-- **Answers of the closed program are finite product runs**, with the final store. -/
theorem responds_iff_run {f : U.F.Op} {q : L.S} {a : UReply} :
    Responds (U.closed P L q) f a ↔
      ∃ (c' : Config Nat) (q' : L.S),
        USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
          c'.code = a.result.toAdmin ∧ c'.store = a.store := by
  constructor
  · exact run_of_responds
  · rintro ⟨c', q', run, final, hs⟩
    have h := responds_of_run f run final
    rw [hs] at h
    exact h

/-! ### Divergence -/

/-- From a waiting state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem cmp_step_waiting (f : U.F.Op) {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args)
    (hinf : InfiniteTrace (UStep P L) (t.config s, q)) :
    ∃ y, (Cmp U P L q₀).step ((q, some ⟨h, s, args⟩), .waiting f s t ⟨h, s, args⟩) none y ∧
      ∃ cq, URel f cq y ∧ InfiniteTrace (UStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases uStep_cases hst with ⟨s₁, t₁, -, hi⟩ | ⟨h', args', hco', hcase⟩
  · exact absurd hi (calloutAt_no_internal hco _)
  · obtain ⟨rfl, rfl⟩ := calloutAt_unique hco' hco
    rcases hcase with ⟨a, q', hans, rfl⟩ | ⟨hs, rfl⟩
    · exact ⟨_, .sync (Ev.ans _ a) (SEnv.DTrans.ans hans) (Trans.uret a),
        _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
    · exact ⟨_, .tau₁ (SEnv.DTrans.loop hs), _, .inr ⟨s, t, h', args', rfl, rfl, hco⟩, hinf₁⟩

/-- From a running state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem cmp_step_running (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hinf : InfiniteTrace (UStep P L) (t.config s, q)) :
    ∃ y, (Cmp U P L q₀).step ((q, none), .running f s t) none y ∧
      ∃ cq, URel f cq y ∧ InfiniteTrace (UStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases uStep_cases hst with ⟨s₁, t₁, rfl, hi⟩ | ⟨h, args, hco, -⟩
  · exact ⟨_, .tau₂ (Trans.tau hi), _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
  · exact ⟨_, .sync (Ev.ask _) (SEnv.DTrans.ask q _) (Trans.ucall hco),
      _, .inr ⟨s, t, h, args, rfl, rfl, hco⟩, hinf⟩

/-- **An infinite product run is divergence of the composite.** -/
theorem cmp_diverges_of_inf (f : U.F.Op) {cq : Config Nat × L.S}
    {x : (Cmp U P L q₀).State} (hc : URel f cq x) (hinf : InfiniteTrace (UStep P L) cq) :
    (Cmp U P L q₀).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ cq, URel f cq x ∧ InfiniteTrace (UStep P L) cq) ?_ ⟨cq, hc, hinf⟩
  rintro x ⟨⟨c, q⟩, ⟨s, t, rfl, hct⟩ | ⟨s, t, h, args, rfl, hct, hco⟩, hinf⟩
  · have hinf' : InfiniteTrace (UStep P L) (t.config s, q) := hct ▸ hinf
    exact cmp_step_running f hinf'
  · have hinf' : InfiniteTrace (UStep P L) (t.config s, q) := hct ▸ hinf
    exact cmp_step_waiting f hco hinf'

/-- A diverging waiting state related to a configuration gives a product step to a related,
diverging state. -/
theorem uStep_waiting (f : U.F.Op) {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args)
    (hd : (Cmp U P L q₀).Diverges ((q, some ⟨h, s, args⟩), .waiting f s t ⟨h, s, args⟩)) :
    ∃ cq₁, UStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, URel f cq₁ x₁ ∧ (Cmp U P L q₀).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop hsil =>
      exact ⟨_, silent_uStep hco hsil, _, .inr ⟨s, t, h, args, rfl, rfl, hco⟩, hd₁⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hans =>
      cases hi with
      | uret a => exact ⟨_, callout_uStep hco hans, _, .inl ⟨_, _, rfl, rfl⟩, hd₁⟩

/-- A diverging running state related to a configuration gives a product step to a related,
diverging state. -/
theorem uStep_running (f : U.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hd : (Cmp U P L q₀).Diverges ((q, none), .running f s t)) :
    ∃ cq₁, UStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, URel f cq₁ x₁ ∧ (Cmp U P L q₀).Diverges x₁ := by
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
      | ucall hco => exact uStep_waiting f hco hd₁

/-- **Divergence of the composite is an infinite product run.** -/
theorem inf_of_cmp_diverges (f : U.F.Op) {cq : Config Nat × L.S}
    {x : (Cmp U P L q₀).State} (hc : URel f cq x) (hd : (Cmp U P L q₀).Diverges x) :
    InfiniteTrace (UStep P L) cq := by
  refine InfiniteTrace.coinduct
    (fun cq => ∃ x, URel (P := P) (q₀ := q₀) f cq x ∧ (Cmp U P L q₀).Diverges x)
    ?_ ⟨x, hc, hd⟩
  rintro ⟨c, q⟩ ⟨x, ⟨s, t, rfl, hct⟩ | ⟨s, t, h, args, rfl, hct, hco⟩, hd⟩
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact uStep_running f hd
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact uStep_waiting f hco hd

/-- The runs of the composite reading the export question from its initial state. -/
theorem run_ask_inv {q : L.S} {f : U.F.Op} {y : (Cmp U P L q).State}
    (h : (Cmp U P L q).Run (Cmp U P L q).init [.inr (.ask f)] y) :
    Relation.ReflTransGen (Cmp U P L q).Silent ((q, none), .running f f.store (U.init f)) y := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (Cmp U P L q).init := init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ((q, none), .running f f.store (U.init f)) := step_ask_inv (hx₁ ▸ hs₁)
  exact hx₂ ▸ Silmaril.Proofs.Wasm.Game.ScalarInstance.silent_of_run_nil hr₂ rfl

/-- **The divergent plays of the closed program after the export question.** -/
theorem mem_div_closedD_iff {q : L.S} (f : U.F.Op) :
    [.inr (.ask f)] ∈ (U.closedD P L q).div ↔
      InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q) := by
  rw [closedD_eq_ofLTS]
  refine (DStrategy.mem_div_ofLTS (L := Cmp U P L q)).trans ?_
  have hc : URel (P := P) (q₀ := q) f (invoke f.store (U.addr f.target) f.args, q)
      ((q, none), .running f f.store (U.init f)) := .inl ⟨f.store, U.init f, rfl, rfl⟩
  constructor
  · rintro ⟨⟨y, hy, hdiv⟩, -⟩
    exact inf_of_cmp_diverges f hc (InfiniteTrace.of_steps (run_ask_inv hy) hdiv)
  · intro hinf
    have hrun : (Cmp U P L q).Run (Cmp U P L q).init [.inr (.ask f)]
        ((q, none), .running f f.store (U.init f)) :=
      .vis (LTS.CompStep.right (Ev.ask f) (Trans.call f)) (.nil _)
    exact ⟨⟨_, hrun, cmp_diverges_of_inf f hc hinf⟩, f, .cons (.ask f) (.nil _)⟩

/-! ### Adequacy -/

/-- The terminating behaviours are the answers. -/
theorem mem_finite_iff (f : U.F.Op) (q : L.S) (b : Behaviour Val) :
    (∃ (c' : Config Nat) (q' : L.S) (r : Result),
      USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧ c'.code = r.toAdmin ∧
        b = r.toBehaviour) ↔
    ∃ a : UReply, Responds (U.closed P L q) f a ∧ b = a.result.toBehaviour := by
  constructor
  · rintro ⟨c', q', r, run, final, rfl⟩
    exact ⟨⟨c'.store, r⟩, responds_of_run f run final, rfl⟩
  · rintro ⟨a, hr, rfl⟩
    obtain ⟨c', q', run, final, -⟩ := responds_iff_run.1 hr
    exact ⟨c', q', a.result, run, final, rfl⟩

/-- **M2 for the untyped game, divergence read off the game, every profile, every
environment and every question.** -/
theorem uAdequacy_div (f : U.F.Op) (L : SEnv UImp) (q : L.S) :
    uBehavioursOf P L q (invoke f.store (U.addr f.target) f.args) =
      uDCompositeObs (U.closedD P L q) f := by
  have hforget : (U.closedD P L q).toStrategy = U.closed P L q := forget_closedD P L q
  ext b
  show (_ ∨ _) ↔ (_ ∨ _)
  rw [hforget]
  exact or_congr (mem_finite_iff f q b) (and_congr_right fun _ => (mem_div_closedD_iff f).symm)

end Silmaril.Proofs.Wasm.Game.Untyped
