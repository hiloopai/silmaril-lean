module

public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Main
public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Comp
public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Diverge
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Divergence against stateful hosts, read off the game: proofs

* `SEnv.denotes_dlts`, `SEnv.silentRunning_dlts`: the divergence-observing
  system of a stateful environment denotes its strategy (the silent loops are
  invisible) and loops only on a pending question.
* `closedSD_eq_ofLTS`: hence, by `DStrategy.ofLTS_comp`, the composite
  `I.closedSD P s L q = (L.dstrategy q).comp (I.dstrategy P s)` is the
  divergence-observing strategy of the composite system
  `(L.dlts q).comp (I.dlts P s)`.
* `sdiverges_iff_scmp`: an infinite product run (`SStep P L`) from an export
  call is an infinite silent run of the composite system after the question.
  The runs correspond through `SRel`, as in the stateless
  `Silmaril.Proofs.Wasm.Game.DivAdequacy.Diverge`, with the host state carried
  by the environment's system: a host-free Core step is a silent instance step,
  an answered host call is the hidden exchange of question and answer (the
  host state moving as `L` does), and a host that may stay silent is the
  environment's self-loop, matching the product self-loop `SStep.silent`.
* `mem_div_closedSD_iff`, `sadequacy_div`: so the divergence part of the
  stateful M2 is read off the composite strategy.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace SEnv

variable {E : Sig.{0}} {L : Silmaril.Wasm.Game.SEnv E}

/-- Runs of the divergence-observing environment are runs of the plain one. -/
theorem lts_run_of_dlts_run {q₀ : L.S} {x y : (L.dlts q₀).State} {p : List (Move Sig.empty E)}
    (h : (L.dlts q₀).Run x p y) : (L.lts q₀).Run x p y := by
  induction h with
  | nil x => exact LTS.Run.nil (L := L.lts q₀) x
  | tau hs _ ih =>
    cases hs
    exact ih
  | vis hs _ ih =>
    cases hs with
    | ask q e => exact .vis (.ask q e) ih
    | ans hw => exact .vis (.ans hw) ih

/-- Runs of the plain environment are runs of the divergence-observing one. -/
theorem dlts_run_of_lts_run {q₀ : L.S} {x y : (L.lts q₀).State} {p : List (Move Sig.empty E)}
    (h : (L.lts q₀).Run x p y) : (L.dlts q₀).Run x p y := by
  induction h with
  | nil x => exact LTS.Run.nil (L := L.dlts q₀) x
  | tau hs _ _ => cases hs
  | vis hs _ ih =>
    cases hs with
    | ask q e => exact .vis (.ask q e) ih
    | ans hw => exact .vis (.ans hw) ih

/-- The divergence-observing system of a stateful environment denotes its strategy. -/
theorem denotes_dlts (L : Silmaril.Wasm.Game.SEnv E) (q : L.S) : (L.dlts q).Denotes (L.strategy q) := by
  intro p
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl, hu⟩ := run_none_aux _ q p y (Nat.le_refl _) (lts_run_of_dlts_run hy)
    exact mem_strategy_iff.2 ⟨u, hu, rfl⟩
  · intro hp
    obtain ⟨u, hu, rfl⟩ := mem_strategy_iff.1 hp
    obtain ⟨y, hy⟩ := run_of_agrees (q₀ := q) hu
    exact ⟨y, dlts_run_of_lts_run hy⟩

/-- The game position of a state of the environment's system. -/
def dpos : L.S × Option E.Op → Pos Sig.empty E
  | (_, none) => .idle
  | (_, some e) => .run e

/-- The environment's system loops only on a pending question. -/
theorem silentRunning_dlts (L : Silmaril.Wasm.Game.SEnv E) (q : L.S) : (L.dlts q).SilentRunning := by
  refine LTS.silentRunning_of_pos (L := L.dlts q) dpos rfl ?_ ?_ ?_
  · intro x y o h
    cases h with
    | ask q e => exact .ask e
    | ans hw => exact .ret _ _
  · intro x y h
    cases h
    rfl
  · intro x y h
    cases h
    exact ⟨_, rfl⟩

/-- The finite plays of the divergence-observing environment are its strategy. -/
theorem forget_dstrategy (L : Silmaril.Wasm.Game.SEnv E) (q : L.S) :
    (L.dstrategy q).forget = L.strategy q :=
  (denotes_dlts L q).ofLTS_eq

end SEnv

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile} {s₀ : Store Nat}
  {L : Silmaril.Wasm.Game.SEnv I.E} {q₀ : L.S}

open Silmaril.Wasm.Game.ScalarInstance

/-- The composite system of the closed program against a stateful environment. -/
abbrev SCmp (I : Silmaril.Wasm.Game.ScalarInstance) (P : Profile) (s₀ : Store Nat)
    (L : Silmaril.Wasm.Game.SEnv I.E) (q₀ : L.S) : LTS Sig.empty I.F :=
  (L.dlts q₀).comp (I.dlts P s₀)

/-- **The composite strategy is the strategy of the composite system.** -/
theorem closedSD_eq_ofLTS (P : Profile) (s : Store Nat) (L : Silmaril.Wasm.Game.SEnv I.E) (q : L.S) :
    I.closedSD P s L q = DStrategy.ofLTS (SCmp I P s L q) :=
  (DStrategy.ofLTS_comp (SEnv.denotes_dlts L q) (denotes_dlts P s)
    (LTS.SilentRunning.divRunning (SEnv.silentRunning_dlts L q))
    (LTS.SilentRunning.divRunning (silentRunning_dlts P s))).symm

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedSD (P : Profile) (s : Store Nat) (L : Silmaril.Wasm.Game.SEnv I.E) (q : L.S) :
    (I.closedSD P s L q).forget = I.closedS P s L q := by
  show (L.dstrategy q).forget.comp (I.dstrategy P s).forget = (L.strategy q).comp (I.strategy P s)
  rw [SEnv.forget_dstrategy, forget_dstrategy]

/-- The relation between product configurations and states of the composite system during the
export call `f`. -/
def SRel (f : I.F.Op) (cq : Config Nat × L.S) (x : (SCmp I P s₀ L q₀).State) : Prop :=
  (∃ (s : Store Nat) (t : Thread), x = ((cq.2, none), .running f s t) ∧ cq.1 = t.config s) ∨
  (∃ (s : Store Nat) (t : Thread) (e : I.E.Op) (h : Nat) (args : List Val),
    x = ((cq.2, some e), .waiting f s t e) ∧ cq.1 = t.config s ∧ CalloutAt s t h args ∧
      I.importOp? h args = some e)

/-- One product step from a thread configuration, read on threads. -/
theorem sstep_cases {s : Store Nat} {t : Thread} {q : L.S} {y : Config Nat × L.S}
    (hstep : SStep P L (t.config s, q) y) :
    (∃ s₁ t₁, y = (t₁.config s₁, q) ∧ InternalP P (s, t) (s₁, t₁)) ∨
      (∃ hh args e, CalloutAt s t hh args ∧ I.importOp? hh args = some e ∧
        ((∃ w q', L.Ans q e w q' ∧
          y = ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s, q')) ∨
        (L.Silent q e ∧ y = (t.config s, q)))) := by
  have hst : (t.config s).store = s := Thread.config_store s t
  cases hstep with
  | internal h0 =>
    rcases (stepP_iff P _ s t _).mp h0 with ⟨s₁, f₁, code₁, rfl, hi⟩ | ⟨-, -, -, -, -, hb⟩
    · exact .inl ⟨s₁, .active f₁ code₁, rfl, hi⟩
    · rcases hb with ⟨-, -, hf, -⟩ | ⟨hf, -⟩ <;> exact hf.elim
  | @answer _ E a hh args e w _ q' hd op ans =>
    have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by
      simpa only [hst] using hd
    refine .inr ⟨hh, args, e, ⟨E, a, hd'⟩, op, .inl ⟨w, q', ans, ?_⟩⟩
    rw [resumeResult_config hd', hst]
  | @silent _ E a hh args e _ hd op hs =>
    have hd' : decompose? s (t.config s).code = some (E, a, hh, args) := by
      simpa only [hst] using hd
    exact .inr ⟨hh, args, e, ⟨E, a, hd'⟩, op, .inr ⟨hs, rfl⟩⟩

/-- A callout on which the host may stay silent is a product self-loop. -/
theorem silent_sstep {s : Store Nat} {t : Thread} {hh : Nat} {args : List Val} {e : I.E.Op}
    {q : L.S} (callout : CalloutAt s t hh args) (op : I.importOp? hh args = some e)
    (hs : L.Silent q e) : SStep P L (t.config s, q) (t.config s, q) := by
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, hh, args) := by
    rw [Thread.config_store]
    exact hd
  exact SStep.silent hd' op hs

/-! ### Infinite product runs to divergence of the composite -/

/-- From a waiting state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem scmp_step_waiting (f : I.F.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hinf : InfiniteTrace (SStep P L) (t.config s, q)) :
    ∃ y, (SCmp I P s₀ L q₀).step ((q, some e), .waiting f s t e) none y ∧
      ∃ cq, SRel f cq y ∧ InfiniteTrace (SStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases sstep_cases hst with ⟨s₁, t₁, -, hi⟩ | ⟨h', args', e', hco', hop', hcase⟩
  · exact absurd hi (calloutAt_no_internal hco _)
  · obtain ⟨rfl, rfl⟩ := calloutAt_unique hco' hco
    obtain rfl : e' = e := Option.some.inj (hop'.symm.trans hop)
    rcases hcase with ⟨w, q', hans, rfl⟩ | ⟨hs, rfl⟩
    · exact ⟨_, .sync (Ev.ans e' w) (Silmaril.Wasm.Game.SEnv.DTrans.ans hans) (DTrans.uret w),
        _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
    · exact ⟨_, .tau₁ (Silmaril.Wasm.Game.SEnv.DTrans.loop hs), _,
        .inr ⟨s, t, e', h', args', rfl, rfl, hco, hop⟩, hinf₁⟩

/-- From a running state related to an infinite product run, the composite takes a silent
step to a related state. -/
theorem scmp_step_running (f : I.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hinf : InfiniteTrace (SStep P L) (t.config s, q)) :
    ∃ y, (SCmp I P s₀ L q₀).step ((q, none), .running f s t) none y ∧
      ∃ cq, SRel f cq y ∧ InfiniteTrace (SStep P L) cq := by
  obtain ⟨y₁, hst, hinf₁⟩ := hinf.unfold
  rcases sstep_cases hst with ⟨s₁, t₁, rfl, hi⟩ | ⟨h, args, e, hco, hop, -⟩
  · exact ⟨_, .tau₂ (DTrans.tau hi), _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
  · exact ⟨_, .sync (Ev.ask e) (Silmaril.Wasm.Game.SEnv.DTrans.ask q e) (DTrans.ucall hco hop),
      _, .inr ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hinf⟩

/-- **An infinite product run is divergence of the composite.** -/
theorem scmp_diverges_of_sinf (f : I.F.Op) {cq : Config Nat × L.S}
    {x : (SCmp I P s₀ L q₀).State} (hc : SRel f cq x) (hinf : InfiniteTrace (SStep P L) cq) :
    (SCmp I P s₀ L q₀).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ cq, SRel f cq x ∧ InfiniteTrace (SStep P L) cq) ?_ ⟨cq, hc, hinf⟩
  rintro x ⟨⟨c, q⟩, ⟨s, t, rfl, hct⟩ | ⟨s, t, e, h, args, rfl, hct, hco, hop⟩, hinf⟩
  · have hinf' : InfiniteTrace (SStep P L) (t.config s, q) := hct ▸ hinf
    exact scmp_step_running f hinf'
  · have hinf' : InfiniteTrace (SStep P L) (t.config s, q) := hct ▸ hinf
    exact scmp_step_waiting f hco hop hinf'

/-! ### Divergence of the composite to infinite product runs -/

/-- A diverging waiting state related to a configuration gives a product step to a related,
diverging state. -/
theorem sstep_waiting (f : I.F.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} {q : L.S} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hd : (SCmp I P s₀ L q₀).Diverges ((q, some e), .waiting f s t e)) :
    ∃ cq₁, SStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, SRel f cq₁ x₁ ∧ (SCmp I P s₀ L q₀).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop hsil =>
      exact ⟨_, silent_sstep hco hop hsil, _, .inr ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hd₁⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hans =>
      cases hi with
      | uret w => exact ⟨_, callout_sstep hco hop hans, _, .inl ⟨_, _, rfl, rfl⟩, hd₁⟩

/-- A diverging running state related to a configuration gives a product step to a related,
diverging state. -/
theorem sstep_running (f : I.F.Op) {s : Store Nat} {t : Thread} {q : L.S}
    (hd : (SCmp I P s₀ L q₀).Diverges ((q, none), .running f s t)) :
    ∃ cq₁, SStep P L (t.config s, q) cq₁ ∧
      ∃ x₁, SRel f cq₁ x₁ ∧ (SCmp I P s₀ L q₀).Diverges x₁ := by
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
      | ucall hco hop => exact sstep_waiting f hco hop hd₁

/-- **Divergence of the composite is an infinite product run.** -/
theorem sinf_of_scmp_diverges (f : I.F.Op) {cq : Config Nat × L.S}
    {x : (SCmp I P s₀ L q₀).State} (hc : SRel f cq x) (hd : (SCmp I P s₀ L q₀).Diverges x) :
    InfiniteTrace (SStep P L) cq := by
  refine InfiniteTrace.coinduct
    (fun cq => ∃ x, SRel (P := P) (s₀ := s₀) (q₀ := q₀) f cq x ∧ (SCmp I P s₀ L q₀).Diverges x)
    ?_ ⟨x, hc, hd⟩
  rintro ⟨c, q⟩ ⟨x, ⟨s, t, rfl, hct⟩ | ⟨s, t, e, h, args, rfl, hct, hco, hop⟩, hd⟩
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact sstep_running f hd
  · have hct' : (c, q) = (t.config s, q) := Prod.ext hct rfl
    rw [hct']
    exact sstep_waiting f hco hop hd

/-- **Infinite product runs, every profile**: the export call diverges against the stateful
host exactly when the composite system diverges silently right after the question. -/
theorem sdiverges_iff_scmp (f : I.F.Op) {s : Store Nat} {q : L.S} :
    InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q) ↔
      (SCmp I P s L q).Diverges ((q, none), .running f s (I.initThread f)) := by
  have hc : SRel (P := P) (s₀ := s) (q₀ := q) f (invoke s (I.addr f.1) f.2.1, q)
      ((q, none), .running f s (I.initThread f)) := .inl ⟨s, I.initThread f, rfl, rfl⟩
  exact ⟨scmp_diverges_of_sinf f hc, sinf_of_scmp_diverges f hc⟩

/-- The runs of the composite reading the export question from its initial state. -/
theorem srun_ask_inv {s : Store Nat} {q : L.S} {f : I.F.Op} {y : (SCmp I P s L q).State}
    (h : (SCmp I P s L q).Run (SCmp I P s L q).init [.inr (.ask f)] y) :
    Relation.ReflTransGen (SCmp I P s L q).Silent ((q, none), .running f s (I.initThread f)) y := by
  cases h with
  | tau hs _ =>
    cases hs with
    | tau₁ hk => cases hk
    | tau₂ hi => cases hi
    | sync g hk hi =>
      cases hk with
      | ask q e => cases hi
  | vis hs hr =>
    cases hs with
    | right g hi =>
      cases hi with
      | call s' f' => exact silent_of_run_nil hr rfl

/-- **The divergent plays of the closed program after the export question, stateful host.** -/
theorem mem_div_closedSD_iff {s : Store Nat} {q : L.S} (f : I.F.Op) :
    [.inr (.ask f)] ∈ (I.closedSD P s L q).div ↔
      InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q) := by
  rw [closedSD_eq_ofLTS]
  refine (DStrategy.mem_div_ofLTS (L := SCmp I P s L q)).trans ?_
  rw [sdiverges_iff_scmp f]
  constructor
  · rintro ⟨⟨y, hy, hdiv⟩, -⟩
    exact InfiniteTrace.of_steps (srun_ask_inv hy) hdiv
  · intro hdiv
    have hrun : (SCmp I P s L q).Run (SCmp I P s L q).init [.inr (.ask f)]
        ((q, none), .running f s (I.initThread f)) :=
      .vis (LTS.CompStep.right (Ev.ask f) (DTrans.call s f)) (.nil _)
    exact ⟨⟨_, hrun, hdiv⟩, f, .cons (.ask f) (.nil _)⟩

/-- **M2 for stateful environments with divergence read off the game, every profile.** -/
theorem sadequacy_div {s : Store Nat} (hw : I.WellFormed s) (L : Silmaril.Wasm.Game.SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    sbehavioursOf P L q (invoke s (I.addr f.1) f.2.1) = dcompositeObs (I.closedSD P s L q) f := by
  have hforget : (I.closedSD P s L q).toStrategy = I.closedS P s L q := forget_closedSD P s L q
  have hdiv : ∀ b : Behaviour Val, (b = .diverges ∧ [.inr (.ask f)] ∈ (I.closedSD P s L q).div) ↔
      (b = .diverges ∧ InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q)) :=
    fun _ => and_congr_right fun _ => mem_div_closedSD_iff f
  rw [sadequacy hw L hL q f]
  ext b
  show (b ∈ compositeObs (I.closedS P s L q) f ∨
      (b = .diverges ∧ InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q))) ↔
    ((∃ w, Responds (I.closedSD P s L q).toStrategy f w ∧
      b = Answer.toBehaviour (ft := I.exports.get f.1) w) ∨
      (b = .diverges ∧ [.inr (.ask f)] ∈ (I.closedSD P s L q).div))
  rw [hforget, hdiv b]
  constructor
  · rintro ((hans | ⟨hb, hno⟩) | hd)
    · exact .inl hans
    · exact .inr ⟨hb, sdiverges_of_no_answer hw hL hno⟩
    · exact .inr hd
  · rintro (hans | hd)
    · exact .inl (.inl hans)
    · exact .inr hd

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
