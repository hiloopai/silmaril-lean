module

public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Logic.Open.Thms
public import Silmaril.Wasm.Logic.OpenTotal.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms

/-!
# The logic and the Wasm game: the strategy of an instance refines its specification

`strategy_sound`: if a scalar instance meets its export specification under its
import specification in the every-run logic (`GameSat P I Inv Ii Ie`), then from
every store meeting the invariant its strategy `I.strategy P s` (the strategy of
`Silmaril.Wasm.Game`, store hidden and persisting) refines `agStrat Ii Ie`.
`dstrategy_sound`: with total correctness (`TGameSat`), the
divergence-observing strategy `I.dstrategy P s` refines `dagStrat Ii Ie`: it
diverges only after a play in which Opponent broke the specifications.

Both proofs are inductions on the runs of the transition system `I.dlts P s`
of `Silmaril.Wasm.Game.DivAdequacy` (host-free machine steps silent; its plays are
those of `I.strategy P s`, `ScalarInstance.forget_dstrategy`) with the
invariant `Good`/`TGood`:

* `idle s`: the store meets `Inv`;
* `running f s t`: the thread is safe (resp. totally correct) under
  `gameHost I Ii` (resp. `gameHostT`) for the postcondition of the export
  question `f`;
* `waiting f s t e`: every allowed answer to `e` resumes a safe thread.

The steps follow `Silmaril.Proofs.Wasm.Logic.Open.Strategy` (`good_call`,
`good_done`), with silmaril-lean's threads (`Thread.config`, `resumeResult`) in
place of the configurations of `Open.modRed`: an export question is the
embedder's `$invoke` (`exportSpec` at `I.addr j`); a silent step is a host-free
Core step; at a callout the configuration is a host-call redex whose only steps
are host calls, so the import precondition holds, and the answer `v` of the game
is the host result `v.toResult` in the same store; an export answer is read off
a final configuration (`Open.final_post`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded (Thread decompose? resumeResult)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome agStrat AG MoveGood)
open Silmaril.Wasm.Logic.OpenTotal (OppGood dagStrat)

variable {I : ScalarInstance} {P : Profile} {Inv : Store Nat → Prop} {Ii : ISpec I.E}
  {Ie : ISpec I.F}

/-! ## Threads -/

/-- A thread's configuration is in the given store. -/
theorem config_store (s : Store Nat) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

/-- Resuming a thread at a callout plugs the result into the callout's context. -/
theorem resume_config {s : Store Nat} {t : Thread} {E : SingleThreaded.Ctx} {a h : Nat}
    {args : List Val} (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    (resumeResult s t r).config s = ⟨s, (t.config s).frame, E.fill r.toAdmin⟩ := by
  simp only [resumeResult, hd]
  rfl

/-- A callout answered by the host in the same store is a Core step to the resumed thread. -/
theorem resume_step {host : HostSemantics Nat} {s : Store Nat} {t : Thread}
    {E : SingleThreaded.Ctx} {a h : Nat} {args : List Val} {r : Result}
    (hd : decompose? s (t.config s).code = some (E, a, h, args))
    (hr : host h s args (.returned s r)) :
    Step P host (t.config s) ((resumeResult s t r).config s) := by
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, h, args) := by
    rw [config_store]
    exact hd
  have hr' : host h (t.config s).store args (.returned s r) := by
    rw [config_store]
    exact hr
  rw [resume_config hd]
  exact Open.redex_step_ret hd' hr'

/-- A host-free machine step is a Core step under every host. -/
theorem internal_step {host : HostSemantics Nat} {s s' : Store Nat} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) : Step P host (t.config s) (t'.config s') := by
  obtain ⟨f', code', ht', hst⟩ := h
  have ht'' : t' = .active f' code' := ht'
  rw [ht'']
  exact Step.of_noHost host hst

/-! ## Import calls -/

/-- The precondition of an import call, read from the host specification. -/
theorem import_pre_of_spec {k : Nat} {s : Store Nat} {args : List Val} {e : I.E.Op}
    (hop : I.importOp? k args = some e)
    (h : ∃ S, importCtx I Ii (id k) = some S ∧ S.pre s args) : Ii.pre e := by
  obtain ⟨S, hS, hpre⟩ := h
  obtain rfl : S = importSpec I Ii k := (Option.some.inj hS).symm
  obtain ⟨e', hop', hpre'⟩ := hpre
  obtain rfl : e' = e := Option.some.inj (hop'.symm.trans hop)
  exact hpre'

/-- An allowed answer to an allowed import call is an outcome of the game's environment. -/
theorem gameHost_answer {k : Nat} {s : Store Nat} {args : List Val} {e : I.E.Op}
    (hop : I.importOp? k args = some e) (hpre : Ii.pre e) {v : I.E.Ar e} (hv : Ii.post e v) :
    gameHost I Ii k s args (.returned s (Answer.toResult (ft := I.imports.get e.1) v)) := by
  refine ⟨importSpec I Ii k, rfl, ⟨e, hop, hpre⟩, rfl, fun e' hop' => ?_⟩
  obtain rfl : e' = e := Option.some.inj (hop'.symm.trans hop)
  exact ⟨v, hv, rfl⟩

/-- An allowed answer to an allowed import call is an outcome of the terminating
environment. -/
theorem gameHostT_answer {k : Nat} {s : Store Nat} {args : List Val} {e : I.E.Op}
    (hop : I.importOp? k args = some e) (hpre : Ii.pre e) {v : I.E.Ar e} (hv : Ii.post e v) :
    gameHostT I Ii k s args (.returned s (Answer.toResult (ft := I.imports.get e.1) v)) :=
  gameHost_answer hop hpre hv

/-! ## Export answers -/

/-- The postcondition of a run answering the export question `f` asked in store `s₀`. -/
abbrev qPost (I : ScalarInstance) (Inv : Store Nat → Prop) (Ie : ISpec I.F) (f : I.F.Op)
    (s₀ : Store Nat) : Post Nat :=
  callPost {} [] ((exportSpec I Inv Ie f.1).post s₀ f.2.1)

/-- What the export postcondition says about the answer read from a result. -/
theorem answer_of_post {f : I.F.Op} {s₀ s : Store Nat} {r : Result} {v : I.F.Ar f}
    (hpost : (exportSpec I Inv Ie f.1).post s₀ f.2.1 s (resultOutcome r))
    (answer : Answer.ofResult? (I.exports.get f.1) r = some v) : Inv s ∧ Ie.post f v := by
  have hv : v.toResult = r := Answer.toResult_of_ofResult? answer
  refine ⟨hpost.1, ?_⟩
  exact hpost.2 f.2.2 v (by rw [hv])

/-- A finished thread that is safe for one step meets the export postcondition. -/
theorem final_answer {host : HostSemantics Nat} {f : I.F.Op} {s₀ s : Store Nat} {t : Thread}
    {r : Result} {v : I.F.Ar f} (hsafe : Safe P host (qPost I Inv Ie f s₀) 1 (t.config s))
    (final : ResultAt s t r) (answer : Answer.ofResult? (I.exports.get f.1) r = some v) :
    Inv s ∧ Ie.post f v := by
  have hcode : (t.config s).code = r.toAdmin := final
  have hc : t.config s = ⟨s, (t.config s).frame, r.toAdmin⟩ :=
    calc t.config s = ⟨(t.config s).store, (t.config s).frame, (t.config s).code⟩ := rfl
      _ = ⟨s, (t.config s).frame, r.toAdmin⟩ := by rw [config_store, hcode]
  have hsafe' : Safe P host (qPost I Inv Ie f s₀) 1 ⟨s, (t.config s).frame, r.toAdmin⟩ :=
    hc ▸ hsafe
  exact answer_of_post (Open.final_post hsafe') answer

/-- The configuration of an export question is the embedder's `$invoke`, which the
export's specification covers. -/
theorem initThread_safe (hm : GameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s) {f : I.F.Op}
    (hf : Ie.pre f) (n : Nat) :
    Safe P (gameHost I Ii) (qPost I Inv Ie f s) n ((I.initThread f).config s) := by
  obtain ⟨j, args, ht⟩ := f
  exact hm j n s args ⟨hs, ht, hf⟩ {} [] _ trivial

/-- The total version of `initThread_safe`. -/
theorem initThread_tsafe (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s)
    {f : I.F.Op} (hf : Ie.pre f) :
    TSafe P (gameHostT I Ii) (qPost I Inv Ie f s) ((I.initThread f).config s) := by
  obtain ⟨j, args, ht⟩ := f
  exact hm j s args ⟨hs, ht, hf⟩ {} [] _ trivial

/-! ## Partial correctness: the invariant -/

/-- **The invariant** of the runs of an instance meeting its specification. -/
def Good (P : Profile) (I : ScalarInstance) (Inv : Store Nat → Prop) (Ii : ISpec I.E)
    (Ie : ISpec I.F) : I.HState → Prop
  | .idle s => Inv s
  | .running f s t => ∃ s₀, ∀ n, Safe P (gameHost I Ii) (qPost I Inv Ie f s₀) n (t.config s)
  | .waiting f s t e => ∃ s₀, ∀ v : I.E.Ar e, Ii.post e v → ∀ n,
      Safe P (gameHost I Ii) (qPost I Inv Ie f s₀) n
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

/-- A good import call: the precondition holds and every allowed answer resumes a good
thread. -/
theorem good_call {f : I.F.Op} {s : Store Nat} {t : Thread} {k : Nat} {args : List Val}
    {e : I.E.Op} (hx : Good P I Inv Ii Ie (.running f s t)) (callout : CalloutAt s t k args)
    (op : I.importOp? k args = some e) :
    Ii.pre e ∧ Good P I Inv Ii Ie (.waiting f s t e) := by
  obtain ⟨s₀, h⟩ := hx
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, k, args) := by
    rw [config_store]
    exact hd
  have hpre : Ii.pre e := by
    have hspec := Open.import_pre (h 1) hd'
    rw [config_store] at hspec
    exact import_pre_of_spec op hspec
  exact ⟨hpre, s₀, fun v hv n => (h (n + 1)).step_inv (resume_step hd (gameHost_answer op hpre hv))⟩

/-- One visible move of a good state is assume/guarantee correct. -/
theorem ag_vis (hm : GameSat P I Inv Ii Ie) {x y : I.HState} {o : Move I.E I.F}
    {p : List (Move I.E I.F)} (hs : I.DTrans P x (some o) y) (hx : Good P I Inv Ii Ie x)
    (ih : Good P I Inv Ii Ie y → AG Ii Ie p) : AG Ii Ie (o :: p) := by
  cases hs with
  | call s f => exact ⟨fun _ hg => ih ⟨s, initThread_safe hm hx hg⟩, fun h => h.elim⟩
  | ucall callout op =>
    exact ⟨fun h => h.elim, fun _ => ⟨(good_call hx callout op).1, ih (good_call hx callout op).2⟩⟩
  | uret v =>
    exact ⟨fun _ hg => ih (by obtain ⟨s₀, h⟩ := hx; exact ⟨s₀, h v hg⟩), fun h => h.elim⟩
  | oret final answer =>
    obtain ⟨s₀, h⟩ := hx
    have hans := final_answer (h 1) final answer
    exact ⟨fun h => h.elim, fun _ => ⟨hans.2, ih hans.1⟩⟩

/-- Silent steps keep the invariant. -/
theorem good_silent {x y : I.HState} (hs : I.DTrans P x none y) (hx : Good P I Inv Ii Ie x) :
    Good P I Inv Ii Ie y := by
  cases hs with
  | tau h =>
    obtain ⟨s₀, hsafe⟩ := hx
    exact ⟨s₀, fun n => (hsafe (n + 1)).step_inv (internal_step h)⟩

/-- Every run from a good state is assume/guarantee correct. -/
theorem run_ag (hm : GameSat P I Inv Ii Ie) {s : Store Nat} {x y : (I.dlts P s).State}
    {p : List (Move I.E I.F)} (hr : (I.dlts P s).Run x p y) :
    Good P I Inv Ii Ie x → AG Ii Ie p := by
  induction hr with
  | nil => exact fun _ => trivial
  | tau hs _ ih => exact fun hx => ih (good_silent hs hx)
  | vis hs _ ih => exact fun hx => ag_vis hm hs hx ih

/-- **The game link, partial correctness.** -/
theorem strategy_sound (hm : GameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s) :
    I.strategy P s ≤ agStrat Ii Ie := by
  rw [← ScalarInstance.forget_dstrategy P s]
  exact Strategy.generate_le fun _ ⟨_, hr⟩ hl => ⟨hl, run_ag hm hr hs⟩

/-- **The game link at the instantiated store**: the strategy `I.σ P` of the instance. -/
theorem σ_sound (hm : GameSat P I Inv Ii Ie) (hs : Inv I.store) : I.σ P ≤ agStrat Ii Ie :=
  strategy_sound hm hs

/-! ## Total correctness: the invariant -/

/-- **The invariant** of the runs of an instance meeting its specification totally. -/
def TGood (P : Profile) (I : ScalarInstance) (Inv : Store Nat → Prop) (Ii : ISpec I.E)
    (Ie : ISpec I.F) : I.HState → Prop
  | .idle s => Inv s
  | .running f s t => ∃ s₀, TSafe P (gameHostT I Ii) (qPost I Inv Ie f s₀) (t.config s)
  | .waiting f s t e => ∃ s₀, ∀ v : I.E.Ar e, Ii.post e v →
      TSafe P (gameHostT I Ii) (qPost I Inv Ie f s₀)
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

/-- A totally correct import call: the precondition holds and every allowed answer resumes
a totally correct thread. -/
theorem tgood_call {f : I.F.Op} {s : Store Nat} {t : Thread} {k : Nat} {args : List Val}
    {e : I.E.Op} (hx : TGood P I Inv Ii Ie (.running f s t)) (callout : CalloutAt s t k args)
    (op : I.importOp? k args = some e) :
    Ii.pre e ∧ TGood P I Inv Ii Ie (.waiting f s t e) := by
  obtain ⟨s₀, h⟩ := hx
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, k, args) := by
    rw [config_store]
    exact hd
  have hpre : Ii.pre e := by
    have hspec := OpenTotal.timport_pre h hd'
    rw [config_store] at hspec
    exact import_pre_of_spec op hspec
  exact ⟨hpre, s₀, fun v hv => h.step_inv (resume_step hd (gameHostT_answer op hpre hv))⟩

/-- Silent steps keep the total invariant. -/
theorem tgood_silent {x y : I.HState} (hs : I.DTrans P x none y) (hx : TGood P I Inv Ii Ie x) :
    TGood P I Inv Ii Ie y := by
  cases hs with
  | tau h =>
    obtain ⟨s₀, hsafe⟩ := hx
    exact ⟨s₀, hsafe.step_inv (internal_step h)⟩

/-- A visible move keeps the total invariant when Opponent's move is good. -/
theorem tgood_vis (hm : TGameSat P I Inv Ii Ie) {x y : I.HState} {o : Move I.E I.F}
    (hs : I.DTrans P x (some o) y) (hx : TGood P I Inv Ii Ie x)
    (ho : Move.IsO o → MoveGood Ii Ie o) : TGood P I Inv Ii Ie y := by
  cases hs with
  | call s f => exact ⟨s, initThread_tsafe hm hx (ho trivial)⟩
  | ucall callout op => exact (tgood_call hx callout op).2
  | uret v => obtain ⟨s₀, h⟩ := hx; exact ⟨s₀, h v (ho trivial)⟩
  | oret final answer =>
    obtain ⟨s₀, h⟩ := hx
    exact (final_answer (TSafe.safe h 1) final answer).1

/-- One visible move of a totally good state is assume/guarantee correct. -/
theorem tag_vis (hm : TGameSat P I Inv Ii Ie) {x y : I.HState} {o : Move I.E I.F}
    {p : List (Move I.E I.F)} (hs : I.DTrans P x (some o) y) (hx : TGood P I Inv Ii Ie x)
    (ih : TGood P I Inv Ii Ie y → AG Ii Ie p) : AG Ii Ie (o :: p) := by
  cases hs with
  | call s f => exact ⟨fun _ hg => ih ⟨s, initThread_tsafe hm hx hg⟩, fun h => h.elim⟩
  | ucall callout op =>
    exact ⟨fun h => h.elim, fun _ =>
      ⟨(tgood_call hx callout op).1, ih (tgood_call hx callout op).2⟩⟩
  | uret v =>
    exact ⟨fun _ hg => ih (by obtain ⟨s₀, h⟩ := hx; exact ⟨s₀, h v hg⟩), fun h => h.elim⟩
  | oret final answer =>
    obtain ⟨s₀, h⟩ := hx
    have hans := final_answer (TSafe.safe h 1) final answer
    exact ⟨fun h => h.elim, fun _ => ⟨hans.2, ih hans.1⟩⟩

/-- Every run from a totally good state is assume/guarantee correct. -/
theorem trun_ag (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} {x y : (I.dlts P s).State}
    {p : List (Move I.E I.F)} (hr : (I.dlts P s).Run x p y) :
    TGood P I Inv Ii Ie x → AG Ii Ie p := by
  induction hr with
  | nil => exact fun _ => trivial
  | tau hs _ ih => exact fun hx => ih (tgood_silent hs hx)
  | vis hs _ ih => exact fun hx => tag_vis hm hs hx ih

/-- After a run whose Opponent moves are good, the total invariant holds. -/
theorem run_tgood (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} {x y : (I.dlts P s).State}
    {p : List (Move I.E I.F)} (hr : (I.dlts P s).Run x p y) :
    TGood P I Inv Ii Ie x → OppGood Ii Ie p → TGood P I Inv Ii Ie y := by
  induction hr with
  | nil => exact fun hx _ => hx
  | tau hs _ ih => exact fun hx hp => ih (tgood_silent hs hx) hp
  | vis hs _ ih =>
    exact fun hx hp => ih (tgood_vis hm hs hx (hp _ (List.mem_cons_self ..)))
      (fun m hm' => hp m (List.mem_cons_of_mem _ hm'))

/-! ## Divergence -/

/-- The Core configuration of a hidden state (that of its thread). -/
def HState.cfg : I.HState → Config Nat
  | .idle s => ⟨s, {}, []⟩
  | .running _ s t => t.config s
  | .waiting _ s t _ => t.config s

/-- A silent infinite run of the instance is an infinite Core run, under every host. -/
theorem diverges_core {host : HostSemantics Nat} {s : Store Nat} {x : I.HState}
    (hd : (I.dlts P s).Diverges x) : Diverges P host (HState.cfg x) :=
  Silmaril.InfiniteTrace.map HState.cfg (fun _ _ hst => by
    cases hst with
    | tau h => exact internal_step h) hd

/-- No silent infinite run from a totally good state. -/
theorem tgood_not_diverges {s : Store Nat} {x : I.HState} (hx : TGood P I Inv Ii Ie x) :
    ¬ (I.dlts P s).Diverges x := by
  intro hd
  cases x with
  | idle s' =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    cases hs
  | running f s' t =>
    obtain ⟨s₀, h⟩ := hx
    exact TSafe.not_diverges h (diverges_core hd)
  | waiting f s' t e =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    cases hs

/-- **No divergence after good Opponent behaviour.** -/
theorem dstrategy_div (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s)
    {p : List (Move I.E I.F)} (hp : p ∈ (I.dstrategy P s).div) : ¬ OppGood Ii Ie p := by
  intro hg
  obtain ⟨⟨y, hr, hd⟩, -⟩ := hp
  exact tgood_not_diverges (run_tgood hm hr hs hg) hd

/-- **The game link, total correctness.** -/
theorem dstrategy_sound (hm : TGameSat P I Inv Ii Ie) {s : Store Nat} (hs : Inv s) :
    I.dstrategy P s ≤ dagStrat Ii Ie := by
  have hfin : (I.dstrategy P s).toStrategy ≤ agStrat Ii Ie :=
    Strategy.generate_le fun _ ⟨_, hr⟩ hl => ⟨hl, trun_ag hm hr hs⟩
  refine ⟨hfin, fun p hp => ⟨hfin ((I.dstrategy P s).div_mem hp),
    (I.dstrategy P s).div_run hp, dstrategy_div hm hs hp⟩, fun J hJ => ?_⟩
  exact ⟨(I.dstrategy P s).inf_isInf hJ, fun q hq => hfin ((I.dstrategy P s).inf_sub hJ hq)⟩


/-- **The total game link at the instantiated store.** -/
theorem dσ_sound (hm : TGameSat P I Inv Ii Ie) (hs : Inv I.store) :
    I.dstrategy P I.store ≤ dagStrat Ii Ie :=
  dstrategy_sound hm hs

end Silmaril.Wasm.Logic.GameLink
