module

public import Silmaril.Wasm.Logic.Open.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.OpenTotal.Defs
public import Silmaril.Games.DivLTS.Thms

/-!
# Open modules with total correctness: the divergence-aware game link

`dmodStrat_sound`: if an open module meets its export specifications **totally**
under its import specifications (`TModuleSat`), its divergence-observing
strategy refines `dagStrat (ctxSpec Γi) (ctxSpec Γe)`:

* every finite play is assume/guarantee correct (as `Open.modStrat_sound`);
* **no divergence after a play in which Opponent behaved** (`OppGood`): the
  module answers every good question without computing forever between visible
  moves;
* infinite plays are plays.

The proof is an induction on the runs of `Open.modRed` with the invariant
`TGood`: while a good question is answered, the configuration is **totally**
correct under `specHostT bind Γi` for the postcondition of the export. After a
run whose Opponent moves are good the invariant holds (`run_tgood`); a silent
infinite run from a totally correct configuration is an infinite run of
`Step P (specHostT bind Γi)` (host-free steps are steps), which total
correctness excludes (`Hoare.TSafe.not_diverges`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenTotal

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Strategy (WCall resultOutcome ctxSpec ISpec agStrat AG MoveGood)

variable {H : Type} {P : Profile} {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}

/-- **The invariant** of the runs of a totally correct open module. -/
def TGood (P : Profile) (M : OMod H) (bind : H → Nat) (Γi Γe : Ctx H) :
    (modRed P M bind).State → Prop
  | .idle => True
  | .run q c => ∃ S, Γe q.1 = some S ∧ TSafe P (specHostT bind Γi) (expPost S q) c
  | .wait q m k => ∃ S, Γe q.1 = some S ∧
      ∀ ans, (ctxSpec Γi).post m ans → TSafe P (specHostT bind Γi) (expPost S q) (k ans)

/-- A good question starts a good run. -/
theorem tgood_start (hm : TModuleSat P M bind Γi Γe) {q : Nat × Store H × List Val}
    (hq : (ctxSpec Γe).pre q) : TGood P M bind Γi Γe (.run q ((modRed P M bind).start q)) := by
  obtain ⟨S, hS, hpre⟩ := hq
  exact ⟨S, hS, hm.2 q.1 S hS q.2.1 q.2.2 hpre {} [] _ trivial⟩

/-- Internal steps keep the invariant. -/
theorem tgood_tau {q : Nat × Store H × List Val} {c c' : Config H}
    (hx : TGood P M bind Γi Γe (.run q c)) (hs : (modRed P M bind).step (q := q) c c') :
    TGood P M bind Γi Γe (.run q c') := by
  obtain ⟨S, hS, h⟩ := hx
  exact ⟨S, hS, h.step_inv (Step.of_noHost _ hs.2)⟩

/-- A totally correct configuration at a host-call redex calls an import whose
precondition holds. -/
theorem timport_pre {Q : Post H} {c : Config H} {E : SingleThreaded.Ctx} {a : Nat}
    {h : H} {args : List Val} (hsafe : TSafe P (specHostT bind Γi) Q c)
    (hd : decompose? c.store c.code = some (E, a, h, args)) :
    ∃ S, Γi (bind h) = some S ∧ S.pre c.store args := by
  cases hsafe with
  | exit o hex _ => exact absurd hex (not_exits_of_redex P hd o)
  | step hp _ =>
    obtain ⟨c', hst⟩ := hp
    rcases redex_step_inv hd hst with ⟨s', r, ⟨S, hS, hpre, -⟩, -⟩ | ⟨⟨S, hS, hpre, -⟩, -⟩
    · exact ⟨S, hS, hpre⟩
    · exact ⟨S, hS, hpre⟩

/-- An import call of a good run meets the import precondition, and every answer
meeting the import postcondition resumes a good run. -/
theorem tgood_call {q : Nat × Store H × List Val} {c : Config H}
    {m : Nat × Store H × List Val} {k : Store H × Result → Config H}
    (hx : TGood P M bind Γi Γe (.run q c)) (hc : (modRed P M bind).call (q := q) c m k) :
    (ctxSpec Γi).pre m ∧ TGood P M bind Γi Γe (.wait q m k) := by
  obtain ⟨S, hS, h⟩ := hx
  obtain ⟨-, E, a, hh, args, hd, rfl, rfl⟩ := hc
  obtain ⟨Si, hSi, hpre⟩ : ∃ Si, Γi (bind hh) = some Si ∧ Si.pre c.store args := timport_pre h hd
  refine ⟨⟨Si, hSi, hpre⟩, S, hS, fun ans hpost => h.step_inv ?_⟩
  exact redex_step_ret hd ⟨Si, hSi, hpre, hpost Si hSi⟩

/-- The answer of a good run meets the export postcondition. -/
theorem tgood_done {q : Nat × Store H × List Val} {c : Config H} {r : Store H × Result}
    (hx : TGood P M bind Γi Γe (.run q c)) (hd : (modRed P M bind).done (q := q) c r) :
    (ctxSpec Γe).post q r := by
  obtain ⟨S, hS, h⟩ := hx
  obtain ⟨-, hs, hcode⟩ := hd
  intro S' hS'
  obtain rfl : S' = S := Option.some.inj (hS'.symm.trans hS)
  rcases c with ⟨s, f, code⟩
  have hc : (⟨s, f, code⟩ : Config H) = ⟨r.1, f, r.2.toAdmin⟩ := by
    rw [← hs, ← hcode]
  exact final_post (hc ▸ TSafe.safe h 1)

/-! ## Finite plays -/

/-- One visible move of a good state. -/
theorem tag_vis (hm : TModuleSat P M bind Γi Γe) {x y : (modRed P M bind).State}
    {o : Move (WCall H) (WCall H)} {p : List (Move (WCall H) (WCall H))}
    (hs : (modRed P M bind).toLTS.step x (some o) y) (hx : TGood P M bind Γi Γe x)
    (ih : TGood P M bind Γi Γe y → AG (ctxSpec Γi) (ctxSpec Γe) p) :
    AG (ctxSpec Γi) (ctxSpec Γe) (o :: p) := by
  cases hs with
  | ask q => exact ⟨fun _ hg => ih (tgood_start hm hg), fun h => h.elim⟩
  | call hc => exact ⟨fun h => h.elim, fun _ => ⟨(tgood_call hx hc).1, ih (tgood_call hx hc).2⟩⟩
  | resume q m k n =>
    exact ⟨fun _ hg => ih (by obtain ⟨S, hS, h⟩ := hx; exact ⟨S, hS, h n hg⟩), fun h => h.elim⟩
  | ret hd => exact ⟨fun h => h.elim, fun _ => ⟨tgood_done hx hd, ih trivial⟩⟩

/-- Silent moves keep the invariant. -/
theorem tgood_silent {x y : (modRed P M bind).State} (hs : (modRed P M bind).toLTS.step x none y)
    (hx : TGood P M bind Γi Γe x) : TGood P M bind Γi Γe y := by
  cases hs with
  | tau h => exact tgood_tau hx h

/-- Every run from a good state is assume/guarantee correct. -/
theorem trun_ag (hm : TModuleSat P M bind Γi Γe) {x y : (modRed P M bind).toLTS.State}
    {p : List (Move (WCall H) (WCall H))} (hr : (modRed P M bind).toLTS.Run x p y) :
    TGood P M bind Γi Γe x → AG (ctxSpec Γi) (ctxSpec Γe) p := by
  induction hr with
  | nil => exact fun _ => trivial
  | tau hs _ ih => exact fun hx => ih (tgood_silent hs hx)
  | vis hs _ ih => exact fun hx => tag_vis hm hs hx ih

/-! ## Divergence -/

/-- One visible move with a good Opponent move keeps the invariant. -/
theorem tgood_vis (hm : TModuleSat P M bind Γi Γe) {x y : (modRed P M bind).State}
    {o : Move (WCall H) (WCall H)} (hs : (modRed P M bind).toLTS.step x (some o) y)
    (hx : TGood P M bind Γi Γe x) (ho : Move.IsO o → MoveGood (ctxSpec Γi) (ctxSpec Γe) o) :
    TGood P M bind Γi Γe y := by
  cases hs with
  | ask q => exact tgood_start hm (ho trivial)
  | call hc => exact (tgood_call hx hc).2
  | resume q m k n => obtain ⟨S, hS, h⟩ := hx; exact ⟨S, hS, h n (ho trivial)⟩
  | ret hd => trivial

/-- After a run whose Opponent moves are good, the invariant holds. -/
theorem run_tgood (hm : TModuleSat P M bind Γi Γe) {x y : (modRed P M bind).toLTS.State}
    {p : List (Move (WCall H) (WCall H))} (hr : (modRed P M bind).toLTS.Run x p y) :
    TGood P M bind Γi Γe x → OppGood (ctxSpec Γi) (ctxSpec Γe) p → TGood P M bind Γi Γe y := by
  induction hr with
  | nil => exact fun hx _ => hx
  | tau hs _ ih => exact fun hx hp => ih (tgood_silent hs hx) hp
  | vis hs _ ih =>
    exact fun hx hp => ih (tgood_vis hm hs hx (hp _ (List.mem_cons_self ..)))
      (fun m hm' => hp m (List.mem_cons_of_mem _ hm'))

/-- A silent infinite run of the module from a running state is an infinite run
of the closed-world semantics, under any host relation. -/
theorem diverges_of_silent {host : HostSemantics H} {q : Nat × Store H × List Val} {c : Config H}
    (hd : (modRed P M bind).toLTS.Diverges (.run q c)) : Diverges P host c := by
  refine Silmaril.InfiniteTrace.coinduct (fun c => (modRed P M bind).toLTS.Diverges (.run q c))
    (fun c hc => ?_) hd
  obtain ⟨y, hs, hy⟩ := Silmaril.InfiniteTrace.unfold hc
  cases hs with
  | tau h => exact ⟨_, Step.of_noHost host h.2, hy⟩

/-- No silent infinite run from a state of the invariant. -/
theorem tgood_not_diverges {x : (modRed P M bind).State} (hx : TGood P M bind Γi Γe x) :
    ¬ (modRed P M bind).toLTS.Diverges x := by
  intro hd
  cases x with
  | idle =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    cases hs
  | run q c =>
    obtain ⟨S, -, h⟩ := hx
    exact TSafe.not_diverges h (diverges_of_silent hd)
  | wait q m k =>
    obtain ⟨y, hs, -⟩ := Silmaril.InfiniteTrace.unfold hd
    cases hs

/-- **No divergence after good Opponent behaviour.** -/
theorem dmodStrat_div (hm : TModuleSat P M bind Γi Γe) {p : List (Move (WCall H) (WCall H))}
    (hp : p ∈ (dmodStrat P M bind).div) : ¬ OppGood (ctxSpec Γi) (ctxSpec Γe) p := by
  intro hg
  obtain ⟨⟨y, hr, hd⟩, -⟩ := hp
  exact tgood_not_diverges (run_tgood hm hr trivial hg) hd

/-- **The divergence-aware game link.** A module meeting its export
specifications totally under its import specifications has a
divergence-observing strategy refining the divergence-aware assume/guarantee
strategy: its finite plays are assume/guarantee correct, it diverges only after
Opponent broke the specifications, and its infinite plays are plays. -/
theorem dmodStrat_sound (hm : TModuleSat P M bind Γi Γe) :
    dmodStrat P M bind ≤ dagStrat (ctxSpec Γi) (ctxSpec Γe) := by
  have hfin : (dmodStrat P M bind).toStrategy ≤ agStrat (ctxSpec Γi) (ctxSpec Γe) :=
    Strategy.generate_le fun _ ⟨_, hr⟩ hl => ⟨hl, trun_ag hm hr trivial⟩
  refine ⟨hfin, fun p hp => ⟨hfin ((dmodStrat P M bind).div_mem hp),
    (dmodStrat P M bind).div_run hp, dmodStrat_div hm hp⟩, fun J hJ => ?_⟩
  exact ⟨(dmodStrat P M bind).inf_isInf hJ, fun s hs => hfin ((dmodStrat P M bind).inf_sub hJ hs)⟩

end Silmaril.Wasm.Logic.OpenTotal
