module

public import Silmaril.Proofs.Wasm.Logic.Open.Stub
public import Silmaril.Wasm.Logic.Strategy.Thms

/-!
# Open modules: the strategy refines the specification strategy

`modStrat_sound`: if an open module meets its export specifications `Γe` under
its import specifications `Γi` (`ModuleSat`), every play of its strategy is
assume/guarantee correct: as long as Opponent asks export questions meeting their
preconditions and answers import calls with results meeting the import
postconditions, the module calls its imports only with arguments meeting their
preconditions and answers with results meeting the export postconditions.

The proof is an induction on the runs of the reduction semantics `modRed` with
the invariant `Good`: while a good question `q` is being answered, the current
configuration is safe for every number of steps under the most general
environment `specHost bind Γi`, for the postcondition of the export of `q`.

* a question: the invariant holds at `$invoke` (`ModuleSat`);
* an internal step: a host-free step is a step under `specHost` (`Safe.step_inv`);
* an import call: the configuration is at a host-call redex; it is not an exit
  (`not_exits_of_redex`), so it steps, and the only steps of a redex are host
  calls, so `specHost` has an outcome there: the precondition holds; every answer
  meeting the postcondition is a `specHost` outcome, so the resumed configuration
  is a successor and is safe;
* an answer: the configuration is final (values, a bare exception or a trap),
  so it cannot step and has exited with an outcome meeting the postcondition.

`link_refines`: with `Silmaril.Wasm.Logic.Strategy.comp_refines`, linked modules
meet the composed specification. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Open

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (WCall resultOutcome ctxSpec ISpec agStrat AG comp_refines)

variable {H : Type} {P : Profile} {M : OMod H} {bind : H → Nat} {Γi Γe : Ctx H}

/-- The postcondition of a run answering the question `q` for the export
specification `S`. -/
abbrev expPost (S : FSpec H) (q : Nat × Store H × List Val) : Post H :=
  callPost {} [] (S.post q.2.1 q.2.2)

/-- **The invariant** of the runs of an open module. -/
def Good (P : Profile) (M : OMod H) (bind : H → Nat) (Γi Γe : Ctx H) :
    (modRed P M bind).State → Prop
  | .idle => True
  | .run q c => ∃ S, Γe q.1 = some S ∧ ∀ n, Safe P (specHost bind Γi) (expPost S q) n c
  | .wait q m k => ∃ S, Γe q.1 = some S ∧
      ∀ ans, (ctxSpec Γi).post m ans → ∀ n, Safe P (specHost bind Γi) (expPost S q) n (k ans)

/-- A good question starts a good run. -/
theorem good_start (hm : ModuleSat P M bind Γi Γe) {q : Nat × Store H × List Val}
    (hq : (ctxSpec Γe).pre q) : Good P M bind Γi Γe (.run q ((modRed P M bind).start q)) := by
  obtain ⟨S, hS, hpre⟩ := hq
  exact ⟨S, hS, fun n => hm.2 n q.1 S hS q.2.1 q.2.2 hpre {} [] _ trivial⟩

/-- Internal steps keep the invariant. -/
theorem good_tau {q : Nat × Store H × List Val} {c c' : Config H}
    (hx : Good P M bind Γi Γe (.run q c)) (hs : (modRed P M bind).step (q := q) c c') :
    Good P M bind Γi Γe (.run q c') := by
  obtain ⟨S, hS, h⟩ := hx
  exact ⟨S, hS, fun n => (h (n + 1)).step_inv (Step.of_noHost _ hs.2)⟩

/-- A safe configuration at a host-call redex calls an import whose precondition
holds. -/
theorem import_pre {Q : Post H} {n : Nat} {c : Config H} {E : SingleThreaded.Ctx} {a : Nat}
    {h : H} {args : List Val} (hsafe : Safe P (specHost bind Γi) Q (n + 1) c)
    (hd : decompose? c.store c.code = some (E, a, h, args)) :
    ∃ S, Γi (bind h) = some S ∧ S.pre c.store args := by
  rcases hsafe with ⟨o, hex, -⟩ | ⟨⟨c', hst⟩, -⟩
  · exact absurd hex (not_exits_of_redex P hd o)
  · rcases redex_step_inv hd hst with ⟨s', r, ⟨S, hS, hpre, -⟩, -⟩ | ⟨⟨S, hS, hpre, -⟩, -⟩
    · exact ⟨S, hS, hpre⟩
    · exact ⟨S, hS, hpre⟩

/-- An import call of a good run meets the import precondition, and every answer
meeting the import postcondition resumes a good run. -/
theorem good_call {q : Nat × Store H × List Val} {c : Config H}
    {m : Nat × Store H × List Val} {k : Store H × Result → Config H}
    (hx : Good P M bind Γi Γe (.run q c)) (hc : (modRed P M bind).call (q := q) c m k) :
    (ctxSpec Γi).pre m ∧ Good P M bind Γi Γe (.wait q m k) := by
  obtain ⟨S, hS, h⟩ := hx
  obtain ⟨-, E, a, hh, args, hd, rfl, rfl⟩ := hc
  obtain ⟨Si, hSi, hpre⟩ : ∃ Si, Γi (bind hh) = some Si ∧ Si.pre c.store args := import_pre (h 1) hd
  refine ⟨⟨Si, hSi, hpre⟩, S, hS, fun ans hpost n => (h (n + 1)).step_inv ?_⟩
  exact redex_step_ret hd ⟨Si, hSi, hpre, hpost Si hSi⟩

/-- A final configuration that is safe meets the call postcondition. -/
theorem final_post {host : HostSemantics H} {R : Store H → Outcome → Prop} {n : Nat}
    {s : Store H} {f : Frame} {r : Result}
    (h : Safe P host (callPost {} [] R) (n + 1) ⟨s, f, r.toAdmin⟩) : R s (resultOutcome r) := by
  rcases r with vs | a | _
  · obtain ⟨o, he, -, hq⟩ := h.exit_of_stuck fun _ => not_step_vals
    have ho : o = .normal vs := exits_vals_inv he
    subst ho
    rcases hq with ⟨res, ho, hR⟩ | ⟨ho, -⟩ | ⟨_, ho, -⟩ <;> cases ho
    simpa [resultOutcome] using hR
  · obtain ⟨o, he, -, hq⟩ := h.exit_of_stuck fun _ => not_step_throwing
    have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa [Result.toAdmin, throwing] using he)
    subst ho
    rcases hq with ⟨res, ho, -⟩ | ⟨ho, -⟩ | ⟨_, ho, hR⟩ <;> cases ho
    exact hR
  · obtain ⟨o, he, -, hq⟩ := h.exit_of_stuck fun _ => not_step_trap
    have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) (by simpa [Result.toAdmin] using he)
    subst ho
    rcases hq with ⟨res, ho, -⟩ | ⟨-, hR⟩ | ⟨_, ho, -⟩ <;> first | cases ho | exact hR

/-- The answer of a good run meets the export postcondition. -/
theorem good_done {q : Nat × Store H × List Val} {c : Config H} {r : Store H × Result}
    (hx : Good P M bind Γi Γe (.run q c)) (hd : (modRed P M bind).done (q := q) c r) :
    (ctxSpec Γe).post q r := by
  obtain ⟨S, hS, h⟩ := hx
  obtain ⟨-, hs, hcode⟩ := hd
  intro S' hS'
  obtain rfl : S' = S := Option.some.inj (hS'.symm.trans hS)
  rcases c with ⟨s, f, code⟩
  have hc : (⟨s, f, code⟩ : Config H) = ⟨r.1, f, r.2.toAdmin⟩ := by
    rw [← hs, ← hcode]
  exact final_post (hc ▸ h 1)

/-- One visible move of a good state. -/
theorem ag_vis (hm : ModuleSat P M bind Γi Γe) {x y : (modRed P M bind).State}
    {o : Move (WCall H) (WCall H)} {p : List (Move (WCall H) (WCall H))}
    (hs : (modRed P M bind).toLTS.step x (some o) y) (hx : Good P M bind Γi Γe x)
    (ih : Good P M bind Γi Γe y → AG (ctxSpec Γi) (ctxSpec Γe) p) :
    AG (ctxSpec Γi) (ctxSpec Γe) (o :: p) := by
  cases hs with
  | ask q => exact ⟨fun _ hg => ih (good_start hm hg), fun h => h.elim⟩
  | call hc => exact ⟨fun h => h.elim, fun _ => ⟨(good_call hx hc).1, ih (good_call hx hc).2⟩⟩
  | resume q m k n =>
    exact ⟨fun _ hg => ih (by obtain ⟨S, hS, h⟩ := hx; exact ⟨S, hS, h n hg⟩), fun h => h.elim⟩
  | ret hd => exact ⟨fun h => h.elim, fun _ => ⟨good_done hx hd, ih trivial⟩⟩

/-- Silent moves keep the invariant. -/
theorem good_silent {x y : (modRed P M bind).State} (hs : (modRed P M bind).toLTS.step x none y)
    (hx : Good P M bind Γi Γe x) : Good P M bind Γi Γe y := by
  cases hs with
  | tau h => exact good_tau hx h

/-- Every run from a good state is assume/guarantee correct. -/
theorem run_ag (hm : ModuleSat P M bind Γi Γe) {x y : (modRed P M bind).toLTS.State}
    {p : List (Move (WCall H) (WCall H))} (hr : (modRed P M bind).toLTS.Run x p y) :
    Good P M bind Γi Γe x → AG (ctxSpec Γi) (ctxSpec Γe) p := by
  induction hr with
  | nil => exact fun _ => trivial
  | tau hs _ ih => exact fun hx => ih (good_silent hs hx)
  | vis hs _ ih => exact fun hx => ag_vis hm hs hx ih

/-- **The game link.** An open module meeting its export specifications under its
import specifications has a strategy refining their assume/guarantee strategy. -/
theorem modStrat_sound (hm : ModuleSat P M bind Γi Γe) :
    modStrat P M bind ≤ agStrat (ctxSpec Γi) (ctxSpec Γe) :=
  Strategy.generate_le fun _ ⟨_, hr⟩ hl => ⟨hl, run_ag hm hr trivial⟩

/-- **Linked modules meet the composed specification.** If `M₁` meets `Γm` under
`Γi` and `M₂` meets `Γe` under `Γm`, the composition of their strategies (the
calls of `M₂` to its imports answered by `M₁`, those of `M₁` by the environment)
refines the assume/guarantee strategy of `Γi` and `Γe`. -/
theorem link_refines {M₁ M₂ : OMod H} {bind₁ bind₂ : H → Nat} {Γm : Ctx H}
    (h₁ : ModuleSat P M₁ bind₁ Γi Γm) (h₂ : ModuleSat P M₂ bind₂ Γm Γe) :
    (modStrat P M₁ bind₁).comp (modStrat P M₂ bind₂) ≤ agStrat (ctxSpec Γi) (ctxSpec Γe) :=
  comp_refines (modStrat_sound h₁) (modStrat_sound h₂)

end Silmaril.Wasm.Logic.Open
