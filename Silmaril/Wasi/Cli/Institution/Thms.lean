module

public import Silmaril.Wasi.Cli.Institution.Defs
public import Silmaril.Wasi.Cli.Thms
public import Silmaril.Cli.Institution.Thms

/-!
# A component that meets `CliSat` is a model of the CLI institution

PROVED (standard axioms):

* `View.seen_eq` (an ended trace is seen as its reading);
* **`cliSat_sat`**: `CliSat σ T V S` makes `wasiModel σ T V` a model of `S` read on partial
  observations (`fun i o => S.Partial i o.seen`);
* `cliSat_outOnly`: a model of `S` itself when `S` reads only stdout, stderr, exit code and
  files (`Spec.OutOnly`);
* `lift_outOnly`, `liftAll_outOnly`: sentences lifted from a level up to `L2` read only those;
* **`cliSat_lift`**, `cliSat_liftAll`, `cliSat_reduct`: for an `L`-sentence `φ` with `L ≤ L2`,
  `CliSat σ T V (Level.lift φ)` makes `wasiModel σ T V` a model of `Level.lift φ`, and its `L`
  reduct a model of `φ`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Cli.Institution (Level Model Sen)
open Silmaril.Wasm.Resource (Protocol)

variable {W : World} {St : Type}

theorem View.seen_eq {V : View} {i : Input} {t : List WEv} (hc : (V.code t).isSome) :
    V.seen i t = (V.obs i t).seen := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
  simp [View.seen, View.obs, Obs.seen, hc]

/-- **`CliSat` is satisfaction on partial observations.** -/
theorem cliSat_sat {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {S : Spec}
    (h : CliSat σ T V S) : (wasiModel σ T V).Sat (fun i o => S.Partial i o.seen) := by
  rintro i o ⟨s, hs, hA, hn, hc, rfl⟩
  have e : V.seen i (wtrace s) = (V.obs i (wtrace s)).seen := View.seen_eq hc
  exact e ▸ h i s hs hA hn

/-- On a complete observation, a partial view of an allowed observation is allowed, for a spec
that reads only stdout, stderr, the exit code and the files. -/
theorem Spec.OutOnly.of_partial {S : Spec} (hS : S.OutOnly) {i : Input} {o : Obs}
    (h : S.Partial i o.seen) : S i o := by
  obtain ⟨o', hS', -, -, -, -, -, hend⟩ := h
  obtain ⟨he, h1, h2, h3⟩ := hend o.exit rfl
  exact hS i o o' h1 h2 he (h3 o.fs rfl) hS'

theorem cliSat_outOnly {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {S : Spec}
    (h : CliSat σ T V S) (hS : S.OutOnly) : (wasiModel σ T V).Sat S :=
  fun i o hr => Spec.OutOnly.of_partial hS (cliSat_sat h i o hr)

/-- Up to `L2`, a level sees only stdout, stderr and the exit code. -/
theorem outProj_eq {L : Level} (hL : L ≤ .command) {o o' : Obs} (h1 : o.stdout = o'.stdout)
    (h2 : o.stderr = o'.stderr) (he : o.exit = o'.exit) : L.outProj o = L.outProj o' := by
  cases L
  · exact he
  · show (⟨o.stdout, o.exit⟩ : Silmaril.Cli.Institution.Out1) = ⟨o'.stdout, o'.exit⟩; rw [h1, he]
  · show (⟨o.stdout, o.stderr, o.exit⟩ : Spec.Out) = ⟨o'.stdout, o'.stderr, o'.exit⟩
    rw [h1, h2, he]
  · exact absurd (Level.le_iff_rank.mp hL) (by simp [Level.rank])

theorem lift_outOnly {L : Level} (hL : L ≤ .command) (φ : Sen L.sig) :
    (Level.lift φ).OutOnly := by
  intro i o o' h1 h2 he _ H a ha
  have := H a ha
  show φ a (L.outProj o)
  rwa [outProj_eq hL h1 h2 he]

theorem liftAll_outOnly {L : Level} (hL : L ≤ .command) (φ : Sen L.sig) :
    (Level.liftAll φ).OutOnly := by
  intro i o o' h1 h2 he _ H
  rw [Level.liftAll_iff] at H ⊢
  rwa [outProj_eq hL h1 h2 he]

/-- **A component meeting the lift of an `L`-sentence (`L ≤ L2`) is a model of it.** -/
theorem cliSat_lift {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {L : Level}
    (hL : L ≤ .command) {φ : Sen L.sig} (h : CliSat σ T V (Level.lift φ)) :
    (wasiModel σ T V).Sat (Level.lift φ) :=
  cliSat_outOnly h (lift_outOnly hL φ)

theorem cliSat_liftAll {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {L : Level}
    (hL : L ≤ .command) {φ : Sen L.sig} (h : CliSat σ T V (Level.liftAll φ)) :
    (wasiModel σ T V).Sat (Level.liftAll φ) :=
  cliSat_outOnly h (liftAll_outOnly hL φ)

/-- **Its `L` reduct satisfies the sentence.** -/
theorem cliSat_reduct {σ : W.Model} {T : Input → Protocol St WEv} {V : View} {L : Level}
    (hL : L ≤ .command) {φ : Sen L.sig} (h : CliSat σ T V (Level.lift φ)) :
    (L.reduct (wasiModel σ T V)).Sat φ :=
  (Level.sat_lift_iff _ φ).mp (cliSat_lift hL h)

end Silmaril.Wasi.Cli
