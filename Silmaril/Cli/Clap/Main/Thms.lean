module

public import Silmaril.Cli.Clap.Main.Defs
public import Silmaril.Cli.Front.Thms

/-!
# Programs behind a clap front end: theorems

PROVED (standard axioms):

* `Tool.modelMain_apply`, `Tool.finish_beh`: what the model of `Tool.main` does;
* **`Tool.main_refines`**: `Tool.main`, read in the behaviour model (`Tool.modelMain`), refines
  `Tool.spec t S` whenever the program it runs on each `Matches` refines `S m`;
  `Tool.main_refines_front`: every program behind the clap front end refines
  `Tool.frontSpec t`;
* **`Tool.frontCheck_sound`**: the harness check `Tool.frontCheck` is sound for
  `Tool.frontSpec`;
* `Tool.spec_usageError`: with usage exit 2, the usage errors of `Tool.spec` refine the loose
  `Spec.usageError` (exit 2, nothing on stdout, no file changed or read, no stdin consumed);
* `Tool.spec_mono`: refining the runs refines the tool;
* `Tool.helpOr_help`: a tool that takes only its help from the grammar (`Tool.helpOr`)
  meets `Tool.spec` on every invocation that asks for help.

As for `Command.main` (`Silmaril.Cli.Front`), the `IO` host reading each host operation as
`Beh.host` does is the trusted step.
-/

@[expose] public section

namespace Silmaril.Cli.Clap

open Silmaril.Cli

theorem Tool.main_eq (t : Tool) (run : Matches → IO UInt32) :
    t.main run = t.mainWith Host.io run := rfl

/-- The model of the clap front end decides its outcome on the declared environment. -/
theorem Tool.modelMain_apply {t : Tool} {run : Matches → Beh UInt32} {i : Input}
    {code : UInt32} {o : Obs} :
    t.modelMain run i code o ↔ t.finish Beh.host i.args run (t.outcome i) i code o := by
  show (Beh.getEnvs t.grammar.envVars >>= fun env =>
      t.finish Beh.host i.args run (t.read env i.args)) i code o ↔ _
  rw [Beh.getEnvs_bind]
  rfl

/-- Help, version and usage errors print their text and return their code. -/
theorem Tool.finish_beh {t : Tool} {argv : List String} {run : Matches → Beh UInt32}
    {out : Outcome} (hout : out.runs = false) {i : Input} {code : UInt32} {o : Obs} :
    t.finish Beh.host argv run out i code o ↔
      code = ((out.exit t).getD 0).toUInt32 ∧ o = Beh.lineObs i (t.text argv out) := by
  cases out with
  | run fs m => cases hout
  | undecided fs m w => cases hout
  | help p => exact Beh.emit_pure
  | version => exact Beh.emit_pure
  | needCommand p => exact Beh.emit_pure
  | error msg => exact Beh.emit_pure

/-- The non-running outcomes of the model show `frontObs`. -/
theorem Tool.modelMain_front {t : Tool} {run : Matches → Beh UInt32} {i : Input}
    (hr : (t.outcome i).runs = false) {code : UInt32} {o : Obs} (h : t.modelMain run i code o) :
    { o with exit := code.toUInt8 } = t.frontObs i (t.outcome i) := by
  rw [Tool.modelMain_apply] at h
  obtain ⟨rfl, rfl⟩ := (Tool.finish_beh hr).mp h
  rfl

/-- **`Tool.main` refines the clap front end's specification**: read in the behaviour model,
the program behind the clap front end refines `Tool.spec t S` whenever the program it runs on
each `Matches` refines `S m`. -/
theorem Tool.main_refines (t : Tool) {run : Matches → Beh UInt32} {S : Matches → Spec}
    (h : ∀ m, Beh.toSpec (run m) ≤ S m) : Beh.toSpec (t.modelMain run) ≤ t.spec S := by
  intro i o ⟨code, o', hrun, ho⟩
  unfold Tool.spec
  have hfront : (t.outcome i).runs = false → o = t.frontObs i (t.outcome i) := fun hr =>
    ho.trans (Tool.modelMain_front hr hrun)
  rw [Tool.modelMain_apply] at hrun
  split
  · next fs m hout =>
    rw [hout] at hrun
    exact h m i o ⟨code, o', hrun, ho⟩
  · next fs m w hout =>
    rw [hout] at hrun
    exact Or.inl (h m i o ⟨code, o', hrun, ho⟩)
  · next out hr1 hr2 =>
    have hr : (t.outcome i).runs = false := by
      cases hc : t.outcome i with
      | run fs m => exact absurd hc (hr1 fs m)
      | undecided fs m w => exact absurd hc (hr2 fs m w)
      | _ => rfl
    exact hfront hr

/-- **Every program behind the clap front end refines the front end's specification.** -/
theorem Tool.main_refines_front (t : Tool) (run : Matches → Beh UInt32) :
    Beh.toSpec (t.modelMain run) ≤ t.frontSpec :=
  t.main_refines fun _ _ _ _ => trivial

/-- Refining the runs refines the tool. -/
theorem Tool.spec_mono (t : Tool) {S T : Matches → Spec} (h : ∀ m, S m ≤ T m) :
    t.spec S ≤ t.spec T := by
  intro i o hs
  unfold Tool.spec at hs ⊢
  cases hout : t.outcome i <;> rw [hout] at hs
  case run fs m => exact h m i o hs
  case undecided fs m w => exact hs.imp (h m i o) id
  all_goals exact hs

/-- A check that passes on a non-running outcome shows `frontObs`. -/
theorem Tool.frontCheck_shows {t : Tool} {i : Input} {s : Io.Snap} (hr : (t.outcome i).runs = false)
    (hs : t.frontCheck i s = true) : s.Agrees i (t.frontObs i (t.outcome i)) := by
  have hc : s.stdout = (t.frontObs i (t.outcome i)).stdout ∧
      s.stderr = (t.frontObs i (t.outcome i)).stderr ∧
      s.exit = (t.frontObs i (t.outcome i)).exit ∧ s.files = [] := by
    simpa [Tool.frontCheck, hr, and_assoc] using hs
  have hfs : (t.frontObs i (t.outcome i)).fs = s.fs i := by
    funext q
    simp [Io.Snap.fs, hc.2.2.2, Tool.frontObs, lineObs_fs]
  exact ⟨hc.1.symm, hc.2.1.symm, hc.2.2.1.symm, hfs⟩

set_option linter.unusedTactic false in
/-- `frontSpec` allows `frontObs` on a non-running outcome. -/
theorem Tool.frontSpec_front {t : Tool} {i : Input} (hr : (t.outcome i).runs = false) :
    t.frontSpec i (t.frontObs i (t.outcome i)) := by
  unfold Tool.frontSpec Tool.spec
  cases hout : t.outcome i <;> rw [hout] at hr <;> first | rfl | cases hr

/-- `frontSpec` allows anything on a running outcome. -/
theorem Tool.frontSpec_runs {t : Tool} {i : Input} (hr : (t.outcome i).runs = true) (o : Obs) :
    t.frontSpec i o := by
  unfold Tool.frontSpec Tool.spec
  cases hout : t.outcome i <;> rw [hout] at hr <;> first | exact True.intro | exact Or.inl True.intro | cases hr

/-- **The front-end check is sound for the front-end specification.** -/
theorem Tool.frontCheck_sound (t : Tool) : t.frontCheck.Sound t.frontSpec := by
  intro i s hs
  cases hr : (t.outcome i).runs
  · exact ⟨_, Tool.frontCheck_shows hr hs, Tool.frontSpec_front hr⟩
  · exact ⟨{ stdout := s.stdout, stderr := s.stderr, exit := s.exit, fs := s.fs i },
      ⟨rfl, rfl, rfl, rfl⟩, Tool.frontSpec_runs hr _⟩

/-- **`helpOr` meets the specification on help**: on an invocation the reading answers with
help, whatever the program `other` does elsewhere, `Tool.helpOr` shows exactly the derived
help and exits 0, as `Tool.spec t S` requires. -/
theorem Tool.helpOr_help (t : Tool) (other : List String → Beh UInt32) (S : Matches → Spec)
    {i : Input} {p : List String} (hp : t.outcome i = .help p) {o : Obs}
    (h : Beh.toSpec (Beh.withArgs (t.helpOr Beh.host other)) i o) : t.spec S i o := by
  obtain ⟨code, o', hrun, rfl⟩ := h
  have hr : (Beh.getEnvs t.grammar.envVars >>= fun env =>
      match t.read env i.args with
      | .help p => Beh.host.emit (t.text i.args (.help p)) >>= fun _ => (pure 0 : Beh UInt32)
      | _ => other i.args) i code o' := hrun
  rw [Beh.getEnvs_bind] at hr
  have hp' : t.read (Beh.envOf t.grammar.envVars i) i.args = .help p := hp
  rw [hp'] at hr
  obtain ⟨rfl, rfl⟩ := Beh.emit_pure.mp hr
  unfold Tool.spec
  rw [hp]
  rfl

/-- **Usage errors refine the loose `Spec.usageError`** when the tool's usage exit is 2. -/
theorem Tool.spec_usageError {t : Tool} (h2 : t.usageExit = 2) {S : Matches → Spec} {i : Input}
    {o : Obs} (herr : (∃ msg, t.outcome i = .error msg) ∨ ∃ p, t.outcome i = .needCommand p)
    (hs : t.spec S i o) : Spec.usageError i o := by
  unfold Tool.spec at hs
  rcases herr with ⟨msg, h⟩ | ⟨p, h⟩ <;> rw [h] at hs <;> subst hs <;>
    exact ⟨by simp [Tool.frontObs, Outcome.exit, h2], rfl, rfl, rfl, rfl⟩

end Silmaril.Cli.Clap
