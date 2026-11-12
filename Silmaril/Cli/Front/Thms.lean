module

public import Silmaril.Cli.Front.Defs
public import Silmaril.Cli.Args.Thms

@[expose] public section

/-!
# The derived front end as a behaviour specification: theorems

PROVED (standard axioms), namespace `Silmaril.Cli`:

* the monad laws the proofs use, on observations: `Input.after_skip`, `Obs.skip_andThen`,
  `Beh.getEnvs_bind`, `Beh.emit_pure`; `Beh.toSpec_ofSpec` (a spec read as a main program and
  back is itself);
* `Command.modelMain_apply`, `Command.finish_beh`: what the model of `Command.main` does;
* **`main_refines`**: `Command.main`, read in the behaviour model (`Command.modelMain`),
  refines `Command.spec c S` whenever the program it runs on each `Matches` refines `S m`;
  **`spec_eq_modelMain`**: `Command.spec c S` is exactly the model of the front end running the
  specs `S m`;
* `spec_usageError`, `spec_inf_usageErr_le`: every usage-error outcome refines the loose
  `Spec.usageError` (exit 2, no stdout, no file changed or read, no stdin consumed);
  `spec_of_help`, `spec_of_version`, `spec_of_error`, `spec_of_run`: the four outcomes.
-/

namespace Silmaril.Cli

theorem Input.after_skip (i : Input) : i.after (Obs.skip i) = i := by
  cases i; simp [Input.after, Obs.skip]

theorem Obs.skip_andThen (i : Input) (o : Obs) : (Obs.skip i).andThen o = o := by
  cases o; simp [Obs.andThen, Obs.skip]

theorem Beh.bind_apply {α β : Type} {p : Beh α} {f : α → Beh β} {i : Input} {b : β} {o : Obs} :
    (p >>= f) i b o ↔ ∃ a o₁ o₂, p i a o₁ ∧ f a (i.after o₁) b o₂ ∧ o = o₁.andThen o₂ :=
  Iff.rfl

theorem Beh.pure_apply {α : Type} {a b : α} {i : Input} {o : Obs} :
    (pure a : Beh α) i b o ↔ b = a ∧ o = Obs.skip i :=
  Iff.rfl

/-- Reading the environment changes nothing. -/
theorem Beh.getEnvs_bind {β : Type} {vs : List String} {f : (String → Option String) → Beh β}
    {i : Input} {b : β} {o : Obs} :
    (Beh.getEnvs vs >>= f) i b o ↔ f (Beh.envOf vs i) i b o := by
  rw [Beh.bind_apply]
  constructor
  · rintro ⟨a, o₁, o₂, ⟨rfl, rfl⟩, h, rfl⟩
    rw [Input.after_skip] at h
    rw [Obs.skip_andThen]
    exact h
  · intro h
    exact ⟨_, _, o, ⟨rfl, rfl⟩, by rw [Input.after_skip]; exact h, (Obs.skip_andThen i o).symm⟩

theorem lineObs_fs (i : Input) (t : Option (Channel × String)) : (Beh.lineObs i t).fs = i.fs := by
  match t with
  | some (.stdout, _) => rfl
  | some (.stderr, _) => rfl
  | none => rfl

theorem lineObs_andThen_skip (i : Input) (t : Option (Channel × String)) :
    (Beh.lineObs i t).andThen (Obs.skip (i.after (Beh.lineObs i t))) = Beh.lineObs i t := by
  match t with
  | some (.stdout, _) => simp [Beh.lineObs, Obs.andThen, Obs.skip, Input.after]
  | some (.stderr, _) => simp [Beh.lineObs, Obs.andThen, Obs.skip, Input.after]
  | none => simp [Beh.lineObs, Obs.andThen, Obs.skip, Input.after]

theorem Beh.emit_apply {t : Option (Channel × String)} {i : Input} {u : Unit} {o : Obs} :
    Beh.host.emit t i u o ↔ o = Beh.lineObs i t := by
  match t with
  | some (ch, s) => exact Iff.rfl
  | none => simp [Host.emit, Beh.pure_apply, Beh.lineObs]

/-- Printing the front end's text, then returning a code. -/
theorem Beh.emit_pure {t : Option (Channel × String)} {x : UInt32} {i : Input} {b : UInt32}
    {o : Obs} :
    (Beh.host.emit t >>= fun _ => (pure x : Beh UInt32)) i b o ↔
      b = x ∧ o = Beh.lineObs i t := by
  rw [Beh.bind_apply]
  constructor
  · rintro ⟨u, o₁, o₂, h₁, ⟨rfl, rfl⟩, rfl⟩
    rw [Beh.emit_apply] at h₁
    subst h₁
    exact ⟨rfl, lineObs_andThen_skip i t⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(), Beh.lineObs i t, _, Beh.emit_apply.mpr rfl, ⟨rfl, rfl⟩,
      (lineObs_andThen_skip i t).symm⟩

/-- A spec read as a main program and back is itself. -/
theorem Beh.toSpec_ofSpec (S : Spec) : Beh.toSpec (Beh.ofSpec S) = S := by
  funext i o
  apply propext
  constructor
  · rintro ⟨c, o', ⟨hS, rfl⟩, rfl⟩
    have ho : { o' with exit := o'.exit.toUInt32.toUInt8 } = o' := by cases o'; simp
    rw [ho]; exact hS
  · intro hS
    exact ⟨o.exit.toUInt32, o, ⟨hS, rfl⟩, by cases o; simp⟩

/-! ## The model of `Command.main` -/

/-- `Command.main` is `Command.mainWith` on the `IO` host. -/
theorem Command.main_eq (c : Command) (run : Matches → IO UInt32) :
    c.main run = c.mainWith Host.io run := rfl

/-- The model of the front end decides its outcome on the declared environment. -/
theorem Command.modelMain_apply {c : Command} {run : Matches → Beh UInt32} {i : Input}
    {code : UInt32} {o : Obs} :
    c.modelMain run i code o ↔ c.finish Beh.host run (c.outcome i) i code o := by
  show (Beh.getEnvs c.envVars >>= fun env => c.finish Beh.host run (interpret c env i.args))
    i code o ↔ _
  rw [Beh.getEnvs_bind]
  rfl

/-- Help, version and usage errors print their text and return their code. -/
theorem Command.finish_beh {c : Command} {run : Matches → Beh UInt32} {out : Outcome}
    (hout : ∀ m, out ≠ .run m) {i : Input} {code : UInt32} {o : Obs} :
    c.finish Beh.host run out i code o ↔
      code = (out.exitCode?.getD 0).toUInt32 ∧ o = Beh.lineObs i (out.text c) := by
  cases out with
  | run m => exact absurd rfl (hout m)
  | help p => exact Beh.emit_pure
  | version v => exact Beh.emit_pure
  | error p e => exact Beh.emit_pure

theorem not_run_help {p : List String} : ∀ m, Outcome.help p ≠ .run m := by
  intro m h; cases h
theorem not_run_version {v : String} : ∀ m, Outcome.version v ≠ .run m := by
  intro m h; cases h
theorem not_run_error {p : List String} {e : ArgError} : ∀ m, Outcome.error p e ≠ .run m := by
  intro m h; cases h

/-- The non-running outcomes of the model. -/
theorem modelMain_text {c : Command} {run : Matches → Beh UInt32} {i : Input} {out : Outcome}
    (hout : c.outcome i = out) (hnr : ∀ m, out ≠ .run m) {code : UInt32} {o : Obs}
    (h : c.modelMain run i code o) :
    code = (out.exitCode?.getD 0).toUInt32 ∧ o = Beh.lineObs i (out.text c) := by
  rw [Command.modelMain_apply, hout] at h
  exact (Command.finish_beh hnr).mp h

/-- **`Command.main` refines the interpreter's specification**: read in the behaviour model,
the program behind the derived front end refines `Command.spec c S` whenever the program it runs
on each `Matches` refines `S m`. -/
theorem main_refines (c : Command) {run : Matches → Beh UInt32} {S : Matches → Spec}
    (h : ∀ m, Beh.toSpec (run m) ≤ S m) : Beh.toSpec (c.modelMain run) ≤ c.spec S := by
  intro i o ⟨code, o', hrun, ho⟩
  unfold Command.spec
  cases hout : c.outcome i with
  | run m =>
    have hr : run m i code o' := by
      rw [Command.modelMain_apply, hout] at hrun; exact hrun
    exact h m i o ⟨code, o', hr, ho⟩
  | help p =>
    obtain ⟨rfl, rfl⟩ := modelMain_text hout not_run_help hrun
    exact ho
  | version v =>
    obtain ⟨rfl, rfl⟩ := modelMain_text hout not_run_version hrun
    exact ho
  | error p e =>
    obtain ⟨rfl, rfl⟩ := modelMain_text hout not_run_error hrun
    exact ho

/-- With the specs themselves as the programs it runs. -/
theorem main_refines_ofSpec (c : Command) (S : Matches → Spec) :
    Beh.toSpec (c.modelMain fun m => Beh.ofSpec (S m)) ≤ c.spec S :=
  main_refines c fun m => (Beh.toSpec_ofSpec (S m)).le

/-- **`Command.spec` is exactly the model of the front end running the specs `S m`.** -/
theorem spec_eq_modelMain (c : Command) (S : Matches → Spec) :
    c.spec S = Beh.toSpec (c.modelMain fun m => Beh.ofSpec (S m)) := by
  apply le_antisymm _ (main_refines_ofSpec c S)
  intro i o hs
  unfold Command.spec at hs
  have htext : ∀ out, c.outcome i = out → (∀ m, out ≠ .run m) →
      o = { Beh.lineObs i (out.text c) with exit := (out.exitCode?.getD 0).toUInt32.toUInt8 } →
      Beh.toSpec (c.modelMain fun m => Beh.ofSpec (S m)) i o := by
    intro out hout hnr ho
    refine ⟨(out.exitCode?.getD 0).toUInt32, Beh.lineObs i (out.text c), ?_, ho⟩
    rw [Command.modelMain_apply, hout]
    exact (Command.finish_beh hnr).mpr ⟨rfl, rfl⟩
  cases hout : c.outcome i with
  | run m =>
    rw [hout] at hs
    refine ⟨o.exit.toUInt32, o, ?_, by cases o; simp⟩
    rw [Command.modelMain_apply, hout]
    exact ⟨hs, rfl⟩
  | help p => rw [hout] at hs; exact htext _ hout not_run_help hs
  | version v => rw [hout] at hs; exact htext _ hout not_run_version hs
  | error p e => rw [hout] at hs; exact htext _ hout not_run_error hs

/-! ## The four outcomes -/

theorem spec_of_run {c : Command} {S : Matches → Spec} {i : Input} {m : Matches}
    (h : c.outcome i = .run m) {o : Obs} : c.spec S i o ↔ S m i o := by
  unfold Command.spec; rw [h]

theorem spec_of_help {c : Command} {S : Matches → Spec} {i : Input} {p : List String}
    (h : c.outcome i = .help p) {o : Obs} :
    c.spec S i o ↔ o = { stdout := utf8 ((c.at p).help p ++ "\n"), exit := 0, fs := i.fs } := by
  unfold Command.spec; rw [h]; rfl

theorem spec_of_version {c : Command} {S : Matches → Spec} {i : Input} {v : String}
    (h : c.outcome i = .version v) {o : Obs} :
    c.spec S i o ↔ o = { stdout := utf8 (c.name ++ " " ++ v ++ "\n"), exit := 0, fs := i.fs } := by
  unfold Command.spec; rw [h]; rfl

/-- A usage error prints the error and the usage of its subcommand on stderr and exits 2. -/
theorem spec_of_error {c : Command} {S : Matches → Spec} {i : Input} {p : List String}
    {e : ArgError} (h : c.outcome i = .error p e) {o : Obs} :
    c.spec S i o ↔ o = { stderr := utf8 (errorText c p e ++ "\n"), exit := 2, fs := i.fs } := by
  unfold Command.spec; rw [h]; rfl

/-- **Usage errors refine the loose `Spec.usageError`.** -/
theorem spec_usageError {c : Command} {S : Matches → Spec} {i : Input} {o : Obs}
    (herr : c.UsageErr i) (hs : c.spec S i o) : Spec.usageError i o := by
  obtain ⟨p, e, h⟩ := herr
  have ho : o = { stderr := utf8 (errorText c p e ++ "\n"), exit := 2, fs := i.fs } :=
    (spec_of_error h).mp hs
  subst ho
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The same, as a refinement: the spec restricted to usage errors refines `Spec.usageError`. -/
theorem spec_inf_usageErr_le (c : Command) (S : Matches → Spec) :
    (c.spec S ⊓ fun i _ => c.UsageErr i) ≤ Spec.usageError :=
  fun _ _ h => spec_usageError h.2 h.1

end Silmaril.Cli
