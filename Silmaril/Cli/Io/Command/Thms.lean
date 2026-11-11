module

public import Silmaril.Cli.Io.Command.Defs
public import Silmaril.Cli.Io.Thms

/-!
# Programs behind a derived front end refine `Command.spec`

* **`obs_ofCommand`**: `Prog.ofCommand c body` is observed as `Command.spec` predicts: the front
  end's text and exit code on help, version and usage errors, `body m` on the matches `m`.
* **`sat_ofCommand_iff`**: it satisfies `Command.spec c S` iff each `body m` satisfies `S m` on
  every invocation whose arguments resolve to `m`; **`sat_ofCommand`**: in particular when
  every body satisfies its spec everywhere.
* **`sat_ofCommandCore_iff`**: for a pure core on the matches and stdin.
* `Command.spec_mono`: the front end is monotone in the bodies (refining the program's work
  refines the CLI).
* **`Command.check_sound`**: `Command.check c body` is sound for `Command.spec c S` when each
  `body m` is sound for `S m`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io

open Silmaril.Cli

/-- The declared variables, looked up in the list the program reads, are `Command.envOf`. -/
theorem lookup_envs_join (vs : List String) (i : Input) :
    (fun v => ((vs.map fun n => (n, i.getEnv n)).lookup v).join) = Beh.envOf vs i := by
  funext v
  induction vs with
  | nil => simp [Beh.envOf]
  | cons n vs ih =>
    by_cases h : v = n
    · subst h
      simp [Beh.envOf]
    · have hb : (v == n) = false := by simpa using h
      simp only [List.map_cons, List.lookup, hb] at ih ⊢
      simp [ih, Beh.envOf, h]

/-- The front end's observation off the `run` outcome is the one `Command.spec` fixes. -/
theorem _root_.Silmaril.Cli.Command.frontObs_eq (c : Command) (out : Outcome) (i : Input) :
    c.frontObs out i =
      { Beh.lineObs i (out.text c) with exit := (out.exitCode?.getD 0).toUInt32.toUInt8 } := by
  unfold Command.frontObs Outcome.code
  generalize out.text c = x
  rcases x with _ | ⟨_ | _, s⟩ <;> rfl

/-- **`Command.spec` with the front end's observation**: the derived front end, then `body m`
on the matches `m`. -/
theorem _root_.Silmaril.Cli.Command.spec_eq (c : Command) (body : Matches → Spec) (i : Input)
    (o : Obs) :
    c.spec body i o ↔
      match interpret c (c.envOf i) i.args with
      | .run m => body m i o
      | res => o = c.frontObs res i := by
  unfold Command.spec Command.outcome
  rcases interpret c (c.envOf i) i.args with m | p | v | e
  · exact Iff.rfl
  all_goals simp only [Command.frontObs_eq]

namespace Prog

/-- The front end evaluates to `interpret` on the declared variables. -/
theorem exec_front_bind {β : Type} (c : Command) (i : Input) (f : Outcome → Prog β) (st : St) :
    exec i ((front c).bind f) st = exec i (f (interpret c (c.envOf i) i.args)) st := by
  show exec i (((getArgs.bind fun args => (getEnvs c.envVars).bind fun vals =>
    Prog.pure (interpret c (fun v => (vals.lookup v).join) args))).bind f) st = _
  rw [exec_bind_bind, exec_getArgs_bind, exec_bind_bind, exec_getEnvs_bind]
  show exec i (f (interpret c (fun v => ((c.envVars.map fun n => (n, i.getEnv n)).lookup v).join)
    i.args)) st = _
  rw [lookup_envs_join]
  rfl

/-- The observation of an outcome's text and exit code. -/
theorem finish_emitText (c : Command) (out : Outcome) (i : Input) :
    finish (exec i ((emitText c out).bind fun _ => Prog.pure out.code) (St.init i)) =
      c.frontObs out i := by
  unfold emitText Command.frontObs
  generalize out.text c = x
  rcases x with _ | ⟨_ | _, s⟩ <;> rfl

/-- **The observation of a program behind the derived front end.** -/
theorem obs_ofCommand (c : Command) (body : Matches → Prog ExitCode) (i : Input) :
    (ofCommand c body).obs i =
      match interpret c (c.envOf i) i.args with
      | .run m => (body m).obs i
      | res => c.frontObs res i := by
  show finish (exec i ((front c).bind fun out => match out with
    | .run m => body m
    | res => (emitText c res).bind fun _ => Prog.pure res.code) (St.init i)) = _
  rw [exec_front_bind]
  rcases interpret c (c.envOf i) i.args with m | p | v | e
  · rfl
  · exact finish_emitText c _ i
  · exact finish_emitText c _ i
  · exact finish_emitText c _ i

/-- **A program behind the derived front end satisfies `Command.spec c S` iff every body
satisfies its spec on the invocations that select it.** -/
theorem sat_ofCommand_iff (c : Command) (body : Matches → Prog ExitCode)
    (S : Matches → Spec) :
    (ofCommand c body).Sat (c.spec S) ↔
      ∀ i m, interpret c (c.envOf i) i.args = .run m → S m i ((body m).obs i) := by
  constructor
  · intro h i m hm
    have hi : c.spec S i ((ofCommand c body).obs i) := h i
    rw [Command.spec_eq, obs_ofCommand] at hi
    simpa [hm] using hi
  · intro h i
    show c.spec S i ((ofCommand c body).obs i)
    rw [Command.spec_eq, obs_ofCommand]
    rcases hm : interpret c (c.envOf i) i.args with m | p | v | e
    · exact h i m hm
    · rfl
    · rfl
    · rfl

/-- **Bodies that satisfy their specs give a program that satisfies `Command.spec`.** -/
theorem sat_ofCommand {c : Command} {body : Matches → Prog ExitCode} {S : Matches → Spec}
    (h : ∀ m, (body m).Sat (S m)) : (ofCommand c body).Sat (c.spec S) :=
  (sat_ofCommand_iff c body S).2 fun i m _ => h m i

/-- **A pure core behind the derived front end** satisfies `Command.spec c S` iff the core's
result does, on every invocation selecting its matches. -/
theorem sat_ofCommandCore_iff (c : Command) (core : Matches → Bytes → Result)
    (S : Matches → Spec) :
    (ofCommandCore c core).Sat (c.spec S) ↔
      ∀ i m, interpret c (c.envOf i) i.args = .run m →
        S m i ((core m i.stdin).obs i i.stdin.length) := by
  rw [ofCommandCore, sat_ofCommand_iff]
  have hobs : ∀ m i, (readStdin.bind fun s => emit (core m s)).obs i =
      (core m i.stdin).obs i i.stdin.length := fun m i => by
    have h := obs_ofCore (fun _ s => core m s) i
    exact h
  simp only [bind_eq, hobs]

end Prog

/-- **`Command.spec` is monotone in the bodies.** -/
theorem _root_.Silmaril.Cli.Command.spec_mono (c : Command) {S T : Matches → Spec}
    (h : ∀ m, S m ≤ T m) : c.spec S ≤ c.spec T := by
  intro i o hs
  rw [Command.spec_eq] at hs ⊢
  split
  · next m hm => rw [hm] at hs; exact h m i o hs
  · next out hnot =>
    split at hs
    · next m hm => exact absurd hm (hnot m)
    · exact hs

/-- The front end changes no file. -/
theorem _root_.Silmaril.Cli.Command.frontObs_fs (c : Command) (res : Outcome) (i : Input) :
    (c.frontObs res i).fs = i.fs := by
  unfold Command.frontObs
  generalize res.text c = x
  rcases x with _ | ⟨_ | _, _⟩ <;> rfl

/-- A snapshot that passes the front-end test shows the front end's observation. -/
theorem _root_.Silmaril.Cli.Command.frontObs_agrees (c : Command) (res : Outcome) (i : Input)
    {s : Snap} (hr : (s.stdout == (c.frontObs res i).stdout && s.stderr == (c.frontObs res i).stderr &&
      s.exit == (c.frontObs res i).exit && s.files.isEmpty) = true) :
    s.Agrees i (c.frontObs res i) := by
  have hc : s.stdout = (c.frontObs res i).stdout ∧ s.stderr = (c.frontObs res i).stderr ∧
      s.exit = (c.frontObs res i).exit ∧ s.files = [] := by
    simpa [and_assoc] using hr
  have hfs : s.fs i = (c.frontObs res i).fs := by
    rw [c.frontObs_fs]
    funext q
    simp [Snap.fs, hc.2.2.2]
  exact ⟨hc.1.symm, hc.2.1.symm, hc.2.2.1.symm, hfs.symm⟩

/-- **`Command.check` is sound for `Command.spec`.** -/
theorem _root_.Silmaril.Cli.Command.check_sound (c : Command) {body : Matches → Check}
    {S : Matches → Spec} (h : ∀ m, (body m).Sound (S m)) : (c.check body).Sound (c.spec S) := by
  intro i s hs
  unfold Command.check at hs
  simp only [Command.spec_eq]
  rcases hm : interpret c (c.envOf i) i.args with m | p | v | e <;> rw [hm] at hs
  · exact h m i s hs
  · exact ⟨_, c.frontObs_agrees _ i hs, rfl⟩
  · exact ⟨_, c.frontObs_agrees _ i hs, rfl⟩
  · exact ⟨_, c.frontObs_agrees _ i hs, rfl⟩

end Silmaril.Cli.Io

end
