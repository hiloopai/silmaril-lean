module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Segments
public import Silmaril.Process.LPS.Problems.Sha256Cli.Simulation

/-! # Segment `bridge`: CLI total correctness gives the LPS statement

`BridgeSegment` (`Segments.lean`) says: for every domain, `CliTotalOn domain → TotalOn domain`.
This file reduces it to one launch-local obligation, `SimulationAt`, and proves the
reduction (`bridge_of_simulation`, VERIFIED).

**`SimulationAt oracle refusals limit en inp message`.** For an admissible LPS launch, there
are a CLI input with the same stdin, a CLI launch state `x₀` (`Launch`, so `CliTotalOn`
applies to it) and a `StutterSim` (`Simulation.lean`) between the LPS run of the pinned ELF
and the CLI process, with LPS events the flattening `evFlat inp.fs` of the CLI events (a
read or write of `bytes` on `fd` is one LPS byte event per byte, an EOF read or an error is
silent, `exit k` is `exitEv k inp.fs`), exit statuses in `[0]`, and the LPS initial
configuration aligned with `x₀`.

**Reduction (VERIFIED).** `CliTotalOn` gives `Leads CStep (Ok message) (Done input message) x₀ []`.
`StutterSim.mustExit` turns it into `MustExitInAt … [0]`, hence error freedom and no
unmodelled state; `StutterSim.obsTrace_prefix` and the CLI event lemmas below
(`trace_shape`: along every CLI run that keeps `Ok`, the flattened events are the message
bytes read so far followed by the answer bytes written so far; at `Done` they are exactly
`idealTrace`) give the trace prefix property; `StutterSim.complete` gives the ideal trace.

**Refinement of the obligation (all VERIFIED reductions).**

* `Instr.lean`: the instruction level. `simulationAt_of_syscallSim` builds the `StutterSim`
  from a concrete relation (cores equal up to more defined LPS flags, equal memories, a
  per-launch relation `MR` between the LPS model and the CLI system state) and proves every
  instruction case, using flag monotonicity of `X86.Ext.exec` (`FlagMono.exec_mono`).
* `Syscalls.lean`: `exit`/`exit_group` (`pend_exit`), leaving `read` and `write`
  (`bridge_of_readWriteSim`).
* `WriteStep.lean`: `write` to stdout (`pend_write`), leaving `read` (`bridge_of_readSim`).

**Open (WIP).** `ReadSimAt` for every admissible launch: a CLI launch with the same stdin, an
`MR` aligning the initial configurations (the loader correspondence: LPS `X86Launch.init` of
`snapshot` against a CLI `Launch` of `cliImage`) and `ReadObligations`: `MR` records the file
system and LPS descriptor 1 as channel 1, puts every CLI-readable buffer in LPS's modelled range,
survives instructions and writes to descriptor 1, and `read` of stdin is simulated.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Fs (FileSystem)

/-! ## Flattening CLI events into LPS events -/

/-- One CLI event as LPS events: one byte event per transferred byte, nothing for an error,
and the exit with the (unchanged) file system `fs`. -/
def evFlat (fs : FileSystem) : Syscall.Event → List Event
  | .read fd bytes => bytes.map (Event.readEv (BitVec.ofNat 64 fd))
  | .write fd bytes => bytes.map (Event.writeEv (BitVec.ofNat 64 fd))
  | .error _ _ => []
  | .exit status => [Event.exitEv (BitVec.ofNat 64 status) fs]

/-! ## What a CLI step does to the event list and the exit status -/

theorem reliable_step_exit {s s' : Syscall.State} {q : Syscall.Request} {k : Nat}
    {r : Syscall.Reply} (step : CLI.Env.reliable.step s q (.exit k) r s') :
    s'.exited = some k := by
  obtain ⟨step, -⟩ := step
  generalize event : Syscall.Event.exit k = e at step
  cases step <;> cases event; rfl

theorem reliable_step_other {s s' : Syscall.State} {q : Syscall.Request} {e : Syscall.Event}
    {r : Syscall.Reply} (step : CLI.Env.reliable.step s q e r s') (other : ∀ k, e ≠ .exit k) :
    s'.exited = s.exited := by
  obtain ⟨step, -⟩ := step
  cases step <;> first | rfl | exact absurd rfl (other _)

/-- A CLI step emits nothing and keeps the exit status, or emits one event; an `exit` event
sets the status, any other keeps it. -/
theorem cstep_cases {x y : PS} {es : List Syscall.Event} (step : CStep x es y) :
    (es = [] ∧ y.sys.exited = x.sys.exited) ∨
      (∃ k, es = [.exit k] ∧ y.sys.exited = some k) ∨
      (∃ e, es = [e] ∧ (∀ k, e ≠ .exit k) ∧ y.sys.exited = x.sys.exited) := by
  cases step with
  | retire running _ => exact .inl ⟨rfl, rfl⟩
  | @call _ _ _ _ _ _ ev _ _ _ _ effect _ =>
    by_cases isExit : ∃ k, ev = .exit k
    · obtain ⟨k, rfl⟩ := isExit
      exact .inr (.inl ⟨k, rfl, reliable_step_exit effect⟩)
    · exact .inr (.inr ⟨ev, rfl, fun k h => isExit ⟨k, h⟩,
        reliable_step_other effect fun k h => isExit ⟨k, h⟩⟩)
  | @exit _ _ _ _ _ ev _ _ _ _ effect =>
    by_cases isExit : ∃ k, ev = .exit k
    · obtain ⟨k, rfl⟩ := isExit
      exact .inr (.inl ⟨k, rfl, reliable_step_exit effect⟩)
    · exact .inr (.inr ⟨ev, rfl, fun k h => isExit ⟨k, h⟩,
        reliable_step_other effect fun k h => isExit ⟨k, h⟩⟩)

/-! ## The shape of the flattened trace along a CLI run (VERIFIED) -/

/-- While running: the flattened events are the stdin bytes read so far, then the stdout
bytes written so far. -/
def Shaped (fs : FileSystem) (h : List Syscall.Event) : Prop :=
  h.flatMap (evFlat fs) =
    (CLI.stdinRead h).map (Event.readEv 0) ++ (CLI.stdout h).map (Event.writeEv 1)

theorem shaped_nil (fs : FileSystem) : Shaped fs [] := rfl

theorem readOn_single_read (fd d : Nat) (bytes : List Byte) :
    CLI.readOn fd [.read d bytes] = if d = fd then bytes else [] := by
  simp [CLI.readOn]

theorem shaped_step {message : List Byte} {fs : FileSystem} {x y : PS}
    {h es : List Syscall.Event} (ok : Ok message x h) (shaped : Shaped fs h)
    (step : CStep x es y) (ok' : Ok message y (h ++ es)) : Shaped fs (h ++ es) := by
  rcases cstep_cases step with ⟨rfl, -⟩ | ⟨k, rfl, exited⟩ | ⟨e, rfl, notExit, -⟩
  · simpa using shaped
  · exact absurd (exited.symm.trans ok'.1) (by simp)
  · obtain ⟨_, only, reads, readPre, _, order⟩ := ok
    obtain ⟨_, only', reads', readPre', _, _⟩ := ok'
    unfold Shaped at shaped ⊢
    cases e with
    | read fd bytes =>
      have fd0 : fd = 0 := reads' fd bytes (by simp)
      subst fd0
      have stdinStep : CLI.stdinRead (h ++ [.read 0 bytes]) = CLI.stdinRead h ++ bytes := by
        simp [CLI.stdinRead, CLI.readOn_append, CLI.readOn]
      have stdoutStep : CLI.stdout (h ++ [.read 0 bytes]) = CLI.stdout h := by
        simp [CLI.stdout, CLI.writtenOn_append, CLI.writtenOn]
      rw [stdinStep] at readPre'
      rw [List.flatMap_append, shaped, stdinStep, stdoutStep]
      rcases order with silent | ⟨whole, -⟩
      · simp [silent, evFlat]
      · rw [whole] at readPre'
        have empty : bytes = [] := by
          have := readPre'.length_le
          simp only [List.length_append] at this
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst empty
        simp [evFlat]
    | write fd bytes =>
      have fd1 : fd = 1 := by simpa using only' fd bytes (by simp)
      subst fd1
      have stdinStep : CLI.stdinRead (h ++ [.write 1 bytes]) = CLI.stdinRead h := by
        simp [CLI.stdinRead, CLI.readOn_append, CLI.readOn]
      have stdoutStep : CLI.stdout (h ++ [.write 1 bytes]) = CLI.stdout h ++ bytes := by
        simp [CLI.stdout, CLI.writtenOn_append, CLI.writtenOn]
      rw [List.flatMap_append, shaped, stdinStep, stdoutStep]
      simp [evFlat]
    | error q errno =>
      have stdinStep : CLI.stdinRead (h ++ [.error q errno]) = CLI.stdinRead h := by
        simp [CLI.stdinRead, CLI.readOn_append, CLI.readOn]
      have stdoutStep : CLI.stdout (h ++ [.error q errno]) = CLI.stdout h := by
        simp [CLI.stdout, CLI.writtenOn_append, CLI.writtenOn]
      rw [List.flatMap_append, shaped, stdinStep, stdoutStep]
      simp [evFlat]
    | exit k => exact absurd rfl (notExit k)

theorem ofList_injective {a b : List Byte} (h : Syscall.InputStream.ofList a =
    Syscall.InputStream.ofList b) : a = b := by
  apply List.ext_getElem?
  intro i
  exact congrArg (fun s : Syscall.InputStream => s.byteAt i) h

theorem shaped_done {input : CLI.ProcInput} {message : List Byte} {fs : FileSystem} {x y : PS}
    {h es : List Syscall.Event} (stdin : input.stdin = .ofList message)
    (ok : Ok message x h) (shaped : Shaped fs h)
    (step : CStep x es y) (done : Done input message y (h ++ es)) :
    (h ++ es).flatMap (evFlat fs) = idealTrace message fs := by
  obtain ⟨exited, ⟨message', stdin', read, -, out⟩, -, -⟩ := done
  have same : message' = message := ofList_injective (stdin'.symm.trans stdin)
  subst same
  rcases cstep_cases step with ⟨rfl, same⟩ | ⟨k, rfl, exited'⟩ | ⟨e, rfl, -, same⟩
  · exact absurd (exited.symm.trans (same.trans ok.1)) (by simp)
  · have k0 : k = 0 := by
      have := exited'.symm.trans exited
      simpa using this
    subst k0
    have stdinStep : CLI.stdinRead (h ++ [.exit 0]) = CLI.stdinRead h := by
      simp [CLI.stdinRead, CLI.readOn_append, CLI.readOn]
    have stdoutStep : CLI.stdout (h ++ [.exit 0]) = CLI.stdout h := by
      simp [CLI.stdout, CLI.writtenOn_append, CLI.writtenOn]
    rw [stdinStep] at read
    rw [stdoutStep] at out
    rw [List.flatMap_append, shaped, read, out]
    simp [evFlat, idealTrace]
  · exact absurd (exited.symm.trans (same.trans ok.1)) (by simp)

theorem done_not_nil {input : CLI.ProcInput} {message : List Byte} {x : PS} :
    ¬ Done input message x [] := by
  rintro ⟨-, ⟨_, -, -, eof, -⟩, -, -⟩
  simp [CLI.SawEof] at eof

/-- Along every CLI run from a state that is `Ok` and shaped, the invariant holds with a
shaped history, or the goal holds with exactly the ideal flattened history. -/
theorem trace_shape {input : CLI.ProcInput} {message : List Byte} {fs : FileSystem}
    (stdin : input.stdin = .ofList message) {x y : PS} {h es : List Syscall.Event}
    (leads : Leads CStep (Ok message) (Done input message) x h)
    (start : Ok message x h ∧ Shaped fs h) (run : Machine.Trace.Runs CStep x es y) :
    (Ok message y (h ++ es) ∧ Shaped fs (h ++ es)) ∨
      (Done input message y (h ++ es) ∧ (h ++ es).flatMap (evFlat fs) = idealTrace message fs) := by
  induction run generalizing h with
  | refl => exact .inl (by simpa using start)
  | @cons x z y es rest s tail ih =>
    have next := leads.after_runs (done_final _ _) (.single s)
    rcases leads.runs (done_final _ _) (.single s) with ok' | done
    · have shaped' := shaped_step start.1 start.2 s ok'
      simpa [List.append_assoc] using ih next ⟨ok', shaped'⟩
    · have ideal := shaped_done stdin start.1 start.2 s done
      cases tail with
      | refl => exact .inr (by simpa using And.intro done ideal)
      | cons s' _ => exact absurd s' (done_final _ _ _ _ done _ _)

/-- A shaped history allowed by `Ok` is a prefix of the ideal trace. -/
theorem shaped_prefix {message : List Byte} {fs : FileSystem} {x : PS} {h : List Syscall.Event}
    (ok : Ok message x h) (shaped : Shaped fs h) :
    h.flatMap (evFlat fs) <+: idealTrace message fs := by
  obtain ⟨_, _, _, readPre, outPre, order⟩ := ok
  rw [shaped]
  unfold idealTrace
  rcases order with silent | ⟨whole, -⟩
  · rw [silent, List.map_nil, List.append_nil, List.append_assoc]
    exact (readPre.map _).trans (List.prefix_append _ _)
  · rw [whole, List.append_assoc]
    apply List.prefix_append_right_inj _ |>.mpr
    exact (outPre.map _).trans (List.prefix_append _ _)

/-! ## The launch-local obligation -/

/-- For one admissible LPS launch: a CLI launch with the same stdin and a stuttering
simulation aligning the LPS initial configuration with it. -/
def SimulationAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (input : CLI.ProcInput) (x₀ : PS)
    (sim : StutterSim (isa := machine oracle) snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals) CStep
      (Ok message) (Done input message) (evFlat inp.fs) [0]),
    input.stdin = .ofList message ∧ input.Valid ∧ Launch input x₀ ∧
      sim.rel (initial oracle limit en inp) x₀ []

/-- **Reduction (VERIFIED).** The launch-local simulations give the bridge segment. -/
theorem bridge_of_simulation
    (simulation : ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      SimulationAt oracle refusals limit en inp message) : BridgeSegment := by
  intro domain cli oracle refusals limit en inp message member admissible
  obtain ⟨input, x₀, sim, stdin, valid, launch, related⟩ :=
    simulation oracle refusals limit en inp message admissible
  have leads := cli message input x₀ member stdin valid launch
  have start : Ok message x₀ [] ∧ Shaped inp.fs [] := by
    refine ⟨?_, shaped_nil _⟩
    rcases leads.now with ok | done
    · exact ok
    · exact absurd done done_not_nil
  have mustExit := (sim.mustExit leads).1 _ related
  refine ⟨⟨?_, ?_, ?_⟩, mustExit, ?_⟩
  · exact mustExit.not_reachesError
  · exact sim.not_reachesUnmodeled leads related
  · intro tr obs
    obtain ⟨es, y, run, -, pre⟩ := sim.obsTrace_prefix (done_final _ _) leads related obs
    rcases trace_shape stdin leads start run with ⟨ok, shaped⟩ | ⟨-, ideal⟩
    · exact pre.trans (shaped_prefix ok (by simpa using shaped))
    · refine pre.trans ?_
      simp only [List.nil_append] at ideal
      rw [ideal]
  · obtain ⟨es, y, c', run, done, star, -⟩ := sim.complete leads related
    refine ⟨es.flatMap (evFlat inp.fs), c', star, ?_⟩
    rcases trace_shape stdin leads start run with ⟨ok, -⟩ | ⟨-, ideal⟩
    · exact absurd (done.1.symm.trans ok.1) (by simp)
    · simp only [List.nil_append] at ideal
      rw [ideal]

end Silmaril.Process.LPS.Problems.Sha256Cli
