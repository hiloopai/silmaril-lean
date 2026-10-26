module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysModel
public import Silmaril.Process.LPS.Problems.Sha256Cli.Simulation

/-! # From the `X86Sys` middle statement to the LPS target (the bridge reduction)

`bridge_of_simulation` (VERIFIED): if every admissible LPS launch of `sha256sum-min` is
aligned, by a stuttering simulation (`Sha256Cli.StutterSim`, model independent), with a
`Launch` of the middle model on a stdin-tier world of the same message, then
`SysTotalOn domain` implies the LPS `TotalOn domain`. This is the `sha256` filter's
`Sha256Cli.bridge_of_simulation` for the GNU middle model: the event flattening `evFlat`
maps a `read(0)` reply to its bytes as LPS `readEv 0` events, the accepted prefix of a
`write(1)` to `writeEv 1` events, `close` to nothing and the exit to LPS's exit event with the
unchanged file system. Along every run that keeps `Ok` the flattened history is the bytes read
so far followed by the bytes written so far (`trace_shape`); at `Done` it is `idealTrace`.

**Open (WIP).** `SimulationObligation`: the simulation itself. Its pieces, each with a proved
analogue for the `sha256` filter that this file's relation can reuse:

* instructions: LPS `x86WithFlagOracle` and `CLI.X86Linux.step` agree up to more defined
  LPS flags (`Sha256Cli.Instr`, `FlagMono.exec_mono`); the middle model uses the same
  `CLI.X86Linux.step`. The 8-bit ALU forms of the `x86/alu8-variant` branch must be covered
  by `FlagMono` once `X86.Ext` has them;
* `read(0)` and `write(1)` (`Sha256Cli.ReadStep`/`ReadSim`, `WriteStep`), with the world
  kernel `Sys.WorldStep` in place of `Syscall.State`;
* `close(fd)` for `fd ≤ 2` (new: LPS removes the descriptor; `Sys.WorldStep.closeOk`);
* `exit_group` (`Sha256Cli.Syscalls.pend_exit`);
* the launch: LPS `X86Launch.init` of `snapshot` against `X86Sys.Init` of
  `Apps.Sha256sum.Binary.Image.image` (`Sha256Cli.Launch`; the segment bytes agree because
  both are the pinned file's `PT_LOAD` contents).

Status: everything proved in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Fs (FileSystem)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads StutterSim)

/-! ## Flattening middle-model events into LPS events -/

/-- The exit as an LPS event. -/
def exitPart (fs : FileSystem) : Ev → List Event
  | .exit n => [Event.exitEv (BitVec.ofNat 64 n) fs]
  | _ => []

/-- One middle-model event as LPS events. -/
def evFlat (fs : FileSystem) (e : Ev) : List Event :=
  (readBytes e).map (Event.readEv 0) ++ (outBytes e).map (Event.writeEv 1) ++ exitPart fs e

/-- While running: the flattened events are the stdin bytes read so far, then the stdout bytes
written so far. -/
def Shaped (fs : FileSystem) (h : List Ev) : Prop :=
  h.flatMap (evFlat fs) = (stdinRead h).map (Event.readEv 0) ++ (out h).map (Event.writeEv 1)

theorem shaped_nil (fs : FileSystem) : Shaped fs [] := rfl

theorem stdinRead_append (h es : List Ev) : stdinRead (h ++ es) = stdinRead h ++ stdinRead es := by
  simp [stdinRead]

theorem out_append (h es : List Ev) : out (h ++ es) = out h ++ out es := by
  simp [out]

/-- What one step does to the history: nothing and the same exit status, one call event and
still running, or the exit event. -/
theorem gstep_cases {w : Apps.Sha256sum.World} {g g' : GS} {es : List Ev} (step : GStep w g es g') :
    (es = [] ∧ g'.exited = g.exited) ∨ (∃ c r, es = [.sys c r] ∧ g'.exited = none) ∨
      (∃ n, es = [.exit n] ∧ g'.exited = some n) := by
  cases step with
  | retire => exact .inl ⟨rfl, rfl⟩
  | call => exact .inr (.inl ⟨_, _, rfl, rfl⟩)
  | exit => exact .inr (.inr ⟨_, rfl, rfl⟩)

theorem shape_merge (R O r o : List Byte) (order : O = [] ∨ r = []) :
    R.map (Event.readEv 0) ++ O.map (Event.writeEv 1) ++
        (r.map (Event.readEv 0) ++ o.map (Event.writeEv 1)) =
      (R ++ r).map (Event.readEv 0) ++ (O ++ o).map (Event.writeEv 1) := by
  rcases order with rfl | rfl <;> simp

theorem shaped_step {message : List Byte} {fs : FileSystem} {w : Apps.Sha256sum.World} {g g' : GS}
    {h es : List Ev} (ok : Ok message g h) (shaped : Shaped fs h)
    (step : GStep w g es g') (ok' : Ok message g' (h ++ es)) : Shaped fs (h ++ es) := by
  rcases gstep_cases step with ⟨rfl, -⟩ | ⟨c, r, rfl, -⟩ | ⟨n, rfl, exited⟩
  · simpa using shaped
  · obtain ⟨_, _, _, _, order, _⟩ := ok
    obtain ⟨_, _, readPre', _, _⟩ := ok'
    unfold Shaped at shaped ⊢
    have e1 : [Ev.sys c r].flatMap (evFlat fs) =
        (readBytes (.sys c r)).map (Event.readEv 0) ++ (outBytes (.sys c r)).map (Event.writeEv 1) := by
      simp [evFlat, exitPart]
    have e2 : stdinRead [Ev.sys c r] = readBytes (.sys c r) := by simp [stdinRead]
    have e3 : out [Ev.sys c r] = outBytes (.sys c r) := by simp [out]
    rw [stdinRead_append, e2] at readPre'
    rw [List.flatMap_append, shaped, stdinRead_append, out_append, e1, e2, e3]
    apply shape_merge
    rcases order with silent | whole
    · exact .inl silent
    · right
      rw [whole] at readPre'
      have := readPre'.length_le
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
  · exact absurd (exited.symm.trans ok'.1) (by simp)

theorem shaped_done {message : List Byte} {fs : FileSystem} {w : Apps.Sha256sum.World} {g g' : GS}
    {h es : List Ev} (ok : Ok message g h) (shaped : Shaped fs h)
    (step : GStep w g es g') (done : Done message g' (h ++ es)) :
    (h ++ es).flatMap (evFlat fs) = idealTrace message fs := by
  obtain ⟨exited, h', split, _, read, written⟩ := done
  rcases gstep_cases step with ⟨rfl, same⟩ | ⟨c, r, rfl, running⟩ | ⟨n, rfl, exited'⟩
  · exact absurd (exited.symm.trans (same.trans ok.1)) (by simp)
  · exact absurd (exited.symm.trans running) (by simp)
  · have n0 : n = 0 := by simpa using exited'.symm.trans exited
    subst n0
    have same : h = h' := (List.append_inj' split rfl).1
    subst same
    rw [List.flatMap_append, shaped, read, written]
    simp [evFlat, readBytes, outBytes, exitPart, idealTrace]

theorem done_not_nil {message : List Byte} {g : GS} : ¬ Done message g [] := by
  rintro ⟨-, h', split, -⟩
  simp at split

/-- Along every run from a state that is `Ok` and shaped, the invariant holds with a shaped
history, or the goal holds with exactly the ideal flattened history. -/
theorem trace_shape {message : List Byte} {fs : FileSystem} {w : Apps.Sha256sum.World}
    {g g' : GS} {h es : List Ev}
    (leads : Leads (GStep w) (Ok message) (Done message) g h)
    (start : Ok message g h ∧ Shaped fs h) (run : Machine.Trace.Runs (GStep w) g es g') :
    (Ok message g' (h ++ es) ∧ Shaped fs (h ++ es)) ∨
      (Done message g' (h ++ es) ∧ (h ++ es).flatMap (evFlat fs) = idealTrace message fs) := by
  induction run generalizing h with
  | refl => exact .inl (by simpa using start)
  | @cons x z y es rest s tail ih =>
    have next := leads.after_runs (done_final _ _) (.single s)
    rcases leads.runs (done_final _ _) (.single s) with ok' | done
    · have shaped' := shaped_step start.1 start.2 s ok'
      simpa [List.append_assoc] using ih next ⟨ok', shaped'⟩
    · have ideal := shaped_done start.1 start.2 s done
      cases tail with
      | refl => exact .inr (by simpa using And.intro done ideal)
      | cons s' _ => exact absurd s' (done_final _ _ _ _ done _ _)

/-- A shaped history allowed by `Ok` is a prefix of the ideal trace. -/
theorem shaped_prefix {message : List Byte} {fs : FileSystem} {g : GS} {h : List Ev}
    (ok : Ok message g h) (shaped : Shaped fs h) :
    h.flatMap (evFlat fs) <+: idealTrace message fs := by
  obtain ⟨_, _, readPre, outPre, order, _⟩ := ok
  rw [shaped]
  unfold idealTrace
  rcases order with silent | whole
  · rw [silent, List.map_nil, List.append_nil, List.append_assoc]
    exact (readPre.map _).trans (List.prefix_append _ _)
  · rw [whole, List.append_assoc]
    apply List.prefix_append_right_inj _ |>.mpr
    exact (outPre.map _).trans (List.prefix_append _ _)

/-! ## The bridge -/

/-- **Segment `bridge`.** The middle statement implies the LPS statement. -/
def BridgeSegment : Prop := ∀ domain : List Byte → Prop, SysTotalOn domain → TotalOn domain

/-- For one admissible LPS launch: a middle-model launch on a stdin-tier world of the same
message, and a stuttering simulation aligning the LPS initial configuration with it. -/
def SimulationAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (prog : List Byte) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (g₀ : GS)
    (sim : StutterSim (isa := machine oracle) snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals)
      (GStep (world [prog] posix fs message)) (Ok message) (Done message) (evFlat inp.fs) [0]),
    Launch (world [prog] posix fs message) g₀ ∧ sim.rel (initial oracle limit en inp) g₀ []

/-- The open part of the bridge: a simulation for every admissible launch. -/
def SimulationObligation : Prop :=
  ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
    SimulationAt oracle refusals limit en inp message

/-- **Reduction (VERIFIED).** The launch-local simulations give the bridge segment. -/
theorem bridge_of_simulation (simulation : SimulationObligation) : BridgeSegment := by
  intro domain sys oracle refusals limit en inp message member admissible
  obtain ⟨prog, posix, fs, g₀, sim, launch, related⟩ :=
    simulation oracle refusals limit en inp message admissible
  have leads := sys prog posix fs message g₀ member launch
  have start : Ok message g₀ [] ∧ Shaped inp.fs [] := by
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
    rcases trace_shape leads start run with ⟨ok, shaped⟩ | ⟨-, ideal⟩
    · exact pre.trans (shaped_prefix ok (by simpa using shaped))
    · refine pre.trans ?_
      simp only [List.nil_append] at ideal
      rw [ideal]
  · obtain ⟨es, y, c', run, done, star, -⟩ := sim.complete leads related
    refine ⟨es.flatMap (evFlat inp.fs), c', star, ?_⟩
    rcases trace_shape leads start run with ⟨ok, -⟩ | ⟨-, ideal⟩
    · exact absurd (done.1.symm.trans ok.1) (by simp)
    · simp only [List.nil_append] at ideal
      rw [ideal]

/-! ## The glue (VERIFIED) -/

/-- The middle statement and the bridge give the LPS target on any domain. -/
theorem totalOn_of_sys {domain : List Byte → Prop} (sys : SysTotalOn domain)
    (bridge : BridgeSegment) : TotalOn domain :=
  bridge domain sys

/-- **Glue**, full target: the five segments (any inner cut points) and the bridge. -/
theorem totalGoal_of_segments {AtDigest AtEof Digested Formatted : Cut}
    (startup : StartupSegment (fun _ => True) AtDigest)
    (readLoop : ReadLoopSegment (fun _ => True) AtDigest AtEof)
    (final : FinalSegment (fun _ => True) AtEof Digested)
    (format : FormatSegment (fun _ => True) Digested Formatted)
    (exit : ExitSegment (fun _ => True) Formatted) (bridge : BridgeSegment) : TotalGoal :=
  totalOn_of_sys (sysTotalOn_of_segments startup readLoop final format exit) bridge

/-- **Glue**, bounded tier: segments for inputs of at most `n` bytes suffice. -/
theorem boundedGoal_of_segments (n : Nat) {AtDigest AtEof Digested Formatted : Cut}
    (startup : StartupSegment (fun m => m.length ≤ n) AtDigest)
    (readLoop : ReadLoopSegment (fun m => m.length ≤ n) AtDigest AtEof)
    (final : FinalSegment (fun m => m.length ≤ n) AtEof Digested)
    (format : FormatSegment (fun m => m.length ≤ n) Digested Formatted)
    (exit : ExitSegment (fun m => m.length ≤ n) Formatted) (bridge : BridgeSegment) :
    BoundedGoal n :=
  totalOn_of_sys (sysTotalOn_of_segments startup readLoop final format exit) bridge

/-- **Glue**, LPS target modulo the middle statement and the simulation obligation. -/
theorem totalGoal_of_sys_simulation (sys : SysTotalOn fun _ => True)
    (simulation : SimulationObligation) : TotalGoal :=
  totalOn_of_sys sys (bridge_of_simulation simulation)

end Silmaril.Process.LPS.Problems.GnuSha256sum
