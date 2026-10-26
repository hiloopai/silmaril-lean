module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Segments
public import Silmaril.Process.CLI.X86Linux.SyscallInversion
public import Silmaril.Process.CLI.X86Linux.SilentTransport

/-! # Segment `output` of the `sha256` end-to-end proof (VERIFIED)

`output_segment_proved : OutputSegment fun _ => True`: from the write-ready cut point
(`OutReady`: the 65 answer bytes in `out`, the write request prepared at `0x4002a9`), every
execution of the actual binary in the reliable CLI environment keeps `Ok`, can always move,
and reaches `Done` (exited 0, `Sha256.Success`, writes only to fd 1, reads only from stdin).

The write loop is covered under every positive write split. `CLI.Env.reliable` excludes error
returns and zero-byte writes (`Syscall.Event.IsRefusal`), so every write accepts `1…remaining` bytes
and the offset strictly increases; the proof is strong induction on the remaining count.

Reuse: the checked instruction paths of the chain (`OutputUniversal.instruction`/`requested`,
`OutputLoop.advance`/`retry_path`/`success_path`/`retry_ready`, `OutputTransfer.write_some`/
`successful_event`/`successful_ledger`), stated for `CLI.Env.linux`, are transported to
`CLI.Env.reliable` by `toReliable`/`toLinux` below; silent instruction segments are cancelled with
`CLI.Proc.Step.unique_of_silent` (`SilentTransport`).

The proved segment is exported as `output_segment_proved` (`EndToEnd.lean` assembles the
segments); `sha256cli_lps_total_of` gives the end-to-end target from the other three.

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.CLI.Sha256Cli
open Silmaril.Process.CLI.Sha256Cli.OutputTransfer
open Silmaril.Process.CLI.Sha256Cli.OutputLoop

namespace OutputProof

set_option maxRecDepth 10000

/-! ## Moving between `Env.linux` and `Env.reliable` -/

/-- The ISA's one-step result is a function. -/
theorem deterministic : ∀ c m (a b : CLI.Step CLI.X86Linux.Core), isa.step c m a → isa.step c m b → a = b :=
  fun _ _ _ _ ha hb => ha.trans hb.symm

/-- Every reliable step is a Linux step. -/
theorem toLinux {x y : PS} {e : List Syscall.Event} (step : CStep x e y) :
    CLI.Proc.Step isa CLI.Env.linux ⟨x.core, x.env⟩ e ⟨y.core, y.env⟩ := by
  cases step with
  | retire running step => exact .retire running step
  | call running step request effect resume => exact .call running step request effect.1 resume
  | exit running step request effect => exact .exit running step request effect.1

/-- A Linux step whose events are not refusals is a reliable step. -/
theorem toReliable {a b : CLI.PState isa CLI.Env.linux} {e : List Syscall.Event} (step : CLI.Proc.Step isa CLI.Env.linux a e b)
    (fine : ∀ ev ∈ e, ¬ ev.IsRefusal) : CStep ⟨a.core, a.env⟩ e ⟨b.core, b.env⟩ := by
  have clean : ∀ {s q ev r s'}, ¬ Syscall.Event.IsRefusal ev → CLI.Env.EintrClean s q ev r s' := by
    intro s q ev r s' notRefusal fd address count _ isError
    subst isError
    exact absurd trivial notRefusal
  cases step with
  | retire running step => exact .retire running step
  | call running step request effect resume =>
    have ok := fine _ (List.mem_singleton_self _)
    exact .call running step request ⟨effect, clean ok, ok⟩ resume
  | exit running step request effect =>
    have ok := fine _ (List.mem_singleton_self _)
    exact .exit running step request ⟨effect, clean ok, ok⟩

/-- A silent Linux step keeps the exit status. -/
theorem silent_exited {a b : CLI.PState isa CLI.Env.linux} (step : CLI.Proc.Step isa CLI.Env.linux a [] b) :
    b.env.exited = a.env.exited := by
  cases step with
  | retire => rfl

/-! ## The invariant -/

theorem readsOnlyStdin_append {evs : List Syscall.Event} (h : ReadsOnlyStdin evs) (ev : Syscall.Event)
    (notRead : ∀ fd bytes, ev ≠ .read fd bytes) : ReadsOnlyStdin (evs ++ [ev]) := by
  intro fd bytes member
  rcases List.mem_append.mp member with old | new
  · exact h fd bytes old
  · exact absurd (List.mem_singleton.mp new).symm (notRead fd bytes)

theorem ok_of_inv {message : List Byte} {x : PS} {evs : List Syscall.Event} {off : Nat}
    (running : x.sys.exited = none) (inv : CLI.Sha256Cli.Driver.OutputInv message evs off)
    (reads : ReadsOnlyStdin evs) : OkE message x evs := by
  refine ⟨running, inv.only, reads, ?_, ?_, .inr ⟨inv.input, inv.eof⟩⟩
  · rw [inv.input]
  · rw [inv.output]
    exact List.take_prefix _ _

theorem ok_of_exited {message : List Byte} {x y : PS} {evs : List Syscall.Event}
    (same : y.sys.exited = x.sys.exited) (ok : OkE message x evs) : OkE message y evs :=
  ⟨same.trans ok.1, ok.2⟩

/-- Cancel a silent instruction segment of the actual binary in front of a `Leads` proof. -/
theorem leads_of_silent {message : List Byte} {Goal : PS → List Syscall.Event → Prop}
    {c c' : CLI.X86Linux.Core} {s s' : Syscall.State} {evs : List Syscall.Event}
    (run : CLI.Proc.Runs isa CLI.Env.linux ⟨c, s⟩ [] ⟨c', s'⟩) (ok : OkE message (⟨c, s⟩ : PS) evs)
    (next : Leads CStep (Ok message) Goal (⟨c', s'⟩ : PS) evs) :
    Leads CStep (Ok message) Goal (⟨c, s⟩ : PS) evs := by
  suffices key : ∀ (a b : CLI.PState isa CLI.Env.linux) (l : List Syscall.Event),
      CLI.Proc.Runs isa CLI.Env.linux a l b → l = [] → OkE message (⟨a.core, a.env⟩ : PS) evs →
      Leads CStep (Ok message) Goal (⟨b.core, b.env⟩ : PS) evs →
      Leads CStep (Ok message) Goal (⟨a.core, a.env⟩ : PS) evs from
    key _ _ _ run rfl ok next
  intro a b l run
  induction run with
  | refl => exact fun _ _ h => h
  | @cons a m b e rest first _ ih =>
    intro empty okA leadsB
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp empty
    have okM : OkE message (⟨m.core, m.env⟩ : PS) evs :=
      ok_of_exited (x := ⟨a.core, a.env⟩) (y := ⟨m.core, m.env⟩) (silent_exited first) okA
    have args : ReadArgs (⟨a.core, a.env⟩ : PS) := by
      cases first with
      | retire _ retired => exact readArgs_of_retired retired.symm
    refine .step (ok_of_okE okA args) ⟨[], _, toReliable first (by simp)⟩ fun e y step => ?_
    obtain ⟨rfl, same⟩ := first.unique_of_silent deterministic (toLinux step)
    rcases y with ⟨yc, ys⟩
    cases same
    simpa using ih rfl okM leadsB

/-! ## The write loop -/

theorem writable_after {before after : Syscall.State} {q : Request} {ev : Syscall.Event} {r : Reply}
    (effect : Syscall.Step before q ev r after)
    (opened : ∃ d : Descriptor, before.descriptors 1 = some d ∧ d.writable = true) :
    ∃ d : Descriptor, after.descriptors 1 = some d ∧ d.writable = true := by
  obtain ⟨d, hd, hw⟩ := opened
  have modes := effect.descriptor_modes 1
  rw [hd] at modes
  cases h : after.descriptors 1 with
  | none => rw [h] at modes; cases modes
  | some d' =>
    rw [h] at modes
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at modes
    exact ⟨d', rfl, modes.2.trans hw⟩

/-- The exit site: `exit(0)` is the only transition, and it reaches `Done`. -/
theorem exit_leads {input : CLI.ProcInput} {message : List Byte} (finite : input.stdin = .ofList message)
    (c : CLI.X86Linux.Core) (off : Fin 65) (count : Nat) (flags : X86.Word) (s : Syscall.State)
    (evs : List Syscall.Event) (intact : Output.Intact s.memory) (running : s.exited = none)
    (ledger : CLI.Sha256Cli.Driver.OutputInv message evs 65) (reads : ReadsOnlyStdin evs) :
    Leads CStep (Ok message) (Done input message) (⟨success c off count flags, s⟩ : PS) evs := by
  have actual : CLI.X86Linux.step (success c off count flags) s.memory =
      Binary.i_4002d1.denote (success c off count flags) s.memory :=
    step_of_entry Binary.ok_4002d1.1 rfl
    (intact Binary.i_4002d1 (by simp [Binary.transcript]))
  have trap : CLI.X86Linux.step (success c off count flags) s.memory =
      .syscall { success c off count flags with rip := 0x4002d3 } := by
    simpa [Entry.denote, Binary.i_4002d1, success] using actual
  have requestExit : CLI.X86Linux.request { success c off count flags with rip := 0x4002d3 } =
      some (.exit 0) := by
    simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, CLI.X86Linux.writeNumber,
      CLI.X86Linux.exitNumber, success, successNumber, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have notExit : ∀ fd bytes, Syscall.Event.exit 0 ≠ .read fd bytes := by simp
  refine .step (ok_of_okE (ok_of_inv (x := ⟨success c off count flags, s⟩) running ledger reads)
    (readArgs_of_not_read trap fun fd a n h => by rw [requestExit] at h; cases h)) ?_ ?_
  · refine ⟨[.exit (0 % 256)], ⟨{ success c off count flags with rip := 0x4002d3 },
      { s with exited := some (0 % 256) }⟩, ?_⟩
    exact toReliable (a := ⟨success c off count flags, s⟩)
      (.exit running trap.symm requestExit (Syscall.Step.exit 0 running))
      (by simp [Syscall.Event.IsRefusal])
  · intro e y step
    obtain ⟨_, returned | exiting⟩ :=
      (CLI.X86Linux.step_iff_of_syscall (E := CLI.Env.reliable) trap requestExit).mp step
    · obtain ⟨_, _, _, effect, _⟩ := returned
      have linuxEffect : Syscall.Step s (.exit 0) _ (.returned _) _ := effect.1
      cases linuxEffect
    · obtain ⟨event, status, rfl, effect, _⟩ := exiting
      rcases y with ⟨yc, ys⟩
      have linuxEffect : Syscall.Step s (.exit 0) event (.exited status) ys := effect.1
      cases linuxEffect
      refine .done ⟨rfl, (Silmaril.Process.CLI.Sha256Cli.OutputUniversal.output_exit ledger 0).success finite,
        (Silmaril.Process.CLI.Sha256Cli.OutputUniversal.output_exit ledger 0).only,
        readsOnlyStdin_append reads _ notExit⟩

/-- The write loop from any unfinished offset, under every positive write split. -/
theorem write_leads {input : CLI.ProcInput} {message : List Byte}
    (finite : input.stdin = .ofList message) :
    ∀ (fuel : Nat) (off : Fin 65) (c : CLI.X86Linux.Core) (s : Syscall.State) (evs : List Syscall.Event),
      remaining off = fuel → OutputLoop.Ready c off → Output.Intact s.memory →
      s.exited = none → s.memory.readBytes 0x4015c0 65 = some (CLI.Sha256.expected message) →
      CLI.Sha256Cli.Driver.OutputInv message evs off.val →
      (∃ d : Descriptor, s.descriptors 1 = some d ∧ d.writable = true) → ReadsOnlyStdin evs →
      Leads CStep (Ok message) (Done input message) (⟨c, s⟩ : PS) evs := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
  intro off c s evs fuelEq ready intact running answer accounted opened reads
  have actual := OutputUniversal.instruction c off s.memory ready intact
  have request := OutputUniversal.requested c off ready
  refine .step (ok_of_okE (ok_of_inv (x := ⟨c, s⟩) running accounted reads)
    (readArgs_of_not_read actual fun fd a n h => by rw [request] at h; cases h)) ?_ ?_
  · -- progress: a full write is admitted
    obtain ⟨d, hd, hw⟩ := opened
    have transfer : remaining off ≤ maxTransfer :=
      (Nat.sub_le 65 off.val).trans (by decide)
    have effect : Syscall.Step s (writeRequest off) (.write 1 (accepted message off (remaining off)))
        (.returned (.ok (remaining off))) (writtenState s d message off (remaining off)) := by
      simpa only [writeRequest, writtenState, accepted] using
        (Syscall.Step.writeSome (written := remaining off) running hd hw
          (tail_read answer off) le_rfl transfer)
    have full : CLI.Proc.Step isa CLI.Env.linux (⟨c, s⟩ : Output.PS) _
        ⟨returned c (.ok (remaining off)) 0, writtenState s d message off (remaining off)⟩ :=
      .call running actual.symm request effect ⟨0, rfl⟩
    refine ⟨_, _, toReliable full ?_⟩
    intro ev member
    rw [List.mem_singleton] at member
    subst member
    have len := accepted_length (message := message) (le_refl (remaining off))
    have pos := remaining_positive off
    cases h : accepted message off (remaining off) with
    | nil => rw [h] at len; simp at len; omega
    | cons _ _ => simp [Syscall.Event.IsRefusal]
  · intro e y step
    rcases y with ⟨yc, after⟩
    obtain ⟨_, returning | exiting⟩ :=
      (CLI.X86Linux.step_iff_of_syscall (E := CLI.Env.reliable) actual request).mp step
    · obtain ⟨event, result, rfl, effect, resume⟩ := returning
      have linuxEffect : Syscall.Step s (writeRequest off) event (.returned result) after := effect.1
      have notRefusal : ¬ event.IsRefusal := effect.2.2
      obtain ⟨flags, coreEq⟩ := resume
      change yc = returned c result flags at coreEq
      subst yc
      have kept := linuxEffect.write_memory_preserved
      have intactAfter : Output.Intact after.memory := by rw [kept]; exact intact
      have answerAfter : after.memory.readBytes 0x4015c0 65 = some (CLI.Sha256.expected message) := by
        rw [kept]; exact answer
      have runningAfter := OutputUniversal.write_running linuxEffect
      have openedAfter := writable_after linuxEffect opened
      cases result with
      | error errno =>
        exact absurd (by rw [error_event linuxEffect]; trivial) notRefusal
      | ok count =>
        have eventEq := successful_event answer linuxEffect
        obtain ⟨_, _, _, fits⟩ := (show Syscall.Step s (.write 1 (address off) (remaining off)) event
          (.returned (.ok count)) after from linuxEffect).write_success
        have ledger := (successful_ledger answer accounted linuxEffect).1
        have readsAfter : ReadsOnlyStdin (evs ++ [event]) :=
          readsOnlyStdin_append reads _ (by rw [eventEq]; simp)
        have nonzero : 0 < count := by
          rcases Nat.eq_zero_or_pos count with zero | pos
          · subst zero
            exact absurd (by rw [eventEq]; simp [accepted, Syscall.Event.IsRefusal]) notRefusal
          · exact pos
        have prefixRun := advance c off count flags after ready intactAfter runningAfter nonzero fits
        have okAfter : OkE message (⟨returned c (.ok count) flags, after⟩ : PS) (evs ++ [event]) :=
          ok_of_inv runningAfter ledger readsAfter
        by_cases unfinished : off.val + count < 65
        · have silent := prefixRun.append
            (retry_path c off count flags after ready intactAfter runningAfter unfinished)
          let nextOff : Fin 65 := ⟨off.val + count, unfinished⟩
          have decreased : remaining nextOff < fuel := by
            have := off.isLt
            dsimp [remaining, nextOff] at *
            omega
          exact leads_of_silent silent okAfter
            (ih (remaining nextOff) decreased nextOff _ after _ rfl
              (retry_ready c off count flags ready unfinished) intactAfter runningAfter answerAfter
              ledger openedAfter readsAfter)
        · have complete : off.val + count = 65 := by
            have := off.isLt
            dsimp [remaining] at fits
            omega
          have silent := prefixRun.append
            (success_path c off count flags after intactAfter runningAfter complete)
          rw [complete] at ledger
          exact leads_of_silent silent okAfter
            (exit_leads finite c off count flags after _ intactAfter runningAfter ledger readsAfter)
    · obtain ⟨event, status, _, effect, _⟩ := exiting
      have linuxEffect : Syscall.Step s (.write 1 (address off) (remaining off)) event
        (.exited status) after := effect.1
      cases linuxEffect

end OutputProof

/-- **Segment `output`** (VERIFIED). -/
theorem output_segment_proved : OutputSegment fun _ => True := by
  rintro message input ⟨c, s⟩ evs - ⟨finite, ⟨initial, ready⟩, accounted, opened, reads⟩
  change HexOutputFrame.Ready initial c s message at ready
  have readyLoop : OutputLoop.Ready c 0 := by
    have h := request_ready c 0
    rwa [ready.request] at h
  exact OutputProof.write_leads finite _ 0 c s evs rfl readyLoop ready.frame.code ready.running
    ready.answer accounted opened reads

/-- The end-to-end target, modulo the three remaining segments `loop`, `tail`, `bridge`
(`output` is `output_segment_proved`). -/
theorem sha256cli_lps_total_of (loop : LoopSegment fun _ => True)
    (tail : TailSegment fun _ => True) (bridge : BridgeSegment) : TotalGoal :=
  totalGoal_of_segments loop tail output_segment_proved bridge

end Silmaril.Process.LPS.Problems.Sha256Cli
