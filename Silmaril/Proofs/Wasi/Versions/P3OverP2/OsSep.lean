module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Os
public import Silmaril.Wasi.Versions.P2OverP3.Sep.Thms

/-!
# Proofs: the OS image needs `PollDone`

`guestPlay` is a play of `p3OverP2` (computed by `Silmaril.Wasi.Versions.P2OverP3.session`): the
guest creates a stream `(1, 2)`, writes the byte `7` to `2` (`BLOCKED`: no reader yet), reads it
back itself from `1` (`COMPLETED 1` with the item `7`), hands `1` to `write-via-stream` (0.2
`get-stdout` answers `0`), joins `2` to a waitable set and waits: the event of `2` is the
`stream-write` event `COMPLETED 1` of the guest's own read. `osTrace3` counts it as a stdout byte,
since `2` is now a stdout writable end; the 0.2 host wrote nothing. The answers are typed for
`p2Ok`; the run is not `PollDone` (the write was answered `BLOCKED`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2OverP3 (session session_mem)

/-- A 0.3 call of the slice. -/
def q3 (f : FnName) (hf : f ∈ p3World.imports) (a : List Val) : (nsig p3World.imports).Op :=
  (⟨f, hf⟩, a)

/-- The guest writes `7`, reads it back, hands the stream to stdout and waits for the writer. -/
def guestCalls : List ((nsig p3World.imports).Op × List (Option (List Val))) :=
  [(q3 cStreamNew (by simp [p3World, canonFns]) [], []),
   (q3 cStreamWrite (by simp [p3World, canonFns]) [natV 2, bytesV [7]], []),
   (q3 cStreamRead (by simp [p3World, canonFns]) [natV 1, natV 1], []),
   (q3 stdoutWrite3 (by simp [p3World, wasiFns3_eq]) [natV 1], [some [.u32 0]]),
   (q3 cWsNew (by simp [p3World, canonFns]) [], []),
   (q3 cJoin (by simp [p3World, canonFns]) [natV 2, natV 5], []),
   (q3 cWait (by simp [p3World, canonFns]) [natV 5], [])]

/-- The session of `guestCalls` runs to its end. -/
theorem guestSession_isSome : (session body init guestCalls).isSome = true := by decide +kernel

/-- **The guest play.** -/
def guestPlay : List (Move (nsig P2.p2Command.imports) (nsig p3World.imports)) :=
  ((session body init guestCalls).get guestSession_isSome).1

/-- `guestPlay` is a play of `p3OverP2`. -/
theorem guestPlay_mem : guestPlay ∈ p3OverP2 := by
  obtain ⟨⟨ms, s'⟩, hs⟩ := Option.isSome_iff_exists.1 guestSession_isSome
  have hp : guestPlay = ms := by simp [guestPlay, hs]
  rw [hp]
  exact session_mem hs

/-- Its 0.2 answers are typed, its write was answered `BLOCKED`, the 0.3 image has the byte `7`
on the channel `1`, the 0.2 image none. -/
theorem guestPlay_facts : (hostView (wtrace guestPlay)).all P2.p2Ok = true ∧
    (retAsImp (wtrace guestPlay)).any blockedW = true ∧
    osTrace3 1 (retAsImp (wtrace guestPlay)) = [.writeEv 1 7] ∧
    P2.osTrace2 1 (hostView (wtrace guestPlay)) = [] := by
  decide +kernel

/-- **REFUTED without `PollDone`**: a play of `p3OverP2` whose 0.2 answers `p2Ok` accepts and
whose 0.3 image is not a prefix of its 0.2 image. -/
theorem p3OverP2_os_needs_pollDone : ∃ t ∈ p3OverP2,
    (∀ e ∈ hostView (wtrace t), P2.p2Ok e = true) ∧ ¬ PollDone (retAsImp (wtrace t)) ∧
      ¬ osTrace3 1 (retAsImp (wtrace t)) <+: P2.osTrace2 1 (hostView (wtrace t)) := by
  obtain ⟨h1, h2, h3, h4⟩ := guestPlay_facts
  refine ⟨guestPlay, guestPlay_mem, fun e he => List.all_eq_true.1 h1 e he, fun hpd => ?_, ?_⟩
  · obtain ⟨e, he, hb⟩ := List.any_eq_true.1 h2
    rw [hpd.2 e he] at hb
    cases hb
  · rw [h3, h4, List.prefix_nil]
    exact List.cons_ne_nil _ _

end Silmaril.Wasi.Versions.P3OverP2
