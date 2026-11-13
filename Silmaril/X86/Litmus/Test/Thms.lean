module

public import Silmaril.X86.Litmus.Test.Defs
public import Silmaril.X86.Litmus.Extract.Thms
import Silmaril.Proofs.X86.Litmus.Test

/-!
# The hand-built litmus tests: extraction computed by `decide`

For each hand-built test (`Test/Defs.lean`), the candidate per-thread traces of every thread,
extracted from the real thread bytes over the test's value domain, are computed by `decide`
(kernel-checked). With `extract_sound`, each of these traces replays on
`Atomic9.step`: `Hand.sb_sound`, ... (`Test.Sound`: extraction succeeds on every thread and
every trace replays), via `Test.sound_of_views`.

`x = 0x10000 = 65536`, `y = 0x10040 = 65600`.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

/-- **A test whose views compute is sound**: extraction succeeded on every thread, and every
extracted trace replays on `Atomic9.step`. -/
theorem Test.sound_of_views {T : Test} {v : List (List View)} (h : T.views = some v) :
    T.Sound :=
  Silmaril.Proofs.X86.Litmus.sound_of_views h

/-- **A `placed` test is non-vacuous.** -/
theorem Test.nonVacuous_of_placed {T : Test} (h : T.placed = true) : T.NonVacuous :=
  Silmaril.Proofs.X86.Litmus.nonVacuous_of_placed h

namespace Hand

/-- The bytes decode to the intended forms (`Atomic9.decode`). -/
theorem decode_forms :
    Atomic9.decode stX1 = some (.open9 (.ext8 (.base (.movI .d
      (.mem (absMem 0x10000#32)) 1#32))), 11) ∧
    Atomic9.decode ldEaxY = some (.open9 (.ext8 (.base (.load .d .rax (absMem 0x10040#32)))),
      7) ∧
    Atomic9.decode ldEbxX = some (.open9 (.ext8 (.base (.load .d .rbx (absMem 0x10000#32)))),
      7) ∧
    Atomic9.decode mfence = some (.new (.fence .mfence), 3) ∧
    Atomic9.decode lockXaddX =
      some (.new (.xadd .d true (.mem (absMem 0x10000#32)) .rax), 9) := by
  decide

/-- **SB**: each thread stores 1 and then reads 0 or 1. -/
theorem sb_views : sb.views = some
    [[⟨[st 65536 1, ld 65600 0], [0]⟩, ⟨[st 65536 1, ld 65600 1], [1]⟩],
     [⟨[st 65600 1, ld 65536 0], [0]⟩, ⟨[st 65600 1, ld 65536 1], [1]⟩]] := by
  decide

/-- **SB+mfences**: as SB, with an `mfence` event between the store and the load. -/
theorem sbMfences_views : sbMfences.views = some
    [[⟨[st 65536 1, mf, ld 65600 0], [0]⟩, ⟨[st 65536 1, mf, ld 65600 1], [1]⟩],
     [⟨[st 65600 1, mf, ld 65536 0], [0]⟩, ⟨[st 65600 1, mf, ld 65536 1], [1]⟩]] := by
  decide

/-- **MP**: the writer has one trace; the reader one per pair of read values. -/
theorem mp_views : mp.views = some
    [[⟨[st 65536 1, st 65600 1], []⟩],
     [⟨[ld 65600 0, ld 65536 0], [0, 0]⟩, ⟨[ld 65600 0, ld 65536 1], [0, 1]⟩,
      ⟨[ld 65600 1, ld 65536 0], [1, 0]⟩, ⟨[ld 65600 1, ld 65536 1], [1, 1]⟩]] := by
  decide

/-- **XADD2**: each `lock xadd` reads `v` and writes `v + 1`, and `eax` gets the old value. -/
theorem xadd2_views : xadd2.views = some
    [[⟨[lrmw 65536 0 1], [0]⟩, ⟨[lrmw 65536 1 2], [1]⟩, ⟨[lrmw 65536 2 3], [2]⟩],
     [⟨[lrmw 65536 0 1], [0]⟩, ⟨[lrmw 65536 1 2], [1]⟩, ⟨[lrmw 65536 2 3], [2]⟩]] := by
  decide

/-- **SB: extraction succeeds on every thread, and every trace replays.** -/
theorem sb_sound : Test.Sound sb := Test.sound_of_views sb_views

/-- **SB+mfences: extraction succeeds on every thread, and every trace replays.** -/
theorem sbMfences_sound : Test.Sound sbMfences := Test.sound_of_views sbMfences_views

/-- **MP: extraction succeeds on every thread, and every trace replays.** -/
theorem mp_sound : Test.Sound mp := Test.sound_of_views mp_views

/-- **XADD2: extraction succeeds on every thread, and every trace replays.** -/
theorem xadd2_sound : Test.Sound xadd2 := Test.sound_of_views xadd2_views

/-- **The replay hypotheses of the hand-built tests are satisfiable** (`decide`). -/
theorem hand_nonVacuous :
    sb.NonVacuous ∧ sbMfences.NonVacuous ∧ mp.NonVacuous ∧ xadd2.NonVacuous :=
  ⟨Test.nonVacuous_of_placed (by decide), Test.nonVacuous_of_placed (by decide),
    Test.nonVacuous_of_placed (by decide), Test.nonVacuous_of_placed (by decide)⟩

/-! ### Byte mutations: the events follow the bytes -/

/-- Dropping the `lock` prefix turns thread 0's events into **unlocked** `rmw`s. -/
theorem xadd2NoLock_views : xadd2NoLock.views = some
    [[⟨[⟨.rmw, 65536, 4, false, 0, 1⟩], [0]⟩, ⟨[⟨.rmw, 65536, 4, false, 1, 2⟩], [1]⟩,
      ⟨[⟨.rmw, 65536, 4, false, 2, 3⟩], [2]⟩],
     [⟨[lrmw 65536 0 1], [0]⟩, ⟨[lrmw 65536 1 2], [1]⟩, ⟨[lrmw 65536 2 3], [2]⟩]] := by
  decide

/-- Dropping the `mfence`s gives exactly SB's views (the fence events disappear). -/
theorem sbMfencesNoFence_views : sbMfencesNoFence.views = sb.views := by
  decide

/-- Changing the store's immediate byte changes the written value. -/
theorem sbImm2_views : sbImm2.views = some
    [[⟨[st 65536 2, ld 65600 0], [0]⟩, ⟨[st 65536 2, ld 65600 1], [1]⟩],
     [⟨[st 65600 1, ld 65536 0], [0]⟩, ⟨[st 65600 1, ld 65536 1], [1]⟩]] := by
  decide

/-- A load from an unreadable address aborts extraction (no vacuous traces). -/
theorem unmappedLoad_none : unmappedLoad.extractAll = none := by
  decide

/-- An unsupported memory form aborts extraction (no silently dropped events). -/
theorem addMem_none : addMem.extractAll = none := by
  decide

end Hand

end Silmaril.X86.Litmus
