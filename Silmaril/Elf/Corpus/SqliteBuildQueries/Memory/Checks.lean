module

public import Silmaril.Elf.Corpus.SqliteBuildQueries.Memory.Thms
import Silmaril.X86.Open.Thms

/-! # Non-vacuity and boundary regressions for the getter

This tiny placement witnesses the direct-call interface, not an OS loader.
The file-backed theorem uses `RoLoaded` instead. RSP points to the caller slot,
not an argument to the build-option getter.
-/

namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Memory.Checks

open Silmaril.Process
open Silmaril.X86
open Silmaril.Machine.LittleEndian (encodeWords)

private def fixture (width : Nat) : MState where
  core := ⟨fun reg => if reg = .rsp then 32 else 0, 0, ⟨none, none, none, none, none, none⟩, 0⟩
  memory := ⟨[⟨0, 6, ⟨true, false, true⟩⟩, ⟨32, width, ⟨true, true, false⟩⟩],
    Process.Memory.install (Process.Memory.install ∅ 0 Getter.threadsafe.code) 32 (encodeWords [96])⟩

private theorem code (width : Nat) : Ext.Loaded (fixture width).memory 0 Getter.threadsafe.code := by
  apply Process.Memory.readWith_eq _ .execute 0 _ (by rfl)
  intro index bound
  change (Process.Memory.install _ 32 _).get? (0 + index) = _
  rw [Process.Memory.install_outside _ _ _ _ (.inl (by change index < 6 at bound; omega))]
  exact Process.Memory.install_get _ 0 _ index bound

private theorem slot : (stackRead (fixture 8)).read = some (encodeWords [96]) :=
  Process.Memory.readWith_eq (fixture 8).memory .read 32 (encodeWords [96]) (by decide +kernel)
    (fun index bound => Process.Memory.install_get _ 32 _ index bound)

example : (machine MemoryModel.Lattice.xl).wp (returns 96) (fixture 8) := wp_of_fetched (code 8) slot

example : Machine.Execution.run Open.step 2 (fixture 7) = none := by
  let next : MState := ⟨{ (fixture 7).core.write .rax 1 with rip := 5 }, (fixture 7).memory⟩
  have mov : Open.step (fixture 7) = some next :=
    Open.step_of_listed (o := 0) (l := 5) (i := .base (.movI32 .rax 1)) (code 7)
      rfl (by decide) (by decide +kernel) rfl
  have fetch : Ext.fetch next.memory 5 = .decoded .ret 1 := Ext.fetch_eq_decoded_iff.mpr
    ⟨_, (code 7).fetchBytes_sub (offset := 5) (len := 1) (by decide) (by decide), by decide +kernel⟩
  have fault : Open.step next = none := by
    simp only [Open.step, show next.core.rip.toNat = 5 from rfl, Ext8.fetch, fetch]
    rfl
  simp only [Machine.Execution.run, mov, Option.bind_some, fault, Option.bind_none]

/-- Removing provenance/bounds is not invertible: this flat slot succeeds but a subobject ends at byte 7. -/
example : (stackRead (fixture 8)).read = some (encodeWords [96]) ∧
    (BlockRead.Request.mk (fun _ : Unit => some ((encodeWords [96]).take 7)) () 0 8).read = none := ⟨slot, rfl⟩

example : (BlockRead.Request.mk (fun _ : Unit => none) () 0 1).read = none := rfl

example : (BlockRead.Request.mk (fun _ : Unit => some [0, 1, 2, 3]) () 1 2).read = some [1, 2] := rfl

end Silmaril.Elf.Corpus.SqliteBuildQueries.Memory.Checks
