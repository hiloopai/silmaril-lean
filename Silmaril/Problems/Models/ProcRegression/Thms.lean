module

public import Silmaril.Problems.Models.ProcRegression.Defs
public import Silmaril.Problems.Models.Proc.Thms
import Silmaril.Proofs.Problems.Models.ProcRegression.Launch

/-!
# Regression tests for the static loader of `musl-str9` (erebor-lean #70)

* `table_static`: the test image's table is derived from its bytes and passes the checks.
* `ordinary_load`, `init_exists`: the ordinary launch is a launch of `Proc.model`
  (so the new loader is satisfiable), and startup reads the file's table there
  (`ordinary_headers`).
* `substitutedAddress_loose`, `substitutedCount_loose`, `extraExec_loose`: the loader
  before #70 (`Proc.LoadLoose`) accepts each substituted launch;
* `substitutedAddress_rejected`, `substitutedCount_rejected`, `extraExec_rejected`:
  `Proc.Load` rejects each of them.
-/

@[expose] public section

namespace Silmaril.Problems.Models.ProcRegression

open Silmaril.Process
open Silmaril.Process.CLI
open Silmaril.Problems.Models (Proc.Load Proc.LoadLoose)

theorem table_static : image.StaticTable table :=
  Silmaril.Proofs.Problems.Models.ProcRegression.table_static

theorem ordinary_load (stdin : List Byte) :
    Proc.Load image (input stdin) core (launchMemory ordinary []) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.ordinary_load stdin

/-- The descriptors of a filter reading `stdin`. -/
def descriptors (stdin : List Byte) : Nat → Option Syscall.Descriptor
  | 0 => some ⟨true, false, .ofList stdin, 0, []⟩
  | 1 | 2 => some ⟨false, true, .ofList [], 0, []⟩
  | _ => none

/-- **Nonvacuity of the static loader**: `Proc.model` has an initial state for this image
on every standard input. -/
theorem init_exists (stdin : List Byte) : ∃ x, Proc.model.Init image (input stdin) x :=
  ⟨⟨core, ⟨launchMemory ordinary [], descriptors stdin, none⟩⟩, launchMemory ordinary [],
    ordinary_load stdin, rfl, rfl, rfl, rfl, rfl⟩

/-- In the ordinary launch, the 112 bytes at `AT_PHDR = 0x400040` are readable and are the
file's two program headers. -/
theorem ordinary_headers (stdin : List Byte) :
    (launchMemory ordinary []).readBytes 0x400040 112 = some table.bytes := by
  obtain ⟨t, static, -, read, -⟩ := Proc.load_headers (ordinary_load stdin)
  rw [Image.StaticTable.unique static table_static] at read
  exact read

theorem substitutedAddress_loose (stdin : List Byte) :
    Proc.LoadLoose image (input stdin) core (launchMemory substitutedAddress []) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.loose rfl (by decide) (.inl rfl) stdin

theorem substitutedCount_loose (stdin : List Byte) :
    Proc.LoadLoose image (input stdin) core (launchMemory substitutedCount []) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.loose rfl (by decide) (.inl rfl) stdin

theorem extraExec_loose (stdin : List Byte) :
    Proc.LoadLoose image (input stdin) core (launchMemory ordinary [extraCode]) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.loose rfl (by decide) (.inr rfl) stdin

theorem substitutedAddress_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory substitutedAddress []) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.substitutedAddress_rejected stdin

theorem substitutedCount_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory substitutedCount []) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.substitutedCount_rejected stdin

theorem extraExec_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory ordinary [extraCode]) :=
  Silmaril.Proofs.Problems.Models.ProcRegression.extraExec_rejected stdin

end Silmaril.Problems.Models.ProcRegression
