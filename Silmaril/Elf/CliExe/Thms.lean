module

public import Silmaril.Elf.CliExe.Defs

/-! # CLI executables: theorems

* `CliExe.exeOk`, `CliExe.sat`: the two conjuncts of a row.
* `CliExe.mono`: a row transfers along an entailment of specifications.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Cli.Institution (Level Sen Model)

variable {V : Type} {exe : Silmaril.Project.Value V} {k : Kind} {ld : CliExe.Loading} {L : Level}
  {M : Silmaril.Formats.Bytes → Model L.sig} {φ ψ : Sen L.sig}

theorem CliExe.exeOk (h : CliExe exe k ld L M φ) : CliExe.ExeOk (Shapes.file exe) k ld := h.1

theorem CliExe.sat (h : CliExe exe k ld L M φ) : (M exe.bytes).Sat φ := h.2

/-- A row for `φ` is a row for every consequence `ψ` of `φ`. -/
theorem CliExe.mono (h : CliExe exe k ld L M φ) (hφψ : ∀ i o, φ i o → ψ i o) :
    CliExe exe k ld L M ψ :=
  ⟨h.1, fun i o hr => hφψ i o (h.2 i o hr)⟩

end Silmaril.Elf

end
