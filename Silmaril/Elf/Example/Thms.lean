module

public import Silmaril.Elf.Facts.Defs

/-! # Worked examples: two tiny files, parsed by the kernel

`relObj` is a bare ELF64 header (`ET_REL`, no tables); `tinyPie` is an `ET_DYN` file with a
`PT_DYNAMIC` holding `DT_FLAGS_1 = DF_1_PIE` and a `PT_INTERP` (`"x"`), so a PIE. Each fact is
closed by `decide +kernel` on the reader `Silmaril.Elf.read`: the specification runs as is on a
small file. (Large files go through pages and the checker `Check.file`.)
-/

@[expose] public section

namespace Silmaril.Elf.Example

open Silmaril.X86.Link (Blob)

/-- A bare `ET_REL` header (64 bytes). -/
def relObj : Blob := ⟨3048582569289050005682646232698498975886072932186739342977404068005836274434714312211680184060448529236993091396050627871820693929782963619199, 64⟩

/-- A 210-byte PIE: header, `PT_DYNAMIC`, `PT_INTERP`, the dynamic entries, `"x"`. -/
def tinyPie : Blob := ⟨98422418118196858478457577004104141228653544812303138285708035557027469147427365473228455554317989029873767913783990416763670525104037172689088640828300279147509771205758488575683879494596468287820530264271228614322729569086149558285792352079088521792412717167977752533793851687089233325545862188207383713370501008197712574327670052160197604505195544449979596383551108247742170663211110152461373433854556854966027670647282327601843470188782518459100510099843412377355700485917578296541778979851988649343, 210⟩

theorem relObj_kind : (parse relObj).map File.kind = some .relocatable := by decide +kernel

theorem tinyPie_kind : (parse tinyPie).map File.kind = some .pie := by decide +kernel

theorem tinyPie_interp : (parse tinyPie).map File.interp = some (some (nameOf "x")) := by
  decide +kernel

/-- The fact form: `KindIs`, from the computed parse. -/
theorem tinyPie_kindIs : KindIs tinyPie .pie := by
  obtain ⟨A, hA⟩ : ∃ A, parse tinyPie = some A := ⟨_, (Option.some_get (by decide +kernel)).symm⟩
  refine ⟨A, hA, ?_⟩
  have h := tinyPie_kind
  rw [hA] at h
  exact Option.some.inj h

end Silmaril.Elf.Example
