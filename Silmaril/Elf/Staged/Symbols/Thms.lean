module

public import Silmaril.Elf.Staged.Symbols.Defs
public import Silmaril.Elf.Check.Defs
import Silmaril.Proofs.Elf.Staged.Symbols

/-! # Symbol indexes: the checks and the lookups are sound

PROVED (standard axioms; `Silmaril.Proofs.Elf.Staged.Symbols`). -/

@[expose] public section

namespace Silmaril.Elf.Staged.Symbols

open Silmaril.Formats.ELF (NameBytes)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.X86.Link (Blob)

variable {F : Blob}

theorem byNameOk_sound {r : Src} (hs : Sub r F) {x : ByName} (h : byNameOk r x = true) :
    x.sorted = true ∧ x.Sound F :=
  Proofs.Elf.Staged.Symbols.byNameOk_sound hs h

theorem byAddrOk_sound {r : Src} (hs : Sub r F) {x : ByAddr} (h : byAddrOk r x = true) :
    x.sorted = true ∧ x.Sound F :=
  Proofs.Elf.Staged.Symbols.byAddrOk_sound hs h

/-- **A forward lookup names an entry with that name.** -/
theorem ByName.find_sound {x : ByName} (hx : x.Sound F) {n : NameBytes} {i : Nat}
    (h : x.find n = some i) : ∃ s, SymAt F x.t i s ∧ s.name = n :=
  hx _ (Proofs.Elf.Staged.Symbols.byName_find h)

/-- **A reverse lookup names an entry whose extent contains the address.** -/
theorem ByAddr.find_sound {x : ByAddr} (hx : x.Sound F) {v i : Nat} (h : x.find v = some i) :
    ∃ s, SymAt F x.t i s ∧ s.raw.value ≤ v ∧ v < s.raw.value + s.raw.size := by
  obtain ⟨e, he, h1, h2, rfl⟩ := Proofs.Elf.Staged.Symbols.byAddr_find h
  obtain ⟨s, hs, hv, hz⟩ := hx e he
  exact ⟨s, hs, hv ▸ h1, hv ▸ hz ▸ h2⟩

end Silmaril.Elf.Staged.Symbols
