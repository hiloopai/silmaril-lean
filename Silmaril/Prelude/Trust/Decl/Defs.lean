module

public import Init.Prelude

/-! # Procedure declarations (Init-only)

A library module declares a decision procedure with two backends, each a `Bool` checker with a
soundness theorem, without importing the trust machinery:

```
import Silmaril.Prelude.Trust.Decl.Defs

/-- The staged ELF layout: the claimed layout matches the file. -/
def Silmaril.Procedures.elf.layout : Silmaril.Trust.ProcDecl where
  doc := "Stage 1 ELF layout. Native: compiled fastRead over the ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.layoutOk, ``Silmaril.Elf.Staged.layoutOk_sound_fast⟩
  kernel := some ⟨``Silmaril.Elf.Staged.layoutOkK, ``Silmaril.Elf.Staged.layoutOkK_sound_pages⟩
```

When several procedures share one generic checker (`Leaf.native l b c` for every leaf `l`), set
`bound := some ``Leaf.layout``: every accepted check, and every native axiom counted for the
procedure, must then have that constant as a direct argument.

The procedure's name is the constant's name after `Silmaril.Procedures.` (`elf.layout`). Each
soundness theorem has the form `∀ xs, check as = true → P bs`, and both backends prove the
**same** `P`; their arguments may differ (a `ByteArray` against 4 KiB page literals). The
tactic `sil_check elf.layout (native := …) (kernel := …)` (`Silmaril.Prelude.Trust.Elab`)
checks the terms against this declaration and picks the backend the policy allows. The kernel
backend is only ever checked by the kernel. `#trust_dump` lists declared procedures.
-/

@[expose] public section

namespace Silmaril.Trust

/-- One backend: a `Bool`-valued checker and the theorem `∀ xs, check … = true → P …`. -/
structure Backend where
  check : Lean.Name
  sound : Lean.Name

/-- A named procedure with a native and a kernel backend proving the same proposition. -/
structure ProcDecl where
  doc : String
  /-- Runs compiled code (trusts the compiler and runtime). -/
  native : Option Backend := none
  /-- Checked by the kernel only. -/
  kernel : Option Backend := none
  /-- The data format, for format checkers (`elf`, `json`, …). -/
  format : Option Lean.Name := none
  /-- For checkers shared by many procedures (a generic runner applied to a leaf, as in
  `Leaf.native Leaf.layout b c`): a constant that must be a direct argument of every check this
  procedure accepts, so `elf.layout` cannot vouch for a run of another leaf. -/
  bound : Option Lean.Name := none

/-- The namespace that names procedures: `Silmaril.Procedures.elf.layout` is `elf.layout`. -/
def proceduresNamespace : Lean.Name := `Silmaril.Procedures

end Silmaril.Trust
