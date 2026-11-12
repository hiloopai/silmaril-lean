module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Defs
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Basic
public import Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Tactic

/-! # Standard executables: theorems and tactics

(proofs in `Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.{Basic,Tactic}`)

* `StdExe.verified_iff : E.Verified ↔ Program.Verified E.bin libc ld E.spec E.tier lib E.env`
  (`Iff.rfl`), `StdExe.verified : E.ok = true → E.Main → E.Verified`;
* `StdExe.Verified.sat : E.Verified → (E.model conv).Sat (E.cli conv)` and through a level
  `StdExe.Verified.sat_lift`, `.sat_liftAll`;
* `Entry.of`, `GlibcView.entry/store/call`, `putc_inline_appended`, `puts_as_printf`;
* the tactics `at_main`, `main_returns`, `main_exits` and the Program API's steps (`mblock`,
  `mcallN`, `mret`, `mcanary`, `mloop`, …). -/
