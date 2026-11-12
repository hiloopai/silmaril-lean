module

public import Silmaril.Elf.Link.Dyn.Crt.Defs
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Basic
public import Silmaril.Raw.Elf.Link.Dyn.Crt.ConstMain
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Dtors
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Extra
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Gate
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Image
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Init
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Run
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Start

/-! # The generic C runtime: theorems

The crt start-up and shutdown code (`_start`, `_init`, `frame_dummy`, `__do_global_dtors_aux`,
`_fini`, the callback gate) of a gcc or clang PIE, over any `Crt.Layout` that `Layout.ok` accepts:
`Silmaril.Raw.Elf.Link.Dyn.Crt.Run` composes them around a contract for `main`. -/
