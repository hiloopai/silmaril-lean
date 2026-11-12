module

public import Silmaril.Libc.X86Alloc.Ladder.Never.Defs
public import Silmaril.Libc.X86Alloc.Pinned.Never
public import Silmaril.X86.Sep.Alloc.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.Never

/-!
# Rung 01 (`never`): results

* `malloc_sat`, `free_sat`: the gcc code (`xor %eax,%eax; ret` and `ret`) meets silmaril's
  `Iface.never` (the loose interface is satisfiable by a real binary; silmaril's own witness uses
  the hand-written `48 31 c0 c3`).
* `init`: the empty static state establishes `Iface.never.mm = strue`.
* `code_loaded`, `data_loaded`: the pinned executable loads the layout.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Never

open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

theorem malloc_sat :
    (mallocSpec Iface.never).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Never.malloc_sat

theorem free_sat :
    (freeSpec Iface.never).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Never.free_sat

theorem init : layout.Init ⊢ₛ Iface.never.mm := entails_strue _

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Never.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Never.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

end Silmaril.Libc.X86Alloc.Ladder.Never
