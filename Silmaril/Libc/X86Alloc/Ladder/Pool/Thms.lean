module

public import Silmaril.Libc.X86Alloc.Ladder.Pool.Defs
public import Silmaril.Libc.X86Alloc.Pinned.Pool
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.Pool

/-!
# Rung 04 (`pool`): results

* `malloc_sat`, `free_sat`: the code meets the LIFO reference model `ref` on `Open.isa`.
* `init`: the loaded static state (all zero) is `([], 0)`: empty free list, no block handed out.
* `code_loaded`, `data_loaded`: the pinned executable loads the layout (kernel evaluation).
* `sim`: `ref` simulates the pool capacity model at `|free list| + (64 - next)`, on `next ≤ 64`
  with non-null free blocks.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Pool

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Pool.malloc_sat

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Pool.free_sat

/-- The initial state. -/
def s0 : ref.St := (([] : List Word), (0 : Nat))

theorem init : layout.Init ⊢ₛ iface.mmS s0 := Silmaril.Raw.Libc.X86Alloc.Ladder.Pool.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Pool.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Pool.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

theorem sim : ref.Sim cap α Inv := Silmaril.Raw.Libc.X86Alloc.Ladder.Pool.sim

theorem inv_s0 : Inv s0 := ⟨Nat.zero_le 64, fun _ h => absurd h List.not_mem_nil⟩

end Silmaril.Libc.X86Alloc.Ladder.Pool
