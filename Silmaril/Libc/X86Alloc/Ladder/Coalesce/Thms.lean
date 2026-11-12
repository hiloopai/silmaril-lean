module

public import Silmaril.Libc.X86Alloc.Ladder.Coalesce.Defs
public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Libc.X86Alloc.Pinned.Coalesce
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitEntry
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit
import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree6
import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceRel

/-!
# Rung 06 (first fit with coalescing): results

The allocator state and tokens are rung 05's (`FirstFit.iface`, seen through `toIface`).

* `malloc_sat`: `malloc`'s 128 bytes are rung 05's, at the same address, so it meets
  `mallocSpecL FirstFit.iface` (hence the loose `mallocSpec`).
* `free_sat`: the coalescing `free` meets the loose `freeSpec` of `FirstFit.iface.toIface`: the
  address-ordered walk (`SPEC.loop`), the link, and both merges, each guarded by an
  address-equality check, so merged blocks are contiguous; no address-order invariant is needed.
* `init`: the loaded `.data` (identical to rung 05's) establishes the state.

* `malloc_sat_coal`, `free_sat_coal`, `init_coal`: against `coalRel`: `malloc` returns the first
  fit of the exact free list; `free` keeps *some* well-formed list (`free(NULL)` keeps it). The
  precise merge relation (address-ordered insertion with both merges) is open.

`FirstFit.ffCap`-liveness is not claimed: merging can absorb a block of the abstract free set into a
larger one, so `dealloc s _ _ = s` does not hold for this `free`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Coalesce

open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc

theorem malloc_sat :
    (mallocSpec FirstFit.iface.toIface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  (mallocSpecL_subH FirstFit.iface).sat
    Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.malloc_sat_coalesce

theorem free_sat :
    (freeSpec FirstFit.iface.toIface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree.free_sat

theorem init : layout.Init ⊢ₛ FirstFit.iface.toIface.mm :=
  entails_trans Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit.init
    (sexists_intro _ (entails_refl _))

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Coalesce.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Coalesce.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

theorem malloc_sat_coal :
    (mallocSpecR ifaceC).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree.malloc_sat_coal

theorem free_sat_coal :
    (freeSpecR ifaceC).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree.free_sat_coal

theorem init_coal : layout.Init ⊢ₛ ifaceC.mmS Silmaril.Libc.X86Alloc.Ladder.FirstFit.relS0 :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree.init_coal

end Silmaril.Libc.X86Alloc.Ladder.Coalesce
