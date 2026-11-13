module

public import Silmaril.X86.AbiFunction.LeafArith.Defs
public import Silmaril.X86.AbiFunction.Thms
public import Silmaril.X86.Ladder.LeafArith.Thms
public import Silmaril.X86.Ladder.Pinned.LeafArith.Thms
meta import Silmaril.X86.AbiFunction.LeafArith.Defs
/-!
# `sat_add_u32` inside the pinned ELF, and its contracts as an `AbiFunction`

* `satAdd_parsed` (`#guard`): `ofGccS` reads the body `satAdd.body` from the `gcc -S` text.
* `satAdd_bytes`, `satAdd_placed`: assembled at `0x401400`, the body is the 29 bytes of the
  transcribed region at offset `0x90` (`decide +kernel`).
* `satAdd_in_elf`: those bytes are what the pinned executable
  `examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` loads at `0x401400` in its `rx`
  segment (the existing binary tie `Pinned.leafArith_region`, sliced by `loadedAt_slice`).
  This is the "function inside the ELF" link: listing → bytes → ELF segment.
* `satAdd_sysv`, `satAdd_contract`: the System V judgement at that placement, from the
  existing `Ladder.LeafArith.sat_add_u32_total`.
* `satAdd_realizes`: the C-level judgement for `u32 sat_add_u32(u32, u32)`, from the existing
  `Ladder.LeafArith.sat_add_u32_realizes`.
* `gcd_assembles`, … (`#guard`): the four other functions of the region, parsed from `gccS`
  and assembled at their symbol addresses, are the region's bytes there (tests of the parser
  and assembler: relaxation, `.p2align` padding of 3 and 8 bytes, `div`, `cmov`, `lea`,
  `bswap`).

Trusted beyond the existing proofs: nothing new. The parser is checked by `#guard` (compiled
evaluation, a test, not a theorem); the theorems are about the term `satAdd`, whose bytes are
checked by the kernel.

Cost (Lean profiler, one run on the development machine): kernel type checking 0.20 s each
for `satAdd_bytes` and `satAdd_placed`, 0.52 s for the whole module; the six `#guard`s
evaluate in 0.21 s (interpreter). The contracts are term-mode transfers.
-/

@[expose] public section

namespace Silmaril.X86.AbiFunction.LeafArith

open Silmaril.X86.AbiFunction
open Silmaril.X86.Ladder.Pinned (LoadedAt sliceAt)

/-! ## The listing is what the compiler printed -/

-- `ofGccS` reads exactly `satAdd`'s body from the `gcc -S` text.
#guard (ofGccS Link.Abi.Conv.sysv64 Ladder.LeafArith.sigU2 "sat_add_u32" gccS).toOption.map
  (·.body) == some satAdd.body

/-! ## The listing is the bytes of the binary -/

/-- The body assembled at `0x401400` is the region's 29 bytes at offset `0x90`. -/
theorem satAdd_bytes :
    satAdd.bytesAt 0x401400 noSymbols = some ((Ladder.LeafArith.code.drop 0x90).take 29) := by
  decide +kernel

/-- `satAdd` is placed by `placement`. -/
theorem satAdd_placed : satAdd.placedIn noSymbols placement = true := by decide +kernel

/-- A slice of a loaded slice is loaded. -/
theorem loadedAt_slice {exe : Silmaril.X86.Link.Blob} {perms : String} {addr : Nat}
    {code : List (BitVec 8)} (h : LoadedAt exe perms addr code) (o n : Nat)
    (hn : o + n ≤ code.length) : LoadedAt exe perms (addr + o) ((code.drop o).take n) := by
  obtain ⟨r, hp, seg, hm, hperm, hs⟩ := h
  refine ⟨r, hp, seg, hm, hperm, ?_⟩
  unfold sliceAt at hs ⊢
  split at hs
  · rename_i hc
    have hlen : ((code.drop o).take n).length = n := by simp; omega
    rw [hlen]
    split
    · simp only [Option.some.injEq] at hs
      have hk : addr + o - seg.base = addr - seg.base + o := by omega
      rw [← hs, hk, List.drop_take, List.take_take, List.drop_drop]
      congr 2; omega
    · exfalso; omega
  · cases hs

/-- **`sat_add_u32` inside the ELF**: the body, assembled at its symbol address, is what the
pinned executable loads there. -/
theorem satAdd_in_elf :
    ∃ bs, satAdd.bytesAt 0x401400 noSymbols = some bs ∧
      LoadedAt Silmaril.X86.Ladder.Pinned.LeafArith.exe "rx" 0x401400 bs :=
  ⟨_, satAdd_bytes,
    loadedAt_slice Silmaril.X86.Ladder.Pinned.leafArith_region 0x90 29 (by decide +kernel)⟩

/-! ## The contracts -/

/-- **The System V contract of the `AbiFunction`**, from the existing proof about the pinned
bytes: no memory written, `rax = sat_add_u32(edi, esi)`. -/
theorem satAdd_sysv :
    SysV satAdd noSymbols placement (fun _ _ => False)
      (fun m t => t.core.read .rax =
        (Ladder.LeafArith.satAddSpec (Ladder.LeafArith.r32 .rdi m)
          (Ladder.LeafArith.r32 .rsi m)).setWidth 64) :=
  ⟨rfl, satAdd_placed, Ladder.LeafArith.sat_add_u32_total⟩

/-- The contract as a `FnContract` on the open machine. -/
def satAdd_contract : FnContract Open.isa := satAdd_sysv.toFnContract

/-- **The C-level judgement**: `satAdd` realizes `u32 sat_add_u32(u32, u32)`. -/
theorem satAdd_realizes :
    SysVRealizes satAdd noSymbols placement Ladder.LeafArith.satResult Ladder.LeafArith.noWrites :=
  ⟨rfl, satAdd_placed, Ladder.LeafArith.sat_add_u32_realizes⟩

/-! ## Assembler checks: the other functions of the region -/

#guard assemblesToPinned "gcd_u32"
#guard assemblesToPinned "clamp_i32"
#guard assemblesToPinned "isqrt_u32"
#guard assemblesToPinned "bswap32_manual"
#guard assemblesToPinned "sat_add_u32"

end Silmaril.X86.AbiFunction.LeafArith
