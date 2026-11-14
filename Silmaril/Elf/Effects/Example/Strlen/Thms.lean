module

public import Silmaril.Elf.Effects.Example.Strlen.Defs
public import Silmaril.X86.Flow.Thms

/-!
# glibc 2.39 `strlen`: CFGs and effects

The IFUNC resolver of `strlen` (`0xb4dc0`) and the four implementations it selects (`0xc1a10`
SSE2, `0x18bac0` AVX2, `0x194580` AVX2 with RTM, `0x19bc40` EVEX) of the pinned
`libc.so.6` (Ubuntu 2.39-0ubuntu8.9, sha256 `3a15d668…98bf`, as `Silmaril.Libc.SysWrap.Glibc.V239`).

* Each CFG is exact (`cfg_is`, by `decide` over the bytes).
* The certificate checks with all five entries as roots, and its reachable nodes are the five
  functions: **no calls, no imports, no system calls**.
* `sse2_syscalls`: every run of the SSE2 implementation, in every admissible world, makes no
  system call and enters no import (`SyscallSet … [] []`, `ForeignCalls … []`). The remaining
  hypotheses are the `CodeAt` rows of the blocks (that the bytes are the file's at their
  addresses), and the world's frame conditions inside `Admissible`.
-/

@[expose] public section

namespace Silmaril.Elf.Effects.Example.Strlen

open Silmaril.X86.Flow (X64.dec UMach)
open Silmaril.Elf.Effects.Shapes
open Silmaril.Project (Value)
open Silmaril.Elf.Shapes (file)

theorem resolver_exact : g_b4dc0.exact X64.dec = true := by decide
theorem sse2_exact : g_c1a10.exact X64.dec = true := by decide
theorem avx2_exact : g_18bac0.exact X64.dec = true := by decide
theorem avx2_rtm_exact : g_194580.exact X64.dec = true := by decide
theorem evex_exact : g_19bc40.exact X64.dec = true := by decide

theorem check : cert.check X64.dec roots = true := by decide
theorem closed : cert.graph.closedB nodes = true := by decide

/-- The SSE2 implementation's certificate facts, given the `CodeAt` rows. -/
theorem sse2_ok {V : Type} (X : Value V)
    (hcode : ∀ f C, (f, C) ∈ cert.fns → ∀ b ∈ C.blocks,
      Silmaril.Elf.Link.ElfBind.CodeAt (file X) b.start b.bytes) :
    CertOk X64.dec X (.addr 0xc1a10) cert [] 0xc1a10 nodes :=
  ⟨Silmaril.X86.Flow.X64.stable, fun _ h => h, by decide, hcode, closed, by decide, by decide⟩

/-- **The SSE2 `strlen` makes no system call.** -/
theorem sse2_syscalls {σ V : Type} (J : UMach σ) (X : Value V)
    (hcode : ∀ f C, (f, C) ∈ cert.fns → ∀ b ∈ C.blocks,
      Silmaril.Elf.Link.ElfBind.CodeAt (file X) b.start b.bytes) :
    SyscallSet J X64.dec X (.addr 0xc1a10) cert [] [] [] :=
  syscallSet_of_cert (sse2_ok X hcode) (by decide)

/-- **The SSE2 `strlen` enters no import.** -/
theorem sse2_foreign {σ V : Type} (J : UMach σ) (X : Value V)
    (hcode : ∀ f C, (f, C) ∈ cert.fns → ∀ b ∈ C.blocks,
      Silmaril.Elf.Link.ElfBind.CodeAt (file X) b.start b.bytes) :
    ForeignCalls J X64.dec X (.addr 0xc1a10) cert [] [] :=
  foreignCalls_of_cert (sse2_ok X hcode)

end Silmaril.Elf.Effects.Example.Strlen
