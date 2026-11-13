module

public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V236
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V240
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeap
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSysMain

/-!
# ptmalloc end to end, glibc 2.36 and 2.40: the tcache hit of `malloc`, unconditional

`E2e.mallocTcache236` and `E2e.mallocTcache240` hold for any `SafeMF` invariant. With the body
obligations proved for every configuration (`Algo.bodyMalloc_cons` with `Algo.sysMainBody`,
`sysHeapBody`; `Algo.bodyFree`; their totality forms), `Algo.ptmalloc_safeMF_bodies` gives
`SafeMF` for the refinement invariant `RefInv` at each pin, so the 2.36 and 2.40 statements hold
from any world satisfying `RefInv`, as `E2e.mallocTcache239` does for 2.39: **`E2e.mallocTcache236_refInv`**,
**`E2e.mallocTcache240_refInv`**. (The load-time world's parameters are instantiated, since
`RefInv` does not mention it.) Data only: no new x86 proof.
-/

@[expose] public section

open Silmaril.X86 (MState Word Reg sysv64)
open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
open Silmaril.Libc.Ptmalloc.Versions (pin236 pin240 pin236_ok pin240_ok)
open Silmaril.Libc

namespace Silmaril.Libc.Ptmalloc.E2e

/-- `SafeMF` for `RefInv` at any configuration, from load time (all body obligations proved). -/
theorem safeMF_refInv (C : Config) (hC : C.Ok) (tid : Nat) :
    SafeMF C (ptmalloc C) tid (initWorld C 1 tid C.page ⟨fun _ => .refuse⟩) (RefInv C tid) :=
  ptmalloc_safeMF_bodies C hC 1 tid C.page ⟨fun _ => .refuse⟩ Nat.one_ne_zero (Nat.le_refl _)
    (Nat.mod_self _) (bodyMalloc_cons C (sysMainBody C) (sysHeapBody C)) (bodyFree C)
    (totalMalloc_cons C (sysMainTotal C) (sysHeapTotal C)) (totalFree C)

/-- **glibc 2.36 `__libc_malloc`, tcache hit, end to end, unconditional** (from any world with
`RefInv`). -/
theorem mallocTcache236_refInv (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin236.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin236.config (pin236.repAt base tp off) str9kMach x s ∧
        Versions.V236.HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin236.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin236.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache236 base tp off x n sp ret regs (safeMF_refInv _ pin236_ok tid) hI hl

/-- **glibc 2.40 `__libc_malloc`, tcache hit, end to end, unconditional** (from any world with
`RefInv`). -/
theorem mallocTcache240_refInv (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin240.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin240.config (pin240.repAt base tp off) str9kMach x s ∧
        Gcc13.HitEntry pin240 Versions.V240.mallocData240 base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin240.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin240.config (pin240.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin240.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin240.config pin240.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache240 base tp off x n sp ret regs (safeMF_refInv _ pin240_ok tid) hI hl

end Silmaril.Libc.Ptmalloc.E2e
