module

public import Silmaril.Proofs.Libc.Ptmalloc.E2e.V239
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeap
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSysMain

/-!
# ptmalloc end to end, glibc 2.39: the tcache paths conditional only on `sysmalloc`

`mallocTcache239_sys`, `freeTcache239_sys`: the `_bodies` theorems with `Task.algo.bodyFree`,
`totalFree` (`Algo.bodyFree`, `totalFree`) and `malloc_consolidate` (`Algo.consolidateBody`,
`consolidateTotal`) proved, so the only hypotheses left are `sysmalloc`'s main-arena and non-main
parts (`Task.algo.sysMainBody`, `sysHeapBody`, `sysMainTotal`, `sysHeapTotal`).

`mallocTcache239_main`, `freeTcache239_main`: the same with the non-main part proved
(`Algo.sysHeapBody`, `sysHeapTotal`), conditional only on `Task.algo.sysMainBody`, `sysMainTotal`.
`mallocTcache239_heap`, `freeTcache239_heap`: the main-arena part proved (`Algo.sysMainBody`,
`Algo.sysMainTotal`), so only the non-main part (`Task.algo.sysHeapBody`, `sysHeapTotal`) is left.

**`mallocTcache239`, `freeTcache239`** (the final forms): all four proved and the load-time
parameters of `initWorld` (main arena, break, kernel oracle) instantiated, since `RefInv` does not
mention the start world. Hypotheses: only the refinement invariant `RefInv` of the current world and
the entry conditions (`LocalAt` + `HitEntry`/`FreeEntry` in the precondition, and for `free` the
chunk being lent out, not mmapped, in a tcache-enabled thread, with its arena's body view `x.1`).
No `Task`, `SafeMF` or machine-simulation (`hX`) hypothesis.
-/

@[expose] public section

open Silmaril.X86 (MState Word Reg sysv64)
open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.V239
open Silmaril.Libc

namespace Silmaril.Libc.Ptmalloc.E2e

/-- **`mallocTcache239` from load time, conditional only on `sysmalloc`'s two parts**
(`Task.algo.{sysMainBody, sysHeapBody, sysMainTotal, sysHeapTotal}`): `mallocTcache239_bodies` with
`Algo.bodyMalloc_cons`, `Algo.totalMalloc_cons`, `Algo.bodyFree`, `Algo.totalFree`. -/
theorem mallocTcache239_sys
    (hM : Task.algo.sysMainBody pin239.config) (hH : Task.algo.sysHeapBody pin239.config)
    (htM : Task.algo.sysMainTotal pin239.config) (htH : Task.algo.sysHeapTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache239_bodies (bodyMalloc_cons _ hM hH) (bodyFree _) (totalMalloc_cons _ htM htH) (totalFree _)
    (o := o) hma hpg hbrk base tp off x n sp ret regs hI hl

/-- **`freeTcache239` from load time, conditional only on `sysmalloc`'s two parts**
(`Task.algo.{sysMainBody, sysHeapBody, sysMainTotal, sysHeapTotal}`): `freeTcache239_bodies` with
`Algo.bodyMalloc_cons`, `Algo.totalMalloc_cons`, `Algo.bodyFree`, `Algo.totalFree`. -/
theorem freeTcache239_sys
    (hM : Task.algo.sysMainBody pin239.config) (hH : Task.algo.sysHeapBody pin239.config)
    (htM : Task.algo.sysMainTotal pin239.config) (htH : Task.algo.sysHeapTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩) {a : Nat}
    (hh : (h (ch.addr + 16)).isSome = true)
    (hmm : Ops.mmapped? w ch.addr = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w ch.addr = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid (ch.addr + 16) = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', h.remove (ch.addr + 16)⟩ ∧
        allocLoose h (.free (ch.addr + 16)) (.ok (h.remove (ch.addr + 16)) 0))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  freeTcache239_bodies (bodyMalloc_cons _ hM hH) (bodyFree _) (totalMalloc_cons _ htM htH) (totalFree _)
    (o := o) hma hpg hbrk base tp off x ch sp ret regs hI hh hmm htc ha hl

/-- **`mallocTcache239` from load time, conditional only on `sysmalloc`'s main-arena part**
(`Task.algo.{sysMainBody, sysMainTotal}`; the non-main part is `Algo.sysHeapBody`, `sysHeapTotal`). -/
theorem mallocTcache239_main
    (hM : Task.algo.sysMainBody pin239.config) (htM : Task.algo.sysMainTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache239_sys hM (sysHeapBody _) htM (sysHeapTotal _)
    (o := o) hma hpg hbrk base tp off x n sp ret regs hI hl

/-- **`freeTcache239` from load time, conditional only on `sysmalloc`'s main-arena part**
(`Task.algo.{sysMainBody, sysMainTotal}`; the non-main part is `Algo.sysHeapBody`, `sysHeapTotal`). -/
theorem freeTcache239_main
    (hM : Task.algo.sysMainBody pin239.config) (htM : Task.algo.sysMainTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩) {a : Nat}
    (hh : (h (ch.addr + 16)).isSome = true)
    (hmm : Ops.mmapped? w ch.addr = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w ch.addr = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid (ch.addr + 16) = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', h.remove (ch.addr + 16)⟩ ∧
        allocLoose h (.free (ch.addr + 16)) (.ok (h.remove (ch.addr + 16)) 0))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  freeTcache239_sys hM (sysHeapBody _) htM (sysHeapTotal _)
    (o := o) hma hpg hbrk base tp off x ch sp ret regs hI hh hmm htc ha hl

/-- **`mallocTcache239` from load time, conditional only on `sysmalloc`'s non-main part**
(`Task.algo.{sysHeapBody, sysHeapTotal}`): `mallocTcache239_bodies` with
`Algo.bodyMalloc_heap`, `Algo.totalMalloc_heap`, `Algo.bodyFree`, `Algo.totalFree`. -/
theorem mallocTcache239_heap
    (hH : Task.algo.sysHeapBody pin239.config) (htH : Task.algo.sysHeapTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache239_bodies (bodyMalloc_heap _ hH) (bodyFree _) (totalMalloc_heap _ htH) (totalFree _)
    (o := o) hma hpg hbrk base tp off x n sp ret regs hI hl

/-- **`freeTcache239` from load time, conditional only on `sysmalloc`'s non-main part**
(`Task.algo.{sysHeapBody, sysHeapTotal}`): `freeTcache239_bodies` with
`Algo.bodyMalloc_heap`, `Algo.totalMalloc_heap`, `Algo.bodyFree`, `Algo.totalFree`. -/
theorem freeTcache239_heap
    (hH : Task.algo.sysHeapBody pin239.config) (htH : Task.algo.sysHeapTotal pin239.config)
    {ma tid brk : Nat} {o : KOracle} (hma : ma ≠ 0) (hpg : pin239.config.page ≤ brk)
    (hbrk : brk % pin239.config.page = 0)
    (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word) (regs : Reg → Word)
    {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩) {a : Nat}
    (hh : (h (ch.addr + 16)).isSome = true)
    (hmm : Ops.mmapped? w ch.addr = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w ch.addr = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid (ch.addr + 16) = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', h.remove (ch.addr + 16)⟩ ∧
        allocLoose h (.free (ch.addr + 16)) (.ok (h.remove (ch.addr + 16)) 0))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  freeTcache239_bodies (bodyMalloc_heap _ hH) (bodyFree _) (totalMalloc_heap _ htH) (totalFree _)
    (o := o) hma hpg hbrk base tp off x ch sp ret regs hI hh hmm htc ha hl

/-- **glibc 2.39 `__libc_malloc`, tcache hit, end to end, unconditional**: x86-64 code →
algorithm model → allocator institution, for any arena of the calling thread, from any world
satisfying the refinement invariant `RefInv`. `mallocTcache239_sys` with all four `sysmalloc` parts
proved (`Algo.sysMainBody`, `sysMainTotal`, `sysHeapBody`, `sysHeapTotal`). -/
theorem mallocTcache239
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word)
    {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcache239_sys (sysMainBody _) (sysHeapBody _) (sysMainTotal _) (sysHeapTotal _)
    (ma := 1) (brk := pin239.config.page) (o := ⟨fun _ => .refuse⟩) Nat.one_ne_zero (Nat.le_refl _)
    (Nat.mod_self _) base tp off x n sp ret regs hI hl

/-- **glibc 2.39 `__libc_free`, tcache path, end to end, unconditional**: x86-64 code → algorithm
model → allocator institution, for any arena, from any world satisfying `RefInv`: on the tcache
path of `free (ch.addr + 16)` (`FreeEntry`), the run returns to the caller with the callee-saved
registers restored, writing only its two stack frames and `tcache_put`'s cells; the model's `free`
makes the same step, and the token state moves by `allocLoose` keeping `RefInv`.
`freeTcache239_sys` with all four `sysmalloc` parts proved. -/
theorem freeTcache239
    (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word) (regs : Reg → Word)
    {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩) {a : Nat}
    (hh : (h (ch.addr + 16)).isSome = true)
    (hmm : Ops.mmapped? w ch.addr = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w ch.addr = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid (ch.addr + 16) = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        RefInv pin239.config tid ⟨w.put tid l', h.remove (ch.addr + 16)⟩ ∧
        allocLoose h (.free (ch.addr + 16)) (.ok (h.remove (ch.addr + 16)) 0))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
  freeTcache239_sys (sysMainBody _) (sysHeapBody _) (sysMainTotal _) (sysHeapTotal _)
    (ma := 1) (brk := pin239.config.page) (o := ⟨fun _ => .refuse⟩) Nat.one_ne_zero (Nat.le_refl _)
    (Nat.mod_self _) base tp off x ch sp ret regs hI hh hmm htc ha hl

end Silmaril.Libc.Ptmalloc.E2e
