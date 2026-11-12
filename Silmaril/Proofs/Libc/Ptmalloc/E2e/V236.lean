module

public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Inst
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Malloc
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V236.MallocHit

/-!
# ptmalloc end to end, glibc 2.36

The 2.36 instances of `E2e.mallocTcache239_safe` and `E2e.freeTcache239_of`. gcc 12 compiled 2.36's
`__libc_malloc` with another frame and register allocation, so its non-heap blocks are new runs
(`Versions.V236.MallocRun`) and its composition is `Versions.V236.mallocTcacheHit236K'`; the
heap block is the generic, register-parametric `tcache_get` (`V236.mallocTcGet`, bin in `rbp`).
The glue is the version-generic `E2e.mallocTcache_post`/`freeTcache_post` and
`E2e.hitBin_utidx`. The model is `ptmalloc pin236.config` (2.36's quirks change `_int_malloc`'s
unsorted scan, realloc and the mmap fallback, not these paths).

* **`mallocTcache236`**: glibc 2.36's `__libc_malloc (n)` on x86-64 (`Str9K`), any load base,
  thread pointer, TLS offset and arena, on a tcache hit, returns `p` with the callee-saved
  registers restored, writing only its stack window and `tcache_get`'s three cells; the model's
  `malloc` returns the same `p`; the token state moves by `allocLoose` and keeps the `SafeMF`
  invariant. Conditional only through `hS`, as for 2.39.
* **`freeTcache236_of`**: the same for `__libc_free (p)`, from any machine triple simulating
  `_int_free` through `LocalAt` (2.36's `_int_free` inlines `tcache_put` in another instruction
  order, which `X86sim.TcPutSeq` does not cover; free's x86 composition is open).
-/

@[expose] public section

open Silmaril.X86 (MState Word Reg sysv64)
open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
open Silmaril.Libc.Ptmalloc.Versions (pin236)
open Silmaril.Libc.Ptmalloc.Versions.V236 (HitEntry mallocTcacheHit236K')
open Silmaril.Libc

namespace Silmaril.Libc.Ptmalloc.E2e

theorem pin236_sizes : pin236.config.sizeSz = 8 ∧ pin236.config.align = 16 ∧
    pin236.config.minSize = 32 ∧ pin236.config.alignMask = 15 := by decide

/-- **glibc 2.36 `__libc_malloc`, tcache hit, end to end.** -/
theorem mallocTcache236 (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin236.config (ptmalloc pin236.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin236.config (pin236.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin236.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes) := by
  intro s hs
  have he := hs.2
  have hn := he.n63
  obtain ⟨tc, htc, hb, -⟩ := he.hit
  obtain ⟨s', hr, ⟨p, l', hg, hL, hrip, hrax, hrsp, hcs⟩, hW⟩ :=
    mallocTcacheHit236K' Algo.leafTcacheGet base tp off x n sp ret regs s hs
  obtain ⟨h8, h16, h32, h15⟩ := pin236_sizes
  rw [hitBin_utidx h8 h16 h32 h15 hn] at hg hb
  obtain ⟨hm, hI', hrel⟩ := mallocTcache_post hS hI hn hl he.init (by simp [htc]) hb hg
  exact ⟨s', hr, ⟨p, l', hm, hL, ⟨hrip, hrax, hrsp, hcs⟩, hI', hrel⟩, hW⟩

/-- **glibc 2.36 `__libc_free`, tcache path, end to end, from its x86 simulation.** -/
theorem freeTcache236_of {Pre : str9kMach.St → Prop} {fp : Nat → Prop} {R : str9kMach.St → Prop}
    (base tp off : Nat) (x : AState) (p : Nat)
    (hX : str9kMach.Triple Pre
      (fun s' => ∃ l', intFree pin236.config x.1 (p - pin236.config.hdr) = .ok l' ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s') fp)
    {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin236.config (ptmalloc pin236.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) {a : Nat} (hp : p ≠ 0) (hh : (h p).isSome = true)
    (hmm : Ops.mmapped? w (p - pin236.config.hdr) = none)
    (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w (p - pin236.config.hdr) = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple Pre
      (fun s' => ∃ l', (ptmalloc pin236.config).free w tid p = .ok (w.put tid l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s' ∧
        Inv ⟨w.put tid l', h.remove p⟩ ∧ allocLoose h (.free p) (.ok (h.remove p) 0)) fp :=
  hX.conseq (fun _ hs => hs)
    (fun _ ⟨l', hf, hL, hR⟩ =>
      have ⟨hm, hI', hrel⟩ := freeTcache_post hS hI hp hh hmm htc ha hl hf
      ⟨l', hm, hL, hR, hI', hrel⟩)
    (fun _ ha => ha)

end Silmaril.Libc.Ptmalloc.E2e
