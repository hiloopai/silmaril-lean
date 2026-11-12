module

public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Inst
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocHit
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.FreePath
public import Silmaril.Libc.Ptmalloc.Version.Thms

/-!
# ptmalloc end to end, glibc 2.39: the tcache paths meet the allocator institution

* `hitBin_eq`: the bin `__libc_malloc`'s code computes (`tcIdx`, with `and $~0xf`) is the
  model's `pin239.config.utidx n` (closes x86sim's open arithmetic point).
* **`mallocTcache239_safe`**: `__libc_malloc (n)` on x86-64 (`Str9K`), at any load base, thread
  pointer and TLS offset, for **any** arena of the calling thread, from a state that represents
  the body view `x.1` of the world `w` (`LocalAt`) on a tcache hit (`HitEntry`), returns `p` to the
  caller with the callee-saved registers restored, writing only its stack window and
  `tcache_get`'s three cells, and
  - the model's `malloc` (`ptmalloc pin239.config`) returns the same `p` with world
    `w.put tid l'`, which the final machine state represents (`LocalAt`);
  - the ghost-token state moves by the institution's `allocLoose` relation and keeps the
    `SafeMF` invariant `Inv` (`AbsAlloc.SatOn Frag.mf … allocLoose` written out).
  It takes `hS : SafeMF …`; `Algo.ptmalloc_safeMF_init` gives it from load time given the open
  world-level Tasks (`Task.algo.wfWorld`, `mallocTotal`, `liveApart`, `tidsKept`). With
  `Inv := RefInv` the token state also satisfies `WorldWF`.
* **`freeTcache239_of`**: the same for `__libc_free (p)`, for **any** machine triple that
  simulates `_int_free` (`intFree`) through `LocalAt`.
* **`freeTcache239_safe`**: `freeTcache239_of` at x86sim's composition of free's tcache path
  (`V239.freeTcachePut239K'`: entry, checks, the `e->key` walk, the put block, the epilogues):
  `__libc_free (ch.addr + 16)` on x86-64 from `LocalAt` + `FreeEntry` is the model's `free` and
  an `allocLoose` step keeping `Inv`; conditional only through `hS`.
* **`mallocTcache239_load`, `freeTcache239_load`**: the two with `hS` discharged from load time
  (`Algo.ptmalloc_safeMF_of`, `Inv := RefInv`): conditional only on `Task.algo.wfWorld` and
  `Task.algo.mallocTotal`.

The unconditional forms `mallocTcache239`, `freeTcache239` (no `SafeMF`, no `Task`) are in
`Silmaril.Proofs.Libc.Ptmalloc.E2e.V239Sys`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

open Silmaril.X86 (MState Word Reg sysv64)
open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.V239
open Silmaril.Libc

namespace Silmaril.Libc.Ptmalloc.E2e

/-- `x &&& (2^64 - 16)` clears the low four bits. -/
theorem nat_and_mask16 (x : Nat) (hx : x < 2 ^ 64) : x &&& (2 ^ 64 - 16) = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h16 : (2 ^ 64 - 16 : Nat) = (2 ^ 60 - 1) * 2 ^ 4 := by decide
  have h16' : x / 16 * 16 = x / 2 ^ 4 * 2 ^ 4 := rfl
  rw [h16, h16', Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 4 ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.sub_add_cancel hi]
    by_cases h64 : i < 64
    · simp [show i - 4 < 60 by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

theorem pin239_sizes : pin239.config.sizeSz = 8 ∧ pin239.config.align = 16 ∧
    pin239.config.minSize = 32 ∧ pin239.config.alignMask = 15 := by decide

/-- **The code's tcache bin is the model's** (`csize2tidx (request2size n)` as gcc compiled it:
`lea 0x17(%rdi)`, `and $~0xf`, `sub $0x11`, `shr $4`, with the `MINSIZE` branch). -/
theorem hitBin_eq {n : Nat} (hn : n < 2 ^ 63) : hitBin n = pin239.config.utidx n := by
  obtain ⟨h8, h16, h32, h15⟩ := pin239_sizes
  have hadd : (BitVec.ofNat 64 n + 0x17#64).toNat = n + 23 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (0x17#64).toNat = 23 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold hitBin tcIdx Config.utidx Config.tidx Config.request2size
  rw [h8, h16, h32, h15, hadd]
  by_cases hs : n + 23 ≤ 0x1f
  · simp only [hs, ite_true, show n + 8 + 15 < 32 by omega]
    rfl
  · simp only [hs, ite_false, show ¬ n + 8 + 15 < 32 by omega]
    have hand : ((BitVec.ofNat 64 n + 0x17#64) &&& 0xfffffffffffffff0#64).toNat = (n + 23) / 16 * 16 := by
      rw [BitVec.toNat_and, hadd, show (0xfffffffffffffff0#64).toNat = 2 ^ 64 - 16 by rfl]
      exact nat_and_mask16 _ (by omega)
    have hsub : (((BitVec.ofNat 64 n + 0x17#64) &&& 0xfffffffffffffff0#64) - 0x11#64).toNat =
        (n + 23) / 16 * 16 - 17 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hand]; simp; omega), hand]
      rfl
    rw [BitVec.toNat_ushiftRight, hsub, Nat.shiftRight_eq_div_pow]
    omega

/-- **glibc 2.39 `__libc_malloc`, tcache hit, end to end**: x86-64 code → algorithm model →
allocator institution (`allocLoose`, ghost tokens), for any arena of the calling thread. -/
theorem mallocTcache239_safe (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin239.config (ptmalloc pin239.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) := by
  intro s hs
  have he := hs.2
  have hn := he.n63
  obtain ⟨tc, htc, hb, -⟩ := he.hit
  obtain ⟨s', hr, ⟨p, l', hg, hL, hrip, hrax, hrsp, hcs⟩, hW⟩ :=
    mallocTcacheHit239K' Algo.leafTcacheGet base tp off x n sp ret regs s hs
  rw [hitBin_eq hn] at hg hb
  obtain ⟨hm, hI', hrel⟩ := mallocTcache_post hS hI hn hl he.init (by simp [htc]) hb hg
  exact ⟨s', hr, ⟨p, l', hm, hL, ⟨hrip, hrax, hrsp, hcs⟩, hI', hrel⟩, hW⟩

/-- **glibc 2.39 `__libc_free`, tcache path, end to end, from its x86 simulation**: any machine
triple (`hX`) that simulates the model's `_int_free` of `p`'s chunk on the chunk's arena through
`LocalAt` is a run of the model's `free` and an institution step of the token state. -/
theorem freeTcache239_of {Pre : str9kMach.St → Prop} {fp : Nat → Prop} {R : str9kMach.St → Prop}
    (base tp off : Nat) (x : AState) (p : Nat)
    (hX : str9kMach.Triple Pre
      (fun s' => ∃ l', intFree pin239.config x.1 (p - pin239.config.hdr) = .ok l' ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s') fp)
    {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin239.config (ptmalloc pin239.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) {a : Nat} (hp : p ≠ 0) (hh : (h p).isSome = true)
    (hmm : Ops.mmapped? w (p - pin239.config.hdr) = none)
    (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w (p - pin239.config.hdr) = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple Pre
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid p = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s' ∧
        Inv ⟨w.put tid l', h.remove p⟩ ∧ allocLoose h (.free p) (.ok (h.remove p) 0)) fp :=
  hX.conseq (fun _ hs => hs)
    (fun _ ⟨l', hf, hL, hR⟩ =>
      have ⟨hm, hI', hrel⟩ := freeTcache_post hS hI hp hh hmm htc ha hl hf
      ⟨l', hm, hL, hR, hI', hrel⟩)
    (fun _ ha => ha)

/-- **glibc 2.39 `__libc_free`, tcache path, end to end**: x86-64 code → algorithm model →
allocator institution, for any arena of the calling thread. From a state that represents the
body view `x.1` of the chunk's arena (`LocalAt`) on the tcache path of `free (ch.addr + 16)`
(`FreeEntry`: a lent-out chunk not parked, a tcache bin with room), the run returns to the caller
with the callee-saved registers restored, writing only its two stack frames and `tcache_put`'s
four cells; the model's `free` makes the same step (`w.put tid l'`, represented by the final
state), and the token state moves by `allocLoose` keeping the `SafeMF` invariant. Conditional
only through `hS` (as `mallocTcache239_safe`). -/
theorem freeTcache239_safe (base tp off : Nat) (x : AState) (ch : Chunk) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin239.config (ptmalloc pin239.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) {a : Nat} (hh : (h (ch.addr + 16)).isSome = true)
    (hmm : Ops.mmapped? w ch.addr = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w ch.addr = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', (ptmalloc pin239.config).free w tid (ch.addr + 16) = .ok (w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        Inv ⟨w.put tid l', h.remove (ch.addr + 16)⟩ ∧
        allocLoose h (.free (ch.addr + 16)) (.ok (h.remove (ch.addr + 16)) 0))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) := by
  have hc : ch.addr + 16 - pin239.config.hdr = ch.addr := by
    show ch.addr + 16 - 16 = ch.addr
    omega
  have hX : str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        FreeEntry base tp off x ch sp ret regs (projK s))
      (fun s' => ∃ l', intFree pin239.config x.1 (ch.addr + 16 - pin239.config.hdr) = .ok l' ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r))
      (fun a => fstk sp a ∨ a ∈ (freeCells pin239.layout x ch).bytes) :=
    (freeTcachePut239K' base tp off x ch sp ret regs).conseq (fun _ hs => hs)
      (fun _ ⟨l', _, hf, hL, hrip, hrsp, hcs⟩ => ⟨l', by rw [hc]; exact hf, hL, hrip, hrsp, hcs⟩)
      (fun _ ha => ha)
  exact freeTcache239_of base tp off x (ch.addr + 16) hX hS hI (by omega) hh (by rw [hc]; exact hmm)
    htc (by rw [hc]; exact ha) hl

/-- **glibc 2.39 `__libc_malloc`, small-bin hit, end to end, from its x86 simulation**: any `Str9K`
triple (`hX`) that simulates the model's small-bin path (`mallocSmall`: `last (bin)` lent out and
the tcache refill) on `main_arena`'s body view through `LocalAt`, for a single-threaded process
whose thread misses in its tcache, is a run of the model's `malloc` and an institution step. The
x86 composition (`__libc_malloc`'s miss, `_int_malloc`'s small-bin code, the refill loop, the
epilogues) is the open x86sim step. -/
theorem mallocSmall239_of {Pre R : str9kMach.St → Prop} {fp : Nat → Prop} (base tp off : Nat)
    (x : AState) (n nb : Nat)
    (hX : str9kMach.Triple Pre (fun s' => ∃ p l', mallocSmall pin239.config x.1 nb = some (p, l') ∧
      LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧ R s') fp)
    {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin239.config (ptmalloc pin239.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) {l0 : Local} (hi : w.shared.init = true)
    (htc : (w.threads tid).tcache.isSome = true)
    (hcr : pin239.config.checkedRequest2size n = some nb)
    (hl0 : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l0)
    (hmiss : (if pin239.config.tidx nb < pin239.config.tcacheBins then
      l0.tcacheGet pin239.config (pin239.config.tidx nb) else none) = none)
    (hsingle : w.single = true) (hl : w.local? tid w.mainArena = some x.1)
    (hfast : nb ≤ pin239.config.maxFast → mallocFast pin239.config x.1 nb = .ok none)
    (hsr : pin239.config.inSmallRange nb = true) :
    str9kMach.Triple Pre
      (fun s' => ∃ p l', (ptmalloc pin239.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧ R s' ∧
        Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p)) fp :=
  mallocSmall_of x n nb hX hS hI hi htc hcr hl0 hmiss hsingle hl hfast hsr

/-- **`mallocTcache239` from load time**: `SafeMF` from `Algo.ptmalloc_safeMF_of` started in
`initWorld` with `Inv := RefInv`; conditional only on `Task.algo.wfWorld` and `mallocTotal`. -/
theorem mallocTcache239_load
    (hwf : Task.algo.wfWorld pin239.config (ptmalloc pin239.config))
    (htot : Task.algo.mallocTotal pin239.config (ptmalloc pin239.config))
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
  mallocTcache239_safe base tp off x n sp ret regs
    (ptmalloc_safeMF_of pin239.config pin239_ok ma tid brk o hma hpg hbrk hwf htot) hI hl

/-- **`freeTcache239` from load time**: as `mallocTcache239_load`; conditional only on
`Task.algo.wfWorld` and `mallocTotal`. -/
theorem freeTcache239_load
    (hwf : Task.algo.wfWorld pin239.config (ptmalloc pin239.config))
    (htot : Task.algo.mallocTotal pin239.config (ptmalloc pin239.config))
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
  freeTcache239_safe base tp off x ch sp ret regs
    (ptmalloc_safeMF_of pin239.config pin239_ok ma tid brk o hma hpg hbrk hwf htot) hI hh hmm htc ha hl

/-- **`mallocTcache239` from load time, conditional only on the body obligations**
(`Task.algo.{bodyMalloc, bodyFree, totalMalloc, totalFree}`): `wfWorld` and `mallocTotal` are
discharged by `Algo.wfWorld_of` and `Algo.mallocTotal_of`. -/
theorem mallocTcache239_bodies
    (hB : Task.algo.bodyMalloc pin239.config) (hF : Task.algo.bodyFree pin239.config)
    (htM : Task.algo.totalMalloc pin239.config) (htF : Task.algo.totalFree pin239.config)
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
  mallocTcache239_load (wfWorld_of _ hB hF) (mallocTotal_of _ hB htM htF) (o := o) hma hpg hbrk base tp off x n
    sp ret regs hI hl

/-- **`freeTcache239` from load time, conditional only on the body obligations.** -/
theorem freeTcache239_bodies
    (hB : Task.algo.bodyMalloc pin239.config) (hF : Task.algo.bodyFree pin239.config)
    (htM : Task.algo.totalMalloc pin239.config) (htF : Task.algo.totalFree pin239.config)
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
  freeTcache239_load (wfWorld_of _ hB hF) (mallocTotal_of _ hB htM htF) (o := o) hma hpg hbrk base tp
    off x ch sp ret regs hI hh hmm htc ha hl

end Silmaril.Libc.Ptmalloc.E2e
