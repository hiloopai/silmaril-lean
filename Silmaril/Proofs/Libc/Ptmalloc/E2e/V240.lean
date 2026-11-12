module

public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Inst
public import Silmaril.Proofs.Libc.Ptmalloc.E2e.Malloc
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.Malloc
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.TcPut

/-!
# ptmalloc end to end, glibc 2.40: data only

The 2.40 instances of `E2e.mallocTcache239_safe` and `E2e.freeTcache239_of`. Their per-version
content is data: `Versions.V240.mallocPin240` (decode facts of the 2.40 bytes and three `rfl`s
against `pin240`), fed to x86sim's generic gcc 13/14 path `X86sim.Gcc13.mallocTcacheHitK'`; the
glue is the version-generic `E2e.mallocTcache_post`/`freeTcache_post` and `E2e.hitBin_utidx`.

* **`mallocTcache240`**: glibc 2.40's `__libc_malloc (n)` on x86-64 (`Str9K`), any load base,
  thread pointer, TLS offset and arena, on a tcache hit, returns `p` with the callee-saved
  registers restored, writing only its stack window and `tcache_get`'s three cells; the model's
  `malloc` (`ptmalloc pin240.config`) returns the same `p`; the token state moves by
  `allocLoose` and keeps the `SafeMF` invariant. Conditional only through `hS`, as for 2.39.
* **`freeTcache240_of`**: the same for `__libc_free (p)`, from any machine triple simulating
  `_int_free` through `LocalAt` (2.40's put block is `Versions.V240.tcachePut240'`; the rest of
  free's x86 composition is open for 2.40 as for 2.39).
-/

@[expose] public section

open Silmaril.X86 (MState Word Reg sysv64)
open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
open Silmaril.Libc.Ptmalloc.X86sim.Gcc13
open Silmaril.Libc.Ptmalloc.Versions (pin240)
open Silmaril.Libc.Ptmalloc.Versions.V240 (mallocData240 mallocPin240)
open Silmaril.Libc

namespace Silmaril.Libc.Ptmalloc.E2e

theorem pin240_sizes : pin240.config.sizeSz = 8 ∧ pin240.config.align = 16 ∧
    pin240.config.minSize = 32 ∧ pin240.config.alignMask = 15 := by decide

/-- **glibc 2.40 `__libc_malloc`, tcache hit, end to end** (data only). -/
theorem mallocTcache240 (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin240.config (ptmalloc pin240.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some x.1) :
    str9kMach.Triple
      (fun s => LocalAt pin240.config (pin240.repAt base tp off) str9kMach x s ∧
        HitEntry pin240 mallocData240 base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', (ptmalloc pin240.config).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt pin240.config (pin240.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        ((projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
          (projK s').core.read .rsp = sp + 8#64 ∧
          ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r) ∧
        Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p))
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin240.config pin240.layout (x.1, x.2.1, [hitBin n])).bytes) := by
  intro s hs
  have he := hs.2
  have hn := he.n63
  obtain ⟨tc, htc, hb, -⟩ := he.hit
  obtain ⟨s', hr, ⟨p, l', hg, hL, hrip, hrax, hrsp, hcs⟩, hW⟩ :=
    mallocTcacheHitK' mallocPin240 Algo.leafTcacheGet base tp off x n sp ret regs s hs
  obtain ⟨h8, h16, h32, h15⟩ := pin240_sizes
  rw [hitBin_utidx h8 h16 h32 h15 hn] at hg hb
  obtain ⟨hm, hI', hrel⟩ := mallocTcache_post hS hI hn hl he.init (by simp [htc]) hb hg
  exact ⟨s', hr, ⟨p, l', hm, hL, ⟨hrip, hrax, hrsp, hcs⟩, hI', hrel⟩, hW⟩

/-- **glibc 2.40 `__libc_free`, tcache path, end to end, from its x86 simulation** (data only). -/
theorem freeTcache240_of {Pre : str9kMach.St → Prop} {fp : Nat → Prop} {R : str9kMach.St → Prop}
    (base tp off : Nat) (x : AState) (p : Nat)
    (hX : str9kMach.Triple Pre
      (fun s' => ∃ l', intFree pin240.config x.1 (p - pin240.config.hdr) = .ok l' ∧
        LocalAt pin240.config (pin240.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s') fp)
    {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF pin240.config (ptmalloc pin240.config) tid w0 Inv) {w : World} {h : Heap}
    (hI : Inv ⟨w, h⟩) {a : Nat} (hp : p ≠ 0) (hh : (h p).isSome = true)
    (hmm : Ops.mmapped? w (p - pin240.config.hdr) = none)
    (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w (p - pin240.config.hdr) = some a) (hl : w.local? tid a = some x.1) :
    str9kMach.Triple Pre
      (fun s' => ∃ l', (ptmalloc pin240.config).free w tid p = .ok (w.put tid l') ∧
        LocalAt pin240.config (pin240.repAt base tp off) str9kMach (l', x.2.1, []) s' ∧ R s' ∧
        Inv ⟨w.put tid l', h.remove p⟩ ∧ allocLoose h (.free p) (.ok (h.remove p) 0)) fp :=
  hX.conseq (fun _ hs => hs)
    (fun _ ⟨l', hf, hL, hR⟩ =>
      have ⟨hm, hI', hrel⟩ := freeTcache_post hS hI hp hh hmm htc ha hl hf
      ⟨l', hm, hL, hR, hI', hrel⟩)
    (fun _ ha => ha)

end Silmaril.Libc.Ptmalloc.E2e
