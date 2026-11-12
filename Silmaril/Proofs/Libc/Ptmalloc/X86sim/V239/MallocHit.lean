module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.MallocPath
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Frame

/-!
# ptmalloc x86sim, glibc 2.39: `__libc_malloc`'s tcache hit simulates `Local.tcacheGet`

`mallocTcacheHit239` (on `Str9Fs`) and `mallocTcacheHit239K` (on `Str9K`): from the entry of
`__libc_malloc (n)` with `HitEntry`, the run returns the payload `p` of `x.1.tcacheGet C i`
(`i = tcIdx n`) to the caller with the callee-saved registers restored, the machine represents the
new state `(l', surr, [p])`, and it wrote only the four stack slots and `tcache_get`'s three
cells. Any arena: the theorem never names `main_arena`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Data
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239

/-- The bin `__libc_malloc (n)` looks up (`csize2tidx (request2size n)`, as the code computes it). -/
def hitBin (n : Nat) : Nat := (tcIdx (BitVec.ofNat 64 n)).toNat

/-- **The entry of `__libc_malloc (n)` on its tcache-hit path**, at load base `base`, thread
pointer `tp`, TLS offset `off`, stack pointer `sp`, return address `ret`, registers `regs`. -/
structure HitEntry (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word)
    (m : MState) : Prop where
  loaded : Loaded m.memory (mallocAt base) mallocCode
  rip : m.core.rip = mallocAt base + BitVec.ofNat 64 0
  regsEq : ∀ r, m.core.read r = regs r
  rsp : regs .rsp = sp
  rdi : regs .rdi = BitVec.ofNat 64 n
  n63 : n < 2 ^ 63
  sp32 : 32 ≤ sp.toNat
  sp64 : sp.toNat + 8 < 2 ^ 64
  w : m.memory.Permitted .write (sp.toNat - 32) 32
  r : m.memory.Permitted .read (sp.toNat - 32) 32
  ret : m.memory.readBytes sp.toNat 8 = some (encodeWords [ret])
  /-- The stack window misses the code. -/
  code : ∀ i < 796, ¬ stk sp ((mallocAt base).toNat + i)
  /-- The GOT slot of `tcache`'s TLS offset (the image's relocation), apart from the stack. -/
  got : ∃ o, loadN m.memory (mallocAt base + 0x156648#64) 8 = some o ∧
    m.core.fsBase + o = BitVec.ofNat 64 (pin239.repAt base tp off).tls.tcache ∧
    Apart (mallocAt base + 0x156648#64).toNat 8 (sp.toNat - 32) (sp.toNat + 8)
  /-- The stack window `[sp - 32, sp + 8)` holds no byte the representation reads. -/
  stack : ∀ a, sp.toNat - 32 ≤ a → a < sp.toNat + 8 → ¬ RepTouches pin239.config (pin239.repAt base tp off) x a
  /-- The abstract hit: initialised, a tcache, the bin non-empty. -/
  init : x.1.shared.init = true
  hit : ∃ tc, x.1.thread.tcache = some tc ∧ hitBin n < pin239.config.tcacheBins ∧ tc.bins (hitBin n) ≠ []
  /-- `tcache_get`'s cells miss the surroundings, the code and the stack window. -/
  cells : FpApart (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n]))
    (envFrag pin239.config pin239.layout (pin239.repAt base tp off).env x.2.1) (mallocAt base) mallocCode.length
  cellsStack : ∀ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes,
    ¬ (sp.toNat - 32 ≤ a ∧ a < sp.toNat + 8)

theorem ofNat_lit_add {base a b : Nat} : BitVec.ofNat 64 (base + a) + BitVec.ofNat 64 b =
    BitVec.ofNat 64 (base + (a + b)) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]

set_option maxHeartbeats 8000000 in
/-- **`malloc (n)` served from the tcache** (glibc 2.39, `Str9Fs`). -/
theorem mallocTcacheHit239 (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    fsMach.Triple
      (fun m => LocalAt pin239.config (pin239.repAt base tp off) fsMach x m ∧
        HitEntry base tp off x n sp ret regs m)
      (fun m' => ∃ p l', x.1.tcacheGet pin239.config (hitBin n) = some (p, l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) fsMach (l', x.2.1, [p]) m' ∧
        m'.core.rip = ret ∧ m'.core.read .rax = BitVec.ofNat 64 p ∧
        m'.core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, m'.core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) := by
  intro m0 ⟨hLA, he⟩
  obtain ⟨o, hgot, hoff, hgotA⟩ := he.got
  obtain ⟨tc, htc, hi, hne⟩ := he.hit
  -- 1. the prologue (stack only)
  obtain ⟨mA, rA, ripA, rspA, rbpA, rbxA, frA, fsA, wwA, s0, s1, s2, s3⟩ :=
    prologue he.loaded he.rip ((he.regsEq _).trans he.rsp) he.sp32 he.w he.r he.code
  have hlA := loadedC_ww mallocCode_length he.loaded wwA he.code
  have LA := localAt_ww hLA wwA fun a ha => he.stack a (by unfold stk at ha; omega)
    (by unfold stk at ha; omega)
  -- the loads the checks make, from the representation
  obtain ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ := LA
  have kInit := cell_load (cell_byte0 (hfs ⟨(pin239.repAt base tp off).statics.mallocInitialized, 1,
    if x.1.shared.init then 1 else 0⟩ (by simp [sharedFrag])) (by simp)
    (by simp [he.init])) (by simp)
  have kTc := cell_load (hft (Cell.w (pin239.repAt base tp off).tls.tcache tc.addr) (by simp [threadFrag, htc]))
    (by simp [Cell.w])
  have kBins := cell_load (henv (Cell.w ((pin239.repAt base tp off).env.mp + (pin239.repAt base tp off).layout.mpTcacheBins) pin239.config.tcacheBins)
    (by simp [envFrag, mpConstFrag])) (by simp [Cell.w])
  simp only [Cell.w, he.init, ↓reduceIte] at kInit kTc kBins
  obtain ⟨kTc1, kTc2, -, -, kTc5⟩ := kTc
  have aInit : mallocAt base + 0x15da38#64 = BitVec.ofNat 64 (pin239.repAt base tp off).statics.mallocInitialized := by
    show BitVec.ofNat 64 (base + 0xad750) + BitVec.ofNat 64 0x15da38 =
      BitVec.ofNat 64 (base + 0x20b188)
    rw [ofNat_lit_add]
  have aBins : mallocAt base + 0x156a98#64 = BitVec.ofNat 64 ((pin239.repAt base tp off).env.mp + pin239.layout.mpTcacheBins) := by
    show BitVec.ofNat 64 (base + 0xad750) + BitVec.ofNat 64 0x156a98 =
      BitVec.ofNat 64 (base + 0x204180 + 0x68)
    rw [ofNat_lit_add, Nat.add_assoc]
  have hgotA' : loadN mA.memory (mallocAt base + 0x156648#64) 8 = some o :=
    ld_ww wwA (fun i hi hs => hgotA i hi ⟨hs.1, by unfold stk at hs; omega⟩) hgot
  have htc0 : BitVec.ofNat 64 tc.addr ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [toNat_ofNat_lt (by simpa using kTc5)] at h1
    exact (hwf.tcache tc htc).struct (by simpa using h1)
  have hmsb : (BitVec.ofNat 64 n).msb = false := by
    have := he.n63
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  -- 2. the checks (no writes)
  obtain ⟨mB, rB, ripB, r12B, rdxB, frB, fsB, memB⟩ :=
    checks (n := BitVec.ofNat 64 n) (off := o) (tc := BitVec.ofNat 64 tc.addr) hlA ripA
      (by rw [rbxA, he.regsEq, he.rdi]) hmsb (by rw [aInit]; exact kInit.1) hgotA'
      (by rw [fsA, hoff]; exact kTc1)
      htc0 (by rw [aBins]; exact kBins.1) (by have h64 : pin239.config.tcacheBins = 64 := rfl; simpa [hitBin, h64] using hi)
  have hidx : tcIdx (BitVec.ofNat 64 n) = BitVec.ofNat 64 (hitBin n) := by simp [hitBin]
  have hcells : FpApart (tcGetCells pin239.config (pin239.repAt base tp off).layout
      (x.1, x.2.1, [hitBin n])) (envFrag pin239.config (pin239.repAt base tp off).layout
      (pin239.repAt base tp off).env x.2.1) (mallocAt base) mallocCode.length := he.cells
  have hcs : ∀ a ∈ (tcGetCells pin239.config (pin239.repAt base tp off).layout
      (x.1, x.2.1, [hitBin n])).bytes, ¬ (sp.toNat - 32 ≤ a ∧ a < sp.toNat + 8) := he.cellsStack
  generalize hitBin n = i at hi hne hidx hcells hcs ⊢
  -- 3. the bin's count test (no writes)
  have hT : (tcacheFrag pin239.config (pin239.repAt base tp off).layout x.1.shared.key tc).Holds (memView mA.memory) :=
    Frag.holds_sub hft (tcacheFrag_sub htc)
  obtain ⟨kCnt, bCnt, -, -, vCnt⟩ := cell_load (hT _ (mem_tcacheFrag_count (key := x.1.shared.key) hi))
    (by simp [show pin239.config.tcacheCountWidth = 2 from rfl])
  simp only [show pin239.config.tcacheCountWidth = 2 from rfl, show pin239.layout.tcCounts = 0 from rfl] at kCnt bCnt vCnt
  have hlen0 : 0 < (tc.bins i).length := List.length_pos_iff.2 hne
  obtain ⟨mC, rC, ripC, rcxC, frC, fsC, memC⟩ :=
    countTest (tc := BitVec.ofNat 64 tc.addr) (idx := tcIdx (BitVec.ofNat 64 n))
      (cnt := BitVec.ofNat 64 (tc.bins i).length) (by rw [memB]; exact hlA) ripB rdxB r12B
      (by rw [memB, hidx, w_count]; exact kCnt)
      (by
        intro h0
        have h1 := congrArg BitVec.toNat h0
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1
        have : (tc.bins i).length < 2 ^ 16 := by simpa using vCnt
        rw [show (0 : BitVec 16).toNat = 0 from rfl] at h1
        omega)
  have hrcx : mC.core.read .rcx = BitVec.ofNat 64 (tc.bins i).length := by
    rw [rcxC]
    apply BitVec.eq_of_toNat_eq
    have : (tc.bins i).length < 2 ^ 16 := by simpa using vCnt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  -- 4. `tcache_get` (the generic block)
  have LC : LocalAt pin239.config (pin239.repAt base tp off) fsMach (x.1, x.2.1, [i]) mC :=
    localAt_args (localAt_mem ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ (by rw [memC, memB]))
  have hlC : Loaded mC.memory (mallocAt base) mallocCode := by rw [memC, memB]; exact hlA
  obtain ⟨mD, rD, ripD, frD, fsD, wwD, p, l', hget, LD, hlD, raxD⟩ :=
    tcGetCore tcShape239 mallocTcGet (mallocAt base) hA hR (x.1, x.2.1, [i]) mC LC
      ⟨hlC, tc, htc, hi, hne, by rw [frC _ (by decide), rdxB], by rw [frC _ (by decide), r12B, hidx]; rfl,
        hrcx, hcells⟩ (by rw [ripC])
  -- 5. the epilogue (reads the slots back)
  have rdD : ∀ {a : Nat} {bs : List Byte}, sp.toNat - 32 ≤ a → a + 8 ≤ sp.toNat + 8 →
      mA.memory.readBytes a 8 = some bs → mD.memory.readBytes a 8 = some bs := by
    intro a bs h1 h2 h
    refine rd_ww wwD (fun j hj hc => hcs _ hc ⟨by omega, by omega⟩) ?_
    rw [memC, memB]; exact h
  have hretA : mA.memory.readBytes sp.toNat 8 = some (encodeWords [ret]) :=
    rd_ww wwA (fun j hj hs => by unfold stk at hs; omega) he.ret
  have rspD : mD.core.read .rsp = sp - 0x38#64 := by
    rw [frD _ (by decide) (by decide) (by decide) (by decide), frC _ (by decide),
      frB _ (by decide) (by decide) (by decide) (by decide), rspA]
  obtain ⟨mE, rE, ripE, rspE, rbxE, r12E, r13E, rbpE, frE, fsE, memE⟩ :=
    epilogue hlD ripD rspD he.sp32 he.sp64 (rdD (by omega) (by omega) s3) (rdD (by omega) (by omega) s2)
      (rdD (by omega) (by omega) s1) (rdD (by omega) (by omega) s0) (rdD (by omega) (by omega) hretA)
  -- the footprint
  have wwE : m0.memory.WritesWithin mE.memory
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [i])).bytes) := by
    rw [memE]
    have h1 := wwA.mono (fun a h => Or.inl (b := a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [i])).bytes) h)
    have h2 := wwD.mono (fun a h => Or.inr (a := stk sp a) h)
    rw [memC, memB] at h2
    exact h1.trans h2
  refine ⟨mE, (((rA.trans rB).trans rC).trans rD).trans rE, ⟨p, l', hget, localAt_mem LD memE, ripE,
    ?_, rspE, ?_⟩, fun a ha => within_of_ww wwE a ha⟩
  · rw [frE _ (by decide) (by decide) (by decide) (by decide) (by decide), raxD]
  · intro r hr
    have h' : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
      simpa [Silmaril.X86.sysv64] using hr
    rcases h' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbxE, he.regsEq]
    · rw [rbpE, he.regsEq]
    · rw [r12E, he.regsEq]
    · rw [r13E, he.regsEq]
    all_goals
      rw [frE _ (by decide) (by decide) (by decide) (by decide) (by decide),
        frD _ (by decide) (by decide) (by decide) (by decide), frC _ (by decide),
        frB _ (by decide) (by decide) (by decide) (by decide),
        frA _ (by decide) (by decide) (by decide), he.regsEq]

/-- **`malloc (n)` served from the tcache, on `Str9K`** (the process machine; the path makes no
system call, so the kernel and its answers are untouched). -/
theorem mallocTcacheHit239K (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', x.1.tcacheGet pin239.config (hitBin n) = some (p, l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
        (projK s').core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  Triple.liftK (mallocTcacheHit239 hA hR base tp off x n sp ret regs)

/-- `mallocTcacheHit239K` with the representation step discharged (`repTcacheGet`). -/
theorem mallocTcacheHit239K' (hA : Task.algo.leafTcacheGet)
    (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin239.config (pin239.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', x.1.tcacheGet pin239.config (hitBin n) = some (p, l') ∧
        LocalAt pin239.config (pin239.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
        (projK s').core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin239.config pin239.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcacheHit239K hA repTcacheGet base tp off x n sp ret regs

end Silmaril.Libc.Ptmalloc.X86sim.V239
