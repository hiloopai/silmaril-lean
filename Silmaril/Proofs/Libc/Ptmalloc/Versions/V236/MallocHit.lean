module

public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V236.MallocRun
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Frame
public import Silmaril.Libc.Ptmalloc.Version.Thms

/-!
# ptmalloc versions, glibc 2.36: `__libc_malloc`'s tcache hit simulates `Local.tcacheGet`

`mallocTcacheHit236` (on `Str9Fs`) and `mallocTcacheHit236K`/`…K'` (on `Str9K`): glibc 2.36's
`__libc_malloc (n)`, loaded at `base + 0x98930`, from its entry with `HitEntry`, returns the
payload `p` of `x.1.tcacheGet C (hitBin n)` to the caller with the callee-saved registers
restored, the machine represents `(l', surr, [p])`, and the run wrote only the stack slots and
`tcache_get`'s three cells. Any arena, any load base, thread pointer and TLS offset.

The heap reasoning is the generic `X86sim.tcGetCore` at `V236.mallocTcGet` (bin in `rbp`; the
register-parametric sequence of finding V1-F3); the non-heap blocks are 2.36's own runs
(`V236.MallocRun`: gcc 12's three-push frame).
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
open Silmaril.Libc.Ptmalloc.X86sim.Malloc
namespace Silmaril.Libc.Ptmalloc.Versions.V236

/-- `__libc_malloc`'s address at load base `base`. -/
def mallocAt (base : Nat) : Word := BitVec.ofNat 64 (base + pin236.entries.malloc)

/-- glibc 2.36 has the x86-64 tcache shape. -/
theorem tcShape236 : TcShape pin236.config pin236.layout := ⟨pin236_ok, rfl, rfl, rfl, rfl⟩

/-- The located copies of `tcache_get` in glibc 2.36 (`__libc_malloc`'s, bin in `rbp`). -/
def tcGetCopies (base tp off : Nat) : List (Block str9kMach AState) :=
  [liftBlock (tcGetBlock pin236.config (pin236.repAt base tp off) mallocCode (mallocAt base) 333
    .rbp 4 4)]

/-- **`Task.sim.tcacheGet` for glibc 2.36** (its located copies), from the leaf lemmas of
layers (b) and (c), with no new simulation proof: the register-parametric `tcGetSim`. -/
theorem tcacheGet236 (hA : Task.algo.leafTcacheGet) (base tp off : Nat) :
    Task.sim.tcacheGet pin236.config (pin236.repAt base tp off) str9kMach (tcGetCopies base tp off) := by
  intro b hb
  simp only [tcGetCopies, List.mem_singleton] at hb
  subst hb
  exact BlockSim.liftK (fun a x => localAt_k _ _ a x) (tcGetSim tcShape236 mallocTcGet _ hA repTcacheGet)

/-- **The entry of `__libc_malloc (n)` on its tcache-hit path**, at load base `base`, thread
pointer `tp`, TLS offset `off`, stack pointer `sp`, return address `ret`, registers `regs`. -/
structure HitEntry (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word)
    (regs : Reg → Word) (m : MState) : Prop where
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
  code : ∀ i < 791, ¬ stk sp ((mallocAt base).toNat + i)
  /-- The GOT slot of `tcache`'s TLS offset (the image's relocation), apart from the stack. -/
  got : ∃ o, loadN m.memory (mallocAt base + 0x13a448#64) 8 = some o ∧
    m.core.fsBase + o = BitVec.ofNat 64 (pin236.repAt base tp off).tls.tcache ∧
    X86sim.Apart (mallocAt base + 0x13a448#64).toNat 8 (sp.toNat - 32) (sp.toNat + 8)
  /-- The stack window `[sp - 32, sp + 8)` holds no byte the representation reads. -/
  stack : ∀ a, sp.toNat - 32 ≤ a → a < sp.toNat + 8 → ¬ RepTouches pin236.config (pin236.repAt base tp off) x a
  /-- The abstract hit: initialised, a tcache, the bin non-empty. -/
  init : x.1.shared.init = true
  hit : ∃ tc, x.1.thread.tcache = some tc ∧ hitBin n < pin236.config.tcacheBins ∧ tc.bins (hitBin n) ≠ []
  /-- `tcache_get`'s cells miss the surroundings, the code and the stack window. -/
  cells : FpApart (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n]))
    (envFrag pin236.config pin236.layout (pin236.repAt base tp off).env x.2.1) (mallocAt base) mallocCode.length
  cellsStack : ∀ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes,
    ¬ (sp.toNat - 32 ≤ a ∧ a < sp.toNat + 8)

set_option maxHeartbeats 8000000 in
/-- **`malloc (n)` served from the tcache** (glibc 2.36, `Str9Fs`). -/
theorem mallocTcacheHit236 (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet) (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    fsMach.Triple
      (fun m => LocalAt pin236.config (pin236.repAt base tp off) fsMach x m ∧
        HitEntry base tp off x n sp ret regs m)
      (fun m' => ∃ p l', x.1.tcacheGet pin236.config (hitBin n) = some (p, l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) fsMach (l', x.2.1, [p]) m' ∧
        m'.core.rip = ret ∧ m'.core.read .rax = BitVec.ofNat 64 p ∧
        m'.core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, m'.core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes) := by
  intro m0 ⟨hLA, he⟩
  obtain ⟨o, hgot, hoff, hgotA⟩ := he.got
  obtain ⟨tc, htc, hi, hne⟩ := he.hit
  -- 1. the prologue (stack only)
  obtain ⟨mA, rA, ripA, rspA, rbxA, frA, fsA, wwA, s0, s1, s2⟩ :=
    prologue he.loaded he.rip ((he.regsEq _).trans he.rsp) he.sp32 he.w he.r (by rw [mallocCode_length]; exact he.code)
  have hlA := loadedC_ww mallocCode_length he.loaded wwA he.code
  have LA := localAt_ww hLA wwA fun a ha => he.stack a (by unfold stk at ha; omega)
    (by unfold stk at ha; omega)
  -- the loads the checks make, from the representation
  obtain ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ := LA
  have kInit := cell_load (cell_byte0 (hfs ⟨(pin236.repAt base tp off).statics.mallocInitialized, 1,
    if x.1.shared.init then 1 else 0⟩ (by simp [sharedFrag])) (by simp)
    (by simp [he.init])) (by simp)
  have kTc := cell_load (hft (Cell.w (pin236.repAt base tp off).tls.tcache tc.addr) (by simp [threadFrag, htc]))
    (by simp [Cell.w])
  have kBins := cell_load (henv (Cell.w ((pin236.repAt base tp off).env.mp + (pin236.repAt base tp off).layout.mpTcacheBins) pin236.config.tcacheBins)
    (by simp [envFrag, mpConstFrag])) (by simp [Cell.w])
  simp only [Cell.w, he.init, ↓reduceIte] at kInit kTc kBins
  obtain ⟨kTc1, kTc2, -, -, kTc5⟩ := kTc
  have aInit : mallocAt base + 0x141b58#64 =
      BitVec.ofNat 64 (pin236.repAt base tp off).statics.mallocInitialized := by
    show BitVec.ofNat 64 (base + 0x98930) + BitVec.ofNat 64 0x141b58 =
      BitVec.ofNat 64 (base + 0x1da488)
    rw [ofNat_lit_add]
  have aBins : mallocAt base + 0x13aa78#64 =
      BitVec.ofNat 64 ((pin236.repAt base tp off).env.mp + pin236.layout.mpTcacheBins) := by
    show BitVec.ofNat 64 (base + 0x98930) + BitVec.ofNat 64 0x13aa78 =
      BitVec.ofNat 64 (base + 0x1d3340 + 0x68)
    rw [ofNat_lit_add, Nat.add_assoc]
  have hgotA' : loadN mA.memory (mallocAt base + 0x13a448#64) 8 = some o :=
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
  obtain ⟨mB, rB, ripB, rbpB, rdxB, frB, fsB, memB⟩ :=
    checks (n := BitVec.ofNat 64 n) (off := o) (tc := BitVec.ofNat 64 tc.addr) hlA ripA
      (by rw [rbxA, he.regsEq, he.rdi]) hmsb (by rw [aInit]; exact kInit.1) hgotA'
      (by rw [fsA, hoff]; exact kTc1)
      htc0 (by rw [aBins]; exact kBins.1) (by have h64 : pin236.config.tcacheBins = 64 := rfl; simpa [hitBin, h64] using hi)
  have hidx : tcIdx (BitVec.ofNat 64 n) = BitVec.ofNat 64 (hitBin n) := by simp [hitBin]
  have hcells : FpApart (tcGetCells pin236.config (pin236.repAt base tp off).layout
      (x.1, x.2.1, [hitBin n])) (envFrag pin236.config (pin236.repAt base tp off).layout
      (pin236.repAt base tp off).env x.2.1) (mallocAt base) mallocCode.length := he.cells
  have hcs : ∀ a ∈ (tcGetCells pin236.config (pin236.repAt base tp off).layout
      (x.1, x.2.1, [hitBin n])).bytes, ¬ (sp.toNat - 32 ≤ a ∧ a < sp.toNat + 8) := he.cellsStack
  generalize hitBin n = i at hi hne hidx hcells hcs ⊢
  -- 3. the bin's count test (no writes)
  have hT : (tcacheFrag pin236.config (pin236.repAt base tp off).layout x.1.shared.key tc).Holds (memView mA.memory) :=
    Frag.holds_sub hft (tcacheFrag_sub htc)
  obtain ⟨kCnt, bCnt, -, -, vCnt⟩ := cell_load (hT _ (mem_tcacheFrag_count (key := x.1.shared.key) hi))
    (by simp [show pin236.config.tcacheCountWidth = 2 from rfl])
  have hcw : pin236.config.tcacheCountWidth = 2 := rfl
  have hcc : (pin236.repAt base tp off).layout.tcCounts = 0 := rfl
  simp only [hcw, hcc] at kCnt bCnt vCnt
  have hlen0 : 0 < (tc.bins i).length := List.length_pos_iff.2 hne
  obtain ⟨mC, rC, ripC, rcxC, frC, fsC, memC⟩ :=
    countTest (tc := BitVec.ofNat 64 tc.addr) (idx := tcIdx (BitVec.ofNat 64 n))
      (cnt := BitVec.ofNat 64 (tc.bins i).length) (by rw [memB]; exact hlA) ripB rdxB rbpB
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
  have LC : LocalAt pin236.config (pin236.repAt base tp off) fsMach (x.1, x.2.1, [i]) mC :=
    localAt_args (localAt_mem ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hra⟩ (by rw [memC, memB]))
  have hlC : Loaded mC.memory (mallocAt base) mallocCode := by rw [memC, memB]; exact hlA
  obtain ⟨mD, rD, ripD, frD, fsD, wwD, p, l', hget, LD, hlD, raxD⟩ :=
    tcGetCore tcShape236 mallocTcGet (mallocAt base) hA hR (x.1, x.2.1, [i]) mC LC
      ⟨hlC, tc, htc, hi, hne, by rw [frC _ (by decide), rdxB], by rw [frC _ (by decide), rbpB, hidx]; rfl,
        hrcx, hcells⟩ (by rw [ripC])
  -- 5. the epilogue (reads the slots back)
  have rdD : ∀ {a : Nat} {bs : List Byte}, sp.toNat - 32 ≤ a → a + 8 ≤ sp.toNat + 8 →
      mA.memory.readBytes a 8 = some bs → mD.memory.readBytes a 8 = some bs := by
    intro a bs h1 h2 h
    refine rd_ww wwD (fun j hj hc => hcs _ hc ⟨by omega, by omega⟩) ?_
    rw [memC, memB]; exact h
  have hretA : mA.memory.readBytes sp.toNat 8 = some (encodeWords [ret]) :=
    rd_ww wwA (fun j hj hs => by unfold stk at hs; omega) he.ret
  have rspD : mD.core.read .rsp = sp - 0x28#64 := by
    rw [frD _ (by decide) (by decide) (by decide) (by decide), frC _ (by decide),
      frB _ (by decide) (by decide) (by decide) (by decide), rspA]
  obtain ⟨mE, rE, ripE, rspE, rbxE, rbpE, r12E, frE, fsE, memE⟩ :=
    epilogue hlD ripD rspD he.sp32 he.sp64 (rdD (by omega) (by omega) s2)
      (rdD (by omega) (by omega) s1) (rdD (by omega) (by omega) s0) (rdD (by omega) (by omega) hretA)
  -- the footprint
  have wwE : m0.memory.WritesWithin mE.memory
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [i])).bytes) := by
    rw [memE]
    have h1 := wwA.mono (fun a h => Or.inl (b := a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [i])).bytes) h)
    have h2 := wwD.mono (fun a h => Or.inr (a := stk sp a) h)
    rw [memC, memB] at h2
    exact h1.trans h2
  refine ⟨mE, (((rA.trans rB).trans rC).trans rD).trans rE, ⟨p, l', hget, localAt_mem LD memE, ripE,
    ?_, rspE, ?_⟩, fun a ha => within_of_ww wwE a ha⟩
  · rw [frE _ (by decide) (by decide) (by decide) (by decide), raxD]
  · intro r hr
    have h' : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
      simpa [Silmaril.X86.sysv64] using hr
    rcases h' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbxE, he.regsEq]
    · rw [rbpE, he.regsEq]
    · rw [r12E, he.regsEq]
    all_goals
      rw [frE _ (by decide) (by decide) (by decide) (by decide),
        frD _ (by decide) (by decide) (by decide) (by decide), frC _ (by decide),
        frB _ (by decide) (by decide) (by decide) (by decide),
        frA _ (by decide) (by decide), he.regsEq]

/-- **`malloc (n)` served from the tcache, on `Str9K`** (the process machine; the path makes no
system call, so the kernel and its answers are untouched). -/
theorem mallocTcacheHit236K (hA : Task.algo.leafTcacheGet) (hR : Task.x86sim.repTcacheGet) (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin236.config (pin236.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', x.1.tcacheGet pin236.config (hitBin n) = some (p, l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
        (projK s').core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  Triple.liftK (mallocTcacheHit236 hA hR base tp off x n sp ret regs)

/-- `mallocTcacheHit236K` with the representation step discharged (`repTcacheGet`). -/
theorem mallocTcacheHit236K' (hA : Task.algo.leafTcacheGet) (base tp off : Nat) (x : AState) (n : Nat) (sp ret : Word) (regs : Reg → Word) :
    str9kMach.Triple
      (fun s => LocalAt pin236.config (pin236.repAt base tp off) str9kMach x s ∧
        HitEntry base tp off x n sp ret regs (projK s))
      (fun s' => ∃ p l', x.1.tcacheGet pin236.config (hitBin n) = some (p, l') ∧
        LocalAt pin236.config (pin236.repAt base tp off) str9kMach (l', x.2.1, [p]) s' ∧
        (projK s').core.rip = ret ∧ (projK s').core.read .rax = BitVec.ofNat 64 p ∧
        (projK s').core.read .rsp = sp + 8#64 ∧ ∀ r ∈ sysv64.calleeSaved, (projK s').core.read r = regs r)
      (fun a => stk sp a ∨ a ∈ (tcGetCells pin236.config pin236.layout (x.1, x.2.1, [hitBin n])).bytes) :=
  mallocTcacheHit236K hA repTcacheGet base tp off x n sp ret regs

end Silmaril.Libc.Ptmalloc.Versions.V236
