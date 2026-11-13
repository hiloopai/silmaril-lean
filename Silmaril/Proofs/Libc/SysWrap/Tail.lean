module

public import Silmaril.Proofs.Libc.SysWrap.Pre

/-!
# System call wrappers: the code after the call

The instructions after the `syscall` (`tailOk`): the error test, the return, and the error
block (the GOT load of `errno`'s TLS offset, `neg %eax`, the `errno` store, the `-1`). Each is
one `Str9G` step (`step_*`); `tail_sound` runs them for every convention.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.SysWrap

open Silmaril.X86 (State Word Byte Reg sysv64)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Libc.SysWrap

/-- A state with a new core and memory (the ghost state kept). -/
abbrev setCore (w : GState) (c : State) (m : Memory) : GState := { w with x := ⟨⟨c, m⟩, w.x.xmm⟩ }

variable {code : List Byte} {A : Word} {w : GState} {o : Nat}

/-! ## Single instructions -/

theorem step_cmpq {imm : BitVec 32} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.aluA .q .cmp imm)) 6 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w { w.x.m.core with
      flags := Silmaril.X86.Ext.subFlagsN (w.x.m.core.read .rax) (imm.signExtend 64)
      rip := w.x.m.core.rip + BitVec.ofNat 64 6 } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.Sz.read_q, ↓reduceIte, Silmaril.X86.Ext.AluOp.flagsN,
      Silmaril.X86.Ext.retire]
    rfl)

theorem step_cmpd {imm : BitVec 32} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.aluA .d .cmp imm)) 5 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w { w.x.m.core with
      flags := Silmaril.X86.Ext.subFlagsN ((w.x.m.core.read .rax).setWidth 32) (imm.signExtend 32)
      rip := w.x.m.core.rip + BitVec.ofNat 64 5 } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      ↓reduceIte, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.retire]
    rfl)

theorem step_jcc8 {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {b : Bool}
    (hl : Loaded w.x.m.memory A code) (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.jcc8 c rel)) 2 = true) (hc : c.eval w.x.m.core.flags = some b) :
    Silmaril.X86.Str9G.step w = some (setCore w { w.x.m.core with
      rip := if b then w.x.m.core.rip + BitVec.ofNat 64 2 + rel.signExtend 64
        else w.x.m.core.rip + BitVec.ofNat 64 2 } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, hc]
    cases b <;> rfl)

theorem step_ret {g : GState} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o) (hok : listed code o (ext .ret) 1 = true)
    (abi : Silmaril.X86.FnContract.AbiEntry g.x.m.core g.x.m.memory)
    (hrsp : w.x.m.core.read .rsp = g.x.m.core.read .rsp)
    (hra : w.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8 =
      g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8) :
    Silmaril.X86.Str9G.step w = some (setCore w { w.x.m.core.write .rsp (g.x.m.core.read .rsp + 8#64) with
      rip := Silmaril.X86.FnContract.retOf g.x.m.core g.x.m.memory } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.popWord, hrsp, hra, abi.returnAddress,
      Option.bind_eq_bind, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords, Option.pure_def])

theorem step_load {reg : Reg} {disp : BitVec 32} {got tls : Word} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.load .q reg (Silmaril.X86.Ext.Mem.ofRip disp))) 7 = true)
    (hgot : got = BitVec.ofNat 64 (o + 7) + disp.signExtend 64)
    (hv : loadN w.x.m.memory (A + got) 8 = some tls) :
    Silmaril.X86.Str9G.step w = some (setCore w { w.x.m.core.write reg tls with
      rip := w.x.m.core.rip + BitVec.ofNat 64 7 } w.x.m.memory) := by
  have haddr : (Silmaril.X86.Ext.Mem.ofRip disp).addr w.x.m.core
      (w.x.m.core.rip + BitVec.ofNat 64 7) = A + got := by
    simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value,
      Option.map_none, Option.getD_none, BitVec.add_zero, hrip, hgot, BitVec.add_assoc]
    rw [← BitVec.add_assoc (BitVec.ofNat 64 o), ← BitVec.ofNat_add]
  refine step_of hl hrip hok ?_
  rw [exec_ext]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, haddr, hv,
    Silmaril.X86.Ext.Sz.bytes, Option.map_some, Silmaril.X86.Ext.retire]
  rfl

theorem step_neg (hl : Loaded w.x.m.memory A code) (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.unary .d .neg (.reg .rax))) 2 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core.write .rax ((0#32 - (w.x.m.core.read .rax).setWidth 32).setWidth 64) with
        flags := Silmaril.X86.Ext.negFlagsN ((w.x.m.core.read .rax).setWidth 32)
        rip := w.x.m.core.rip + BitVec.ofNat 64 2 } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
      Option.map_some, Silmaril.X86.Ext.retire]
    rfl)

theorem step_fsStore {reg : Reg} {m'' : Memory} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o) (hok : listed code o (fsStore reg) 3 = true)
    (hs : storeN w.x.m.memory (w.x.m.core.fsBase + w.x.m.core.read reg) 4
      (((w.x.m.core.read .rax).setWidth 32).setWidth 64) = some m'') :
    Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core with rip := w.x.m.core.rip + BitVec.ofNat 64 3 } m'') := by
  refine step_of hl hrip hok ?_
  simp only [fsStore, Silmaril.X86.Str9FsX.exec, Silmaril.X86.Str9Fs.exec,
    Silmaril.X86.Str9Fs.execNew, Silmaril.X86.Str9Fs.execFs, Silmaril.X86.Str9Fs.ext,
    Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
    Silmaril.X86.Ext.writeRM, Silmaril.X86.Str9Fs.fs0, Silmaril.X86.Ext.Mem.fsAt,
    Silmaril.X86.Ext.Mem.ofFs, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.addr,
    Silmaril.X86.Ext.Base.value, Option.map_none, Option.getD_none, BitVec.add_zero,
    Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.read, State.read_mk_regs]
  rw [show BitVec.signExtend 64 (0 : BitVec 32) = 0#64 from by decide, BitVec.add_zero,
    BitVec.add_zero]
  change (match Silmaril.X86.Ext.retire _ (Option.map _ (storeN w.x.m.memory
    (w.x.m.core.fsBase + w.x.m.core.read reg) 4
    (((w.x.m.core.read .rax).setWidth 32).setWidth 64))) with
    | .ok c memory' => _ | r => r) = _
  rw [hs]
  rfl

theorem step_orM1 (hl : Loaded w.x.m.memory A code) (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.aluI8 .q .or (.reg .rax) 0xff#8)) 4 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core.write .rax (w.x.m.core.read .rax ||| BitVec.allOnes 64) with
        flags := Silmaril.X86.Ext.AluOp.flagsN .or (w.x.m.core.read .rax) (BitVec.allOnes 64)
        rip := w.x.m.core.rip + BitVec.ofNat 64 4 } w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, Option.map_some, Silmaril.X86.Ext.retire, reduceCtorEq,
      ↓reduceIte, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Sz.read_q]
    rw [show (0xff#8).signExtend Silmaril.X86.Ext.Sz.q.bits = BitVec.allOnes 64 from rfl]
    rfl)

theorem step_movI32 {r : Reg} {imm : BitVec 32} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.movI32 r imm)) 5 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core.write r (imm.setWidth 64) with rip := w.x.m.core.rip + BitVec.ofNat 64 5 }
      w.x.m.memory) :=
  step_of hl hrip hok (by rw [exec_ext]; rfl)

theorem step_movIq {imm : BitVec 32} (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.movI .q (.reg .rax) imm)) 7 = true) :
    Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core.write .rax (imm.signExtend 64) with rip := w.x.m.core.rip + BitVec.ofNat 64 7 }
      w.x.m.memory) :=
  step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire]
    rfl)

theorem step_xorRax (hl : Loaded w.x.m.memory A code) (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext (.alu .d .xor (.reg .rax) .rax)) 2 = true) :
    ∃ f, Silmaril.X86.Str9G.step w = some (setCore w
      { w.x.m.core.write .rax 0 with flags := f, rip := w.x.m.core.rip + BitVec.ofNat 64 2 }
      w.x.m.memory) :=
  ⟨_, step_of hl hrip hok (by
    rw [exec_ext]
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, Option.map_some, Silmaril.X86.Ext.retire, reduceCtorEq,
      ↓reduceIte, Silmaril.X86.Ext.AluOp.resultN, BitVec.xor_self, Silmaril.X86.Ext.Sz.write]
    rfl)⟩

/-! ## Frames and comparisons -/

/-- What the code after the call keeps of the entry `g`. -/
structure TFr (g w : GState) : Prop where
  keep : ∀ q ∈ kept, w.x.m.core.read q = g.x.m.core.read q
  fs : w.x.m.core.fsBase = g.x.m.core.fsBase

theorem TFr.set {g w : GState} (f : TFr g w) {c : State} {m : Memory}
    (hk : ∀ q ∈ kept, c.read q = w.x.m.core.read q) (hfs : c.fsBase = w.x.m.core.fsBase) :
    TFr g (setCore w c m) :=
  ⟨fun q hq => (hk q hq).trans (f.keep q hq), hfs.trans f.fs⟩

theorem kept_write {c : State} {r : Reg} (hr : r ∉ kept) (v : Word) (rip : Word) (fl : Silmaril.X86.Flags) :
    ∀ q ∈ kept, ({ c.write r v with rip := rip, flags := fl } : State).read q = c.read q := by
  intro q hq
  have : q ≠ r := fun h => hr (h ▸ hq)
  simp [State.read_mk_regs, this]

theorem kept_rip {c : State} (rip : Word) (fl : Silmaril.X86.Flags) :
    ∀ q ∈ kept, ({ c with rip := rip, flags := fl } : State).read q = c.read q :=
  fun _ _ => rfl

theorem sw32 (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem rax_nk : Reg.rax ∉ kept := by decide
theorem rcx_nk : Reg.rcx ∉ kept := by decide
theorem rdx_nk : Reg.rdx ∉ kept := by decide

theorem ae_err (r : Word) :
    (Silmaril.X86.Ext.Cond.afterCmp (w := 63) r ((0xfffff001#32).signExtend 64) .ae) = isErr r := by
  rw [show (0xfffff001#32).signExtend 64 = 0xfffffffffffff001#64 from by decide]
  simp only [Silmaril.X86.Ext.Cond.afterCmp, isErr, BitVec.ult, BitVec.toNat_ofNat]
  by_cases h : r.toNat < 18446744073709547521
  · have : ¬ (18446744073709547520 < r.toNat) := by omega
    simp [h, this]
  · have : 18446744073709547520 < r.toNat := by omega
    simp [h, this]

theorem a_err (r : Word) :
    (Silmaril.X86.Ext.Cond.afterCmp (w := 63) r ((0xfffff000#32).signExtend 64) .a) = isErr r := by
  rw [show (0xfffff000#32).signExtend 64 = 0xfffffffffffff000#64 from by decide]
  simp only [Silmaril.X86.Ext.Cond.afterCmp, isErr, BitVec.ule, BitVec.ult, BitVec.toNat_ofNat]
  by_cases h : r.toNat ≤ 18446744073709547520
  · have : ¬ (18446744073709547520 < r.toNat) := by omega
    simp [h, this]
  · have : 18446744073709547520 < r.toNat := by omega
    simp [h, this]

theorem a_err32 (r : Word) :
    (Silmaril.X86.Ext.Cond.afterCmp (w := 31) (r.setWidth 32) ((0xfffff000#32).signExtend 32) .a) =
      isErr32 r := by
  rw [show (0xfffff000#32).signExtend 32 = 0xfffff000#32 from by decide]
  simp only [Silmaril.X86.Ext.Cond.afterCmp, isErr32, BitVec.ule, BitVec.ult, BitVec.toNat_ofNat]
  generalize (BitVec.setWidth 32 r).toNat = n
  by_cases h : n ≤ 4294963200
  · simp [h, show ¬ 4294963200 < n by omega]
  · simp [h, show 4294963200 < n by omega]

/-! ## The return and the error block -/

/-- **The return**: `Returned`, from a state at a listed `ret` that keeps the frame. -/
theorem finish_ret {g : GState} {d : Desc} {r : Word} {m' : Memory} {tls : Word}
    (hl : Loaded w.x.m.memory A code) (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o (ext .ret) 1 = true)
    (abi : Silmaril.X86.FnContract.AbiEntry g.x.m.core g.x.m.memory) (fr : TFr g w)
    (hra : w.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8 =
      g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8)
    (hres : if d.conv.err r then w.x.m.core.read .rax = d.conv.failValue ∧
        storeN m' (g.x.m.core.fsBase + tls) 4 (errnoOf r) = some w.x.m.memory
      else w.x.m.core.read .rax = d.conv.okValue r ∧ w.x.m.memory = m') :
    ∃ v, Reaches Silmaril.X86.Str9G.step w v ∧ Returned d g r m' tls v := by
  have hrsp : w.x.m.core.read .rsp = g.x.m.core.read .rsp := fr.keep .rsp (by decide)
  refine ⟨_, reaches_step (step_ret hl hrip hok abi hrsp hra), ?_⟩
  refine ⟨rfl, by simp, ?_, by simpa using fr.fs, ?_⟩
  · intro q hq
    have hq' : q ∈ kept := by revert hq; revert q; decide
    have hne : q ≠ .rsp := by revert hq; revert q; decide
    simp only [State.read_mk_regs, State.read_write_other _ _ _ _ hne]
    exact fr.keep q hq'
  · simp only [State.read_mk_regs, State.read_write_other _ _ _ _ (show Reg.rax ≠ .rsp by decide)]
    exact hres

/-- **The error block**: from its first instruction to the `-1`, with `errno` stored. -/
theorem err_path {g : GState} {d : Desc} {t : Tail} {r tls : Word} {m'' : Memory}
    (hb : errBlock code d t = true) (hl : Loaded w.x.m.memory A code)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 t.e) (fr : TFr g w)
    (hgot : loadN w.x.m.memory (A + d.errnoGot) 8 = some tls)
    (hs : storeN w.x.m.memory (g.x.m.core.fsBase + tls) 4 (errnoOf r) = some m'')
    (hrax : (w.x.m.core.read .rax).setWidth 32 = r.setWidth 32) :
    ∃ w', Reaches Silmaril.X86.Str9G.step w w' ∧
      w'.x.m.core.rip = A + BitVec.ofNat 64 (t.e + 12) ∧ w'.x.m.memory = m'' ∧ TFr g w' := by
  simp only [errBlock, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, hreg⟩, hgd⟩ := hb
  have hrk : t.reg ∉ kept := by rcases hreg with h | h <;> rw [h] <;> decide
  have hra : Reg.rax ≠ t.reg := by rcases hreg with h | h <;> rw [h] <;> decide
  have s1 := step_load hl hrip h1 hgd hgot
  generalize hw1 : setCore w { w.x.m.core.write t.reg tls with
    rip := w.x.m.core.rip + BitVec.ofNat 64 7 } w.x.m.memory = w1 at s1
  have hm1 : w1.x.m.memory = w.x.m.memory := by rw [← hw1]
  have hr1 : w1.x.m.core.rip = A + BitVec.ofNat 64 (t.e + 7) := by rw [← hw1]; simp [hrip, add_ofNat]
  have hreg1 : w1.x.m.core.read t.reg = tls := by rw [← hw1]; simp
  have hax1 : w1.x.m.core.read .rax = w.x.m.core.read .rax := by
    rw [← hw1]; simp [State.read_write_other _ _ _ _ hra]
  have hfs1 : w1.x.m.core.fsBase = w.x.m.core.fsBase := by rw [← hw1]; rfl
  have hk1 : ∀ q ∈ kept, w1.x.m.core.read q = w.x.m.core.read q := by
    intro q hq; rw [← hw1]
    have : q ≠ t.reg := fun h => hrk (h ▸ hq)
    simp [State.read_write_other _ _ _ _ this]
  have s2 := step_neg (by rw [hm1]; exact hl) hr1 h2
  generalize hw2 : setCore w1 { w1.x.m.core.write .rax ((0#32 - (w1.x.m.core.read .rax).setWidth 32).setWidth 64) with
    flags := Silmaril.X86.Ext.negFlagsN ((w1.x.m.core.read .rax).setWidth 32)
    rip := w1.x.m.core.rip + BitVec.ofNat 64 2 } w1.x.m.memory = w2 at s2
  have hm2 : w2.x.m.memory = w.x.m.memory := by rw [← hw2, ← hm1]
  have hr2 : w2.x.m.core.rip = A + BitVec.ofNat 64 (t.e + 9) := by rw [← hw2]; simp [hr1, add_ofNat]
  have hreg2 : w2.x.m.core.read t.reg = tls := by
    rw [← hw2]; simp [State.read_write_other _ _ _ _ hra.symm, hreg1]
  have hax2 : ((w2.x.m.core.read .rax).setWidth 32).setWidth 64 = errnoOf r := by
    rw [← hw2]; simp only [State.read_mk_regs, State.read_write_same]
    rw [sw32, hax1, hrax]; rfl
  have hfs2 : w2.x.m.core.fsBase = g.x.m.core.fsBase := by rw [← hw2]; simp [hfs1, fr.fs]
  have hk2 : ∀ q ∈ kept, w2.x.m.core.read q = w.x.m.core.read q := by
    intro q hq; rw [← hw2]
    have : q ≠ .rax := fun h => rax_nk (h ▸ hq)
    simp [State.read_write_other _ _ _ _ this, hk1 q hq]
  have s3 := step_fsStore (m'' := m'') (by rw [hm2]; exact hl) hr2 h3 (by rw [hax2, hreg2, hfs2, hm2]; exact hs)
  refine ⟨_, reaches_cons s1 (reaches_cons s2 (reaches_step s3)), ?_, rfl, ?_⟩
  · simp [hr2, add_ofNat]
  · exact ⟨fun q hq => by simpa using (hk2 q hq).trans (fr.keep q hq), by simpa using hfs2⟩

/-! ## Steps as facts -/

/-- `u` is at offset `o`, with memory `M`, keeping the frame of the entry `g`. -/
structure At (g : GState) (A : Word) (u : GState) (o : Nat) (M : Memory) : Prop where
  rip : u.x.m.core.rip = A + BitVec.ofNat 64 o
  mem : u.x.m.memory = M
  fr : TFr g u

variable {g : GState} {M : Memory}

theorem at_cmpq {imm : BitVec 32} (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.aluA .q .cmp imm)) 6 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 6) M ∧
      u.x.m.core.read .rax = w.x.m.core.read .rax ∧
      u.x.m.core.flags = Silmaril.X86.Ext.subFlagsN (w.x.m.core.read .rax) (imm.signExtend 64) :=
  ⟨_, step_cmpq (h.mem ▸ hl) h.rip hok,
    ⟨by simp only; rw [h.rip, add_ofNat], h.mem, h.fr.set (kept_rip _ _) rfl⟩, rfl, rfl⟩

theorem at_cmpd {imm : BitVec 32} (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.aluA .d .cmp imm)) 5 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 5) M ∧
      u.x.m.core.read .rax = w.x.m.core.read .rax ∧
      u.x.m.core.flags = Silmaril.X86.Ext.subFlagsN ((w.x.m.core.read .rax).setWidth 32)
        (imm.signExtend 32) :=
  ⟨_, step_cmpd (h.mem ▸ hl) h.rip hok,
    ⟨by simp only; rw [h.rip, add_ofNat], h.mem, h.fr.set (kept_rip _ _) rfl⟩, rfl, rfl⟩

theorem at_jcc {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {b : Bool} {e : Nat}
    (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.jcc8 c rel)) 2 = true) (hc : c.eval w.x.m.core.flags = some b)
    (hbr : BitVec.ofNat 64 (o + 2) + rel.signExtend 64 = BitVec.ofNat 64 e) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (if b then e else o + 2) M ∧
      u.x.m.core.read .rax = w.x.m.core.read .rax := by
  refine ⟨_, step_jcc8 (h.mem ▸ hl) h.rip hok hc, ⟨?_, h.mem, h.fr.set (kept_rip _ _) rfl⟩, rfl⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [h.rip, add_ofNat]
  · simp only [↓reduceIte]; rw [h.rip, add_ofNat, BitVec.add_assoc, hbr]

theorem at_xor (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.alu .d .xor (.reg .rax) .rax)) 2 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 2) M ∧ u.x.m.core.read .rax = 0 := by
  obtain ⟨f, hs⟩ := step_xorRax (h.mem ▸ hl) h.rip hok
  exact ⟨_, hs, ⟨by simp only; rw [h.rip, add_ofNat], h.mem,
    h.fr.set (kept_write rax_nk _ _ _) rfl⟩, by simp⟩

theorem at_or (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.aluI8 .q .or (.reg .rax) 0xff#8)) 4 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 4) M ∧
      u.x.m.core.read .rax = BitVec.allOnes 64 :=
  ⟨_, step_orM1 (h.mem ▸ hl) h.rip hok, ⟨by simp only; rw [h.rip, add_ofNat], h.mem,
    h.fr.set (kept_write rax_nk _ _ _) rfl⟩, by simp only [State.read_mk_regs, State.read_write_same]; exact BitVec.or_allOnes⟩

theorem at_movI32 {imm : BitVec 32} (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.movI32 .rax imm)) 5 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 5) M ∧
      u.x.m.core.read .rax = imm.setWidth 64 :=
  ⟨_, step_movI32 (h.mem ▸ hl) h.rip hok, ⟨by simp only; rw [h.rip, add_ofNat], h.mem,
    h.fr.set (fun q hq => by
      have : q ≠ .rax := fun e => rax_nk (e ▸ hq)
      simp [State.read_write_other _ _ _ _ this]) rfl⟩, by simp⟩

theorem at_movIq {imm : BitVec 32} (hl : Loaded M A code) (h : At g A w o M)
    (hok : listed code o (ext (.movI .q (.reg .rax) imm)) 7 = true) :
    ∃ u, Silmaril.X86.Str9G.step w = some u ∧ At g A u (o + 7) M ∧
      u.x.m.core.read .rax = imm.signExtend 64 :=
  ⟨_, step_movIq (h.mem ▸ hl) h.rip hok, ⟨by simp only; rw [h.rip, add_ofNat], h.mem,
    h.fr.set (fun q hq => by
      have : q ≠ .rax := fun e => rax_nk (e ▸ hq)
      simp [State.read_write_other _ _ _ _ this]) rfl⟩, by simp⟩

theorem at_ret {d : Desc} {r : Word} {m' : Memory} {tls : Word} (hl : Loaded M A code)
    (h : At g A w o M) (hok : listed code o (ext .ret) 1 = true)
    (abi : Silmaril.X86.FnContract.AbiEntry g.x.m.core g.x.m.memory)
    (hra : M.readBytes (g.x.m.core.read .rsp).toNat 8 =
      g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8)
    (hres : if d.conv.err r then w.x.m.core.read .rax = d.conv.failValue ∧
        storeN m' (g.x.m.core.fsBase + tls) 4 (errnoOf r) = some M
      else w.x.m.core.read .rax = d.conv.okValue r ∧ M = m') :
    ∃ v, Reaches Silmaril.X86.Str9G.step w v ∧ Returned d g r m' tls v :=
  finish_ret (h.mem ▸ hl) h.rip hok abi h.fr (by rw [h.mem]; exact hra) (by rw [h.mem]; exact hres)

end Silmaril.Proofs.Libc.SysWrap
