module

public import Silmaril.X86.Ladder.ZlibChecksums.Defs
public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Thms
public import Silmaril.X86.BlockCert.Ext8.Instr.Thms
public import Silmaril.X86.BlockCert.Thms

/-!
# `crc32_z` (zlib 1.3.1, `-O2`, `Z_SOLO`): block VCs and total correctness
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Mem Loaded loadN)
open Silmaril.X86 Silmaril.X86.BlockCert8
open Silmaril.X86.Stencils
open Silmaril.X86.Stencils.TableFold (stepL stepAddL tblMem TableAt bytesAt byteAt)
open Silmaril.X86.Stencils.ByteLoop (Readable arg0 arg1 arg2)
open Silmaril.X86.Ladder.ZlibChecksums

/-- The exit condition: the contract's result. -/
abbrev zQ (entry : Word) : MState → MState → Prop :=
  fun m0 t => (crc32zContract entry).Result Open.isa m0 t

theorem sub_base (b x : Word) : b + x - b = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Registers a block may change. -/
def Scratch (r : Reg) : Prop := r = .rax ∨ r = .rcx ∨ r = .rdx ∨ r = .rsi ∨ r = .rdi

theorem cs_not_scratch {r : Reg} (h : r ∈ Silmaril.X86.sysv64.calleeSaved) : ¬ Scratch r := by
  simp [Silmaril.X86.sysv64_calleeSaved] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Scratch]

theorem frame_of {m0 m t : MState} (h : BlockCert.Frame m0 m) (hmem : t.memory = m.memory)
    (hk : ∀ r, ¬ Scratch r → t.core.read r = m.core.read r) : BlockCert.Frame m0 t :=
  h.step hmem (hk _ (by simp [Scratch])) (fun r hr => hk r (cs_not_scratch hr))

theorem base_of {entry : Word} {m0 m t : MState} (h : Base entry m0 m) (hmem : t.memory = m.memory)
    (hk : ∀ r, ¬ Scratch r → t.core.read r = m.core.read r) : Base entry m0 t :=
  ⟨frame_of h.frame hmem hk, h.pre, h.nz⟩

theorem F_zero (m0 : MState) : F m0 0 = crcIn m0 := rfl

theorem F_succ (m0 : MState) (t : Nat) :
    F m0 (t + 1) = crcByte (F m0 t) (byteAt m0.memory (arg1 m0) t) := by
  simp [F, TableFold.bytesAt_succ, List.foldl_append]

theorem blocks_mem (entry : Word) {o : Nat} {L : List LI} (h : (⟨o, L⟩ : Blk) ∈ crc32zBlocks) :
    (⟨o, L⟩ : Blk) ∈ (crc32zCert entry).blocks := h

theorem nxt {entry : Word} {m0 m' : MState} {μ : Nat} (o : Nat) (L : List LI)
    (hb : (⟨o, L⟩ : Blk) ∈ crc32zBlocks) (hrip : m'.core.rip = entry + BitVec.ofNat 64 o)
    (ha : zAnn entry o m0 m') (hμ : zMeasure o m0 m' < μ) :
    (crc32zCert entry).Next (zQ entry) m0 μ m' :=
  Cert.next_of ⟨o, L⟩ hb hrip ha hμ

/-! ## Entry and the null buffer -/

theorem b00 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x00, zL00⟩ := by
  intro m0 m ⟨hm, hab, he⟩ hrip _
  subst hm
  obtain ⟨c1, h1, e1⟩ := mov_q m.core m.memory 3 .rax .rdi
  obtain ⟨c2, h2, e2⟩ := mov_q c1 m.memory 3 .rcx .rsi
  obtain ⟨c3, h3, e3⟩ := mov_q c2 m.memory 3 .rdi .rdx
  obtain ⟨c4, h4, r4, p4⟩ := test_je_end ⟨c3, m.memory⟩ .rsi 0x10e#32
  have hrun : run8 zL00 m = some ⟨c4, m.memory⟩ := by
    simp only [zL00]
    rw [run8_cons_of h1 e1.1, run8_cons_of h2 e2.1, run8_cons_of h3 e3.1]; exact h4
  refine ⟨_, hrun, ?_⟩
  have rd : ∀ r, c4.read r = if r = .rdi then m.core.read .rdx else if r = .rcx then
      m.core.read .rsi else if r = .rax then m.core.read .rdi else m.core.read r := by
    intro r; rw [r4]; simp only [e3.2, e2.2, e1.2]
    by_cases a : r = .rdi <;> by_cases b : r = .rcx <;> by_cases c : r = .rax <;> simp_all
  have hk : ∀ r, ¬ Scratch r → c4.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr; rw [rd]; simp [hr]
  have hfr : BlockCert.Frame m ⟨c4, m.memory⟩ := frame_of (BlockCert.Frame.entry hab) rfl hk
  have hrsi : c3.read .rsi = m.core.read .rsi := by rw [← r4 .rsi, rd]; simp
  by_cases hz : m.core.read .rsi = 0
  · have hA : arg1 m = 0 := by simp [arg1, hz]
    refine nxt 0x120 zL120 (by simp [crc32zBlocks]) ?_ ⟨hfr, he, hA⟩ (by simp [zMeasure, crc32zCert])
    show c4.rip = _
    rw [p4, ite_t (by show c3.read .rsi = 0; rw [hrsi]; exact hz), e3.1, e2.1, e1.1, hrip]
    simp only [BitVec.add_assoc]; rfl
  · have hA : arg1 m ≠ 0 := by
      intro h0; apply hz; apply BitVec.eq_of_toNat_eq; simpa [arg1] using h0
    refine nxt 0x12 zL12 (by simp [crc32zBlocks]) ?_ ⟨⟨hfr, he, hA⟩, ?_, ?_, ?_, ?_, ?_⟩
      (by simp [zMeasure, crc32zCert])
    · show c4.rip = _
      rw [p4, ite_f (by show ¬ c3.read .rsi = 0; rw [hrsi]; exact hz), e3.1, e2.1, e1.1, hrip]
      simp only [BitVec.add_assoc]; rfl
    all_goals (show c4.read _ = _; rw [rd]; simp)

theorem b120 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x120, zL120⟩ := by
  intro m0 m ⟨hf, he, hA⟩ _ _
  obtain ⟨c1, h1, e1⟩ := xor_d_self m.core m.memory 2 .rax
  obtain ⟨c2, h2, p2, s2, o2⟩ := ret_end ⟨c1, m.memory⟩ (w := FnContract.retOf m0.core m0.memory)
    (by rw [show (⟨c1, m.memory⟩ : MState).core.read .rsp = m.core.read .rsp by
          show c1.read .rsp = _; rw [e1.2]; simp]
        exact hf.pop)
  refine ⟨_, by simp only [zL120]; rw [run8_cons_of h1 e1.1]; exact h2, .inl ?_⟩
  refine Silmaril.X86.BlockCert.Frame.result_open hf p2
    (by rw [s2]; show c1.read .rsp + _ = _; rw [e1.2]; simp) (fun r hr => ?_) rfl ?_
  · have := cs_not_scratch hr
    simp only [Scratch, not_or] at this
    rw [o2 r (by simp [Silmaril.X86.sysv64_calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    show c1.read r = _; rw [e1.2]; simp [this.1]
  · show (c2.read .rax) = _
    rw [o2 .rax (by decide)]; show c1.read .rax = _; rw [e1.2]; simp [hA]

theorem arg2_lt (m0 : MState) : arg2 m0 < 2 ^ 64 := (m0.core.read .rdx).isLt

theorem rdx_eq (m0 : MState) : m0.core.read .rdx = BitVec.ofNat 64 (arg2 m0) := by
  simp [arg2]

theorem b12 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x12, zL12⟩ := by
  intro m0 m ⟨hb, hrax, hrcx, hrsi, hrdx, hrdi⟩ hrip _
  obtain ⟨c1, h1, e1⟩ := not_d m.core m.memory 2 .rax
  obtain ⟨c2, h2, r2, p2⟩ := cmpi8_jbe_end ⟨c1, m.memory⟩ .rdx 0x07#8 0xc9#32
  refine ⟨_, by simp only [zL12]; rw [run8_cons_of h1 e1.1]; exact h2, ?_⟩
  have rd : ∀ r, c2.read r = if r = .rax then W (crcIn m0) else m.core.read r := by
    intro r; rw [r2]; show c1.read r = _; rw [e1.2]; simp [hrax, crcIn]
  have hk : ∀ r, ¬ Scratch r → c2.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr; rw [rd]; simp [hr]
  have hB : Base entry m0 ⟨c2, m.memory⟩ := base_of hb rfl hk
  have hdx : c1.read .rdx = m0.core.read .rdx := by rw [e1.2]; simpa using hrdx
  have hN := arg2_lt m0
  by_cases hs : arg2 m0 ≤ 7
  · have hle : c1.read .rdx ≤ (0x07#8).signExtend 64 := by
      rw [hdx]; show (m0.core.read .rdx).toNat ≤ _; simp [arg2] at hs ⊢; omega
    refine nxt 0xe7 zLe7 (by simp [crc32zBlocks]) ?_ ⟨hB, ?_, ?_, ?_⟩ (by simp [zMeasure, crc32zCert])
    · show c2.rip = _
      rw [p2, ite_t hle, e1.1, hrip]; simp only [BitVec.add_assoc]; rfl
    · show c2.read .rax = _; rw [rd]; simp [Nat.div_eq_of_lt (show arg2 m0 < 8 by omega), F_zero]
    · show c2.read .rsi = _; rw [rd]; simp [hrsi, Nat.div_eq_of_lt (show arg2 m0 < 8 by omega)]
    · show c2.read .rdi = _; rw [rd]; simp [hrdi, Nat.mod_eq_of_lt (show arg2 m0 < 8 by omega), rdx_eq]
  · have hle : ¬ c1.read .rdx ≤ (0x07#8).signExtend 64 := by
      rw [hdx]; show ¬ (m0.core.read .rdx).toNat ≤ _; simp [arg2] at hs ⊢; omega
    refine nxt 0x1e zL1e (by simp [crc32zBlocks]) ?_ ⟨hB, by omega, ?_, ?_, ?_, ?_, ?_⟩
      (by simp [zMeasure, crc32zCert])
    · show c2.rip = _
      rw [p2, ite_f hle, e1.1, hrip]; simp only [BitVec.add_assoc]; rfl
    all_goals (show c2.read _ = _; rw [rd]; simp [hrcx, hrsi, hrdx, hrdi, F_zero])

theorem lea8 (x : Word) (h8 : 8 ≤ x.toNat) :
    (x + 0#64 + BitVec.signExtend 64 4294967288#32) >>> (3#8).toNat =
      BitVec.ofNat 64 ((x.toNat - 8) / 8) := by
  have hs : BitVec.signExtend 64 4294967288#32 = 0xfffffffffffffff8#64 := by decide +kernel
  have h3 : (3#8 : BitVec 8).toNat = 3 := rfl
  rw [hs, h3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hc : (18446744073709551608#64 : BitVec 64).toNat = 18446744073709551608 := rfl
  rw [hc, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  omega

theorem lea2 (b : Word) (n : Nat) (hn : n < 2 ^ 64) (h8 : 8 ≤ n) :
    b + BitVec.ofNat 64 ((n - 8) / 8) <<< (3#2 : BitVec 2).toNat + BitVec.signExtend 64 8#32 =
      b + BitVec.ofNat 64 (8 * (n / 8)) := by
  have hs : BitVec.signExtend 64 8#32 = 8#64 := by decide +kernel
  have h3 : (3#2 : BitVec 2).toNat = 3 := rfl
  rw [hs, h3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat]
  have hb := b.isLt
  omega

theorem b1e (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x1e, zL1e⟩ := by
  intro m0 m ⟨hb, h8, hrax, hrcx, hrsi, hrdx, hrdi⟩ hrip _
  obtain ⟨c1, h1, e1⟩ := lea_q m.core m.memory 4 .rdx (Mem.ofReg .rdx none 0xfffffff8#32) (by decide)
  obtain ⟨c2, h2, e2⟩ := shr_q c1 m.memory 4 .rdx 0x03#8 (by decide)
  obtain ⟨c3, h3, e3⟩ := lea_q c2 m.memory 5 .rsi
    (Mem.ofReg .rsi (some ⟨.rdx, 3#2, by decide⟩) 0x8#32) (by decide)
  obtain ⟨c4, h4, e4⟩ := nop_eff c3 m.memory 5 4
  have hrun : run8 zL1e m = some ⟨c4, m.memory⟩ := by
    simp only [zL1e]
    rw [run8_cons_of h1 e1.1, run8_cons_of h2 e2.1, run8_cons_of h3 e3.1, run8_cons_of h4 e4.1]
    rfl
  refine ⟨_, hrun, ?_⟩
  have hN := arg2_lt m0
  have hdx : c2.read .rdx = BitVec.ofNat 64 ((arg2 m0 - 8) / 8) := by
    rw [e2.2]; simp only [ite_true]; rw [e1.2]
    simp only [ite_true, Mem.addr, Mem.ofReg, Silmaril.X86.Ext.Base.value, Option.map_none,
      Option.getD_none, hrdx]
    exact lea8 _ h8
  have hsi : c3.read .rsi = m0.core.read .rsi + BitVec.ofNat 64 (8 * (arg2 m0 / 8)) := by
    rw [e3.2]; simp only [ite_true, Mem.addr, Mem.ofReg, Silmaril.X86.Ext.Base.value,
      Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value]
    rw [hdx]; simp only [e2.2, e1.2, reduceCtorEq, ite_false, hrsi]
    exact lea2 _ _ hN h8
  have rd : ∀ r, r ≠ .rdx → r ≠ .rsi → c4.read r = m.core.read r := by
    intro r h1 h2; simp only [e4.2, e3.2, e2.2, e1.2]; simp [h1, h2]
  have hk : ∀ r, ¬ Scratch r → c4.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr; exact rd r hr.2.2.1 hr.2.2.2.1
  have hB : Base entry m0 ⟨c4, m.memory⟩ := base_of hb rfl hk
  have hrcx' : c4.read .rcx = m0.core.read .rsi := by rw [rd _ (by decide) (by decide), hrcx]
  have hj : 0 < arg2 m0 / 8 := by omega
  refine nxt 0x30 zL30 (by simp [crc32zBlocks]) ?_ ⟨hB, 0, hj, ?_, ?_, ?_, ?_⟩ ?_
  · show c4.rip = _
    rw [e4.1, e3.1, e2.1, e1.1, hrip]; simp only [BitVec.add_assoc]; rfl
  · show c4.read .rax = _; rw [rd _ (by decide) (by decide), hrax]
  · show c4.read .rcx = _; rw [hrcx']; simp
  · show c4.read .rsi = _; simp only [e4.2]; exact hsi
  · show c4.read .rdi = _; rw [rd _ (by decide) (by decide), hrdi]
  · simp only [zMeasure, crc32zCert]
    show _ - (c4.read .rcx - _).toNat / 8 + 20 < _
    rw [hrcx', BitVec.sub_self]; simp; omega

theorem and7 (x : Word) :
    ((x.setWidth 32) &&& (0x07#8 : BitVec 8).signExtend 32).setWidth 64 =
      BitVec.ofNat 64 (x.toNat % 8) := by
  have hs : (0x07#8 : BitVec 8).signExtend 32 = 7#32 := by decide +kernel
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have h7 : (7 : Nat) % 2 ^ 32 = 2 ^ 3 - 1 := by decide
  rw [h7, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem be4 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0xe4, zLe4⟩ := by
  intro m0 m ⟨hb, hrax, hrsi, hrdi⟩ hrip _
  obtain ⟨c1, h1, e1⟩ := and_d_i8 m.core m.memory 3 .rdi 0x07#8
  refine ⟨_, by simp only [zLe4]; rw [run8_cons_of h1 e1.1]; rfl, ?_⟩
  have hk : ∀ r, ¬ Scratch r → c1.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr; simp only [e1.2]; simp [hr]
  refine nxt 0xe7 zLe7 (by simp [crc32zBlocks]) ?_ ⟨base_of hb rfl hk, ?_, ?_, ?_⟩
    (by simp [zMeasure, crc32zCert])
  · show c1.rip = _; rw [e1.1, hrip]; simp only [BitVec.add_assoc]; rfl
  · show c1.read .rax = _; simp only [e1.2]; simp [hrax]
  · show c1.read .rsi = _; simp only [e1.2]; simp [hrsi]
  · show c1.read .rdi = _; simp only [e1.2, ite_true, hrdi]; exact and7 _

theorem be7 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0xe7, zLe7⟩ := by
  intro m0 m ⟨hb, hrax, hrsi, hrdi⟩ hrip _
  obtain ⟨c1, h1, r1, p1⟩ := test_je8_end m .rdi 0x25#8
  refine ⟨_, h1, ?_⟩
  have hk : ∀ r, ¬ Scratch r → c1.read r = m.core.read r := fun r _ => r1 r
  have hB := base_of hb (t := ⟨c1, m.memory⟩) rfl hk
  have hz : m.core.read .rdi = 0 ↔ arg2 m0 % 8 = 0 := by
    rw [hrdi]; constructor
    · intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simpa using this
    · intro h; rw [h]; rfl
  by_cases h0 : arg2 m0 % 8 = 0
  · refine nxt 0x111 zL111 (by simp [crc32zBlocks]) ?_ ⟨hB, ?_⟩ (by simp [zMeasure, crc32zCert])
    · show c1.rip = _; rw [p1, ite_t (hz.mpr h0), hrip]; simp only [BitVec.add_assoc]; rfl
    · show c1.read .rax = _; rw [r1, hrax]
      congr 3; omega
  · refine nxt 0xec zLec (by simp [crc32zBlocks]) ?_ ⟨hB, ?_, ?_, ?_, h0⟩
      (by simp [zMeasure, crc32zCert])
    · show c1.rip = _; rw [p1, ite_f (fun h => h0 (hz.mp h)), hrip]
      simp only [BitVec.add_assoc]; rfl
    · show c1.read .rax = _; rw [r1, hrax]
    · show c1.read .rsi = _; rw [r1, hrsi]
    · show c1.read .rdi = _; rw [r1, hrdi]

theorem add_end (b : Word) (n : Nat) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n % 8) + (b + BitVec.ofNat 64 (8 * (n / 8))) = b + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  have hb := b.isLt
  omega

theorem bec (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0xec, zLec⟩ := by
  intro m0 m ⟨hb, hrax, hrsi, hrdi, h0⟩ hrip _
  obtain ⟨c1, h1, e1⟩ := add_q_rr m.core m.memory 3 .rdi .rsi
  obtain ⟨c2, h2, e2⟩ := nop_eff c1 m.memory 1 0
  refine ⟨_, by simp only [zLec]; rw [run8_cons_of h1 e1.1, run8_cons_of h2 e2.1]; rfl, ?_⟩
  have hk : ∀ r, ¬ Scratch r → c2.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr; simp only [e2.2, e1.2]; simp [hr]
  have hN := arg2_lt m0
  have h8 : 8 * (arg2 m0 / 8) < 2 ^ 64 := by omega
  refine nxt 0xf0 zLf0 (by simp [crc32zBlocks]) ?_
    ⟨base_of hb rfl hk, 8 * (arg2 m0 / 8), le_rfl, by omega, ?_, ?_, ?_⟩ ?_
  · show c2.rip = _; rw [e2.1, e1.1, hrip]; simp only [BitVec.add_assoc]; rfl
  · show c2.read .rax = _; simp only [e2.2, e1.2]; simp [hrax]
  · show c2.read .rsi = _; simp only [e2.2, e1.2]; simp [hrsi]
  · show c2.read .rdi = _; simp only [e2.2, e1.2, ite_true, hrdi, hrsi]
    rw [add_end _ _ hN, rdx_eq]
  · simp only [zMeasure, crc32zCert]
    show _ - (c2.read .rsi - _).toNat + 1 < _
    have : c2.read .rsi = m0.core.read .rsi + BitVec.ofNat 64 (8 * (arg2 m0 / 8)) := by
      simp only [e2.2, e1.2]; simp [hrsi]
    rw [this, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8]
    omega

theorem xor_ff (x : BitVec 32) : W x ^^^ (0xffffffff#32 : BitVec 32).setWidth 64 = W (~~~x) := by
  rw [W, ← BitVec.setWidth_xor]
  congr 1
  have : (0xffffffff#32 : BitVec 32) = BitVec.allOnes 32 := by decide +kernel
  rw [this, BitVec.xor_allOnes]

theorem b111 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x111, zL111⟩ := by
  intro m0 m ⟨hb, hrax⟩ _ _
  obtain ⟨c1, h1, e1⟩ := movI32_eff m.core m.memory 5 .rdx 0xffffffff#32
  obtain ⟨c2, h2, e2⟩ := xor_q_rr c1 m.memory 3 .rax .rdx
  have hsp2 : c2.read .rsp = m.core.read .rsp := by simp only [e2.2, e1.2]; simp
  obtain ⟨c3, h3, p3, s3, o3⟩ := ret_end ⟨c2, m.memory⟩ (w := FnContract.retOf m0.core m0.memory)
    (by show (m.memory.readBytes (c2.read .rsp).toNat 8).bind _ = _
        rw [hsp2]; exact hb.frame.pop)
  refine ⟨_, by simp only [zL111]; rw [run8_cons_of h1 e1.1, run8_cons_of h2 e2.1]; exact h3, .inl ?_⟩
  refine Silmaril.X86.BlockCert.Frame.result_open hb.frame p3
    (by rw [s3]; show c2.read .rsp + _ = _; rw [hsp2]) (fun r hr => ?_) rfl ?_
  · have := cs_not_scratch hr
    simp only [Scratch, not_or] at this
    rw [o3 r (by simp [Silmaril.X86.sysv64_calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    show c2.read r = _; simp only [e2.2, e1.2]; simp [this.1, this.2.2.1]
  · show c3.read .rax = _
    rw [o3 .rax (by decide)]; show c2.read .rax = _
    simp only [e2.2, e1.2, ite_true, reduceCtorEq, ite_false, hrax]
    rw [xor_ff, ite_f hb.nz]
    rfl

theorem tbl_lt : crcTblAddr.toNat < 2 ^ 31 := by decide

theorem rsi_ofNat (m0 : MState) : m0.core.read .rsi = BitVec.ofNat 64 (arg1 m0) := by
  simp [arg1]

/-- The buffer byte `i` loads from `rB + i`. -/
theorem buf_load {entry : Word} {m0 m : MState} (hb : Base entry m0 m) {i : Nat}
    (hi : i < arg2 m0) {w : Word} (hw : w = m0.core.read .rsi + BitVec.ofNat 64 i) :
    loadN m.memory w 1 = some (BitVec.ofNat 64 (byteAt m0.memory (arg1 m0) i).toNat) := by
  rw [hb.frame.mem]
  exact TableFold.load_byte (hb.pre.2.2.2 hb.nz) hi (by rw [hw, rsi_ofNat])

theorem tbl_of {entry : Word} {m0 m : MState} (hb : Base entry m0 m) :
    TableAt m.memory crcTblAddr.toNat 256 crcT := by
  rw [hb.frame.mem]; exact hb.pre.2.2.1

/-- One table step on the zero-extended fold is the next fold. -/
theorem step_F (m0 : MState) (t : Nat) :
    TableFold.step crcT (W (F m0 t)) (byteAt m0.memory (arg1 m0) t) = W (F m0 (t + 1)) := by
  rw [step_crcT, F_succ]

set_option maxRecDepth 20000 in
theorem bf0 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0xf0, zLf0⟩ := by
  intro m0 m ⟨hb, t, hlo, hhi, hrax, hrsi, hrdi⟩ hrip _
  have hN := arg2_lt m0
  obtain ⟨c1, h1, e1⟩ := add_q_i8 m.core m.memory 4 .rsi 0x01#8
  obtain ⟨c2, h2, e2⟩ := mov_q c1 m.memory 3 .rdx .rax
  have hp2 : c2.read .rsi = m0.core.read .rsi + BitVec.ofNat 64 (t + 1) := by
    simp only [e2.2, e1.2]; simp only [reduceCtorEq, ite_false, ite_true, hrsi]
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    have : ((0x01#8 : BitVec 8).signExtend 64).toNat = 1 := by decide +kernel
    rw [this]; omega
  obtain ⟨c3, h3, r3, l3, o3⟩ := xor8_mem c2 m.memory 3 .rax .rsi 0xffffffff#32 _
    (buf_load hb hhi (i := t) (by
      rw [hp2]
      have : (0xffffffff#32 : BitVec 32).signExtend 64 = 0xffffffffffffffff#64 := by decide +kernel
      rw [this]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      have := (m0.core.read .rsi).isLt; omega))
  obtain ⟨c4, h4, e4⟩ := shr_q c3 m.memory 4 .rdx 8#8 (by decide)
  obtain ⟨c5, h5, e5⟩ := movzb c4 m.memory 3 .rax
  have hidx : c5.read .rax = BitVec.ofNat 64
      (TableFold.index (W (F m0 t)) (byteAt m0.memory (arg1 m0) t)) := by
    simp only [e5.2, ite_true, e4.2, reduceCtorEq, ite_false]
    exact TableFold.movzb_index (by rw [l3]; simp only [e2.2, e1.2, reduceCtorEq, ite_false, hrax])
  obtain ⟨c6, h6, e6⟩ := xor_q_mem c5 m.memory 8 .rdx (tblMem .rax rax_ne_rsp crcTblAddr)
    (crcT (TableFold.index (W (F m0 t)) (byteAt m0.memory (arg1 m0) t))) rfl (by
      rw [TableFold.tbl_addr tbl_lt c5 (TableFold.index_lt _ _) hidx]
      exact tbl_of hb _ (TableFold.index_lt _ _))
  obtain ⟨c7, h7, e7⟩ := mov_q c6 m.memory 3 .rax .rdx
  obtain ⟨c8, h8, r8, p8⟩ := cmp_jne8_end ⟨c7, m.memory⟩ .rsi .rdi 0xdf#8
  have hrun : run8 zLf0 m = some ⟨c8, m.memory⟩ := by
    simp only [zLf0]
    rw [run8_cons_of h1 e1.1, run8_cons_of h2 e2.1, run8_cons_of (m := ⟨c2, m.memory⟩) h3 r3,
      run8_cons_of (m := ⟨c3, m.memory⟩) h4 e4.1, run8_cons_of (m := ⟨c4, m.memory⟩) h5 e5.1,
      run8_cons_of (m := ⟨c5, m.memory⟩) h6 e6.1, run8_cons_of (m := ⟨c6, m.memory⟩) h7 e7.1]
    exact h8
  refine ⟨_, hrun, ?_⟩
  have hax : c8.read .rax = W (F m0 (t + 1)) := by
    rw [r8]; show c7.read .rax = _
    simp only [e7.2, ite_true, e6.2]
    rw [← step_F]; simp only [e5.2, e4.2, ite_true, reduceCtorEq, ite_false]
    rw [o3 .rdx (by decide)]; simp only [e2.2, e1.2, ite_true, reduceCtorEq, ite_false, hrax]
    rfl
  have hsi : c8.read .rsi = m0.core.read .rsi + BitVec.ofNat 64 (t + 1) := by
    rw [r8]; show c7.read .rsi = _
    simp only [e7.2, e6.2, e5.2, e4.2, reduceCtorEq, ite_false]
    rw [o3 .rsi (by decide)]; exact hp2
  have hdi : c8.read .rdi = m0.core.read .rsi + m0.core.read .rdx := by
    rw [r8]; show c7.read .rdi = _
    simp only [e7.2, e6.2, e5.2, e4.2, reduceCtorEq, ite_false]
    rw [o3 .rdi (by decide)]; simp only [e2.2, e1.2, reduceCtorEq, ite_false, hrdi]
  have hk : ∀ r, ¬ Scratch r → c8.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr
    rw [r8]; show c7.read r = _
    simp only [e7.2, e6.2, e5.2, e4.2, hr, ite_false]
    rw [o3 r hr.1]; simp only [e2.2, e1.2, hr, ite_false]
  have hB : Base entry m0 ⟨c8, m.memory⟩ := base_of hb rfl hk
  have heq : (c7.read .rsi = c7.read .rdi) ↔ t + 1 = arg2 m0 := by
    rw [← r8, ← r8, hsi, hdi, rdx_eq m0]
    exact Silmaril.X86.Stencils.ByteLoop.ptr_eq_iff (by omega) |>.trans (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN])
  by_cases hend : t + 1 = arg2 m0
  · refine nxt 0x111 zL111 (by simp [crc32zBlocks]) ?_ ⟨hB, ?_⟩ (by simp [zMeasure, crc32zCert])
    · show c8.rip = _
      rw [p8, ite_t (heq.mpr hend), e7.1, e6.1, e5.1, e4.1, r3, e2.1, e1.1, hrip]
      simp only [BitVec.add_assoc]; rfl
    · show c8.read .rax = _; rw [hax, hend]
  · refine nxt 0xf0 zLf0 (by simp [crc32zBlocks]) ?_
      ⟨hB, t + 1, by omega, by omega, hax, hsi, hdi⟩ ?_
    · show c8.rip = _
      rw [p8, ite_f (fun h => hend (heq.mp h)), e7.1, e6.1, e5.1, e4.1, r3, e2.1, e1.1, hrip]
      simp only [BitVec.add_assoc]; rfl
    · simp only [zMeasure, crc32zCert]
      show _ - (c8.read .rsi - _).toNat + 1 < _ - (m.core.read .rsi - _).toNat + 1
      rw [hsi, hrsi, sub_base, sub_base, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show t + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
      omega

theorem kOf_ne (g : Nat) (h1 : 1 ≤ g) (h7 : g ≤ 7) : kOf g ≠ 0 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨
    g = 6 ∨ g = 7 := by omega
  all_goals decide +kernel

theorem kOf_toNat (g : Nat) (h1 : 1 ≤ g) (h7 : g ≤ 7) :
    ((kOf g).signExtend 64).toNat = 2 ^ 64 - 8 + g := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨
    g = 6 ∨ g = 7 := by omega
  all_goals decide +kernel

theorem grp_addr (b : Word) (j g : Nat) (h1 : 1 ≤ g) (h7 : g ≤ 7) :
    b + BitVec.ofNat 64 (8 * j) + (8#8 : BitVec 8).signExtend 64 + (kOf g).signExtend 64 =
      b + BitVec.ofNat 64 (8 * j + g) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, kOf_toNat g h1 h7]
  have h8 : ((8#8 : BitVec 8).signExtend 64).toNat = 8 := by decide +kernel
  rw [h8]; simp only [BitVec.toNat_ofNat]
  have := b.isLt
  omega

/-- One of the seven `stepL` groups of the unrolled body. -/
theorem grp {entry : Word} {m0 m : MState} (hb : Base entry m0 m) {a d : Reg} (ha : a ≠ .rsp)
    (had : a ≠ d) (hcd : Reg.rcx ≠ d) {j g : Nat} (h1 : 1 ≤ g) (h7 : g ≤ 7)
    (hj : 8 * j + 8 ≤ arg2 m0) (s : MState) (hmem : s.memory = m.memory)
    (hrcx : s.core.read .rcx = m0.core.read .rsi + BitVec.ofNat 64 (8 * j) +
      (8#8 : BitVec 8).signExtend 64)
    (hA : s.core.read a = W (F m0 (8 * j + g))) (rest : List LI) :
    ∃ c, run8 (stepL a d .rcx (kOf g) crcTblAddr ha ++ rest) s = run8 rest ⟨c, s.memory⟩ ∧
      c.rip = s.core.rip + 21#64 ∧ c.read d = W (F m0 (8 * j + g + 1)) ∧
      ∀ r, r ≠ a → r ≠ d → c.read r = s.core.read r := by
  have hb' : loadN s.memory (s.core.read .rcx + (kOf g).signExtend 64) 1 =
      some (BitVec.ofNat 64 (byteAt m0.memory (arg1 m0) (8 * j + g)).toNat) := by
    rw [hmem]; exact buf_load hb (by omega) (by rw [hrcx, grp_addr _ _ _ h1 h7])
  have hT : TableAt s.memory crcTblAddr.toNat 256 crcT := by rw [hmem]; exact tbl_of hb
  obtain ⟨c, hrun, hrip, hd, _, ho⟩ := TableFold.stepL_run had hcd tbl_lt rest s hb' hT
  refine ⟨c, hrun, by rw [hrip, ite_f (kOf_ne g h1 h7)], ?_, ho⟩
  rw [hd, hA, step_F]

set_option maxRecDepth 20000 in
theorem b30 (entry : Word) : (crc32zCert entry).BlockVC (zQ entry) ⟨0x30, zL30⟩ := by
  intro m0 m ⟨hb, j, hj, hrax, hrcx, hrsi, hrdi⟩ hrip _
  have hN := arg2_lt m0
  have hj8 : 8 * j + 8 ≤ arg2 m0 := by omega
  have hT : TableAt m.memory crcTblAddr.toNat 256 crcT := tbl_of hb
  have hb0 : loadN m.memory (m.core.read .rcx + (0#32 : BitVec 32).signExtend 64) 1 =
      some (BitVec.ofNat 64 (byteAt m0.memory (arg1 m0) (8 * j)).toNat) := by
    refine buf_load hb (by omega) ?_
    have : (0#32 : BitVec 32).signExtend 64 = 0#64 := by decide +kernel
    rw [this, BitVec.add_zero, hrcx]
  obtain ⟨c1, run1, rip1, d1, _, p1, o1⟩ := TableFold.stepAddL_run (a := .rax) (d := .rdx) (p := .rcx) (k := 0) (tbl := crcTblAddr)
    (j := 8#8) (ha := rax_ne_rsp)
    (by decide) (by decide) (by decide) tbl_lt _ m hb0 hT
  have hrcx1 : c1.read .rcx = m0.core.read .rsi + BitVec.ofNat 64 (8 * j) +
      (8#8 : BitVec 8).signExtend 64 := by rw [p1, hrcx]
  have hA1 : c1.read .rdx = W (F m0 (8 * j + 1)) := by rw [d1, hrax, step_F]
  obtain ⟨c2, run2, rip2, d2, o2⟩ := grp hb (a := .rdx) (d := .rax) rdx_ne_rsp (by decide) (by decide) (le_refl 1)
    (by decide) hj8 ⟨c1, m.memory⟩ rfl hrcx1 hA1 _
  have hrcx2 : c2.read .rcx = _ := (o2 .rcx (by decide) (by decide)).trans hrcx1
  obtain ⟨c3, run3, rip3, d3, o3⟩ := grp hb (a := .rax) (d := .rdx) rax_ne_rsp (by decide) (by decide) (g := 2)
    (by decide) (by decide) hj8 ⟨c2, m.memory⟩ rfl hrcx2 d2 _
  have hrcx3 : c3.read .rcx = _ := (o3 .rcx (by decide) (by decide)).trans hrcx2
  obtain ⟨c4, run4, rip4, d4, o4⟩ := grp hb (a := .rdx) (d := .rax) rdx_ne_rsp (by decide) (by decide) (g := 3)
    (by decide) (by decide) hj8 ⟨c3, m.memory⟩ rfl hrcx3 d3 _
  have hrcx4 : c4.read .rcx = _ := (o4 .rcx (by decide) (by decide)).trans hrcx3
  obtain ⟨c5, run5, rip5, d5, o5⟩ := grp hb (a := .rax) (d := .rdx) rax_ne_rsp (by decide) (by decide) (g := 4)
    (by decide) (by decide) hj8 ⟨c4, m.memory⟩ rfl hrcx4 d4 _
  have hrcx5 : c5.read .rcx = _ := (o5 .rcx (by decide) (by decide)).trans hrcx4
  obtain ⟨c6, run6, rip6, d6, o6⟩ := grp hb (a := .rdx) (d := .rax) rdx_ne_rsp (by decide) (by decide) (g := 5)
    (by decide) (by decide) hj8 ⟨c5, m.memory⟩ rfl hrcx5 d5 _
  have hrcx6 : c6.read .rcx = _ := (o6 .rcx (by decide) (by decide)).trans hrcx5
  obtain ⟨c7, run7, rip7, d7, o7⟩ := grp hb (a := .rax) (d := .rdx) rax_ne_rsp (by decide) (by decide) (g := 6)
    (by decide) (by decide) hj8 ⟨c6, m.memory⟩ rfl hrcx6 d6 _
  have hrcx7 : c7.read .rcx = _ := (o7 .rcx (by decide) (by decide)).trans hrcx6
  obtain ⟨c8, run8', rip8, d8, o8⟩ := grp hb (a := .rdx) (d := .rax) rdx_ne_rsp (by decide) (by decide) (g := 7)
    (by decide) (by decide) hj8 ⟨c7, m.memory⟩ rfl hrcx7 d7 _
  have hrcx8 : c8.read .rcx = _ := (o8 .rcx (by decide) (by decide)).trans hrcx7
  obtain ⟨c9, h9, r9, p9⟩ := cmp_jne_end ⟨c8, m.memory⟩ .rcx .rsi 0xffffff4c#32
  have hrun : run8 zL30 m = some ⟨c9, m.memory⟩ :=
    run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8'.trans h9)))))))
  refine ⟨_, hrun, ?_⟩
  -- registers outside the scratch set are kept
  have hk : ∀ r, ¬ Scratch r → c9.read r = m.core.read r := by
    intro r hr; simp only [Scratch, not_or] at hr
    obtain ⟨ha, hc, hd, _, _⟩ := hr
    rw [r9]; show c8.read r = _
    rw [o8 r hd ha, o7 r ha hd, o6 r hd ha, o5 r ha hd, o4 r hd ha, o3 r ha hd, o2 r hd ha,
      o1 r ha hd hc]
  have hB : Base entry m0 ⟨c9, m.memory⟩ := base_of hb rfl hk
  have hcx : c9.read .rcx = m0.core.read .rsi + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [r9]; show c8.read .rcx = _; rw [hrcx8, BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    have h8 : ((8#8 : BitVec 8).signExtend 64).toNat = 8 := by decide +kernel
    rw [h8]; simp only [BitVec.toNat_ofNat]; omega
  have hsi : c9.read .rsi = m0.core.read .rsi + BitVec.ofNat 64 (8 * (arg2 m0 / 8)) := by
    rw [r9]; show c8.read .rsi = _
    rw [o8 _ (by decide) (by decide), o7 _ (by decide) (by decide), o6 _ (by decide) (by decide),
      o5 _ (by decide) (by decide), o4 _ (by decide) (by decide), o3 _ (by decide) (by decide),
      o2 _ (by decide) (by decide), o1 _ (by decide) (by decide) (by decide), hrsi]
  have hdi : c9.read .rdi = m0.core.read .rdx := by
    rw [r9]; show c8.read .rdi = _
    rw [o8 _ (by decide) (by decide), o7 _ (by decide) (by decide), o6 _ (by decide) (by decide),
      o5 _ (by decide) (by decide), o4 _ (by decide) (by decide), o3 _ (by decide) (by decide),
      o2 _ (by decide) (by decide), o1 _ (by decide) (by decide) (by decide), hrdi]
  have hax : c9.read .rax = W (F m0 (8 * (j + 1))) := by
    rw [r9]; exact d8
  have heq : (c8.read .rcx = c8.read .rsi) ↔ j + 1 = arg2 m0 / 8 := by
    rw [show c8.read .rcx = c9.read .rcx from (r9 _).symm,
      show c8.read .rsi = c9.read .rsi from (r9 _).symm, hcx, hsi]
    exact (Silmaril.X86.Stencils.ByteLoop.ptr_eq_iff (by omega)).trans (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  have hripE : ∀ o : Nat, c8.rip + 9#64 = entry + BitVec.ofNat 64 0xe4 := by
    intro _
    rw [rip8, rip7, rip6, rip5, rip4, rip3, rip2, rip1, hrip]
    simp only [BitVec.add_assoc]; rfl
  by_cases hend : j + 1 = arg2 m0 / 8
  · refine nxt 0xe4 zLe4 (by simp [crc32zBlocks]) ?_ ⟨hB, ?_, hsi, hdi⟩
      (by simp only [zMeasure, crc32zCert]; omega)
    · show c9.rip = _; rw [p9, ite_t (heq.mpr hend)]; exact hripE 0
    · rw [← hend]; exact hax
  · refine nxt 0x30 zL30 (by simp [crc32zBlocks]) ?_
      ⟨hB, j + 1, by omega, hax, hcx, hsi, hdi⟩ ?_
    · show c9.rip = _; rw [p9, ite_f (fun h => hend (heq.mp h)), hripE 0]
      simp only [BitVec.add_assoc]; rfl
    · simp only [zMeasure, crc32zCert]
      show _ - (c9.read .rcx - _).toNat / 8 + 20 < _ - (m.core.read .rcx - _).toNat / 8 + 20
      rw [hcx, hrcx, sub_base, sub_base, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 8 * (j + 1) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega)]
      omega

theorem crc32z_checked0 : (crc32zCert 0).checked = true := by decide +kernel

theorem crc32z_checked (entry : Word) : (crc32zCert entry).checked = true := crc32z_checked0

theorem crc32z_vc (entry : Word) : (crc32zCert entry).VC (zQ entry) := Cert.vc_of_blocks (by
  simp only [crc32zCert, crc32zBlocks, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [b00 entry, b12 entry, b1e entry, b30 entry, be4 entry, be7 entry, bec entry, bf0 entry,
    b111 entry, b120 entry])

/-- **`crc32_z` is totally correct** on the open machine, for every load address. -/
theorem crc32z_total (entry : Word) : (crc32zContract entry).Total Open.isa :=
  Cert.total _ (entry := ⟨0x00, zL00⟩) (by simp [crc32zCert, crc32zBlocks]) (crc32z_checked entry)
    (crc32z_vc entry) fun m hab he => ⟨he.2.1, by rw [he.1]; simp [crc32zCert], rfl, hab, he⟩

end Silmaril.Proofs.X86.Ladder.ZlibChecksums
