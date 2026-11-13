module

public import Silmaril.Machine.RiscV.Lir.Bits.Defs
/-!
# Memory access selection

## Linear memory

The Lir linear memory of `size` bytes is placed at `memBase` in the
`Process.Memory` of the machine; `MemRel base lm mem` says that byte `a < size`
of the Lir memory is the backing byte at `base + a`. Register `s11` holds
`memBase`.

A Lir access at address `x + off` (no wrap-around, in bounds) becomes an access
at `memBase + x + off`. The effective address is computed into `t0`
(`add t0, s11, x`, and for offsets above 2040 also `li t1, off; add t0, t0, t1`).

Lir accesses have no alignment requirement, while this machine model traps on
misaligned `LH/LW/LD/SH/SW/SD`. Linear-memory accesses are therefore always
performed one byte at a time: loads assemble `LBU` results with `SLLI`/`OR`
(followed by `SLLI`/`SRAI` for sign extension), and stores write `SB` of
`SRLI`-shifted source values. Stack slots are always 8-byte aligned and use
`LD`/`SD`.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.Process (Memory)
open Silmaril.RiscV.Ext (Compute MState)

/-! ## Immediates and effective addresses -/

def imm12 (n : Nat) : BitVec 12 := BitVec.ofNat 12 n

theorem imm12_signExtend {n : Nat} (h : n < 2048) :
    (imm12 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp [imm12, BitVec.toNat_setWidth]
    omega
  · rw [BitVec.msb_eq_decide]; simp [imm12]; omega

theorem ea_toNat {s : State} {b : Reg} {B n : Nat} (hb : s.read b = BitVec.ofNat 64 B)
    (hn : n < 2048) (hB : B + n < 2 ^ 64) :
    (Ext.effectiveAddress s b (imm12 n)).toNat = B + n := by
  rw [Ext.effectiveAddress, hb, imm12_signExtend hn, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hB

/-! ## One-instruction steps -/

theorem runSeq_compute_cons (c : Compute) (rest : List Ext.Instr) (m : MState) :
    runSeq (.compute c :: rest) m = runSeq rest ⟨c.step m.core, m.memory⟩ :=
  runSeq_cons_of (Ext.Instr.exec_compute m c) (Ext.Compute.step_pc c m.core)

theorem runSeq_computes_append (cs : List Compute) (rest : List Ext.Instr) (m : MState) :
    runSeq (cs.map .compute ++ rest) m =
      runSeq rest ⟨Machine.Block.run Compute.step cs m.core, m.memory⟩ := by
  rw [runSeq_append, runSeq_compute]; rfl

theorem runSeq_load_cons {op : Ext.LoadOp} {rd rs : Reg} {off : BitVec 12}
    {rest : List Ext.Instr} {m : MState} {bytes : List Process.Byte}
    (aligned : (Ext.effectiveAddress m.core rs off).toNat % op.width = 0)
    (read : m.memory.readBytes (Ext.effectiveAddress m.core rs off).toNat op.width = some bytes) :
    runSeq (.load op rd rs off :: rest) m =
      runSeq rest ⟨{ m.core.write rd (op.value bytes) with pc := m.core.pc + 4 }, m.memory⟩ :=
  runSeq_cons_of (Ext.Instr.exec_load m aligned read) (by simp)

theorem runSeq_store_cons {op : Ext.StoreOp} {rs1 rs2 : Reg} {off : BitVec 12}
    {rest : List Ext.Instr} {m : MState} {after : Memory}
    (aligned : (Ext.effectiveAddress m.core rs1 off).toNat % op.width = 0)
    (written : m.memory.writeBytes (Ext.effectiveAddress m.core rs1 off).toNat
      (Ext.leBytes op.width (m.core.read rs2)) = some after) :
    runSeq (.store op rs1 rs2 off :: rest) m =
      runSeq rest ⟨{ m.core with pc := m.core.pc + 4 }, after⟩ :=
  runSeq_cons_of (Ext.Instr.exec_store m aligned written) rfl

/-! ## Stack words -/

theorem wordAt_write {mem mem' : Memory} {a : Nat} {v : Word}
    (hw : mem.writeBytes a (Ext.leBytes 8 v) = some mem') (hr : mem.Permitted .read a 8) :
    WordAt mem' a v := by
  have := Ext.MemoryLemmas.readBytes_writeBytes hw (by simpa using hr)
  unfold WordAt; simpa using this

theorem wordAt_frame {mem mem' : Memory} {a len b : Nat} {x : Word}
    (hw : Memory.WritesOnly mem mem' a len) (hd : b + 8 ≤ a ∨ a + len ≤ b) (h : WordAt mem b x) :
    WordAt mem' b x := by
  unfold WordAt Memory.readBytes at *
  rw [Ext.MemoryLemmas.readWith_writesOnly hw .read b 8 hd]
  exact h

/-- `LD rd, n(base)` of a word at an 8-byte-aligned stack address. -/
theorem runSeq_ld {rd b : Reg} {n B : Nat} {x : Word} {rest : List Ext.Instr} {m : MState}
    (hb : m.core.read b = BitVec.ofNat 64 B) (hn : n < 2048) (hB : B + n < 2 ^ 64)
    (hal : (B + n) % 8 = 0) (hw : WordAt m.memory (B + n) x) :
    runSeq (.load .ld rd b (imm12 n) :: rest) m =
      runSeq rest ⟨{ m.core.write rd x with pc := m.core.pc + 4 }, m.memory⟩ := by
  have e := ea_toNat hb hn hB
  rw [runSeq_load_cons (bytes := Ext.leBytes 8 x) (by rw [e]; simpa [Ext.LoadOp.width] using hal)
    (by rw [e]; exact hw), Ext.ld_value_leBytes]

/-- `SD rs, n(base)` at an 8-byte-aligned writable address. -/
theorem runSeq_sd {rs b : Reg} {n B : Nat} {rest : List Ext.Instr} {m : MState}
    (hb : m.core.read b = BitVec.ofNat 64 B) (hn : n < 2048) (hB : B + n < 2 ^ 64)
    (hal : (B + n) % 8 = 0) (hp : m.memory.Permitted .write (B + n) 8) :
    ∃ mem', m.memory.writeBytes (B + n) (Ext.leBytes 8 (m.core.read rs)) = some mem' ∧
      runSeq (.store .sd b rs (imm12 n) :: rest) m =
        runSeq rest ⟨{ m.core with pc := m.core.pc + 4 }, mem'⟩ := by
  have e := ea_toNat hb hn hB
  have hw : m.memory.writeBytes (B + n) (Ext.leBytes 8 (m.core.read rs)) =
      some { m.memory with
        bytes := (Memory.install m.memory.bytes (B + n) (Ext.leBytes 8 (m.core.read rs))) } :=
    Ext.MemoryLemmas.writeBytes_eq_some_iff.mpr ⟨by simpa using hp, rfl⟩
  refine ⟨_, hw, ?_⟩
  apply runSeq_store_cons
  · rw [e]; simpa [Ext.StoreOp.width] using hal
  · rw [e]; exact hw

/-! ## The linear memory relation -/

/-- Byte `a` of the Lir memory is the backing byte at `base + a`. -/
def MemRel (base : Nat) (lm : Machine.Lir.Memory) (mem : Memory) : Prop :=
  ∀ a < lm.size, mem.bytes.get? (base + a) = some (lm.bytes a)

/-! ## Byte loads -/

def lbu (rd rs : Reg) (i : Nat) : Ext.Instr := .load .lbu rd rs (imm12 i)

/-- Load the `n + 1` bytes at `t0 + i … t0 + i + n` into `rd`, little-endian. -/
def loadBytes (rd : Reg) (i : Nat) : Nat → List Ext.Instr
  | 0 => [lbu rd t0 i]
  | n + 1 => loadBytes rd (i + 1) n ++
      [.compute (.base (.shift .sll rd rd 8#6)), lbu t1 t0 i,
        .compute (.base (.reg .or rd rd t1))]

theorem lbu_value (b : Process.Byte) : Ext.LoadOp.lbu.value [b] = b.setWidth 64 := by
  simp [Ext.LoadOp.value, Ext.LoadOp.width, Ext.LoadOp.signed, Ext.leValue]

theorem readByte {S : Space} {n : Nat} {mem : Memory} (hr : mem.regions = S.regions n)
    (hv : S.Valid n) {lm : Machine.Lir.Memory} (hs : lm.size = S.memSize)
    (hrel : MemRel S.memBase lm mem) {a : Nat} (ha : a < lm.size) :
    mem.readBytes (S.memBase + a) 1 = some [lm.bytes a] := by
  apply Memory.readWith_eq mem .read (S.memBase + a) [lm.bytes a]
  · exact permitted_mem hr hv .read (by decide) (by omega) (by simp; omega)
  · intro k hk
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    simpa using hrel a ha

theorem loadBytes_spec {S : Space} {n : Nat} (hv : S.Valid n) {lm : Machine.Lir.Memory}
    (hs : lm.size = S.memSize) {rd : Reg} (hrd : ¬ Scratch rd) (hrd0 : rd ≠ 0#5) {A : Nat} :
    ∀ (k i : Nat) (m : MState), m.memory.regions = S.regions n → MemRel S.memBase lm m.memory →
    m.core.read t0 = BitVec.ofNat 64 (S.memBase + A) → i + k < 2048 → A + i + k < lm.size →
    ∃ m', runSeq (loadBytes rd i k) m = some m' ∧ m'.memory = m.memory ∧
      m'.core.read rd = Machine.Lir.readLE lm.bytes (A + i) (k + 1) ∧
      ∀ r, r ≠ rd → r ≠ t1 → m'.core.read r = m.core.read r := by
  obtain ⟨hrd0', hrd1, hrd2⟩ := ne_scratch hrd
  have hmem := hv.mem_end
  intro k
  induction k with
  | zero =>
    intro i m hr hrel ht0 hi hA
    have e := ea_toNat ht0 (show i < 2048 by omega) (show S.memBase + A + i < 2 ^ 64 by omega)
    have rb := readByte hr hv hs hrel (a := A + i) (by omega)
    rw [← Nat.add_assoc] at rb
    refine ⟨_, runSeq_load_cons (rest := []) (by rw [e]; exact Nat.mod_one _)
      (by rw [e]; exact rb), rfl, ?_, ?_⟩
    · simp [State.read_setPc, hrd0, lbu_value, Machine.Lir.readLE]
    · intro r hr1 _
      simp [State.read_setPc, State.read_write_eq, hr1]
  | succ k ih =>
    intro i m hr hrel ht0 hi hA
    obtain ⟨m₁, h₁, mem₁, rd₁, fr₁⟩ := ih (i + 1) m hr hrel ht0 (by omega) (by omega)
    have t0₁ : m₁.core.read t0 = BitVec.ofNat 64 (S.memBase + A) := by
      rw [fr₁ t0 hrd0'.symm (by simp)]; exact ht0
    set c₁ : Compute := .base (.shift .sll rd rd 8#6)
    have t0₂ : (c₁.step m₁.core).read t0 = BitVec.ofNat 64 (S.memBase + A) := by
      simp [c₁, RiscV.Instr.dest, hrd0'.symm, t0₁]
    have e := ea_toNat t0₂ (show i < 2048 by omega) (show S.memBase + A + i < 2 ^ 64 by omega)
    have rb := readByte (mem₁ ▸ hr) hv hs (mem₁ ▸ hrel) (a := A + i) (by omega)
    rw [← Nat.add_assoc] at rb
    set c₃ : Compute := .base (.reg .or rd rd t1)
    let core₃ : State :=
      { (c₁.step m₁.core).write t1 (Ext.LoadOp.lbu.value [lm.bytes (A + i)]) with
        pc := (c₁.step m₁.core).pc + 4 }
    refine ⟨⟨c₃.step core₃, m₁.memory⟩, ?_, mem₁, ?_, ?_⟩
    · rw [loadBytes, runSeq_append, h₁, Option.bind_some, runSeq_compute_cons,
        lbu, runSeq_load_cons (m := ⟨c₁.step m₁.core, m₁.memory⟩)
          (by rw [e]; exact Nat.mod_one _) (by rw [e]; exact rb),
        runSeq_compute_cons, runSeq_nil]
    · simp only [core₃, c₃, c₁, Ext.Compute.step_base, read_base_step,
        RiscV.Instr.dest, RiscV.Instr.value, RiscV.RegOp.eval, State.read_setPc,
        State.read_write_eq, RiscV.ShiftOp.eval, hrd0, hrd1, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte, t1_ne_zero, lbu_value, rd₁, and_true]
      conv_rhs => rw [Machine.Lir.readLE]
      rw [BitVec.or_comm, show A + (i + 1) = A + i + 1 by omega]
      rfl
    · intro r h1 h2
      simp only [core₃, c₃, c₁, Ext.Compute.step_base, read_base_step,
        RiscV.Instr.dest, State.read_setPc, State.read_write_eq, h1, h2, false_and, ↓reduceIte]
      exact fr₁ r h1 h2

/-! ## Byte stores -/

def sb (base src : Reg) (i : Nat) : Ext.Instr := .store .sb base src (imm12 i)

/-- Store bytes `0 … n - 1` of `rs` at `t0 + i … t0 + i + n - 1`. -/
def storeBytes (rs : Reg) (i : Nat) : Nat → List Ext.Instr
  | 0 => []
  | n + 1 => storeBytes rs i n ++
      [.compute (.base (.shift .srl t1 rs (BitVec.ofNat 6 (8 * n)))), sb t0 t1 (i + n)]

theorem leBytes_one (w : Word) : Ext.leBytes 1 w = [w.setWidth 8] := rfl

theorem storeBytes_spec {S : Space} {n : Nat} (hv : S.Valid n) {lm : Machine.Lir.Memory}
    (hs : lm.size = S.memSize) {rs : Reg} (hrs : ¬ Scratch rs) {A i : Nat} :
    ∀ (k : Nat) (m : MState), m.memory.regions = S.regions n →
    m.core.read t0 = BitVec.ofNat 64 (S.memBase + A) → i + k ≤ 2048 → A + i + k ≤ lm.size →
    k ≤ 8 →
    ∃ m', runSeq (storeBytes rs i k) m = some m' ∧ m'.memory.regions = m.memory.regions ∧
      (∀ q, m'.memory.bytes.get? q =
        if S.memBase + A + i ≤ q ∧ q < S.memBase + A + i + k then
          some (Machine.LittleEndian.wordByte (m.core.read rs) (q - (S.memBase + A + i)))
        else m.memory.bytes.get? q) ∧
      ∀ r, r ≠ t1 → m'.core.read r = m.core.read r := by
  obtain ⟨hrs0, hrs1, hrs2⟩ := ne_scratch hrs
  have hmem := hv.mem_end
  intro k
  induction k with
  | zero =>
    intro m _ _ _ _ _
    refine ⟨m, rfl, rfl, fun q => ?_, fun _ _ => rfl⟩
    simp only [Nat.add_zero]
    rw [ite_false_of (by omega)]
  | succ k ih =>
    intro m hr ht0 hi hA hk
    obtain ⟨m₁, h₁, reg₁, bytes₁, fr₁⟩ := ih m hr ht0 (by omega) (by omega) (by omega)
    set c : Compute := .base (.shift .srl t1 rs (BitVec.ofNat 6 (8 * k)))
    have t0₂ : (c.step m₁.core).read t0 = BitVec.ofNat 64 (S.memBase + A) := by
      simp only [c, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, t0_ne_t1, false_and,
        ↓reduceIte]
      rw [fr₁ t0 t0_ne_t1]; exact ht0
    have t1₂ : (c.step m₁.core).read t1 = m.core.read rs >>> (8 * k) := by
      simp only [c, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq, t1_ne_zero,
        not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.ShiftOp.eval]
      rw [fr₁ rs hrs1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have e := ea_toNat t0₂ (show i + k < 2048 by omega) (show S.memBase + A + (i + k) < 2 ^ 64 by omega)
    have perm : m₁.memory.Permitted .write (S.memBase + A + (i + k)) 1 :=
      permitted_mem (reg₁.trans hr) hv .write (by decide) (by omega) (by omega)
    have hw : m₁.memory.writeBytes (S.memBase + A + (i + k))
        (Ext.leBytes 1 ((c.step m₁.core).read t1)) =
        some { m₁.memory with bytes := (Memory.install m₁.memory.bytes (S.memBase + A + (i + k))
          (Ext.leBytes 1 ((c.step m₁.core).read t1))) } :=
      Ext.MemoryLemmas.writeBytes_eq_some_iff.mpr ⟨by simpa using perm, rfl⟩
    refine ⟨⟨{ c.step m₁.core with pc := (c.step m₁.core).pc + 4 },
      { m₁.memory with bytes := (Memory.install m₁.memory.bytes (S.memBase + A + (i + k))
          (Ext.leBytes 1 ((c.step m₁.core).read t1))) }⟩, ?_, reg₁, ?_, ?_⟩
    · rw [storeBytes, runSeq_append, h₁, Option.bind_some, runSeq_compute_cons, sb,
        runSeq_store_cons (m := ⟨c.step m₁.core, m₁.memory⟩) (by rw [e]; exact Nat.mod_one _)
          (by rw [e]; exact hw), runSeq_nil]
    · intro q
      by_cases hq : q = S.memBase + A + (i + k)
      · subst hq
        have := Memory.install_get m₁.memory.bytes (S.memBase + A + (i + k))
          (Ext.leBytes 1 ((c.step m₁.core).read t1)) 0 (by simp)
        simp only [Nat.add_zero] at this
        have hb : (Ext.leBytes 1 ((c.step m₁.core).read t1))[0]'(by simp) =
            Machine.LittleEndian.wordByte (m.core.read rs) k := by
          simp only [leBytes_one, List.getElem_cons_zero, t1₂, Machine.LittleEndian.wordByte]
        rw [this, hb, ite_true_of (by omega)]
        congr 2; omega
      · rw [Memory.install_outside _ _ _ _ (by simp; omega), bytes₁ q]
        by_cases hin : S.memBase + A + i ≤ q ∧ q < S.memBase + A + i + k
        · rw [ite_true_of hin, ite_true_of (by omega)]
        · rw [ite_false_of hin, ite_false_of (by omega)]
    · intro r hr1
      simp only [c, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, State.read_setPc, hr1,
        false_and, ↓reduceIte]
      exact fr₁ r hr1

/-! ## Linear-memory loads and stores -/

/-- Effective address into `t0`, and the remaining immediate. -/
def addrSetup (rb : Reg) (off : Nat) : List Ext.Instr × Nat :=
  if off ≤ 2040 then ([.compute (.base (.reg .add t0 s11 rb))], off)
  else ((li t1 (BitVec.ofNat 64 off)).map .compute ++
    [.compute (.base (.reg .add t0 s11 rb)), .compute (.base (.reg .add t0 t0 t1))], 0)

theorem addrSetup_spec {rb : Reg} (hrb : ¬ Scratch rb) (off : Nat) {base : Nat} (m : MState)
    (hbase : m.core.read s11 = BitVec.ofNat 64 base) :
    ∃ m', runSeq (addrSetup rb off).1 m = some m' ∧ m'.memory = m.memory ∧
      (addrSetup rb off).2 ≤ 2040 ∧ (addrSetup rb off).2 ≤ off ∧
      m'.core.read t0 = BitVec.ofNat 64 (base + (m.core.read rb).toNat + (off - (addrSetup rb off).2)) ∧
      ∀ r, ¬ Scratch r → m'.core.read r = m.core.read r := by
  obtain ⟨hrb0, hrb1, hrb2⟩ := ne_scratch hrb
  unfold addrSetup
  split
  · rename_i hoff
    refine ⟨_, runSeq_compute_cons _ _ _, ?_, hoff, le_rfl, ?_, ?_⟩
    · rfl
    · simp only [Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq, t0_ne_zero,
        not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.RegOp.eval, hbase,
        Nat.sub_self, Nat.add_zero]
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · intro r hr
      obtain ⟨h0, _, _⟩ := ne_scratch hr
      simp [RiscV.Instr.dest, h0]
  · rename_i hoff
    refine ⟨_, by rw [runSeq_computes_append, runSeq_compute_cons, runSeq_compute_cons]; rfl,
      ?_, by omega, by omega, ?_, ?_⟩
    · rfl
    · have hl := li_value t1 t1_ne_zero (BitVec.ofNat 64 off) m.core
      have hs := run_frame (li_dests t1 (BitVec.ofNat 64 off)) m.core s11 (by decide) (by decide)
      have hb := run_frame (li_dests t1 (BitVec.ofNat 64 off)) m.core rb hrb1 hrb
      simp only [Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq, t0_ne_zero,
        not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.RegOp.eval, t1_ne_t0,
        false_and, hl, hs, hb, hbase, Nat.sub_zero]
      rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · intro r hr
      obtain ⟨h0, h1, _⟩ := ne_scratch hr
      simp only [Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, h0, false_and,
        ↓reduceIte]
      exact run_frame (li_dests t1 _) m.core r h1 hr

def signTail (w : Machine.Lir.Width) (e : Machine.Lir.Ext) (rd : Reg) : List Ext.Instr :=
  match e, w with
  | .sign, .b1 => [.compute (.base (.shift .sll rd rd (BitVec.ofNat 6 56))),
      .compute (.base (.shift .sra rd rd (BitVec.ofNat 6 56)))]
  | .sign, .b2 => [.compute (.base (.shift .sll rd rd (BitVec.ofNat 6 48))),
      .compute (.base (.shift .sra rd rd (BitVec.ofNat 6 48)))]
  | .sign, .b4 => [.compute (.base (.shift .sll rd rd (BitVec.ofNat 6 32))),
      .compute (.base (.shift .sra rd rd (BitVec.ofNat 6 32)))]
  | _, _ => []

def selLoad (w : Machine.Lir.Width) (e : Machine.Lir.Ext) (rd rb : Reg) (off : Nat) :
    List Ext.Instr :=
  (addrSetup rb off).1 ++ loadBytes rd (addrSetup rb off).2 (w.bytes - 1) ++ signTail w e rd

def selStore (w : Machine.Lir.Width) (rb : Reg) (off : Nat) (rs : Reg) : List Ext.Instr :=
  (addrSetup rb off).1 ++ storeBytes rs (addrSetup rb off).2 w.bytes

theorem width_bytes_pos (w : Machine.Lir.Width) : 0 < w.bytes ∧ w.bytes ≤ 8 := by
  cases w <;> decide

theorem signTail_sext (sh k : Nat) (hk0 : 0 < k) (hsh : sh + k = 64) {w : Machine.Lir.Width}
    (hw : 8 * w.bytes = k) {rd : Reg} (hrd0 : rd ≠ 0#5) (m : MState) :
    ∃ m', runSeq [.compute (.base (.shift .sll rd rd (BitVec.ofNat 6 sh))),
        .compute (.base (.shift .sra rd rd (BitVec.ofNat 6 sh)))] m = some m' ∧
      m'.memory = m.memory ∧
      m'.core.read rd = Machine.Lir.extend w .sign (m.core.read rd) ∧
      ∀ r, r ≠ rd → m'.core.read r = m.core.read r := by
  subst hw
  refine ⟨_, by rw [runSeq_compute_cons, runSeq_compute_cons, runSeq_nil], ?_, ?_, ?_⟩
  · rfl
  · have h := sext_shifts (m.core.read rd) (8 * w.bytes) hk0 (by omega)
    have e : (BitVec.ofNat 6 sh).toNat = 64 - 8 * w.bytes := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq, hrd0,
      not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.ShiftOp.eval,
      Machine.Lir.extend, e]
    exact h
  · intro r hr
    simp [RiscV.Instr.dest, hr]

theorem signTail_spec (w : Machine.Lir.Width) (e : Machine.Lir.Ext) {rd : Reg} (hrd0 : rd ≠ 0#5)
    (m : MState) :
    ∃ m', runSeq (signTail w e rd) m = some m' ∧ m'.memory = m.memory ∧
      m'.core.read rd = Machine.Lir.extend w e (m.core.read rd) ∧
      ∀ r, r ≠ rd → m'.core.read r = m.core.read r := by
  cases e with
  | zero =>
    refine ⟨m, ?_, rfl, ?_, fun _ _ => rfl⟩
    · cases w <;> rfl
    · rfl
  | sign =>
    cases w
    case b8 =>
      refine ⟨m, rfl, rfl, ?_, fun _ _ => rfl⟩
      simp [Machine.Lir.extend, Machine.Lir.Width.bytes]
    case b1 => exact signTail_sext 56 8 (by decide) (by decide) rfl hrd0 m
    case b2 => exact signTail_sext 48 16 (by decide) (by decide) rfl hrd0 m
    case b4 => exact signTail_sext 32 32 (by decide) (by decide) rfl hrd0 m

theorem selLoad_spec {S : Space} {n : Nat} (hv : S.Valid n) {lm : Machine.Lir.Memory}
    (hs : lm.size = S.memSize) {rd rb : Reg} (hrd : ¬ Scratch rd) (hrd0 : rd ≠ 0#5)
    (hrb : ¬ Scratch rb) (m : MState) (hr : m.memory.regions = S.regions n)
    (hrel : MemRel S.memBase lm m.memory) (hbase : m.core.read s11 = BitVec.ofNat 64 S.memBase)
    {w : Machine.Lir.Width} {e : Machine.Lir.Ext} {off : Nat} {z : Word}
    (hl : lm.load w e ((m.core.read rb).toNat + off) = some z) :
    ∃ m', runSeq (selLoad w e rd rb off) m = some m' ∧ m'.memory = m.memory ∧
      m'.core.read rd = z ∧ ∀ r, r ≠ rd → ¬ Scratch r → m'.core.read r = m.core.read r := by
  unfold Machine.Lir.Memory.load at hl
  split at hl
  · rename_i hin
    cases hl
    unfold Machine.Lir.Memory.InBounds at hin
    obtain ⟨wpos, wle⟩ := width_bytes_pos w
    obtain ⟨m₁, h₁, mem₁, hi, hioff, t0₁, fr₁⟩ := addrSetup_spec hrb off m hbase
    set i := (addrSetup rb off).2
    obtain ⟨m₂, h₂, mem₂, rd₂, fr₂⟩ := loadBytes_spec hv hs hrd hrd0 (A := (m.core.read rb).toNat + (off - i))
      (w.bytes - 1) i m₁ (mem₁ ▸ hr) (mem₁ ▸ hrel) (by rw [t0₁, Nat.add_assoc]) (by omega)
      (by omega)
    obtain ⟨m₃, h₃, mem₃, rd₃, fr₃⟩ := signTail_spec w e hrd0 m₂
    refine ⟨m₃, ?_, by rw [mem₃, mem₂, mem₁], ?_, ?_⟩
    · rw [selLoad, runSeq_append, runSeq_append, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
    · rw [rd₃, rd₂, show w.bytes - 1 + 1 = w.bytes by omega,
        show (m.core.read rb).toNat + (off - i) + i = (m.core.read rb).toNat + off by omega]
    · intro r h1 h2
      obtain ⟨_, h2', _⟩ := ne_scratch h2
      rw [fr₃ r h1, fr₂ r h1 h2', fr₁ r h2]
  · cases hl

theorem selStore_spec {S : Space} {n : Nat} (hv : S.Valid n) {lm lm' : Machine.Lir.Memory}
    (hs : lm.size = S.memSize) {rb rs : Reg} (hrb : ¬ Scratch rb) (hrs : ¬ Scratch rs)
    (m : MState) (hr : m.memory.regions = S.regions n)
    (hrel : MemRel S.memBase lm m.memory) (hbase : m.core.read s11 = BitVec.ofNat 64 S.memBase)
    {w : Machine.Lir.Width} {off : Nat}
    (hst : lm.store w ((m.core.read rb).toNat + off) (m.core.read rs) = some lm') :
    ∃ m', runSeq (selStore w rb off rs) m = some m' ∧ m'.memory.regions = m.memory.regions ∧
      MemRel S.memBase lm' m'.memory ∧
      (∀ q, ¬ S.InMem q → m'.memory.bytes.get? q = m.memory.bytes.get? q) ∧
      ∀ r, ¬ Scratch r → m'.core.read r = m.core.read r := by
  unfold Machine.Lir.Memory.store at hst
  split at hst
  · rename_i hin
    cases hst
    unfold Machine.Lir.Memory.InBounds at hin
    obtain ⟨wpos, wle⟩ := width_bytes_pos w
    obtain ⟨m₁, h₁, mem₁, hi, hioff, t0₁, fr₁⟩ := addrSetup_spec hrb off m hbase
    set i := (addrSetup rb off).2
    set A := (m.core.read rb).toNat + (off - i)
    obtain ⟨m₂, h₂, reg₂, bytes₂, fr₂⟩ := storeBytes_spec hv hs hrs (A := A) (i := i)
      w.bytes m₁ (mem₁ ▸ hr) (by rw [t0₁, Nat.add_assoc]) (by omega) (by omega) wle
    have hmem := hv.mem_end
    refine ⟨m₂, ?_, by rw [reg₂, mem₁], ?_, ?_, ?_⟩
    · rw [selStore, runSeq_append, h₁, Option.bind_some, h₂]
    · intro a ha
      rw [bytes₂, mem₁, fr₁ rs hrs]
      simp only [Machine.Lir.writeLE]
      by_cases hin' : (m.core.read rb).toNat + off ≤ a ∧ a < (m.core.read rb).toNat + off + w.bytes
      · rw [ite_true_of (by omega), ite_true_of hin']
        congr 2; omega
      · rw [ite_false_of (by omega), ite_false_of hin']
        exact hrel a ha
    · intro q hq
      rw [bytes₂, mem₁, ite_false_of]
      intro hc
      apply hq
      simp only [Space.InMem, ← hs]
      omega
    · intro r hr'
      obtain ⟨_, h1, _⟩ := ne_scratch hr'
      rw [fr₂ r h1, fr₁ r hr']
  · cases hst

end Silmaril.RiscV.Backend
