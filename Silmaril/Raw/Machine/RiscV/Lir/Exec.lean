module

public import Silmaril.Machine.RiscV.Lir.Regs.Defs
/-!
# Machine-level execution of compiled code

This file fixes the memory layout of a compiled program on the `Ext.MState`
machine and proves the execution lemmas the backend correctness proof uses.

* `Space` places three regions: the code (readable and executable, not
  writable), the stack `[stackLo, stackHi)` and the linear memory
  `[memBase, memBase + memSize)` (both readable and writable, not executable).
  `Space.Valid` requires them to be pairwise disjoint and below `2^64`.
* `Good S code m`: the memory has exactly these regions, holds the encoded
  `code` at `codeBase`, and backs every stack byte. `step_good` shows that every
  retiring step preserves `Good`: a store can only write a writable byte, and no
  code byte is writable.
* `runSeq` executes a straight-line instruction list as a partial function; it
  fails on anything but a retirement with a sequential next PC. `chunk` turns a
  successful `runSeq` of code found at the PC into machine steps.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.Process (Memory Region Permissions)
open Silmaril.RiscV.Ext (MState)
open Relation

theorem ite_true_of {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

theorem ite_false_of {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-! ## The target transition relation -/

/-- One retiring step of the extended machine. -/
def TStep (m m' : MState) : Prop := m.step = .retired m'

/-! ## Memory layout -/

structure Space where
  codeBase : Nat
  stackLo : Nat
  stackHi : Nat
  memBase : Nat
  memSize : Nat

def codePerm : Permissions := ⟨true, false, true⟩
def dataPerm : Permissions := ⟨true, true, false⟩

namespace Space

variable (S : Space)

/-- The regions of a program of `n` instructions. -/
def regions (n : Nat) : List Region :=
  [⟨S.codeBase, 4 * n, codePerm⟩, ⟨S.stackLo, S.stackHi - S.stackLo, dataPerm⟩,
    ⟨S.memBase, S.memSize, dataPerm⟩]

/-- The static layout conditions for a program of `n` instructions. -/
structure Valid (n : Nat) : Prop where
  code_align : S.codeBase % 4 = 0
  code_end : S.codeBase + 4 * n < 2 ^ 64
  stack_le : S.stackLo ≤ S.stackHi
  stack_end : S.stackHi < 2 ^ 64
  mem_end : S.memBase + S.memSize < 2 ^ 64
  code_stack : S.codeBase + 4 * n ≤ S.stackLo ∨ S.stackHi ≤ S.codeBase
  code_mem : S.codeBase + 4 * n ≤ S.memBase ∨ S.memBase + S.memSize ≤ S.codeBase
  stack_mem : S.stackHi ≤ S.memBase ∨ S.memBase + S.memSize ≤ S.stackLo
  stack_align : S.stackHi % 16 = 0
  stack_floor : 2048 ≤ S.stackLo

def InStack (a : Nat) : Prop := S.stackLo ≤ a ∧ a < S.stackHi
def InMem (a : Nat) : Prop := S.memBase ≤ a ∧ a < S.memBase + S.memSize

end Space

theorem permits_eq {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hle : S.stackLo ≤ S.stackHi) (acc : Process.Access) (a : Nat) :
    mem.permits acc a = true ↔
      ((S.codeBase ≤ a ∧ a < S.codeBase + 4 * n) ∧ codePerm.allows acc = true) ∨
      (S.InStack a ∧ dataPerm.allows acc = true) ∨ (S.InMem a ∧ dataPerm.allows acc = true) := by
  have key : ∀ r : Region, (decide (r.Contains a) && r.permissions.allows acc) = true ↔
      (r.base ≤ a ∧ a < r.base + r.size) ∧ r.permissions.allows acc = true := by
    intro r
    constructor
    · intro h; rw [Bool.and_eq_true] at h; exact ⟨of_decide_eq_true h.1, h.2⟩
    · intro h; rw [Bool.and_eq_true]; exact ⟨decide_eq_true h.1, h.2⟩
  simp only [Memory.permits, h, Space.regions, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true, key, Space.InStack, Space.InMem, Nat.add_sub_cancel' hle]

theorem permits_write {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hle : S.stackLo ≤ S.stackHi) (a : Nat) :
    mem.permits .write a = true ↔ S.InStack a ∨ S.InMem a := by
  rw [permits_eq h hle]
  simp [codePerm, dataPerm, Permissions.allows]

theorem permitted_stack {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hv : S.Valid n) (acc : Process.Access) (hacc : acc ≠ .execute) {a len : Nat}
    (lo : S.stackLo ≤ a) (hi : a + len ≤ S.stackHi) : mem.Permitted acc a len := by
  have := hv.stack_end
  rw [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp [Process.addressLimit]; omega, by simp [Process.addressLimit]; omega, ?_⟩
  intro k hk
  rw [permits_eq h hv.stack_le]
  refine .inr (.inl ⟨⟨by omega, by omega⟩, ?_⟩)
  cases acc <;> simp_all [dataPerm, Permissions.allows]

theorem permitted_mem {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hv : S.Valid n) (acc : Process.Access) (hacc : acc ≠ .execute) {a len : Nat}
    (lo : S.memBase ≤ a) (hi : a + len ≤ S.memBase + S.memSize) : mem.Permitted acc a len := by
  have := hv.mem_end
  rw [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp [Process.addressLimit]; omega, by simp [Process.addressLimit]; omega, ?_⟩
  intro k hk
  rw [permits_eq h hv.stack_le]
  refine .inr (.inr ⟨⟨by omega, by omega⟩, ?_⟩)
  cases acc <;> simp_all [dataPerm, Permissions.allows]

/-! ## Byte-level frame of one step -/

theorem readBacking_congr {b b' : Process.ByteMemory} :
    ∀ {a n : Nat}, (∀ k < n, b'.get? (a + k) = b.get? (a + k)) →
      Memory.readBacking b' a n = Memory.readBacking b a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    have hr : Memory.readBacking b' (a + 1) n = Memory.readBacking b (a + 1) n :=
      readBacking_congr fun k hk => by
        have := h (k + 1) (by omega); rwa [Nat.add_assoc, Nat.add_comm 1 k]
    simp only [Nat.add_zero, Std.ExtHashMap.get?_eq_getElem?] at h0
    simp only [Memory.readBacking, hr, Std.ExtHashMap.get?_eq_getElem?, h0]

theorem readWith_congr {mem mem' : Memory} (hr : mem'.regions = mem.regions)
    (acc : Process.Access) {a n : Nat}
    (hb : ∀ k < n, mem'.bytes.get? (a + k) = mem.bytes.get? (a + k)) :
    mem'.readWith acc a n = mem.readWith acc a n := by
  simp only [Memory.readWith, Ext.MemoryLemmas.checkSpan_congr hr, readBacking_congr hb]

/-- A retiring step changes no mapping, and changes or creates only bytes that
were writable. -/
theorem step_frame {m m' : MState} (h : m.step = .retired m') :
    m'.memory.regions = m.memory.regions ∧
      ∀ a, m'.memory.bytes.get? a = m.memory.bytes.get? a ∨
        (m.memory.permits .write a = true ∧ (m'.memory.bytes.get? a).isSome = true) := by
  unfold MState.step at h
  split at h
  · cases h
  · rename_i word _
    split at h
    · cases h
    · rename_i instr _
      cases instr with
      | store op rs1 rs2 off =>
        simp only [Ext.Instr.exec] at h
        split at h
        · split at h
          · rename_i after written
            cases h
            have perm := Memory.writeBytes_permitted written
            have wo := Memory.writeBytes_writesOnly written
            refine ⟨wo.1, fun a => ?_⟩
            rw [Memory.Permitted, Memory.checkSpan_iff] at perm
            simp only [Ext.leBytes_length] at perm wo
            by_cases hin : (Ext.effectiveAddress m.core rs1 off).toNat ≤ a ∧
                a < (Ext.effectiveAddress m.core rs1 off).toNat + op.width
            · right
              refine ⟨?_, ?_⟩
              · have := perm.2.2 (a - (Ext.effectiveAddress m.core rs1 off).toNat) (by omega)
                rwa [Nat.add_sub_cancel' hin.1] at this
              · have := Memory.writeBytes_get written
                  (a - (Ext.effectiveAddress m.core rs1 off).toNat) (by simp; omega)
                rw [Nat.add_sub_cancel' hin.1] at this
                rw [this]; rfl
            · left
              exact wo.2 a (by omega)
          · cases h
        · cases h
      | _ =>
        have := Ext.Instr.exec_memory h (by intros; simp)
        rw [this]
        exact ⟨rfl, fun _ => .inl rfl⟩

/-! ## The loaded-program invariant -/

/-- The code is installed at `codeBase`. -/
def CodeAt (base : Nat) (code : List Ext.Instr) (mem : Memory) : Prop :=
  mem.fetchBytes base (4 * code.length) = some (Ext.byteDecoder.encodeBlock code)

/-- Invariant of every reachable machine state: the regions, the code, and
backing for every stack byte. -/
structure Good (S : Space) (code : List Ext.Instr) (m : MState) : Prop where
  regions : m.memory.regions = S.regions code.length
  code : CodeAt S.codeBase code m.memory
  backed : ∀ a, S.InStack a → (m.memory.bytes.get? a).isSome = true

theorem step_good {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length) {m m' : MState}
    (hg : Good S code m) (h : m.step = .retired m') : Good S code m' := by
  obtain ⟨hreg, hbytes⟩ := step_frame h
  have unchanged : ∀ a, m.memory.permits .write a = false →
      m'.memory.bytes.get? a = m.memory.bytes.get? a := by
    intro a ha
    rcases hbytes a with e | ⟨e, _⟩
    · exact e
    · rw [ha] at e; cases e
  refine ⟨hreg.trans hg.regions, ?_, ?_⟩
  · unfold CodeAt Memory.fetchBytes
    rw [readWith_congr hreg]
    · exact hg.code
    · intro k hk
      apply unchanged
      cases e : m.memory.permits .write (S.codeBase + k) with
      | false => rfl
      | true =>
        rw [permits_write hg.regions hv.stack_le] at e
        have := hv.code_stack; have := hv.code_mem
        simp only [Space.InStack, Space.InMem] at e
        omega
  · intro a ha
    rcases hbytes a with e | ⟨_, e⟩
    · rw [e]; exact hg.backed a ha
    · exact e

/-! ## Fetching the code -/

def addrOf (base i : Nat) : Word := BitVec.ofNat 64 (base + 4 * i)

theorem addrOf_succ (base i : Nat) : addrOf base (i + 1) = addrOf base i + 4 := by
  simp only [addrOf, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, BitVec.ofNat_add]
  rfl

theorem addrOf_add (base i j : Nat) :
    addrOf base (i + j) = addrOf base i + BitVec.ofNat 64 (4 * j) := by
  simp only [addrOf, Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]

theorem codeAt_bound {base : Nat} {code : List Ext.Instr} {mem : Memory}
    (hc : CodeAt base code mem) : base + 4 * code.length ≤ 2 ^ 64 := by
  have := Memory.readWith_permitted hc
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  simpa [Process.addressLimit] using this.2.1

theorem addrOf_toNat {base : Nat} {code : List Ext.Instr} {mem : Memory}
    (hc : CodeAt base code mem) {k : Nat} (hk : k < code.length) :
    (addrOf base k).toNat = base + 4 * k := by
  have := codeAt_bound hc
  simp only [addrOf, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem encodeBlock_slice (code : List Ext.Instr) {k : Nat} (hk : k < code.length) :
    ((Ext.byteDecoder.encodeBlock code).drop (4 * k)).take 4 = Ext.encodeBytes code[k] := by
  have split : code = code.take k ++ code[k] :: code.drop (k + 1) := by
    simp
  conv => lhs; rw [split]
  rw [Machine.Decoder.encodeBlock_append, Machine.Decoder.encodeBlock_cons,
    List.drop_append_of_le_length (by rw [Ext.encodeBlock_length]; simp; omega)]
  rw [List.drop_eq_nil_of_le (by rw [Ext.encodeBlock_length]; simp), List.nil_append]
  exact List.take_left' (by simp)

theorem fetch_at {base : Nat} {code : List Ext.Instr} {mem : Memory}
    (hc : CodeAt base code mem) (hal : base % 4 = 0) {k : Nat} (hk : k < code.length) :
    Ext.fetch mem (addrOf base k) = some (Ext.encode code[k]) := by
  apply Ext.fetch_of_fetchBytes
  · rw [addrOf_toNat hc hk]; omega
  · rw [addrOf_toNat hc hk]
    have := Ext.MemoryLemmas.readWith_slice hc (4 * k) 4 (by decide) (by omega)
    rw [encodeBlock_slice code hk] at this
    exact this

theorem step_at {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length) {m : MState}
    (hg : Good S code m) {k : Nat} (hpc : m.core.pc = addrOf S.codeBase k) {i : Ext.Instr}
    (hi : code[k]? = some i) : m.step = i.exec m := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  apply MState.step_of_fetch
  rw [hpc]
  exact fetch_at hg.code hv.code_align hk

/-- One step of the instruction at the PC. -/
theorem tstep_at {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length) {m m' : MState}
    (hg : Good S code m) {k : Nat} (hpc : m.core.pc = addrOf S.codeBase k) {i : Ext.Instr}
    (hi : code[k]? = some i) (he : i.exec m = .retired m') : TStep m m' ∧ Good S code m' := by
  have hs : m.step = .retired m' := by rw [step_at hv hg hpc hi]; exact he
  exact ⟨hs, step_good hv hg hs⟩

/-! ## Straight-line execution -/

/-- Execute instructions that retire with a sequential next PC. -/
def runSeq : List Ext.Instr → MState → Option MState
  | [], m => some m
  | i :: is, m =>
    match i.exec m with
    | .retired m' => if m'.core.pc = m.core.pc + 4 then runSeq is m' else none
    | _ => none

@[simp] theorem runSeq_nil (m : MState) : runSeq [] m = some m := rfl

theorem runSeq_cons_of {i : Ext.Instr} {is : List Ext.Instr} {m m' : MState}
    (he : i.exec m = .retired m') (hpc : m'.core.pc = m.core.pc + 4) :
    runSeq (i :: is) m = runSeq is m' := by
  simp [runSeq, he, hpc]

theorem runSeq_append (a b : List Ext.Instr) (m : MState) :
    runSeq (a ++ b) m = (runSeq a m).bind (runSeq b) := by
  induction a generalizing m with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, runSeq]
    split
    · split
      · exact ih _
      · rfl
    · rfl

theorem runSeq_compute (cs : List Ext.Compute) (m : MState) :
    runSeq (cs.map .compute) m = some ⟨Machine.Block.run Ext.Compute.step cs m.core, m.memory⟩ := by
  induction cs generalizing m with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, runSeq_cons_of (Ext.Instr.exec_compute m c) (Ext.Compute.step_pc c m.core)]
    exact ih _

theorem runSeq_pc {is : List Ext.Instr} {m m' : MState} (h : runSeq is m = some m') :
    m'.core.pc = m.core.pc + BitVec.ofNat 64 (4 * is.length) := by
  induction is generalizing m with
  | nil => cases h; simp
  | cons i rest ih =>
    simp only [runSeq] at h
    split at h
    · split at h
      · rename_i m₁ _ hpc
        rw [ih h, hpc, List.length_cons, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc,
          BitVec.add_comm (4 : Word)]
        rfl
      · cases h
    · cases h

/-- A straight-line chunk found at the PC runs as machine steps. -/
theorem chunk {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length) :
    ∀ {seq rest : List Ext.Instr} {m m' : MState} {k : Nat},
    Good S code m → m.core.pc = addrOf S.codeBase k → code.drop k = seq ++ rest →
    runSeq seq m = some m' →
    ReflTransGen TStep m m' ∧ Good S code m' ∧ m'.core.pc = addrOf S.codeBase (k + seq.length)
  | [], _, m, m', k, hg, hpc, _, hr => by
    cases hr; exact ⟨.refl, hg, by simpa using hpc⟩
  | i :: is, rest, m, m', k, hg, hpc, hcode, hr => by
    simp only [runSeq] at hr
    split at hr
    · split at hr
      · rename_i m₁ he hpc₁
        have hi : code[k]? = some i := by
          have := congrArg (·[0]?) hcode
          simpa [List.getElem?_drop] using this
        obtain ⟨st, hg₁⟩ := tstep_at hv hg hpc hi he
        have hcode₁ : code.drop (k + 1) = is ++ rest := by
          have := congrArg (List.drop 1) hcode
          simpa [List.drop_drop, Nat.add_comm] using this
        obtain ⟨r, g, p⟩ := chunk hv hg₁ (by rw [hpc₁, hpc, addrOf_succ]) hcode₁ hr
        refine ⟨.head st r, g, ?_⟩
        rw [p]; congr 1; simp; omega
      · cases hr
    · cases hr

theorem chunk_trans {S : Space} {code : List Ext.Instr} (hv : S.Valid code.length)
    {seq rest : List Ext.Instr} {m m' : MState} {k : Nat} (hne : seq ≠ [])
    (hg : Good S code m) (hpc : m.core.pc = addrOf S.codeBase k) (hcode : code.drop k = seq ++ rest)
    (hr : runSeq seq m = some m') :
    TransGen TStep m m' ∧ Good S code m' ∧ m'.core.pc = addrOf S.codeBase (k + seq.length) := by
  cases seq with
  | nil => exact absurd rfl hne
  | cons i is =>
    simp only [runSeq] at hr
    split at hr
    · split at hr
      · rename_i m₁ he hpc₁
        have hi : code[k]? = some i := by
          have := congrArg (·[0]?) hcode
          simpa [List.getElem?_drop] using this
        obtain ⟨st, hg₁⟩ := tstep_at hv hg hpc hi he
        have hcode₁ : code.drop (k + 1) = is ++ rest := by
          have := congrArg (List.drop 1) hcode
          simpa [List.drop_drop, Nat.add_comm] using this
        obtain ⟨r, g, p⟩ := chunk hv hg₁ (by rw [hpc₁, hpc, addrOf_succ]) hcode₁ hr
        refine ⟨.head' st r, g, ?_⟩
        rw [p]; congr 1; simp; omega
      · cases hr
    · cases hr

/-! ## Words in memory -/

/-- Eight little-endian bytes of `x` are readable at `a`. -/
def WordAt (mem : Memory) (a : Nat) (x : Word) : Prop :=
  mem.readBytes a 8 = some (Ext.leBytes 8 x)

end Silmaril.RiscV.Backend
