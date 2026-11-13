module

public import Silmaril.Machine.X86.Lir.Code.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.IntervalCases

/-!
# The loaded machine of a compiled program

This file fixes the memory layout of a compiled program on the `X86.Ext`
machine and proves the execution lemmas the correctness proof uses.

* `Space` places three regions: the code (readable and executable, not
  writable), the stack `[stackLo, stackHi)` and the linear memory
  `[memBase, memBase + memSize)` (both readable and writable, not executable).
  `Space.Valid` requires them to be pairwise disjoint and below `2^64`.
* `Good S code mem`: the memory has exactly these regions and holds `code` at
  `codeBase`. `good_of_exec` shows that every retired instruction preserves
  `Good`: a store can only change a writable byte, and no code byte is
  writable.
* `runSeq` executes a straight-line instruction list as a partial function; it
  fails on anything but a retirement with a sequential next RIP (and on RET).
  `steps_runSeq` turns a successful `runSeq` of code found at RIP into machine
  steps.
* `WordAt mem a v`: the eight bytes at `a` hold `v` in little-endian order.
  Loads, stores, pushes and pops of stack words are stated with it.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory Region Permissions)
open Silmaril.X86 (State MState Word Byte Reg)
open Relation

/-! ## The target transition relation -/

/-- One retiring step of the machine, with `exit` the designated return address. -/
def RStep (exit : Word) (m m' : MState) : Prop := Ext.step exit m = .retired m'

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

/-- The regions of a program of `n` code bytes. -/
def regions (n : Nat) : List Region :=
  [⟨S.codeBase, n, codePerm⟩, ⟨S.stackLo, S.stackHi - S.stackLo, dataPerm⟩,
    ⟨S.memBase, S.memSize, dataPerm⟩]

/-- The static layout conditions for a program of `n` code bytes. -/
structure Valid (n : Nat) : Prop where
  code_end : S.codeBase + n < 2 ^ 64
  stack_le : S.stackLo + 8 ≤ S.stackHi
  stack_end : S.stackHi < 2 ^ 64
  mem_end : S.memBase + S.memSize < 2 ^ 64
  code_stack : S.codeBase + n ≤ S.stackLo ∨ S.stackHi ≤ S.codeBase
  code_mem : S.codeBase + n ≤ S.memBase ∨ S.memBase + S.memSize ≤ S.codeBase
  stack_mem : S.stackHi ≤ S.memBase ∨ S.memBase + S.memSize ≤ S.stackLo
  stack_align : S.stackHi % 16 = 0

def InStack (a : Nat) : Prop := S.stackLo ≤ a ∧ a < S.stackHi
def InMem (a : Nat) : Prop := S.memBase ≤ a ∧ a < S.memBase + S.memSize

end Space

theorem permits_eq {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hle : S.stackLo ≤ S.stackHi) (acc : Process.Access) (a : Nat) :
    mem.permits acc a = true ↔
      ((S.codeBase ≤ a ∧ a < S.codeBase + n) ∧ codePerm.allows acc = true) ∨
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
  have := hv.stack_le
  rw [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp [Process.addressLimit]; omega, by simp [Process.addressLimit]; omega, ?_⟩
  intro k hk
  rw [permits_eq h (by omega)]
  refine .inr (.inl ⟨⟨by omega, by omega⟩, ?_⟩)
  cases acc <;> simp_all [dataPerm, Permissions.allows]

theorem permitted_mem {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hv : S.Valid n) (acc : Process.Access) (hacc : acc ≠ .execute) {a len : Nat}
    (lo : S.memBase ≤ a) (hi : a + len ≤ S.memBase + S.memSize) : mem.Permitted acc a len := by
  have := hv.mem_end
  have := hv.stack_le
  rw [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp [Process.addressLimit]; omega, by simp [Process.addressLimit]; omega, ?_⟩
  intro k hk
  rw [permits_eq h (by omega)]
  refine .inr (.inr ⟨⟨by omega, by omega⟩, ?_⟩)
  cases acc <;> simp_all [dataPerm, Permissions.allows]

theorem permitted_code {S : Space} {n : Nat} {mem : Memory} (h : mem.regions = S.regions n)
    (hv : S.Valid n) {a len : Nat} (lo : S.codeBase ≤ a) (hi : a + len ≤ S.codeBase + n) :
    mem.Permitted .execute a len := by
  have := hv.code_end
  have := hv.stack_le
  rw [Memory.Permitted, Memory.checkSpan_iff]
  refine ⟨by simp [Process.addressLimit]; omega, by simp [Process.addressLimit]; omega, ?_⟩
  intro k hk
  rw [permits_eq h (by omega)]
  exact .inl ⟨⟨by omega, by omega⟩, rfl⟩

/-! ## Memory frames -/

/-- The regions are unchanged and every non-writable byte is unchanged. -/
def MemFrame (m m' : Memory) : Prop :=
  m'.regions = m.regions ∧ ∀ a, m.permits .write a = false → m'.bytes.get? a = m.bytes.get? a

theorem MemFrame.refl (m : Memory) : MemFrame m m := ⟨rfl, fun _ _ => rfl⟩

theorem memFrame_writeBytes {m m' : Memory} {a : Nat} {bytes : List Byte}
    (h : m.writeBytes a bytes = some m') : MemFrame m m' := by
  have perm := Memory.writeBytes_permitted h
  have wo := Memory.writeBytes_writesOnly h
  refine ⟨wo.1, fun x hx => wo.2 x ?_⟩
  rw [Memory.Permitted, Memory.checkSpan_iff] at perm
  by_contra hin
  have := perm.2.2 (x - a) (by omega)
  rw [Nat.add_sub_cancel' (by omega)] at this
  rw [this] at hx; cases hx

theorem memFrame_storeN {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : Ext.storeN m a k v = some m') : MemFrame m m' :=
  memFrame_writeBytes h

theorem memFrame_pushWord {s t : State} {m m' : Memory} {v : Word}
    (h : X86.pushWord s m v = some (t, m')) : MemFrame m m' := by
  simp only [X86.pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, w, _, rfl⟩ := h
  exact memFrame_writeBytes w

theorem memFrame_writeRM {sz : Ext.Sz} {op : Ext.RM} {v : BitVec sz.bits} {s t : State}
    {m m' : Memory} {next : Word} (h : Ext.writeRM sz op v s m next = some (t, m')) :
    MemFrame m m' := by
  cases op with
  | reg r => simp only [Ext.writeRM, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact .refl _
  | mem mm =>
    simp only [Ext.writeRM, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, w, _, rfl⟩ := h
    exact memFrame_storeN w

theorem memFrame_writeRM8 {op : Ext.RM} {v : BitVec 8} {s t : State}
    {m m' : Memory} {next : Word} (h : Ext.writeRM8 op v s m next = some (t, m')) :
    MemFrame m m' := by
  cases op with
  | reg r => simp only [Ext.writeRM8, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact .refl _
  | mem mm =>
    simp only [Ext.writeRM8, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, w, _, rfl⟩ := h
    exact memFrame_storeN w

theorem retire_ok {next : Word} {r : Option (State × Memory)} {s : State} {m : Memory}
    (h : Ext.retire next r = .ok s m) : ∃ t, r = some (t, m) := by
  cases r with
  | none => cases h
  | some r => obtain ⟨t, m'⟩ := r; simp only [Ext.retire, Ext.Result.ok.injEq] at h; exact ⟨t, by rw [h.2]⟩

/-- Every retired instruction keeps the regions and all non-writable bytes. -/
theorem exec_frame {i : Ext.Instr} {s s' : State} {m m' : Memory}
    (h : Ext.exec i s m = .ok s' m') : MemFrame m m' := by
  have same : ∀ {t : State} {r : Option (State × Memory)} {next : Word},
      Ext.retire next r = .ok s' m' → (∀ t m'', r = some (t, m'') → MemFrame m m'') →
      MemFrame m m' := by
    intro t r next hr hf
    obtain ⟨t', rfl⟩ := retire_ok hr
    exact hf _ _ rfl
  cases i with
  | mov sz dst src =>
    exact same (t := s) h fun _ _ e => memFrame_writeRM e
  | movI sz dst imm =>
    exact same (t := s) h fun _ _ e => memFrame_writeRM e
  | movabs dst imm =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | load sz dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | store n dst src =>
    exact same (t := s) h fun _ _ e => by
      cases dst with
      | reg r =>
        simp only [Ext.writeNarrow, Option.some.injEq, Prod.mk.injEq] at e
        rw [← e.2]; exact .refl _
      | mem mm =>
        simp only [Ext.writeNarrow, Option.map_eq_some_iff, Prod.mk.injEq] at e
        obtain ⟨_, w, _, rfl⟩ := e; exact memFrame_storeN w
  | movx sx sz n dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | movsxd dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | lea sz dst src =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | alu sz op dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Ext.aluStep] at e
      split at e
      · cases e
      · split at e
        · cases e; exact .refl _
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
          obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | aluI sz op dst imm =>
    exact same (t := s) h fun _ _ e => by
      simp only [Ext.aluStep] at e
      split at e
      · cases e
      · split at e
        · cases e; exact .refl _
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
          obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | aluI8 sz op dst imm =>
    exact same (t := s) h fun _ _ e => by
      simp only [Ext.aluStep] at e
      split at e
      · cases e
      · split at e
        · cases e; exact .refl _
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
          obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | aluR sz op dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Ext.aluStepR] at e
      split at e
      · cases e
      · split at e <;> (cases e; exact .refl _)
  | test sz dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | test8 dst src =>
    exact same (t := s) h fun _ _ e => by
      cases hv : Ext.readNarrow .b dst s m
          (s.rip + BitVec.ofNat 64 (Ext.Instr.test8 dst src).length) with
      | none => rw [hv] at e; cases e
      | some v => rw [hv] at e; cases e; exact .refl _
  | cmpI8 dst imm =>
    exact same (t := s) h fun _ _ e => by
      cases hv : Ext.readNarrow .b dst s m
          (s.rip + BitVec.ofNat 64 (Ext.Instr.cmpI8 dst imm).length) with
      | none => rw [hv] at e; cases e
      | some v => rw [hv] at e; cases e; exact .refl _
  | testI8 dst imm =>
    exact same (t := s) h fun _ _ e => by
      cases hv : Ext.readNarrow .b dst s m
          (s.rip + BitVec.ofNat 64 (Ext.Instr.testI8 dst imm).length) with
      | none => rw [hv] at e; cases e
      | some v => rw [hv] at e; cases e; exact .refl _
  | testA8 imm =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | cmpA8 imm =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | unary sz op dst =>
    cases op with
    | neg =>
      simp only [Ext.exec] at h
      split at h
      · cases h
      · exact same (t := s) h fun _ _ e => by
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
          obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
    | not =>
      simp only [Ext.exec] at h
      split at h
      · cases h
      · exact same (t := s) h fun _ _ e => memFrame_writeRM e
  | imul sz dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | mul sz src =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · exact same (t := s) h fun _ _ e => by cases e; exact .refl _
  | shift sz op dst count =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · exact same (t := s) h fun _ _ e => by
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
        obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | cxd sz =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | cxe sz =>
    cases sz <;>
      (simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _)
  | div sz signed src =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact same (t := s) h fun _ _ e => by cases e; exact .refl _
  | cmov sz c dst src =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Ext.retire, Ext.Result.ok.injEq] at h
        rw [← h.2]; exact .refl _
  | setcc c dst =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · exact same (t := s) h fun _ _ e => memFrame_writeRM8 e
  | jmp rel => simp only [Ext.exec, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | jmp8 rel => simp only [Ext.exec, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | jcc c rel =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
    · simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | jcc8 c rel =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
    · simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | movI32 dst imm =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | bswap sz dst =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | testA sz imm =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | movI16 dst imm =>
    cases dst with
    | reg r =>
      simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
    | mem mm =>
      exact same (t := s) h fun _ _ e => by
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
        obtain ⟨_, w, _, rfl⟩ := e; exact memFrame_storeN w
  | aluA sz op imm =>
    exact same (t := s) h fun _ _ e => by
      simp only [Ext.aluStep] at e
      split at e
      · cases e
      · split at e
        · cases e; exact .refl _
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
          obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | incdec sz dec dst =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · exact same (t := s) h fun _ _ e => by
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
        obtain ⟨⟨_, _⟩, w, _, rfl⟩ := e; exact memFrame_writeRM w
  | pushRM src =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · exact same (t := s) h fun _ _ e => memFrame_pushWord e
  | nop len =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | endbr64 =>
    simp only [Ext.exec, Ext.retire, Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | mov8 dst src =>
    exact same (t := s) h fun _ _ e => by
      cases hv : Ext.readNarrow .b src s m
          (s.rip + BitVec.ofNat 64 (Ext.Instr.mov8 dst src).length) with
      | none => rw [hv] at e; cases e
      | some v => rw [hv] at e; cases e; exact .refl _
  | movI8 dst imm => exact same (t := s) h fun _ _ e => memFrame_writeRM8 e
  | leave =>
    exact same (t := s) h fun _ _ e => by
      cases hv : X86.popWord (s.write .rsp (s.read .rbp)) m with
      | none => rw [hv] at e; cases e
      | some v => rw [hv] at e; cases e; exact .refl _
  | call rel =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · rename_i t mm e
      simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact memFrame_pushWord e
  | ret =>
    simp only [Ext.exec] at h
    split at h
    · cases h
    · simp only [Ext.Result.ok.injEq] at h; rw [← h.2]; exact .refl _
  | push src =>
    exact same (t := s) h fun _ _ e => memFrame_pushWord e
  | pop dst =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _
  | ud2 => cases h
  | bitcount op sz dst src =>
    exact same (t := s) h fun _ _ e => by
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at e
      obtain ⟨_, _, _, rfl⟩ := e; exact .refl _

/-! ## The loaded-program invariant -/

/-- The memory has the regions of the space and holds `code` at `codeBase`. -/
structure Good (S : Space) (code : List Byte) (mem : Memory) : Prop where
  regions : mem.regions = S.regions code.length
  code : ∀ i (h : i < code.length), mem.bytes.get? (S.codeBase + i) = some code[i]

theorem good_of_frame {S : Space} {code : List Byte} (hv : S.Valid code.length) {m m' : Memory}
    (hg : Good S code m) (hf : MemFrame m m') : Good S code m' := by
  refine ⟨hf.1.trans hg.regions, fun i hi => ?_⟩
  rw [hf.2 _ ?_]
  · exact hg.code i hi
  · cases e : m.permits .write (S.codeBase + i) with
    | false => rfl
    | true =>
      rw [permits_write hg.regions (by have := hv.stack_le; omega)] at e
      have := hv.code_stack; have := hv.code_mem
      simp only [Space.InStack, Space.InMem] at e
      omega

theorem good_of_exec {S : Space} {code : List Byte} (hv : S.Valid code.length) {m m' : Memory}
    {i : Ext.Instr} {s s' : State} (hg : Good S code m) (h : Ext.exec i s m = .ok s' m') :
    Good S code m' :=
  good_of_frame hv hg (exec_frame h)

/-- The bytes of the code starting at offset `o` are fetched. -/
theorem fetchBytes_code {S : Space} {code : List Byte} (hv : S.Valid code.length) {m : Memory}
    (hg : Good S code m) {o : Nat} {bytes rest : List Byte} (hd : code.drop o = bytes ++ rest)
    (hpos : 0 < bytes.length) :
    m.fetchBytes (S.codeBase + o) bytes.length = some bytes := by
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_append] at hlen
  apply Memory.readWith_eq
  · exact permitted_code hg.regions hv (by omega) (by omega)
  · intro k hk
    have := hg.code (o + k) (by omega)
    rw [← Nat.add_assoc] at this
    rw [this]
    congr 1
    have e : code[o + k]? = (bytes ++ rest)[k]? := by rw [← hd, List.getElem?_drop]
    rw [List.getElem?_append_left hk] at e
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk] at e
    exact Option.some.inj e

/-- The step at an address holding the encoding of `i`. -/
theorem step_code {S : Space} {code : List Byte} (hv : S.Valid code.length) {t : MState}
    (hg : Good S code t.memory) {o : Nat} (hrip : t.core.rip.toNat = S.codeBase + o)
    {i : Ext.Instr} {rest : List Byte} (hd : code.drop o = Ext.encode i ++ rest) (exit : Word) :
    Ext.step exit t =
      match Ext.exec i t.core t.memory with
      | .ok core memory =>
        if i = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault i
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  apply Ext.step_of_fetch (bytes := Ext.encode i)
  · rw [hrip]; exact fetchBytes_code hv hg hd (Ext.encode_length i).1
  · exact Ext.decode_encode i

theorem rstep_code {S : Space} {code : List Byte} (hv : S.Valid code.length) {t : MState}
    (hg : Good S code t.memory) {o : Nat} (hrip : t.core.rip.toNat = S.codeBase + o)
    {i : Ext.Instr} {rest : List Byte} (hd : code.drop o = Ext.encode i ++ rest) {exit : Word}
    {c : State} {m : Memory} (he : Ext.exec i t.core t.memory = .ok c m)
    (hnr : ¬ (i = .ret ∧ c.rip = exit)) : RStep exit t ⟨c, m⟩ := by
  unfold RStep
  rw [step_code hv hg hrip hd exit, he]
  simp only [hnr, ite_false]

/-! ## Straight-line execution -/

/-- Execute instructions that retire with a sequential next RIP. -/
def runSeq : List Ext.Instr → State → Memory → Option (State × Memory)
  | [], s, m => some (s, m)
  | i :: is, s, m =>
    match Ext.exec i s m with
    | .ok s' m' =>
      if i ≠ .ret ∧ s'.rip = s.rip + BitVec.ofNat 64 (Ext.encode i).length then runSeq is s' m'
      else none
    | _ => none

@[simp] theorem runSeq_nil (s : State) (m : Memory) : runSeq [] s m = some (s, m) := rfl

theorem runSeq_cons_of {i : Ext.Instr} {is : List Ext.Instr} {s s' : State} {m m' : Memory}
    (he : Ext.exec i s m = .ok s' m') (hr : i ≠ .ret)
    (hpc : s'.rip = s.rip + BitVec.ofNat 64 (Ext.encode i).length) :
    runSeq (i :: is) s m = runSeq is s' m' := by
  simp [runSeq, he, hr, hpc]

theorem runSeq_append (a b : List Ext.Instr) (s : State) (m : Memory) :
    runSeq (a ++ b) s m = (runSeq a s m).bind fun r => runSeq b r.1 r.2 := by
  induction a generalizing s m with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, runSeq]
    split
    · split
      · exact ih _ _
      · rfl
    · rfl

theorem runSeq_append_of {a b : List Ext.Instr} {s s₁ : State} {m m₁ : Memory}
    (h : runSeq a s m = some (s₁, m₁)) : runSeq (a ++ b) s m = runSeq b s₁ m₁ := by
  rw [runSeq_append, h]; rfl

theorem runSeq_frame {is : List Ext.Instr} {s s' : State} {m m' : Memory}
    (h : runSeq is s m = some (s', m')) : MemFrame m m' ∨ m' = m := by
  induction is generalizing s m with
  | nil => cases h; exact .inr rfl
  | cons i is ih =>
    simp only [runSeq] at h
    split at h
    · rename_i s₁ m₁ he
      split at h
      · have f₁ := exec_frame he
        rcases ih h with f | e
        · refine .inl ⟨f.1.trans f₁.1, fun a ha => ?_⟩
          rw [f.2 a (by
            cases e : m₁.permits .write a with
            | false => rfl
            | true =>
              rw [Memory.permits, f₁.1, ← Memory.permits, ha] at e; cases e), f₁.2 a ha]
        · subst e; exact .inl f₁
      · cases h
    · cases h

theorem steps_runSeq {S : Space} {code : List Byte} (hv : S.Valid code.length) {exit : Word} :
    ∀ {is : List Ext.Instr} {t : MState} {o : Nat} {rest : List Byte} {c' : State}
      {m' : Memory},
    Good S code t.memory → t.core.rip.toNat = S.codeBase + o →
    code.drop o = is.flatMap Ext.encode ++ rest →
    runSeq is t.core t.memory = some (c', m') →
    ReflTransGen (RStep exit) t ⟨c', m'⟩ ∧ Good S code m' ∧
      c'.rip.toNat = S.codeBase + o + (is.flatMap Ext.encode).length
  | [], t, o, rest, c', m', hg, hrip, _, h => by
    cases h; exact ⟨.refl, hg, by simpa using hrip⟩
  | i :: is, t, o, rest, c', m', hg, hrip, hd, h => by
    simp only [runSeq] at h
    split at h
    · rename_i s₁ m₁ he
      split at h
      · rename_i hc
        have hlen := congrArg List.length hd
        simp only [List.length_drop, List.length_append, List.flatMap_cons] at hlen
        have hd₁ : code.drop o = Ext.encode i ++ (is.flatMap Ext.encode ++ rest) := by
          rw [hd, List.flatMap_cons, List.append_assoc]
        have st : RStep exit t ⟨s₁, m₁⟩ :=
          rstep_code hv hg hrip hd₁ he (fun e => hc.1 e.1)
        have hg₁ := good_of_exec hv hg he
        have hrip₁ : s₁.rip.toNat = S.codeBase + (o + (Ext.encode i).length) := by
          rw [hc.2, BitVec.toNat_add, hrip, BitVec.toNat_ofNat]
          have := hv.code_end
          rw [Nat.mod_eq_of_lt (a := (Ext.encode i).length) (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hd₂ : code.drop (o + (Ext.encode i).length) = is.flatMap Ext.encode ++ rest := by
          rw [← List.drop_drop, hd₁, List.drop_left]
        obtain ⟨r, g, e⟩ := steps_runSeq (t := ⟨s₁, m₁⟩) hv hg₁ hrip₁ hd₂ h
        refine ⟨.head st r, g, ?_⟩
        rw [e, List.flatMap_cons, List.length_append]
        omega
      · cases h
    · cases h

theorem transGen_runSeq {S : Space} {code : List Byte} (hv : S.Valid code.length) {exit : Word}
    {i : Ext.Instr} {is : List Ext.Instr} {t : MState} {o : Nat} {rest : List Byte} {c' : State}
    {m' : Memory} (hg : Good S code t.memory) (hrip : t.core.rip.toNat = S.codeBase + o)
    (hd : code.drop o = (i :: is).flatMap Ext.encode ++ rest)
    (h : runSeq (i :: is) t.core t.memory = some (c', m')) :
    TransGen (RStep exit) t ⟨c', m'⟩ ∧ Good S code m' ∧
      c'.rip.toNat = S.codeBase + o + ((i :: is).flatMap Ext.encode).length := by
  simp only [runSeq] at h
  split at h
  · rename_i s₁ m₁ he
    split at h
    · rename_i hc
      have hlen := congrArg List.length hd
      simp only [List.length_drop, List.length_append, List.flatMap_cons] at hlen
      have hd₁ : code.drop o = Ext.encode i ++ (is.flatMap Ext.encode ++ rest) := by
        rw [hd, List.flatMap_cons, List.append_assoc]
      have st : RStep exit t ⟨s₁, m₁⟩ := rstep_code hv hg hrip hd₁ he (fun e => hc.1 e.1)
      have hg₁ := good_of_exec hv hg he
      have hrip₁ : s₁.rip.toNat = S.codeBase + (o + (Ext.encode i).length) := by
        rw [hc.2, BitVec.toNat_add, hrip, BitVec.toNat_ofNat]
        have := hv.code_end
        rw [Nat.mod_eq_of_lt (a := (Ext.encode i).length) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      have hd₂ : code.drop (o + (Ext.encode i).length) = is.flatMap Ext.encode ++ rest := by
        rw [← List.drop_drop, hd₁, List.drop_left]
      obtain ⟨r, g, e⟩ := steps_runSeq (t := ⟨s₁, m₁⟩) (exit := exit) hv hg₁ hrip₁ hd₂ h
      refine ⟨TransGen.head' st r, g, ?_⟩
      rw [e, List.flatMap_cons, List.length_append]
      omega
    · cases h
  · cases h

/-! ## Stack words -/

/-- The eight bytes at `a` hold `v`, least significant first. -/
def WordAt (mem : Memory) (a : Nat) (v : Word) : Prop :=
  ∀ i < 8, mem.bytes.get? (a + i) = some (Machine.LittleEndian.wordByte v i)

theorem WordAt.of_writesOnly {m m' : Memory} {b : Nat} {w : Word} (h : WordAt m b w)
    {a n : Nat} (hw : Memory.WritesOnly m m' a n) (hd : b + 8 ≤ a ∨ a + n ≤ b) :
    WordAt m' b w := by
  intro i hi
  rw [hw.2 _ (by omega)]
  exact h i hi

theorem leBytes_ext {v w : Word} (h : ∀ i < 8, Machine.LittleEndian.wordByte v i =
    Machine.LittleEndian.wordByte w i) : Ext.leBytes v 8 = Ext.leBytes w 8 := by
  simp only [Ext.leBytes]
  congr 1
  funext i
  exact h i i.isLt

/-- The eight bytes determine the word. -/
theorem WordAt.unique {m : Memory} {a : Nat} {v w : Word} (hv : WordAt m a v) (hw : WordAt m a w) :
    v = w := by
  have e := leBytes_ext (v := v) (w := w) fun i hi => by
    have := (hv i hi).symm.trans (hw i hi)
    exact Option.some.inj this
  have := congrArg Ext.leValue e
  rw [Ext.leValue_leBytes, Ext.leValue_leBytes, Nat.mod_eq_of_lt v.isLt, Nat.mod_eq_of_lt w.isLt] at this
  exact BitVec.eq_of_toNat_eq this

theorem WordAt.congr {m m' : Memory} {b : Nat} {w : Word} (h : WordAt m b w)
    (hb : ∀ i < 8, m'.bytes.get? (b + i) = m.bytes.get? (b + i)) : WordAt m' b w := by
  intro i hi
  rw [hb i hi]
  exact h i hi

theorem leBytes_getElem (v : Word) (k i : Nat) (h : i < (Ext.leBytes v k).length) :
    (Ext.leBytes v k)[i] = Machine.LittleEndian.wordByte v i := by
  simp [Ext.leBytes]

theorem storeN_some {m : Memory} {a k : Nat} (ha : a < 2 ^ 64) (v : Word)
    (hp : m.Permitted .write a k) :
    ∃ m', Ext.storeN m (BitVec.ofNat 64 a) k v = some m' := by
  have hp' : m.checkSpan .write a (Ext.leBytes v k).length = true := by
    rw [Ext.length_leBytes]; exact hp
  refine ⟨{ m with bytes := Memory.install m.bytes a (Ext.leBytes v k) }, ?_⟩
  simp only [Ext.storeN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Memory.writeBytes, hp', ite_true]

theorem storeN_writesOnly' {m m' : Memory} {a k : Nat} (ha : a < 2 ^ 64) {v : Word}
    (h : Ext.storeN m (BitVec.ofNat 64 a) k v = some m') : Memory.WritesOnly m m' a k := by
  have := Ext.storeN_writesOnly h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this

theorem storeN_get {m m' : Memory} {a k : Nat} (ha : a < 2 ^ 64) {v : Word}
    (h : Ext.storeN m (BitVec.ofNat 64 a) k v = some m') (i : Nat) (hi : i < k) :
    m'.bytes.get? (a + i) = some (Machine.LittleEndian.wordByte v i) := by
  have := Memory.writeBytes_get h i (by simpa using hi)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, leBytes_getElem] at this
  exact this

theorem wordAt_storeN {m m' : Memory} {a : Nat} (ha : a < 2 ^ 64) {v : Word}
    (h : Ext.storeN m (BitVec.ofNat 64 a) 8 v = some m') : WordAt m' a v :=
  fun i hi => storeN_get ha h i hi

theorem readBytes_of_wordAt {m : Memory} {a : Nat} {v : Word} (h : WordAt m a v)
    (hp : m.Permitted .read a 8) : m.readBytes a 8 = some (Ext.leBytes v 8) := by
  have := Memory.readWith_eq m .read a (Ext.leBytes v 8) (by simpa using hp)
    (fun i hi => by rw [leBytes_getElem]; exact h i (by simpa using hi))
  rw [Ext.length_leBytes] at this
  exact this

theorem loadN_of_wordAt {m : Memory} {a : Nat} (ha : a < 2 ^ 64) {v : Word} (h : WordAt m a v)
    (hp : m.Permitted .read a 8) : Ext.loadN m (BitVec.ofNat 64 a) 8 = some v := by
  simp only [Ext.loadN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, readBytes_of_wordAt h hp,
    Option.map_some, Ext.leValue_leBytes, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt v.isLt]

theorem popWord_of_wordAt {s : State} {m : Memory} {v : Word} (h : WordAt m (s.read .rsp).toNat v)
    (hp : m.Permitted .read (s.read .rsp).toNat 8) :
    X86.popWord s m = some (v, s.write .rsp (s.read .rsp + 8#64)) := by
  apply X86.popWord_of_readBytes
  rw [readBytes_of_wordAt h hp, Ext.leBytes_eight]

theorem pushWord_some {s : State} {m : Memory} (v : Word)
    (hp : m.Permitted .write (s.read .rsp - 8#64).toNat 8) :
    ∃ m', X86.pushWord s m v = some (s.write .rsp (s.read .rsp - 8#64), m') ∧
      WordAt m' (s.read .rsp - 8#64).toNat v ∧
      Memory.WritesOnly m m' (s.read .rsp - 8#64).toNat 8 := by
  refine ⟨_, X86.pushWord_eq_some hp, ?_, ?_⟩
  · intro i hi
    have := X86.pushWord_get (X86.pushWord_eq_some (value := v) hp) i hi
    rw [this]
    congr 1
    simp only [X86.encodeWords_singleton]
    interval_cases i <;> rfl
  · exact X86.pushWord_writesOnly (X86.pushWord_eq_some (value := v) hp)

end Silmaril.X86.Backend
