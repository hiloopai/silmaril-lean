module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGetRun

/-!
# ptmalloc x86sim: the code-independent kit of `__libc_malloc`'s tcache-hit path

What every version's `__libc_malloc` tcache-hit proof shares, for **any** code bytes: the
stack window below the return address (`stk`, `slot`, `push_slot`), a push as a continuation
step (`ex_push`, any code), the tcache index the code computes (`tcIdx`, `hitBin`: gcc emits the
same `lea 0x17`, `and $~0xf`, `lea -0x11`, `shr $4` in 2.36, 2.39 and 2.40) and the arithmetic of
rip-relative operands (`ripRel`). The version-specific parts are the decode-fact bundles
(`X86sim.Gcc13.MallocSeq` for gcc 13/14, `Versions.V236` for gcc 12).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.Malloc
variable {A : Word}
set_option maxRecDepth 100000

/-- The stack slots `[sp - 32, sp)`. -/
def stk (sp : Word) (a : Nat) : Prop := sp.toNat - 32 ≤ a ∧ a < sp.toNat

/-- One push inside the slots: it writes only there, and reads back. -/
theorem push_facts {c : State} {mem : Memory} {v sp : Word} (k : Nat) (hk : k < 4)
    (hsp : 32 ≤ sp.toNat) (hrsp : c.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : mem.Permitted .write (sp.toNat - 32) 32) (hr : mem.Permitted .read (sp.toNat - 32) 32) :
    ∃ mem', Silmaril.X86.pushWord c mem v = some (c.write .rsp (c.read .rsp - 8#64), mem') ∧
      mem.WritesWithin mem' (stk sp) ∧
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [v]) ∧
      mem'.Permitted .write (sp.toNat - 32) 32 ∧ mem'.Permitted .read (sp.toNat - 32) 32 := by
  have ha : (c.read .rsp - 8#64).toNat = sp.toNat - 8 * (k + 1) := by
    rw [hrsp]; bv_omega
  have hsub : ∀ {acc}, mem.Permitted acc (sp.toNat - 32) 32 → mem.Permitted acc (sp.toNat - 8 * (k + 1)) 8 := by
    intro acc h
    simp only [Memory.Permitted, Memory.checkSpan_iff] at h ⊢
    refine ⟨by omega, by omega, fun o ho => ?_⟩
    have := h.2.2 (32 - 8 * (k + 1) + o) (by omega)
    rwa [show sp.toNat - 32 + (32 - 8 * (k + 1) + o) = sp.toNat - 8 * (k + 1) + o by omega] at this
  have hp := Silmaril.X86.pushWord_eq_some (s := c) (value := v) (by rw [ha]; exact hsub hw)
  refine ⟨_, hp, ?_, ?_, ?_, ?_⟩
  · have wo := Silmaril.X86.pushWord_writesOnly hp
    rw [Memory.writesOnly_iff_writesWithin] at wo
    refine wo.mono ?_
    intro a ⟨h1, h2⟩; rw [ha] at h1 h2; exact ⟨by omega, by omega⟩
  · rw [← ha]; exact Silmaril.X86.pushWord_readBytes hp (by rw [ha]; exact hsub hr)
  · exact hw
  · exact hr


theorem slot_apart {sp : Word} {k j : Nat} (hkj : k ≠ j) (hk : k < 4) (hj : j < 4) (hsp : 32 ≤ sp.toNat) :
    ∀ i < 8, ¬ (sp.toNat - 8 * (j + 1) ≤ sp.toNat - 8 * (k + 1) + i ∧
      sp.toNat - 8 * (k + 1) + i < sp.toNat - 8 * (j + 1) + 8) := by
  intro i hi ⟨h1, h2⟩; omega
/-- Slot `k` below `sp`. -/
def slot (sp : Word) (k : Nat) (a : Nat) : Prop := sp.toNat - 8 * (k + 1) ≤ a ∧ a < sp.toNat - 8 * (k + 1) + 8

theorem slot_stk {sp : Word} {k : Nat} (hk : k < 4) (hsp : 32 ≤ sp.toNat) {a : Nat} (h : slot sp k a) :
    stk sp a := by unfold slot at h; unfold stk; omega

theorem push_slot {c : State} {mem : Memory} {v sp : Word} (k : Nat) (hk : k < 4)
    (hsp : 32 ≤ sp.toNat) (hrsp : c.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : mem.Permitted .write (sp.toNat - 32) 32) (hr : mem.Permitted .read (sp.toNat - 32) 32) :
    ∃ mem', Silmaril.X86.pushWord c mem v = some (c.write .rsp (c.read .rsp - 8#64), mem') ∧
      mem.WritesWithin mem' (slot sp k) ∧
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [v]) ∧
      mem'.Permitted .write (sp.toNat - 32) 32 ∧ mem'.Permitted .read (sp.toNat - 32) 32 := by
  have ha : (c.read .rsp - 8#64).toNat = sp.toNat - 8 * (k + 1) := by
    rw [hrsp]; bv_omega
  obtain ⟨mem', hp, -, hb, hw', hr'⟩ := push_facts (v := v) k hk hsp hrsp hw hr
  refine ⟨mem', hp, ?_, hb, hw', hr'⟩
  have wo := Silmaril.X86.pushWord_writesOnly hp
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine wo.mono ?_
  intro a ⟨h1, h2⟩; rw [ha] at h1 h2; exact ⟨h1, h2⟩

/-- **A push as a continuation** (any code): the new memory, its frame and the pushed slot. -/
theorem ex_push {code : List Byte} {P : MState → Prop} {m : MState} {sp : Word} {k o l : Nat} {r : Reg}
    (hl : Loaded m.memory A code) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length)
    (hdec : Str9Fs.decode ((code.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.push r)))), l))
    (hk : k < 4) (hsp : 32 ≤ sp.toNat) (hrsp : m.core.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : m.memory.Permitted .write (sp.toNat - 32) 32) (hr : m.memory.Permitted .read (sp.toNat - 32) 32)
    (hcode : ∀ i < code.length, ¬ stk sp (A.toNat + i))
    (cont : ∀ mem', m.memory.WritesWithin mem' (slot sp k) →
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [m.core.read r]) →
      mem'.Permitted .write (sp.toNat - 32) 32 → mem'.Permitted .read (sp.toNat - 32) 32 →
      Loaded mem' A code →
      ∃ u, Reaches Str9Fs.step
        ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with rip := m.core.rip + BitVec.ofNat 64 l }, mem'⟩ u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  have hN : code.length = code.length := rfl
  obtain ⟨mem', hp, hw', hb, hw2, hr2⟩ := push_slot (c := m.core) (mem := m.memory) (v := m.core.read r)
    k hk hsp hrsp hw hr
  exact ex_head (stepC hN hl hrip hfit hdec (exec_push hp)) (cont mem' hw' hb hw2 hr2
    (loadedC_ww hN hl hw' (fun i hi h => hcode i hi (slot_stk hk hsp h))))

/-- The tcache index `malloc` computes from the request `n` (`csize2tidx (request2size n)`,
in machine words). -/
def tcIdx (n : Word) : Word :=
  if (n + 0x17#64).toNat ≤ 0x1f then 0 else (((n + 0x17#64) &&& 0xfffffffffffffff0#64) - 0x11#64) >>> 4

theorem ex_of {P Q : MState → Prop} {m : MState} (h : ∃ u, Reaches Str9Fs.step m u ∧ Q u)
    (hq : ∀ u, Q u → P u) : ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨u, hu, h⟩ := h; exact ⟨u, hu, hq u h⟩

/-- The bin `__libc_malloc (n)` looks up (`csize2tidx (request2size n)`, as the code computes it). -/
def hitBin (n : Nat) : Nat := (tcIdx (BitVec.ofNat 64 n)).toNat

/-- A rip-relative operand: the instruction at `o`, `l` bytes long, with displacement `d`, reads
`A + t` when `o + l + d = t` (in words). -/
theorem ripRel {o l t : Nat} {d : BitVec 32}
    (h : BitVec.ofNat 64 (o + l) + d.signExtend 64 = BitVec.ofNat 64 t) :
    A + BitVec.ofNat 64 o + BitVec.ofNat 64 l + d.signExtend 64 = A + BitVec.ofNat 64 t := by
  rw [rip_add, BitVec.add_assoc, h]

/-- `ripRel` once the instruction's end `n = o + l` is folded. -/
theorem ripRel' {n t : Nat} {d : BitVec 32}
    (h : BitVec.ofNat 64 n + d.signExtend 64 = BitVec.ofNat 64 t) :
    A + BitVec.ofNat 64 n + d.signExtend 64 = A + BitVec.ofNat 64 t := by
  rw [BitVec.add_assoc, h]

/-- Adding a literal to a word at `base + a` (no kernel evaluation of `base + _`). -/
theorem ofNat_lit_add {base a b : Nat} : BitVec.ofNat 64 (base + a) + BitVec.ofNat 64 b =
    BitVec.ofNat 64 (base + (a + b)) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]

end Silmaril.Libc.Ptmalloc.X86sim.Malloc
