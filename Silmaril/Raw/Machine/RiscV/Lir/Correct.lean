module

public import Silmaril.Machine.RiscV.Lir.Frame.Defs
/-!
# Correctness of the Lir-to-RV64 backend

`Match A p S N s m` relates a Lir state `s` of program `p` to a machine state
`m` running `emitProg A.reg N p` laid out by `S`:

* the machine invariant `Good` holds and the PC is the address of `s.point`;
* the current frame is at `spAt d = stackHi - (d + 1) * frameSize N`, where `d`
  is the number of suspended activations, and fits above `stackLo`;
* `s11` holds `memBase` and `s10` holds `stackLo`;
* every defined register of the current frame is in its RV64 register, every
  defined slot below `N` is in the frame, and the frame's return-address word is
  the return address of the innermost suspended call (the halt stub for the
  outermost frame);
* every suspended activation's defined registers are in its frame's save area,
  its slots in its frame, and its return address word is correct (`StackOK`);
* the Lir linear memory is the machine memory at `memBase` (`MemRel`).

The simulation is stated for the machine extended with a *stack-overflow
stutter*: a state stopped at the overflow stub (`Overflowed`) may take
self-loops. Lir has an unbounded stack while the machine stack is
`[stackLo, stackHi)`; a call whose frame does not fit branches to the overflow
stub. The final theorems (`Silmaril.RiscV.Lir.Loader`) project the self-loops
away: each Lir outcome is matched on the machine, *or* the machine reaches the
overflow stub. `simulationBounded` is the variant without stutter for runs
whose call depth is bounded by a number of frames that fits in the stack.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.Process (Memory)
open Silmaril.RiscV.Ext (Compute MState)
open Machine.Lir (Prog Func Block Point Loc Op Term Frame Activation)
open Relation

/-! ## Control-transfer arithmetic -/

theorem bmod_small21 {v : Int} (h1 : -(2 ^ 20 : Int) ≤ v) (h2 : v < 2 ^ 20) :
    v.bmod (2 ^ 21) = v :=
  Int.bmod_eq_of_le (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)

theorem bmod_small64 {v : Int} (h1 : -(2 ^ 20 : Int) ≤ v) (h2 : v < 2 ^ 20) :
    v.bmod (2 ^ 64) = v :=
  Int.bmod_eq_of_le (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)

theorem signExtend_ofInt21 {v : Int} (h1 : -(2 ^ 20 : Int) ≤ v) (h2 : v < 2 ^ 20) :
    (BitVec.ofInt 21 v).signExtend 64 = BitVec.ofInt 64 v := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    bmod_small21 h1 h2, bmod_small64 h1 h2]

theorem ofInt21_even (k : Int) : (BitVec.ofInt 21 (4 * k)).getLsbD 0 = false := by
  rw [← BitVec.testBit_toNat, Nat.testBit_zero, BitVec.toNat_ofInt]
  simp only [decide_eq_false_iff_not]
  omega

/-- A `JAL` whose offset fits reaches its target index. -/
theorem jal_target {cb src dst : Nat} (h : jalFits src dst = true) :
    addrOf cb src + Ext.jalOffset (jalHalf src dst) = addrOf cb dst := by
  simp only [jalFits, decide_eq_true_eq] at h
  rw [jalHalf, Ext.jalOffset_of_even _ (ofInt21_even ((dst : Int) - src)),
    signExtend_ofInt21 h.1 h.2]
  simp only [addrOf]
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  omega

theorem addrOf_align {cb : Nat} (h : cb % 4 = 0) (k : Nat) : (addrOf cb k).toNat % 4 = 0 := by
  simp only [addrOf, BitVec.toNat_ofNat]
  omega

theorem jalr_self {cb : Nat} (h : cb % 4 = 0) (k : Nat) :
    (addrOf cb k + (0#12).signExtend 64) &&& ~~~1#64 = addrOf cb k := by
  have hz : (0#12).signExtend 64 = 0#64 := by decide
  rw [hz, BitVec.add_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0
    have := addrOf_align h k
    rw [← BitVec.testBit_toNat, Nat.testBit_zero]
    simp; omega
  · simp [hi, h0]

theorem branch_eight : Ext.branchOffset 4#12 = 8#64 := by decide

theorem addi_neg (B F : Nat) (hF : F ≤ 2032) (hB : F ≤ B) :
    BitVec.ofNat 64 B + (BitVec.ofInt 12 (-(F : Int))).signExtend 64 = BitVec.ofNat 64 (B - F) := by
  have e : (BitVec.ofInt 12 (-(F : Int))).signExtend 64 = BitVec.ofInt 64 (-(F : Int)) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
    rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
  rw [e, ← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  omega

theorem addi_pos (B F : Nat) (hF : F < 2048) :
    BitVec.ofNat 64 B + (imm12 F).signExtend 64 = BitVec.ofNat 64 (B + F) := by
  rw [imm12_signExtend hF, BitVec.ofNat_add]

/-! ## Code lookup helpers -/

theorem getElem?_of_drop {α : Type} {l rest : List α} {k : Nat} {x : α}
    (h : l.drop k = x :: rest) : l[k]? = some x := by
  have := congrArg (·[0]?) h
  simpa [List.getElem?_drop] using this

theorem drop_split {α : Type} {l a b : List α} {k : Nat} (h : l.drop k = a ++ b) :
    l.drop (k + a.length) = b := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ## The matching relation -/

variable {P : Type} [DecidableEq P] (A : Assign P) (p : Prog P) (S : Space) (N : Nat)

/-- The frame base at depth `d`. -/
def spAt (d : Nat) : Nat := S.stackHi - (d + 1) * frameSize N

/-- The return address stored in the frame whose caller activations are `stk`. -/
def retAddr : List (Activation P) → Word
  | [] => addrOf S.codeBase haltIdx
  | a :: _ => addrOf S.codeBase (retIdx p a.point)

/-- Suspended activations: registers in the save area, slots and return
address in the frame. The head of the list is the innermost caller. -/
def StackOK (mem : Memory) : List (Activation P) → Prop
  | [] => True
  | a :: rest =>
    (SavedAt A mem (spAt S N rest.length) a.frame ∧
      SlotsAt N mem (spAt S N rest.length) a.frame ∧
      WordAt mem (spAt S N rest.length + raOff N) (retAddr p S rest)) ∧
    StackOK mem rest

structure Match (s : Machine.Lir.State P) (m : MState) : Prop where
  good : Good S (emitProg A.reg N p) m
  pc : m.core.pc = addrOf S.codeBase (pointIdx p s.point)
  depth : S.stackLo + (s.stack.length + 1) * frameSize N ≤ S.stackHi
  sp : m.core.read sp = BitVec.ofNat 64 (spAt S N s.stack.length)
  base : m.core.read s11 = BitVec.ofNat 64 S.memBase
  limit : m.core.read s10 = BitVec.ofNat 64 S.stackLo
  regs : RegsAt A s.frame m.core
  slots : SlotsAt N m.memory (spAt S N s.stack.length) s.frame
  ra : WordAt m.memory (spAt S N s.stack.length + raOff N) (retAddr p S s.stack)
  stack : StackOK A p S N m.memory s.stack
  mem : MemRel S.memBase s.mem m.memory
  size : s.mem.size = S.memSize

/-- The machine stopped at the stack-overflow stub. -/
def Overflowed (m : MState) : Prop :=
  Good S (emitProg A.reg N p) m ∧ m.core.pc = addrOf S.codeBase overflowIdx

/-- A whole-program return: at the halt stub with the values in `a0 …` and the
final linear memory at `memBase`. -/
def Returned (vs : List Word) (mem : Machine.Lir.Memory) (m : MState) : Prop :=
  Good S (emitProg A.reg N p) m ∧ m.core.pc = addrOf S.codeBase haltIdx ∧ vs.length ≤ 8 ∧
    (∀ k (h : k < vs.length), m.core.read (argRegN k) = vs[k]) ∧
    MemRel S.memBase mem m.memory ∧ mem.size = S.memSize

/-- A Lir trap: at the trap stub with the linear memory at `memBase`. -/
def Trapped (mem : Machine.Lir.Memory) (m : MState) : Prop :=
  Good S (emitProg A.reg N p) m ∧ m.core.pc = addrOf S.codeBase trapIdx ∧
    MemRel S.memBase mem m.memory ∧ mem.size = S.memSize

/-! ## Invariance under memory writes -/

omit [DecidableEq P] in
theorem spAt_frame {n : Nat} (hv : S.Valid n) (hsm : frameSize N ≤ 2032) {d : Nat}
    (hd : S.stackLo + (d + 1) * frameSize N ≤ S.stackHi) : FrameAt S N (spAt S N d) := by
  have := hv.stack_align
  have hm : (d + 1) * frameSize N % 16 = 0 := by
    rw [Nat.mul_mod, frameSize_mod]; simp
  have hX : frameSize N ≤ (d + 1) * frameSize N := Nat.le_mul_of_pos_left _ (by omega)
  unfold spAt
  generalize (d + 1) * frameSize N = X at *
  refine ⟨?_, ?_, ?_, hsm⟩
  · omega
  · omega
  · omega

omit [DecidableEq P] in
theorem spAt_succ (d : Nat) (hd : (d + 2) * frameSize N ≤ S.stackHi) :
    spAt S N d = spAt S N (d + 1) + frameSize N := by
  unfold spAt
  rw [show d + 1 + 1 = d + 2 by omega]
  rw [show (d + 2) * frameSize N = (d + 1) * frameSize N + frameSize N by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.succ_mul]] at hd ⊢
  generalize (d + 1) * frameSize N = X at *
  omega

omit [DecidableEq P] in
/-- A write below the frames of `stk`, or outside the stack, preserves them. -/
theorem StackOK.of_writesIn {mem mem' : Memory} {lo hi : Nat} (hw : WritesIn mem mem' lo hi) :
    ∀ {stk : List (Activation P)},
    (∀ b, S.stackHi - stk.length * frameSize N ≤ b → b + 8 ≤ S.stackHi → b + 8 ≤ lo ∨ hi ≤ b) →
    S.stackLo + (stk.length + 1) * frameSize N ≤ S.stackHi →
    StackOK A p S N mem stk → StackOK A p S N mem' stk
  | [], _, _, _ => trivial
  | a :: rest, hd, hdepth, ⟨⟨hsave, hslots, hra⟩, hrest⟩ => by
    have hF := frameSize_ge N
    have hra' := raOff_lt N
    have hsl : ∀ k < N, slotOff k + 8 ≤ frameSize N := fun k hk => by
      have := slotOff_lt hk; omega
    simp only [List.length_cons] at hd hdepth
    have e1 : (rest.length + 1 + 1) * frameSize N = (rest.length + 1) * frameSize N + frameSize N :=
      Nat.succ_mul _ _
    have e2 : (rest.length + 1) * frameSize N = rest.length * frameSize N + frameSize N :=
      Nat.succ_mul _ _
    have base : S.stackHi - (rest.length + 1) * frameSize N = spAt S N rest.length := rfl
    rw [e1] at hdepth
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact hsave.of_writesIn A hw fun i => hd _ (by omega) (by omega)
    · exact hslots.of_writesIn hw fun k hk => hd _ (by omega) (by have := hsl k hk; omega)
    · exact hw.wordAt (hd _ (by omega) (by omega)) hra
    · apply StackOK.of_writesIn hw _ (by omega) hrest
      intro b hb hb'
      exact hd b (by omega) hb'

/-- Stack writes leave the linear memory unchanged. -/
theorem MemRel.of_writesIn {mem mem' : Memory} {lm : Machine.Lir.Memory} {lo hi : Nat}
    (h : MemRel S.memBase lm mem) (hw : WritesIn mem mem' lo hi) (hs : lm.size = S.memSize)
    (hd : ∀ a, S.InMem a → a < lo ∨ hi ≤ a) : MemRel S.memBase lm mem' := by
  intro a ha
  rw [hw.2 _ (hd _ ⟨by omega, by omega⟩)]
  exact h a ha

/-! ## Updating the match -/

section Updates

variable {A p S N}

omit [DecidableEq P] in
theorem Match.frameAt {s : Machine.Lir.State P} {m : MState} (hm : Match A p S N s m)
    (hv : S.Valid (emitProg A.reg N p).length) (hsm : frameSize N ≤ 2032) :
    FrameAt S N (spAt S N s.stack.length) :=
  spAt_frame S N hv hsm hm.depth

/-- An operation that writes one Lir register and leaves memory unchanged. -/
theorem Match.set_reg {s : Machine.Lir.State P} {t t' : MState} {d : P} {z : Word}
    (hm : Match A p S N s t) (hgood : Good S (emitProg A.reg N p) t')
    (hpc : t'.core.pc = addrOf S.codeBase (pointIdx p s.point.next))
    (hmem : t'.memory = t.memory) (hdst : t'.core.read (A.reg d) = z)
    (hother : ∀ r, r ≠ A.reg d → ¬ Scratch r → t'.core.read r = t.core.read r) :
    Match A p S N ⟨s.point.next, s.frame.set d z, s.stack, s.mem⟩ t' where
  good := hgood
  pc := hpc
  depth := hm.depth
  sp := (hother Backend.sp (fun e => A.reg_ne_sp d e.symm) not_scratch_sp).trans hm.sp
  base := (hother s11 (fun e => A.reg_ne_s11 d e.symm) not_scratch_s11).trans hm.base
  limit := (hother s10 (fun e => A.reg_ne_s10 d e.symm) not_scratch_s10).trans hm.limit
  regs := by
    intro r x hx
    simp only [Frame.regs_set] at hx
    by_cases e : r = d
    · subst e; simp only [ite_true, Option.some.injEq] at hx; rw [← hx]; exact hdst
    · simp only [e, ite_false] at hx
      rw [hother _ (fun h => e (A.reg_injective h)) (A.not_scratch r)]
      exact hm.regs r x hx
  slots := by rw [hmem]; exact hm.slots
  ra := by rw [hmem]; exact hm.ra
  stack := by rw [hmem]; exact hm.stack
  mem := by rw [hmem]; exact hm.mem
  size := hm.size

omit [DecidableEq P] in
/-- A linear-memory store. -/
theorem Match.set_mem {s : Machine.Lir.State P} {t t' : MState} {mem' : Machine.Lir.Memory}
    (hv : S.Valid (emitProg A.reg N p).length)
    (hm : Match A p S N s t) (hgood : Good S (emitProg A.reg N p) t')
    (hpc : t'.core.pc = addrOf S.codeBase (pointIdx p s.point.next))
    (hregs : ∀ r, ¬ Scratch r → t'.core.read r = t.core.read r)
    (hreg : t'.memory.regions = t.memory.regions)
    (hout : ∀ q, ¬ S.InMem q → t'.memory.bytes.get? q = t.memory.bytes.get? q)
    (hrel : MemRel S.memBase mem' t'.memory) (hsize : mem'.size = S.memSize) :
    Match A p S N ⟨s.point.next, s.frame, s.stack, mem'⟩ t' := by
  have hsm := hv.stack_mem
  have hw : WritesIn t.memory t'.memory S.memBase (S.memBase + S.memSize) :=
    ⟨hreg, fun q hq => hout q (by simp only [Space.InMem]; omega)⟩
  have hd : ∀ b, S.stackLo ≤ b → b + 8 ≤ S.stackHi →
      b + 8 ≤ S.memBase ∨ S.memBase + S.memSize ≤ b := fun b h1 h2 => by omega
  have hF := frameSize_ge N
  have hB := hm.depth
  have hlo : S.stackLo ≤ spAt S N s.stack.length := by
    unfold spAt; generalize (s.stack.length + 1) * frameSize N = X at *; omega
  have hhi : spAt S N s.stack.length + frameSize N ≤ S.stackHi := by
    have hX : frameSize N ≤ (s.stack.length + 1) * frameSize N := Nat.le_mul_of_pos_left _ (by omega)
    unfold spAt; generalize (s.stack.length + 1) * frameSize N = X at *; omega
  exact {
    good := hgood
    pc := hpc
    depth := hm.depth
    sp := (hregs Backend.sp not_scratch_sp).trans hm.sp
    base := (hregs s11 not_scratch_s11).trans hm.base
    limit := (hregs s10 not_scratch_s10).trans hm.limit
    regs := hm.regs.congr A fun r => hregs _ (A.not_scratch r)
    slots := hm.slots.of_writesIn hw fun k hk => by
      have := slotOff_lt hk; have := raOff_lt N
      exact hd _ (by omega) (by omega)
    ra := hw.wordAt (by dsimp only; have := raOff_lt N; exact hd _ (by omega) (by omega)) hm.ra
    stack := StackOK.of_writesIn A p S N hw (fun b h1 h2 => by
        dsimp only at h1
        have : S.stackLo ≤ b := by
          have e : S.stackHi - s.stack.length * frameSize N = spAt S N s.stack.length + frameSize N := by
            have hX : (s.stack.length + 1) * frameSize N = s.stack.length * frameSize N + frameSize N :=
              Nat.succ_mul _ _
            unfold spAt; rw [hX] at hB ⊢; generalize s.stack.length * frameSize N = Y at *; omega
          omega
        exact hd b this h2) hm.depth hm.stack
    mem := hrel
    size := hsize }

omit [DecidableEq P] in
/-- A stack-slot store in the current frame. -/
theorem Match.set_slot {s : Machine.Lir.State P} {t t' : MState} {k : Nat} {x : Word}
    (hv : S.Valid (emitProg A.reg N p).length)
    (hm : Match A p S N s t) (hgood : Good S (emitProg A.reg N p) t')
    (hpc : t'.core.pc = addrOf S.codeBase (pointIdx p s.point.next))
    (hregs : ∀ r, t'.core.read r = t.core.read r) (hk : k < N)
    (hw : WordAt t'.memory (spAt S N s.stack.length + slotOff k) x)
    (hwi : WritesIn t.memory t'.memory (spAt S N s.stack.length + slotOff k)
      (spAt S N s.stack.length + slotOff k + 8)) :
    Match A p S N ⟨s.point.next, s.frame.setSlot k x, s.stack, s.mem⟩ t' := by
  have hF := frameSize_ge N
  have hB := hm.depth
  have hsk := slotOff_lt hk
  have hra := raOff_lt N
  have hsm := hv.stack_mem
  have hlo : S.stackLo ≤ spAt S N s.stack.length := by
    unfold spAt; generalize (s.stack.length + 1) * frameSize N = X at *; omega
  have e : S.stackHi - s.stack.length * frameSize N = spAt S N s.stack.length + frameSize N := by
    have hX : (s.stack.length + 1) * frameSize N = s.stack.length * frameSize N + frameSize N :=
      Nat.succ_mul _ _
    unfold spAt; rw [hX] at hB ⊢; generalize s.stack.length * frameSize N = Y at *; omega
  exact {
    good := hgood
    pc := hpc
    depth := hm.depth
    sp := (hregs Backend.sp).trans hm.sp
    base := (hregs s11).trans hm.base
    limit := (hregs s10).trans hm.limit
    regs := hm.regs.congr A fun r => hregs _
    slots := by
      intro k' x' hk' hx'
      simp only [Frame.slots_setSlot] at hx'
      by_cases e' : k' = k
      · subst e'; simp only [ite_true, Option.some.injEq] at hx'; subst hx'; exact hw
      · simp only [e', ite_false] at hx'
        apply hwi.wordAt _ (hm.slots k' x' hk' hx')
        unfold slotOff; have : k' ≠ k := e'; omega
    ra := hwi.wordAt (by dsimp only; unfold slotOff raOff at *; omega) hm.ra
    stack := StackOK.of_writesIn A p S N hwi (fun b h1 h2 => by dsimp only at h1; omega) hm.depth
      hm.stack
    mem := hm.mem.of_writesIn S hwi hm.size fun a ha => by
      simp only [Space.InMem] at ha; omega
    size := hm.size }

end Updates

/-! ## Operations -/

section Cases

variable {A p S N}
variable (hc : checkProg p N = none) (hv : S.Valid (emitProg A.reg N p).length)
include hc hv

omit hc in
theorem compute_case {s : Machine.Lir.State P} {t : MState} {cs : List Compute} {d : P} {z : Word}
    {rest : List Ext.Instr} (hm : Match A p S N s t)
    (hcode : (emitProg A.reg N p).drop (pointIdx p s.point) = cs.map .compute ++ rest)
    (hnext : pointIdx p s.point.next = pointIdx p s.point + cs.length) (hne : cs ≠ [])
    (hdests : DestsIn cs (A.reg d))
    (hval : (Machine.Block.run Compute.step cs t.core).read (A.reg d) = z) :
    ∃ t', TransGen TStep t t' ∧ Match A p S N ⟨s.point.next, s.frame.set d z, s.stack, s.mem⟩ t' := by
  obtain ⟨tg, hg, hpc⟩ := chunk_trans hv (by simpa using hne) hm.good hm.pc hcode (runSeq_compute cs t)
  refine ⟨_, tg, hm.set_reg hg (by rw [hpc, hnext, List.length_map]) rfl hval
    (fun r h1 h2 => run_frame hdests _ r h1 h2)⟩

theorem op_case {s : Machine.Lir.State P} {t : MState} {o : Op P} {fr : Frame P}
    {mem : Machine.Lir.Memory} (hm : Match A p S N s t)
    (hf : p.fetch s.point = some (.instr (.op o))) (he : o.exec s.frame s.mem = some (fr, mem)) :
    ∃ t', TransGen TStep t t' ∧ Match A p S N ⟨s.point.next, fr, s.stack, mem⟩ t' := by
  obtain ⟨rest, hcode⟩ := code_at_instr A.reg N p hf
  have hnext := pointIdx_next p hf
  have hsz : instrSize (.op o : Machine.Lir.Instr P) = (opCode A.reg o).length :=
    opCode_length _ _ o
  rw [hsz] at hnext
  simp only [emitInstr] at hcode
  have hsm := check_frame hc
  have hci := check_instr hc hf
  have hfr := hm.frameAt hv hsm
  cases o with
  | const d v =>
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact compute_case hv hm hcode (by simpa [opCode] using hnext) (li_ne_nil _ _)
      (li_dests _ _) (li_value _ (A.reg_ne_zero d) v _)
  | move d x =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨y, hy, rfl, rfl⟩ := he
    exact compute_case hv hm hcode (by simpa [opCode] using hnext) (by simp [selMove])
      (selMove_dests _ _) (by rw [selMove_value (A.reg_ne_zero d)]; exact hm.regs x y hy)
  | unary op d x =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨y, hy, rfl, rfl⟩ := he
    have hsome := selUnop_isSome op (A.reg d) (A.reg x)
    obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp hsome
    simp only [opCode, hcs, Option.getD_some] at hcode hnext
    exact compute_case hv hm hcode (by simpa using hnext) (selUnop_ne_nil hcs) (selUnop_dests hcs)
      (by rw [selUnop_value hcs (A.not_scratch x) (A.reg_ne_zero d), hm.regs x y hy])
  | binary op d x y =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, b, hb, z, hz, rfl, rfl⟩ := he
    simp only [opCode] at hcode hnext
    exact compute_case hv hm hcode (by simpa using hnext) (selBinop_ne_nil _ _ _ _)
      (selBinop_dests _ _ _ _)
      (selBinop_value op (A.reg_ne_zero d) (A.not_scratch x) (A.not_scratch y) _
        (by rw [hm.regs x a ha, hm.regs y b hb]; exact hz))
  | load w e d b off =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, z, hz, rfl, rfl⟩ := he
    simp only [opCode] at hcode hnext
    obtain ⟨t', hrun, hmem, hdst, hother⟩ := selLoad_spec hv hm.size (A.not_scratch d)
      (A.reg_ne_zero d) (A.not_scratch b) t hm.good.regions hm.mem hm.base
      (by rw [hm.regs b a ha]; exact hz)
    have hne : selLoad w e (A.reg d) (A.reg b) off ≠ [] := by
      intro h; have := congrArg List.length h
      simp [selLoad, loadBytes_length] at this
    obtain ⟨tg, hg, hpc⟩ := chunk_trans hv hne hm.good hm.pc hcode hrun
    exact ⟨_, tg, hm.set_reg hg (by rw [hpc, hnext]) hmem hdst hother⟩
  | store w b off x =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, y, hy, mem', hst, rfl, rfl⟩ := he
    simp only [opCode] at hcode hnext
    obtain ⟨t', hrun, hreg, hrel, hout, hregs⟩ := selStore_spec hv hm.size (A.not_scratch b)
      (A.not_scratch x) t hm.good.regions hm.mem hm.base
      (by rw [hm.regs b a ha, hm.regs x y hy]; exact hst)
    have hne : selStore w (A.reg b) off (A.reg x) ≠ [] := by
      intro h; have hl := congrArg List.length h
      have hw := width_bytes_pos w
      simp [selStore, storeBytes_length] at hl; omega
    obtain ⟨tg, hg, hpc⟩ := chunk_trans hv hne hm.good hm.pc hcode hrun
    exact ⟨_, tg, hm.set_mem hv hg (by rw [hpc, hnext]) hregs hreg hout hrel
      (by rw [Machine.Lir.Memory.store_size hst]; exact hm.size)⟩
  | slotGet d k =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨y, hy, rfl, rfl⟩ := he
    have hk : k < N := by
      simp only [checkInstr] at hci; split at hci
      · assumption
      · cases hci
    simp only [opCode] at hcode hnext
    have := slotOff_lt hk; have := raOff_lt N
    have hrun := frame_ld hv hfr (rd := A.reg d) (rest := []) (by unfold slotOff; omega) (by omega)
      hm.sp (hm.slots k y hk hy)
    obtain ⟨tg, hg, hpc⟩ := chunk_trans hv (by simp) hm.good hm.pc hcode hrun
    refine ⟨_, tg, hm.set_reg hg (by rw [hpc, hnext]) rfl ?_ ?_⟩
    · simp only [State.read_setPc]; exact State.read_write_same _ _ _ (A.reg_ne_zero d)
    · intro r h1 _; simp only [State.read_setPc]; exact State.read_write_other _ _ _ _ h1
  | slotSet k x =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨y, hy, rfl, rfl⟩ := he
    have hk : k < N := by
      simp only [checkInstr] at hci; split at hci
      · assumption
      · cases hci
    simp only [opCode] at hcode hnext
    have := slotOff_lt hk; have := raOff_lt N
    obtain ⟨mem', hrun, hw, hwi⟩ := frame_sd hv hfr (r := A.reg x) (off := slotOff k) (rest := []) (m := t)
      (by unfold slotOff; omega) (by omega) hm.good.regions hm.sp
    obtain ⟨tg, hg, hpc⟩ := chunk_trans hv (by simp) hm.good hm.pc hcode (hrun.trans rfl)
    refine ⟨_, tg, hm.set_slot hv hg (by rw [hpc, hnext]) (fun r => rfl) hk ?_ hwi⟩
    rw [hm.regs x y hy] at hw; exact hw

/-! ## Jumps, branches and traps -/

omit [DecidableEq P] hc in
/-- A `JAL` at index `k` to index `dst`. -/
theorem jal_step {t : MState} {k dst : Nat} {rd : Reg} (hg : Good S (emitProg A.reg N p) t)
    (hpc : t.core.pc = addrOf S.codeBase k) (hcode : (emitProg A.reg N p)[k]? = some (jalI rd k dst))
    (hfit : jalFits k dst = true) :
    TStep t ⟨{ t.core.write rd (t.core.pc + 4) with pc := addrOf S.codeBase dst }, t.memory⟩ ∧
      Good S (emitProg A.reg N p) ⟨{ t.core.write rd (t.core.pc + 4) with
        pc := addrOf S.codeBase dst }, t.memory⟩ := by
  have ht : t.core.pc + Ext.jalOffset (jalHalf k dst) = addrOf S.codeBase dst := by
    rw [hpc]; exact jal_target hfit
  apply tstep_at hv hg hpc hcode
  rw [jalI, Ext.Instr.exec_jal t (by rw [ht]; exact addrOf_align hv.code_align dst), ht]

omit [DecidableEq P] hc hv in
theorem Match.set_point {s : Machine.Lir.State P} {t t' : MState} {pt : Point}
    (hm : Match A p S N s t) (hg : Good S (emitProg A.reg N p) t')
    (hpc : t'.core.pc = addrOf S.codeBase (pointIdx p pt)) (hmem : t'.memory = t.memory)
    (hregs : ∀ r, t'.core.read r = t.core.read r) :
    Match A p S N ⟨pt, s.frame, s.stack, s.mem⟩ t' where
  good := hg
  pc := hpc
  depth := hm.depth
  sp := (hregs _).trans hm.sp
  base := (hregs _).trans hm.base
  limit := (hregs _).trans hm.limit
  regs := hm.regs.congr A fun r => hregs _
  slots := by rw [hmem]; exact hm.slots
  ra := by rw [hmem]; exact hm.ra
  stack := by rw [hmem]; exact hm.stack
  mem := by rw [hmem]; exact hm.mem
  size := hm.size

omit [DecidableEq P] in
theorem jump_case {s : Machine.Lir.State P} {t : MState} {l : Nat} (hm : Match A p S N s t)
    (hf : p.fetch s.point = some (.term (.jump l))) :
    ∃ t', TransGen TStep t t' ∧ Match A p S N ⟨⟨s.point.func, l, 0⟩, s.frame, s.stack, s.mem⟩ t' := by
  obtain ⟨rest, hcode⟩ := code_at_term A.reg N p hf
  have hct := check_term hc hf
  simp only [checkTerm] at hct
  have hfit : jalFits (pointIdx p s.point) (blockStart p s.point.func l) = true := by
    split at hct
    · assumption
    · cases hct
  simp only [emitTerm, List.singleton_append] at hcode
  obtain ⟨st, hg⟩ := jal_step hv hm.good hm.pc (getElem?_of_drop hcode) hfit
  refine ⟨_, .single st, hm.set_point hg ?_ rfl ?_⟩
  · simp only [pointIdx_zero]
  · intro r; simp only [State.write_zero]; rfl

omit [DecidableEq P] in
theorem branch_case {s : Machine.Lir.State P} {t : MState} {c : P} {l₁ l₂ : Nat} {x : Word}
    (hm : Match A p S N s t) (hf : p.fetch s.point = some (.term (.branch c l₁ l₂)))
    (hx : s.frame.get c = some x) :
    ∃ t', TransGen TStep t t' ∧
      Match A p S N ⟨⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩, s.frame, s.stack, s.mem⟩ t' := by
  obtain ⟨rest, hcode⟩ := code_at_term A.reg N p hf
  have hct := check_term hc hf
  simp only [checkTerm] at hct
  have hfit : jalFits (pointIdx p s.point + 1) (blockStart p s.point.func l₁) = true ∧
      jalFits (pointIdx p s.point + 2) (blockStart p s.point.func l₂) = true := by
    split at hct
    · rename_i h; simpa using h
    · cases hct
  simp only [emitTerm, List.cons_append] at hcode
  have hc0 := getElem?_of_drop hcode
  have hc1 := getElem?_of_drop (drop_split (a := [_]) hcode)
  have hc2 := getElem?_of_drop (drop_split (a := [_, _]) hcode)
  simp only [List.length_cons, List.length_nil, Nat.zero_add,
    show pointIdx p s.point + (1 + 1) = pointIdx p s.point + 2 from rfl] at hc1 hc2
  have hxr : t.core.read (A.reg c) = x := hm.regs c x hx
  by_cases h0 : x = 0
  · -- taken: skip to the second jump
    have htaken : Ext.BranchOp.eval .eq (t.core.read (A.reg c)) (t.core.read 0#5) = true := by
      simp [Ext.BranchOp.eval, hxr, h0]
    have ht : t.core.pc + Ext.branchOffset 4#12 = addrOf S.codeBase (pointIdx p s.point + 2) := by
      rw [hm.pc, branch_eight, addrOf_add]
    obtain ⟨st₁, hg₁⟩ := tstep_at hv hm.good hm.pc hc0 (Ext.Instr.exec_branch_taken t htaken
      (by rw [ht]; exact addrOf_align hv.code_align _))
    obtain ⟨st₂, hg₂⟩ := jal_step hv hg₁ (by simp only; rw [ht]) hc2 hfit.2
    refine ⟨_, .tail (.single st₁) st₂, hm.set_point hg₂ ?_ rfl ?_⟩
    · simp [pointIdx_zero, h0]
    · intro r; simp only [State.write_zero]; rfl
  · have h0' : x ≠ 0#64 := h0
    have hnot : Ext.BranchOp.eval .eq (t.core.read (A.reg c)) (t.core.read 0#5) = false := by
      simp [Ext.BranchOp.eval, hxr, h0']
    have ht : t.core.pc + 4 = addrOf S.codeBase (pointIdx p s.point + 1) := by
      rw [hm.pc, addrOf_succ]
    obtain ⟨st₁, hg₁⟩ := tstep_at hv hm.good hm.pc hc0 (Ext.Instr.exec_branch_not_taken t hnot)
    obtain ⟨st₂, hg₂⟩ := jal_step hv hg₁ (by simp only; rw [ht]) hc1 hfit.1
    refine ⟨_, .tail (.single st₁) st₂, hm.set_point hg₂ ?_ rfl ?_⟩
    · simp [pointIdx_zero, h0']
    · intro r; simp only [State.write_zero]; rfl

omit [DecidableEq P] in
theorem trap_case {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    (hf : p.fetch s.point = some (.term .trap)) :
    ∃ t', ReflTransGen TStep t t' ∧ Trapped A p S N s.mem t' := by
  obtain ⟨rest, hcode⟩ := code_at_term A.reg N p hf
  have hct := check_term hc hf
  simp only [checkTerm] at hct
  have hfit : jalFits (pointIdx p s.point) trapIdx = true := by
    split at hct
    · assumption
    · cases hct
  simp only [emitTerm, List.singleton_append] at hcode
  obtain ⟨st, hg⟩ := jal_step hv hm.good hm.pc (getElem?_of_drop hcode) hfit
  exact ⟨_, .single st, hg, by simp, hm.mem, hm.size⟩

/-! ## Returns -/

omit [DecidableEq P] hc hv in
theorem readAll_length {fr : Frame P} :
    ∀ {locs : List (Loc P)} {vals : List Word}, fr.readAll locs = some vals → vals.length = locs.length
  | [], vals, h => by
    simp only [Frame.readAll, List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | l :: ls, vals, h => by
    obtain ⟨x, xs, _, hxs, rfl⟩ := readAll_cons h
    simp [readAll_length hxs]

omit [DecidableEq P] in
/-- The return sequence: returned values into `a0 …`, `ra` reloaded, `sp`
popped, and `JALR` to the return address. -/
theorem ret_seq {s : Machine.Lir.State P} {t : MState} {locs : List (Loc P)} {vals : List Word}
    (hm : Match A p S N s t) (hf : p.fetch s.point = some (.term (.ret locs)))
    (hvals : s.frame.readAll locs = some vals) :
    ∃ t', TransGen TStep t t' ∧ Good S (emitProg A.reg N p) t' ∧
      t'.core.pc = retAddr p S s.stack ∧ t'.memory = t.memory ∧
      t'.core.read sp = BitVec.ofNat 64 (spAt S N s.stack.length + frameSize N) ∧
      vals.length ≤ 8 ∧ (∀ k (h : k < vals.length), t'.core.read (argRegN k) = vals[k]) ∧
      (∀ r, r ≠ sp → r ≠ ra → (∀ k < 8, r ≠ argRegN k) → t'.core.read r = t.core.read r) := by
  obtain ⟨rest, hcode⟩ := code_at_term A.reg N p hf
  have hct := check_term hc hf
  simp only [checkTerm] at hct
  have hlen : locs.length ≤ 8 ∧ locsBelow N locs = true := by
    split at hct
    · cases hct
    · split at hct
      · cases hct
      · rename_i h1 h2; simp at h1 h2; exact ⟨by omega, h2⟩
  have hsm := check_frame hc
  have hfr := hm.frameAt hv hsm
  have hvl := readAll_length hvals
  simp only [emitTerm, List.append_assoc] at hcode
  -- values into a0 …
  obtain ⟨t₁, h₁, mem₁, vals₁, fr₁⟩ := loadLocsFrom_spec A hv hfr locs 0 vals t hvals hlen.2
    (by omega) hm.regs hm.slots hm.sp
  have hra := raOff_lt N
  have hF := frameSize_ge N
  have hsp₁ : t₁.core.read sp = BitVec.ofNat 64 (spAt S N s.stack.length) := by
    rw [fr₁ sp fun k hk => (argRegN_ne_sp (by omega)).symm]; exact hm.sp
  -- ld ra; addi sp
  have hld := frame_ld hv hfr (rd := ra) (off := raOff N)
    (rest := [addiI sp sp (imm12 (frameSize N))]) (m := t₁) (by unfold raOff; omega) hra hsp₁
    (by rw [mem₁]; exact hm.ra)
  set t₂ : MState := ⟨{ t₁.core.write ra (retAddr p S s.stack) with pc := t₁.core.pc + 4 }, t₁.memory⟩
  set c₃ : Compute := .base (.imm .add sp sp (imm12 (frameSize N)))
  have hrun : runSeq (loadLocs A.reg locs ++ [ldI ra sp (raOff N), addiI sp sp (imm12 (frameSize N))]) t =
      some ⟨c₃.step t₂.core, t₂.memory⟩ := by
    rw [runSeq_append, loadLocs, h₁, Option.bind_some, hld]
    exact runSeq_compute_cons _ _ _
  obtain ⟨tg, hg, hpc⟩ := chunk_trans hv (by simp) hm.good hm.pc
    (rest := Ext.Instr.jalr 0#5 ra 0#12 :: rest) (by rw [hcode]; simp) hrun
  set t₃ : MState := ⟨c₃.step t₂.core, t₂.memory⟩
  have hra₃ : t₃.core.read ra = retAddr p S s.stack := by
    simp [t₃, c₃, t₂, RiscV.Instr.dest, State.read_setPc]
  have hsp₃ : t₃.core.read sp = BitVec.ofNat 64 (spAt S N s.stack.length + frameSize N) := by
    simp only [t₃, c₃, t₂, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq,
      sp_ne_zero, not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.ImmOp.eval,
      State.read_setPc]
    rw [State.read_write_other _ _ _ _ (by decide), hsp₁, addi_pos _ _ (by omega)]
  -- jalr x0, 0(ra)
  have hcj : (emitProg A.reg N p)[pointIdx p s.point + (loadLocs A.reg locs ++
      [ldI ra sp (raOff N), addiI sp sp (imm12 (frameSize N))]).length]? = some (.jalr 0#5 ra 0#12) := by
    apply getElem?_of_drop (rest := rest)
    rw [drop_split (b := Ext.Instr.jalr 0#5 ra 0#12 :: rest) (by rw [hcode]; simp)]
  have htarget : Ext.jalrTarget t₃.core ra 0#12 = retAddr p S s.stack := by
    rw [Ext.jalrTarget, Ext.effectiveAddress, hra₃]
    cases hs : s.stack with
    | nil => exact jalr_self hv.code_align _
    | cons a rest' => exact jalr_self hv.code_align _
  have hal : (Ext.jalrTarget t₃.core ra 0#12).toNat % 4 = 0 := by
    rw [htarget]; cases s.stack <;> exact addrOf_align hv.code_align _
  obtain ⟨st₄, hg₄⟩ := tstep_at hv hg hpc hcj (Ext.Instr.exec_jalr t₃ hal)
  refine ⟨_, .tail tg st₄, hg₄, by simp [htarget], by simp [t₃, t₂, mem₁], ?_, by omega, ?_, ?_⟩
  · simp only [State.write_zero, State.read_setPc]; exact hsp₃
  · intro k hk
    have hk8 : k < 8 := by omega
    have e1 := argRegN_ne_sp hk8
    have e2 := argRegN_ne_ra hk8
    have := vals₁ k hk
    simp only [Nat.zero_add] at this
    simp only [State.write_zero, State.read_setPc, t₃, c₃, t₂, Ext.Compute.step_base,
      read_base_step, RiscV.Instr.dest, e1, e2, false_and, ↓reduceIte, State.read_write_eq, this]
  · intro r h1 h2 h3
    have := fr₁ r fun k hk => by simpa using h3 k (by omega)
    simp only [State.write_zero, State.read_setPc, t₃, c₃, t₂, Ext.Compute.step_base,
      read_base_step, RiscV.Instr.dest, h1, h2, false_and, ↓reduceIte, State.read_write_eq, this]

omit [DecidableEq P] in
theorem halt_case {s : Machine.Lir.State P} {t : MState} {locs : List (Loc P)} {vals : List Word}
    (hm : Match A p S N s t) (hf : p.fetch s.point = some (.term (.ret locs)))
    (hvals : s.frame.readAll locs = some vals) (hs : s.stack = []) :
    ∃ t', ReflTransGen TStep t t' ∧ Returned A p S N vals s.mem t' := by
  obtain ⟨t', tg, hg, hpc, hmem, _, hlen, hargs, _⟩ := ret_seq hc hv hm hf hvals
  refine ⟨t', tg.to_reflTransGen, hg, by rw [hpc, hs]; rfl, hlen, hargs, by rw [hmem]; exact hm.mem,
    hm.size⟩

theorem ret_case {s : Machine.Lir.State P} {t : MState} {locs : List (Loc P)} {vals : List Word}
    {a : Activation P} {rest : List (Activation P)} {f : Machine.Lir.FuncId}
    {args results : List (Loc P)} {fr : Frame P}
    (hm : Match A p S N s t) (hf : p.fetch s.point = some (.term (.ret locs)))
    (hvals : s.frame.readAll locs = some vals) (hs : s.stack = a :: rest)
    (ha : p.fetch a.point = some (.instr (.call f args results)))
    (hw : a.frame.writeAll results vals = some fr) :
    ∃ t', TransGen TStep t t' ∧ Match A p S N ⟨a.point.next, fr, rest, s.mem⟩ t' := by
  obtain ⟨t₁, tg₁, hg₁, hpc₁, hmem₁, hsp₁, hlen, hargs₁, hother₁⟩ := ret_seq hc hv hm hf hvals
  have hsm := check_frame hc
  have hF := frameSize_ge N
  have hra := raOff_lt N
  have hci := check_instr hc ha
  simp only [checkInstr] at hci
  have hcall : args.length ≤ 8 ∧ results.length ≤ 8 ∧ locsBelow N results = true := by
    split at hci
    · cases hci
    · split at hci
      · cases hci
      · split at hci
        · cases hci
        · rename_i h1 h2 h3; simp at h1 h2 h3; exact ⟨by omega, by omega, h3.2⟩
  -- depths
  have hdepth := hm.depth
  rw [hs] at hdepth hsp₁
  simp only [List.length_cons] at hdepth hsp₁
  have hd2 : (rest.length + 2) * frameSize N ≤ S.stackHi := by
    have : (rest.length + 1 + 1) * frameSize N = (rest.length + 2) * frameSize N := rfl
    omega
  have hsp₁' : t₁.core.read sp = BitVec.ofNat 64 (spAt S N rest.length) := by
    rw [hsp₁, ← spAt_succ S N rest.length hd2]
  have hdepth' : S.stackLo + (rest.length + 1) * frameSize N ≤ S.stackHi := by
    have : (rest.length + 1) * frameSize N ≤ (rest.length + 1 + 1) * frameSize N :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hfr := spAt_frame S N hv hsm hdepth'
  have hstk := hm.stack
  rw [hs] at hstk
  obtain ⟨⟨hsave, hslots, hraw⟩, hrest⟩ := hstk
  -- the caller's code after its JAL
  obtain ⟨R, hcode⟩ := code_at_instr A.reg N p ha
  simp only [emitInstr, List.append_assoc] at hcode
  have hcode' := drop_split (a := saveAll ++ loadLocs A.reg args ++
    [jalI ra (pointIdx p a.point + 14 + args.length) (funcStart p f)])
    (b := restoreAll ++ storeLocs A.reg results ++ R) (by rw [hcode]; simp)
  have hidx : pointIdx p a.point + (saveAll ++ loadLocs A.reg args ++
      [jalI ra (pointIdx p a.point + 14 + args.length) (funcStart p f)]).length =
      retIdx p a.point := by
    simp [retIdx, ha]; omega
  rw [hidx] at hcode'
  have hpc₁' : t₁.core.pc = addrOf S.codeBase (retIdx p a.point) := by rw [hpc₁, hs]; rfl
  -- restore the caller's registers
  obtain ⟨t₂, h₂, mem₂, oth₂, val₂⟩ := restoreAll_spec hv hfr t₁ hg₁.regions hg₁.backed hsp₁'
  have hregs₂ : RegsAt A a.frame t₂.core := by
    intro r x hx
    exact val₂ (A.idx r) x (by rw [hmem₁]; exact hsave r x hx)
  -- write the results into the caller's frame
  have hwl := writeAll_length hw
  have hargs₂ : ∀ k (h : k < vals.length), t₂.core.read (argRegN (0 + k)) = vals[k] := by
    intro k hk
    have hk8 : k < 8 := by omega
    rw [Nat.zero_add, oth₂ _ (fun i e => argRegN_ne_alloc hk8 i e)]
    exact hargs₁ k hk
  have hsp₂ : t₂.core.read sp = BitVec.ofNat 64 (spAt S N rest.length) := by
    rw [oth₂ sp (fun i e => allocReg_ne_sp i e.symm)]; exact hsp₁'
  obtain ⟨t₃, h₃, regs₃, slots₃, wi₃, oth₃⟩ := storeLocsFrom_spec A hv hfr results 0 vals a.frame fr
    t₂ hw hcall.2.2 (by omega) hargs₂ hregs₂ (by rw [mem₂, hmem₁]; exact hslots) hsp₂
    (by rw [mem₂]; exact hg₁.regions)
  have hrun : runSeq (restoreAll ++ storeLocs A.reg results) t₁ = some t₃ := by
    rw [runSeq_append, h₂, Option.bind_some, storeLocs, h₃]
  obtain ⟨tg₂, hg₃, hpc₃⟩ := chunk_trans hv (by simp [restoreAll]) hg₁ hpc₁' hcode' hrun
  have hnext := pointIdx_next p ha
  have hret : retIdx p a.point = pointIdx p a.point + 15 + args.length := by simp [retIdx, ha]
  have hslot0 : ∀ k < N, slotOff 0 ≤ slotOff k := fun k _ => by unfold slotOff; omega
  -- the frame layout of the caller
  have hB' : spAt S N rest.length + frameSize N = S.stackHi - rest.length * frameSize N := by
    unfold spAt
    have e : (rest.length + 1) * frameSize N = rest.length * frameSize N + frameSize N :=
      Nat.succ_mul _ _
    rw [e] at hdepth' ⊢
    generalize rest.length * frameSize N = Y at *
    omega
  have hlo := hfr.lo
  have hsm' := hv.stack_mem
  have hread : ∀ r, r ≠ sp → r ≠ ra → (∀ k < 8, r ≠ argRegN k) → (∀ i, r ≠ allocReg i) →
      t₃.core.read r = t.core.read r := by
    intro r h1 h2 h3 h4
    rw [oth₃ r (fun q e => h4 _ e), oth₂ r h4, hother₁ r h1 h2 h3]
  have wi₃' : WritesIn t.memory t₃.memory (spAt S N rest.length + slotOff 0)
      (spAt S N rest.length + raOff N) := by
    rw [← hmem₁, ← mem₂]; exact wi₃
  have hbound : spAt S N rest.length + raOff N ≤ S.stackHi - rest.length * frameSize N := by
    omega
  have hpcn : retIdx p a.point + (restoreAll ++ storeLocs A.reg results).length =
      pointIdx p a.point.next := by
    rw [hnext, hret, List.length_append, restoreAll_length, storeLocs_length]
    simp only [instrSize]
    omega
  refine ⟨t₃, tg₁.trans tg₂, {
    good := hg₃
    pc := by rw [hpc₃, hpcn]
    depth := hdepth'
    sp := by
      rw [oth₃ sp (fun q e => A.reg_ne_sp q e.symm)]; exact hsp₂
    base := by
      rw [hread s11 (by decide) (by decide) (fun k hk => (argRegN_ne_s11 hk).symm)
        (fun i => (allocReg_ne_s11 i).symm)]
      exact hm.base
    limit := by
      rw [hread s10 (by decide) (by decide) (fun k hk => (argRegN_ne_s10 hk).symm)
        (fun i => (allocReg_ne_s10 i).symm)]
      exact hm.limit
    regs := regs₃
    slots := slots₃
    ra := wi₃.wordAt (.inr le_rfl) (by rw [mem₂, hmem₁]; exact hraw)
    stack := StackOK.of_writesIn A p S N wi₃' (fun b h1 h2 => .inr (by dsimp only at h1; omega))
      hdepth' hrest
    mem := hm.mem.of_writesIn S wi₃' hm.size (by
      intro a' ha'; simp only [Space.InMem] at ha'; unfold slotOff raOff at *
      have := hfr.hi
      omega)
    size := hm.size }⟩

/-! ## Calls -/

omit hc hv in
theorem geu_eval (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Ext.BranchOp.eval .geu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  simp only [Ext.BranchOp.eval, ult_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : b ≤ a
  · simp [h]
  · simp [h]; omega

omit hc hv in
theorem enter_some {f : Machine.Lir.FuncId} {vals : List Word} {pt : Point} {fr : Frame P}
    (he : p.enter f vals = some (pt, fr)) :
    ∃ fn, p.func? f = some fn ∧ Frame.empty.writeAll fn.params vals = some fr ∧
      pt = ⟨f, fn.entry, 0⟩ := by
  unfold Prog.enter at he
  cases hfn : p.func? f with
  | none => simp [hfn] at he
  | some fn =>
    simp only [hfn, Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨fr', hw, rfl, rfl⟩ := he
    exact ⟨fn, rfl, hw, rfl⟩

omit [DecidableEq P] in
/-- The prologue of `f` entered with `d` frames on the stack: either the new
frame is established (parameters stored, return address saved) at
`spAt S N d`, or the machine reaches the overflow stub. -/
theorem prologue_run [DecidableEq P] {f : Machine.Lir.FuncId} {fn : Func P} {vals : List Word}
    {fr : Frame P} (hfn : p.func? f = some fn) (hwp : Frame.empty.writeAll fn.params vals = some fr)
    {t : MState} (hg : Good S (emitProg A.reg N p) t)
    (hpc : t.core.pc = addrOf S.codeBase (funcStart p f)) {d : Nat}
    (hd : S.stackLo + d * frameSize N ≤ S.stackHi)
    (hsp : t.core.read sp = BitVec.ofNat 64 (S.stackHi - d * frameSize N))
    (hlim : t.core.read s10 = BitVec.ofNat 64 S.stackLo)
    (hargs : ∀ k (h : k < vals.length), t.core.read (argRegN k) = vals[k]) :
    ∃ t', TransGen TStep t t' ∧ Good S (emitProg A.reg N p) t' ∧
      ((Overflowed A p S N t' ∧ S.stackHi < S.stackLo + (d + 1) * frameSize N) ∨
        (t'.core.pc = addrOf S.codeBase (pointIdx p ⟨f, fn.entry, 0⟩) ∧
          S.stackLo + (d + 1) * frameSize N ≤ S.stackHi ∧
          t'.core.read sp = BitVec.ofNat 64 (spAt S N d) ∧
          RegsAt A fr t'.core ∧ SlotsAt N t'.memory (spAt S N d) fr ∧
          WordAt t'.memory (spAt S N d + raOff N) (t.core.read ra) ∧
          WritesIn t.memory t'.memory (spAt S N d) (spAt S N d + frameSize N) ∧
          (∀ r, (∀ q, r ≠ A.reg q) → r ≠ sp → t'.core.read r = t.core.read r))) := by
  have hsm := check_frame hc
  have hF := frameSize_ge N
  have hra := raOff_lt N
  have hch := check_head hc hfn
  simp only [checkFuncHead] at hch
  have hhead : fn.params.length ≤ 8 ∧ locsBelow N fn.params = true ∧
      jalFits (funcStart p f + 2) overflowIdx = true ∧
      jalFits (funcStart p f + 4 + fn.params.length) (blockStart p f fn.entry) = true := by
    split at hch
    · cases hch
    · split at hch
      · cases hch
      · split at hch
        · cases hch
        · rename_i h1 h2 h3; simp at h1 h2 h3; exact ⟨by omega, h2, h3.1, h3.2⟩
  have hpl := writeAll_length hwp
  obtain ⟨R', hpro⟩ := code_at_prologue A.reg N p hfn
  simp only [prologue, List.append_assoc, List.cons_append] at hpro
  have hfl := hv.stack_floor
  have hsend := hv.stack_end
  set B := S.stackHi - d * frameSize N
  have hBF : frameSize N ≤ B := by omega
  have hBlt : B < 2 ^ 64 := by omega
  set c₄ : Compute := .base (.imm .add sp sp (BitVec.ofInt 12 (-(frameSize N : Int))))
  obtain ⟨tg₄, hg₄, hpc₄⟩ := chunk_trans hv (seq := [.compute c₄]) (by simp) hg hpc
    (by rw [hpro]; rfl) (runSeq_compute_cons c₄ [] t)
  set t₄ : MState := ⟨c₄.step t.core, t.memory⟩
  have sp₄ : t₄.core.read sp = BitVec.ofNat 64 (B - frameSize N) := by
    simp only [t₄, c₄, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, ne_eq, sp_ne_zero,
      not_false_eq_true, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.ImmOp.eval, hsp]
    exact addi_neg _ _ hsm hBF
  have fix₄ : ∀ r, r ≠ sp → t₄.core.read r = t.core.read r := by
    intro r hr
    simp only [t₄, c₄, Ext.Compute.step_base, read_base_step, RiscV.Instr.dest, hr, false_and,
      ↓reduceIte]
  have s10₄ : t₄.core.read s10 = BitVec.ofNat 64 S.stackLo := by
    rw [fix₄ s10 (by decide)]; exact hlim
  have hcb : (emitProg A.reg N p)[funcStart p f + 1]? = some (.branch .geu sp s10 4#12) :=
    getElem?_of_drop (drop_split (a := [.compute c₄]) (by rw [hpro]; rfl))
  have heval : Ext.BranchOp.eval .geu (t₄.core.read sp) (t₄.core.read s10) =
      decide (S.stackLo ≤ B - frameSize N) := by
    rw [sp₄, s10₄]; exact geu_eval _ _ (by omega) (by omega)
  have hpc₄' : t₄.core.pc = addrOf S.codeBase (funcStart p f + 1) := by rw [hpc₄]; rfl
  by_cases hfit : S.stackLo ≤ B - frameSize N
  · have htaken : Ext.BranchOp.eval .geu (t₄.core.read sp) (t₄.core.read s10) = true := by
      rw [heval]; simp [hfit]
    have ht : t₄.core.pc + Ext.branchOffset 4#12 = addrOf S.codeBase (funcStart p f + 3) := by
      rw [hpc₄', branch_eight]
      simp only [addrOf]
      rw [← BitVec.ofNat_add]
      congr 1
    obtain ⟨st₅, hg₅⟩ := tstep_at hv hg₄ hpc₄' hcb (Ext.Instr.exec_branch_taken t₄ htaken
      (by rw [ht]; exact addrOf_align hv.code_align _))
    set t₅ : MState := ⟨{ t₄.core with pc := t₄.core.pc + Ext.branchOffset 4#12 }, t₄.memory⟩
    have hB' : spAt S N d = B - frameSize N := by
      unfold spAt
      rw [Nat.succ_mul]
      omega
    have hdepth' : S.stackLo + (d + 1) * frameSize N ≤ S.stackHi := by
      rw [Nat.succ_mul]; omega
    have hfr' := spAt_frame S N hv hsm hdepth'
    have sp₅ : t₅.core.read sp = BitVec.ofNat 64 (spAt S N d) := by
      simp only [t₅, State.read_setPc]; rw [sp₄, hB']
    obtain ⟨mem₆, hrun₆, hw₆, wi₆⟩ := frame_sd hv hfr' (r := ra) (off := raOff N)
      (rest := storeLocs A.reg fn.params) (m := t₅) (by unfold raOff; omega) hra
      (by simp only [t₅]; exact hg₄.regions) sp₅
    set t₆ : MState := ⟨{ t₅.core with pc := t₅.core.pc + 4 }, mem₆⟩
    have hsl₆ : SlotsAt N t₆.memory (spAt S N d) (Frame.empty : Frame P) :=
      fun k x _ hx => by simp [Frame.empty] at hx
    have hrg₆ : RegsAt A (Frame.empty : Frame P) t₆.core := fun r x hx => by
      simp [Frame.empty] at hx
    have args₆ : ∀ k (h : k < vals.length), t₆.core.read (argRegN (0 + k)) = vals[k] := by
      intro k hk
      simp only [t₆, t₅, State.read_setPc, Nat.zero_add]
      rw [fix₄ _ (argRegN_ne_sp (by omega))]
      exact hargs k hk
    obtain ⟨t₇, h₇, regs₇, slots₇, wi₇, oth₇⟩ := storeLocsFrom_spec A hv hfr' fn.params 0 vals
      Frame.empty fr t₆ hwp hhead.2.1 (by omega) args₆ hrg₆ hsl₆
      (by simp only [t₆, State.read_setPc]; exact sp₅)
      (by simp only [t₆]; exact wi₆.1.trans hg₄.regions)
    have hrun₇ : runSeq (sdI sp ra (raOff N) :: storeLocs A.reg fn.params) t₅ = some t₇ := by
      rw [hrun₆]; exact h₇
    have hd3 : (emitProg A.reg N p).drop (funcStart p f + 3) = sdI sp ra (raOff N) ::
        (storeLocs A.reg fn.params ++
          (jalI 0#5 (funcStart p f + 4 + fn.params.length) (blockStart p f fn.entry) :: R')) :=
      drop_split (a := [.compute c₄, .branch .geu sp s10 4#12,
          jalI 0#5 (funcStart p f + 2) overflowIdx]) (by rw [hpro]; rfl)
    obtain ⟨tg₇, hg₇, hpc₇⟩ := chunk_trans hv (by simp) hg₅ ht (by rw [hd3]; rfl) hrun₇
    have hce : (emitProg A.reg N p)[funcStart p f + 4 + fn.params.length]? =
        some (jalI 0#5 (funcStart p f + 4 + fn.params.length) (blockStart p f fn.entry)) := by
      have h := getElem?_of_drop (drop_split (a := [.compute c₄, .branch .geu sp s10 4#12,
          jalI 0#5 (funcStart p f + 2) overflowIdx, sdI sp ra (raOff N)] ++ storeLocs A.reg fn.params)
        (b := jalI 0#5 (funcStart p f + 4 + fn.params.length) (blockStart p f fn.entry) :: R')
        (by rw [hpro]; rfl))
      simp only [List.length_append, List.length_cons, List.length_nil, storeLocs_length] at h
      rwa [show funcStart p f + (0 + 1 + 1 + 1 + 1 + fn.params.length) =
        funcStart p f + 4 + fn.params.length by omega] at h
    have hpc₇' : t₇.core.pc = addrOf S.codeBase (funcStart p f + 4 + fn.params.length) := by
      rw [hpc₇]; congr 1; simp; omega
    obtain ⟨st₈, hg₈⟩ := jal_step hv hg₇ hpc₇' hce hhead.2.2.2
    set t₈ : MState := ⟨{ t₇.core.write 0#5 (t₇.core.pc + 4) with
      pc := addrOf S.codeBase (blockStart p f fn.entry) }, t₇.memory⟩
    have r₈ : ∀ r, t₈.core.read r = t₇.core.read r := by
      intro r
      show ({ t₇.core.write 0#5 (t₇.core.pc + 4) with
        pc := addrOf S.codeBase (blockStart p f fn.entry) } : State).read r = _
      rw [State.read_setPc, State.write_zero]
    have hsl0 : slotOff 0 = 112 := rfl
    have hro : 112 ≤ raOff N := by unfold raOff; omega
    have wiT : WritesIn t.memory t₇.memory (spAt S N d) (spAt S N d + frameSize N) :=
      (wi₆.mono (by omega) (by omega)).trans (wi₇.mono (by omega) (by omega))
    refine ⟨t₈, ((tg₄.tail st₅).trans tg₇).tail st₈, hg₈, .inr ⟨?_, hdepth', ?_, ?_, slots₇,
      ?_, wiT, ?_⟩⟩
    · rw [pointIdx_zero]
    · rw [r₈, oth₇ sp fun q e => A.reg_ne_sp q e.symm]
      simp only [t₆, State.read_setPc]; exact sp₅
    · exact regs₇.congr A fun q => r₈ _
    · apply wi₇.wordAt (.inr le_rfl)
      have : t₅.core.read ra = t.core.read ra := by
        simp only [t₅, State.read_setPc]; exact fix₄ ra ra_ne_sp
      rw [this] at hw₆; exact hw₆
    · intro r h1 h2
      rw [r₈, oth₇ r h1]
      simp only [t₆, t₅, State.read_setPc]
      exact fix₄ r h2
  · have hnot : Ext.BranchOp.eval .geu (t₄.core.read sp) (t₄.core.read s10) = false := by
      rw [heval]; simp [hfit]
    obtain ⟨st₅, hg₅⟩ := tstep_at hv hg₄ hpc₄' hcb (Ext.Instr.exec_branch_not_taken t₄ hnot)
    have hco : (emitProg A.reg N p)[funcStart p f + 2]? =
        some (jalI 0#5 (funcStart p f + 2) overflowIdx) :=
      getElem?_of_drop (drop_split (a := [.compute c₄, .branch .geu sp s10 4#12]) (by rw [hpro]; rfl))
    obtain ⟨st₆, hg₆⟩ := jal_step hv hg₅ (by simp only; rw [hpc₄', ← addrOf_succ]) hco hhead.2.2.1
    refine ⟨_, (tg₄.tail st₅).tail st₆, hg₆, .inl ⟨⟨hg₆, rfl⟩, ?_⟩⟩
    rw [Nat.succ_mul]; omega

theorem call_case {s : Machine.Lir.State P} {t : MState} {f : Machine.Lir.FuncId}
    {args results : List (Loc P)} {vals : List Word} {pt : Point} {fr : Frame P}
    (hm : Match A p S N s t) (hf : p.fetch s.point = some (.instr (.call f args results)))
    (hvals : s.frame.readAll args = some vals) (he : p.enter f vals = some (pt, fr)) :
    ∃ t', TransGen TStep t t' ∧
      (Match A p S N ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩ t' ∨
        (Overflowed A p S N t' ∧ S.stackHi < S.stackLo + (s.stack.length + 1 + 1) * frameSize N)) := by
  obtain ⟨fn, hfn, hwp, rfl⟩ := enter_some he
  have hsm := check_frame hc
  have hF := frameSize_ge N
  have hra := raOff_lt N
  have hfr := hm.frameAt hv hsm
  -- checks
  have hci := check_instr hc hf
  simp only [checkInstr] at hci
  have hcall : args.length ≤ 8 ∧ locsBelow N args = true ∧
      jalFits (pointIdx p s.point + 14 + args.length) (funcStart p f) = true := by
    split at hci
    · cases hci
    · split at hci
      · cases hci
      · split at hci
        · cases hci
        · split at hci
          · cases hci
          · rename_i h1 h2 h3 h4; simp at h1 h2 h3 h4; exact ⟨by omega, h3.1, h4⟩
  have hvl := readAll_length hvals
  -- the caller's code
  obtain ⟨R, hcode⟩ := code_at_instr A.reg N p hf
  simp only [emitInstr, List.append_assoc] at hcode
  -- save the allocatable registers
  obtain ⟨t₁, h₁, regs₁, wi₁, saved₁⟩ := saveAll_spec hv hfr t hm.good.regions hm.sp
  have hslots₁ : SlotsAt N t₁.memory (spAt S N s.stack.length) s.frame :=
    hm.slots.of_writesIn wi₁ fun k hk => .inr (by unfold slotOff; omega)
  -- arguments into a0 …
  obtain ⟨t₂, h₂, mem₂, vals₂, oth₂⟩ := loadLocsFrom_spec A hv hfr args 0 vals t₁ hvals hcall.2.1
    (by omega) (hm.regs.congr A fun r => regs₁ _) hslots₁ (by rw [regs₁]; exact hm.sp)
  have hrun₂ : runSeq (saveAll ++ loadLocs A.reg args) t = some t₂ := by
    rw [runSeq_append, h₁, Option.bind_some, loadLocs, h₂]
  obtain ⟨tg₂, hg₂, hpc₂⟩ := chunk_trans hv (by simp [saveAll]) hm.good hm.pc
    (by rw [hcode, List.append_assoc]) hrun₂
  have hjidx : pointIdx p s.point + (saveAll ++ loadLocs A.reg args).length =
      pointIdx p s.point + 14 + args.length := by
    rw [List.length_append, saveAll_length, loadLocs_length]; omega
  rw [hjidx] at hpc₂
  -- jal ra, callee
  have hcj : (emitProg A.reg N p)[pointIdx p s.point + 14 + args.length]? =
      some (jalI ra (pointIdx p s.point + 14 + args.length) (funcStart p f)) := by
    have h := getElem?_of_drop (drop_split (a := saveAll ++ loadLocs A.reg args)
      (b := jalI ra (pointIdx p s.point + 14 + args.length) (funcStart p f) ::
        (restoreAll ++ (storeLocs A.reg results ++ R)))
      (by rw [hcode, List.append_assoc]; rfl))
    rwa [hjidx] at h
  obtain ⟨st₃, hg₃⟩ := jal_step hv hg₂ hpc₂ hcj hcall.2.2
  set t₃ : MState := ⟨{ t₂.core.write ra (t₂.core.pc + 4) with pc := addrOf S.codeBase (funcStart p f) },
    t₂.memory⟩
  have hret : t₂.core.pc + 4 = addrOf S.codeBase (retIdx p s.point) := by
    rw [hpc₂, ← addrOf_succ]; simp only [retIdx, hf]; congr 1; omega
  have read₃ : ∀ r, r ≠ ra → t₃.core.read r = t₂.core.read r := fun r hr => by
    simp only [t₃, State.read_setPc]; exact State.read_write_other _ _ _ _ hr
  have ra₃ : t₃.core.read ra = addrOf S.codeBase (retIdx p s.point) := by
    simp only [t₃, State.read_setPc]; rw [State.read_write_same _ _ _ ra_ne_zero, hret]
  have sp₃ : t₃.core.read sp = BitVec.ofNat 64 (spAt S N s.stack.length) := by
    rw [read₃ sp sp_ne_ra, oth₂ sp fun k hk => (argRegN_ne_sp (by omega)).symm, regs₁]; exact hm.sp
  have fix₃ : ∀ r, r ≠ ra → (∀ k < 8, r ≠ argRegN k) → t₃.core.read r = t.core.read r := by
    intro r h1 h2
    rw [read₃ r h1, oth₂ r fun k hk => by simpa using h2 k (by omega), regs₁]
  have args₃ : ∀ k (h : k < vals.length), t₃.core.read (argRegN (0 + k)) = vals[k] := by
    intro k hk
    rw [Nat.zero_add, read₃ _ (argRegN_ne_ra (by omega))]
    simpa using vals₂ k hk
  -- the callee prologue
  have hdl : S.stackLo + (s.stack.length + 1) * frameSize N ≤ S.stackHi := hm.depth
  obtain ⟨t', tg', hg', hout⟩ := prologue_run hc hv hfn hwp hg₃ rfl (d := s.stack.length + 1) hdl
    sp₃ (by rw [fix₃ s10 (by decide) fun k hk => (argRegN_ne_s10 hk).symm]; exact hm.limit)
    (fun k hk => by simpa using args₃ k hk)
  have tg : TransGen TStep t t' := (tg₂.trans (.single st₃)).trans tg'
  rcases hout with ho | ⟨hpc', hdepth', hsp', hregs', hslots', hra', wi', hfix'⟩
  · exact ⟨t', tg, .inr ho⟩
  have hsucc : spAt S N s.stack.length = spAt S N (s.stack.length + 1) + frameSize N := by
    apply spAt_succ
    have : (s.stack.length + 1 + 1) * frameSize N = (s.stack.length + 2) * frameSize N := rfl
    omega
  have hro : 112 ≤ raOff N := by unfold raOff; omega
  have hsl0 : ∀ k < N, 112 ≤ slotOff k := fun k _ => by unfold slotOff; omega
  have e₃ : t₃.memory = t₁.memory := mem₂
  have wiA : WritesIn t₁.memory t'.memory (spAt S N (s.stack.length + 1)) (spAt S N s.stack.length) := by
    rw [← e₃, hsucc]; exact wi'
  have wiT : WritesIn t.memory t'.memory (spAt S N (s.stack.length + 1))
      (spAt S N s.stack.length + 112) :=
    (wi₁.mono (by omega) le_rfl).trans (wiA.mono le_rfl (by omega))
  have hsp : spAt S N s.stack.length + frameSize N = S.stackHi - s.stack.length * frameSize N := by
    have e : (s.stack.length + 1) * frameSize N = s.stack.length * frameSize N + frameSize N :=
      Nat.succ_mul _ _
    have := hm.depth
    unfold spAt
    rw [e] at this ⊢
    generalize s.stack.length * frameSize N = Y at *
    omega
  refine ⟨t', tg, .inl {
    good := hg'
    pc := hpc'
    depth := by simpa using hdepth'
    sp := by simpa using hsp'
    base := by
      rw [hfix' s11 (fun q e => A.reg_ne_s11 q e.symm) (by decide),
        fix₃ s11 (by decide) fun k hk => (argRegN_ne_s11 hk).symm]
      exact hm.base
    limit := by
      rw [hfix' s10 (fun q e => A.reg_ne_s10 q e.symm) (by decide),
        fix₃ s10 (by decide) fun k hk => (argRegN_ne_s10 hk).symm]
      exact hm.limit
    regs := hregs'
    slots := by simpa using hslots'
    ra := by simp only [List.length_cons]; rw [ra₃] at hra'; exact hra'
    stack := by
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro r x hx
        apply wiA.wordAt (.inr (by omega))
        have := saved₁ (A.idx r)
        rw [show allocReg (A.idx r) = A.reg r from rfl, hm.regs r x hx] at this
        exact this
      · exact hm.slots.of_writesIn wiT fun k hk => .inr (by have := hsl0 k hk; omega)
      · exact wiT.wordAt (.inr (by omega)) hm.ra
      · exact StackOK.of_writesIn A p S N wiT (fun b h1 h2 => .inr (by omega)) hm.depth hm.stack
    mem := hm.mem.of_writesIn S wiT hm.size fun a ha => by
      have := hv.stack_mem; have := hfr.hi
      have := (spAt_frame S N hv hsm hdepth').lo
      simp only [Space.InMem] at ha; omega
    size := hm.size }⟩

end Cases

/-! ## The simulation -/

/-- Machine steps, extended with self-loops at the overflow stub. -/
def XStep (m m' : MState) : Prop := TStep m m' ∨ (Overflowed A p S N m ∧ m' = m)

omit [DecidableEq P] in
theorem TransGen.toX {a b : MState} (h : TransGen TStep a b) : TransGen (XStep A p S N) a b := by
  induction h with
  | single h => exact .single (.inl h)
  | tail _ h ih => exact .tail ih (.inl h)

omit [DecidableEq P] in
theorem ReflTransGen.toX {a b : MState} (h : ReflTransGen TStep a b) :
    ReflTransGen (XStep A p S N) a b := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.inl h)

omit [DecidableEq P] in
/-- The self-loops are identities, so an extended path is a machine path. -/
theorem ReflTransGen.ofX {a b : MState} (h : ReflTransGen (XStep A p S N) a b) :
    ReflTransGen TStep a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hs | ⟨_, rfl⟩
    · exact ih.tail hs
    · exact ih

omit [DecidableEq P] in
/-- An infinite extended path is an infinite machine path, unless the machine
reaches the overflow stub. -/
theorem InfiniteTrace.ofX {a : MState} (h : InfiniteTrace (XStep A p S N) a) :
    InfiniteTrace TStep a ∨ ∃ b, ReflTransGen TStep a b ∧ Overflowed A p S N b := by
  by_cases hov : ∃ b, ReflTransGen TStep a b ∧ Overflowed A p S N b
  · exact .inr hov
  · left
    refine Silmaril.InfiniteTrace.coinduct
      (fun x => ReflTransGen TStep a x ∧ Silmaril.InfiniteTrace (XStep A p S N) x) ?_ ⟨.refl, h⟩
    intro x hxi
    obtain ⟨hx, hi⟩ := hxi
    obtain ⟨y, hxy, hy⟩ := hi.unfold
    rcases hxy with hxy | ⟨ho, _⟩
    · exact ⟨y, hxy, hx.tail hxy, hy⟩
    · exact absurd ⟨x, hx, ho⟩ hov

variable {A p S N}

omit [DecidableEq P] in
theorem progress_of {s s' : Machine.Lir.State P} {t : MState}
    (h : ∃ t', TransGen TStep t t' ∧ Match A p S N s' t') :
    Machine.Lir.Progress (XStep A p S N) (fun s m => Match A p S N s m ∨ Overflowed A p S N m) (fun _ => 0)
      s t s' := by
  obtain ⟨t', tg, hm⟩ := h
  exact ⟨t', .inl hm, .inl (TransGen.toX A p S N tg)⟩

omit [DecidableEq P] in
theorem progress_overflow {s s' : Machine.Lir.State P} {t : MState} (h : Overflowed A p S N t) :
    Machine.Lir.Progress (XStep A p S N) (fun s m => Match A p S N s m ∨ Overflowed A p S N m) (fun _ => 0)
      s t s' :=
  ⟨t, .inr h, .inl (.single (.inr ⟨h, rfl⟩))⟩

variable (A p S N)

/-- **The backend as a per-transition simulation** of the Lir program by the
machine running its compiled code, with the overflow stutter. -/
def simulation (hc : checkProg p N = none) (hv : S.Valid (emitProg A.reg N p).length) :
    Machine.Lir.CaseSimulation p (XStep A p S N) where
  Match s m := Match A p S N s m ∨ Overflowed A p S N m
  measure _ := 0
  Returned vs mem m := Returned A p S N vs mem m ∨ Overflowed A p S N m
  Trapped mem m := Trapped A p S N mem m ∨ Overflowed A p S N m
  op := by
    intro s t o fr m hm hf he
    rcases hm with hm | ho
    · exact progress_of (op_case hc hv hm hf he)
    · exact progress_overflow ho
  call := by
    intro s t f args results vals pt fr hm hf ha he
    rcases hm with hm | ho
    · obtain ⟨t', tg, hm' | ⟨ho', -⟩⟩ := call_case hc hv hm hf ha he
      · exact ⟨t', .inl hm', .inl (TransGen.toX A p S N tg)⟩
      · exact ⟨t', .inr ho', .inl (TransGen.toX A p S N tg)⟩
    · exact progress_overflow ho
  fop := by
    intro s t op d x y fr hm hf he
    have := check_instr hc hf
    simp [checkInstr] at this
  jump := by
    intro s t l hm hf
    rcases hm with hm | ho
    · exact progress_of (jump_case hc hv hm hf)
    · exact progress_overflow ho
  branch := by
    intro s t c l₁ l₂ x hm hf hx
    rcases hm with hm | ho
    · exact progress_of (branch_case hc hv hm hf hx)
    · exact progress_overflow ho
  ret := by
    intro s t locs vals a rest f args results fr hm hf hvals hs ha hw
    rcases hm with hm | ho
    · exact progress_of (ret_case hc hv hm hf hvals hs ha hw)
    · exact progress_overflow ho
  halt := by
    intro s t locs vals hm hf hvals hs
    rcases hm with hm | ho
    · obtain ⟨t', tg, hr⟩ := halt_case hc hv hm hf hvals hs
      exact ⟨t', ReflTransGen.toX A p S N tg, .inl hr⟩
    · exact ⟨t, .refl, .inr ho⟩
  trap := by
    intro s t hm hf
    rcases hm with hm | ho
    · obtain ⟨t', tg, hr⟩ := trap_case hc hv hm hf
      exact ⟨t', ReflTransGen.toX A p S N tg, .inl hr⟩
    · exact ⟨t, .refl, .inr ho⟩

/-! ## Runs of bounded call depth -/

/-- Every state reachable from `s` has at most `D` suspended activations. -/
def DepthBounded (p : Prog P) (s : Machine.Lir.State P) (D : Nat) : Prop :=
  ∀ s', Machine.Lir.Steps p s s' → s'.stack.length ≤ D

theorem DepthBounded.step {s s' : Machine.Lir.State P} {D : Nat} (h : DepthBounded p s D)
    (hs : Machine.Lir.Step p s s') : DepthBounded p s' D :=
  fun s'' h'' => h s'' (.head hs h'')

/-- When every reachable Lir state has at most `D` suspended activations and
the stack region holds `D + 1` frames, the prologue never branches to the
overflow stub, and the simulation needs no stutter. -/
def simulationBounded (hc : checkProg p N = none) (hv : S.Valid (emitProg A.reg N p).length)
    (D : Nat) (hD : S.stackLo + (D + 1) * frameSize N ≤ S.stackHi) :
    Machine.Lir.CaseSimulation p TStep where
  Match s m := Match A p S N s m ∧ DepthBounded p s D
  measure _ := 0
  Returned vs mem m := Returned A p S N vs mem m
  Trapped mem m := Trapped A p S N mem m
  op := by
    intro s t o fr m hm hf he
    obtain ⟨t', tg, hm'⟩ := op_case hc hv hm.1 hf he
    exact ⟨t', ⟨hm', hm.2.step p (Machine.Lir.Transition.op hf he).step_eq⟩, .inl tg⟩
  call := by
    intro s t f args results vals pt fr hm hf ha he
    have hst := (Machine.Lir.Transition.call hf ha he).step_eq
    obtain ⟨t', tg, hm' | ⟨_, hlt⟩⟩ := call_case hc hv hm.1 hf ha he
    · exact ⟨t', ⟨hm', hm.2.step p hst⟩, .inl tg⟩
    · have hd := hm.2 _ (.single hst)
      simp only [List.length_cons] at hd
      have : (s.stack.length + 1 + 1) * frameSize N ≤ (D + 1) * frameSize N :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  fop := by
    intro s t op d x y fr hm hf he
    have := check_instr hc hf
    simp [checkInstr] at this
  jump := by
    intro s t l hm hf
    obtain ⟨t', tg, hm'⟩ := jump_case hc hv hm.1 hf
    exact ⟨t', ⟨hm', hm.2.step p (Machine.Lir.Transition.jump hf).step_eq⟩, .inl tg⟩
  branch := by
    intro s t c l₁ l₂ x hm hf hx
    obtain ⟨t', tg, hm'⟩ := branch_case hc hv hm.1 hf hx
    exact ⟨t', ⟨hm', hm.2.step p (Machine.Lir.Transition.branch hf hx).step_eq⟩, .inl tg⟩
  ret := by
    intro s t locs vals a rest f args results fr hm hf hvals hs ha hw
    obtain ⟨t', tg, hm'⟩ := ret_case hc hv hm.1 hf hvals hs ha hw
    exact ⟨t', ⟨hm', hm.2.step p (Machine.Lir.Transition.ret hf hvals hs ha hw).step_eq⟩, .inl tg⟩
  halt := by
    intro s t locs vals hm hf hvals hs
    exact halt_case hc hv hm.1 hf hvals hs
  trap := by
    intro s t hm hf
    exact trap_case hc hv hm.1 hf

/-! ## Behaviours -/

section Behaviours

variable {A p S N} (hc : checkProg p N = none) (hv : S.Valid (emitProg A.reg N p).length)
include hc hv

/-- A Lir execution that returns is matched by a machine execution that
reaches the halt stub with the returned values in `a0 …` and the final linear
memory, or that reaches the stack-overflow stub. -/
theorem returns {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    {vs : List Word} {mem : Machine.Lir.Memory} (hb : Machine.Lir.Behaves p s (.returned vs mem)) :
    ∃ t', ReflTransGen TStep t t' ∧ (Returned A p S N vs mem t' ∨ Overflowed A p S N t') := by
  obtain ⟨t', h, r⟩ := (simulation A p S N hc hv).toForward.returns (.inl hm) hb
  exact ⟨t', ReflTransGen.ofX A p S N h, r⟩

theorem traps {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    {mem : Machine.Lir.Memory} (hb : Machine.Lir.Behaves p s (.trapped mem)) :
    ∃ t', ReflTransGen TStep t t' ∧ (Trapped A p S N mem t' ∨ Overflowed A p S N t') := by
  obtain ⟨t', h, r⟩ := (simulation A p S N hc hv).toForward.traps (.inl hm) hb
  exact ⟨t', ReflTransGen.ofX A p S N h, r⟩

theorem diverges {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    (hb : Machine.Lir.Diverges p s) :
    InfiniteTrace TStep t ∨ ∃ t', ReflTransGen TStep t t' ∧ Overflowed A p S N t' :=
  InfiniteTrace.ofX A p S N ((simulation A p S N hc hv).toForward.diverges (.inl hm) hb)

variable {D : Nat} (hD : S.stackLo + (D + 1) * frameSize N ≤ S.stackHi)
include hD

/-- With bounded call depth, a returning Lir execution is matched exactly. -/
theorem returns_bounded {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    (hb : DepthBounded p s D) {vs : List Word} {mem : Machine.Lir.Memory}
    (h : Machine.Lir.Behaves p s (.returned vs mem)) :
    ∃ t', ReflTransGen TStep t t' ∧ Returned A p S N vs mem t' :=
  (simulationBounded A p S N hc hv D hD).toForward.returns ⟨hm, hb⟩ h

theorem traps_bounded {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    (hb : DepthBounded p s D) {mem : Machine.Lir.Memory}
    (h : Machine.Lir.Behaves p s (.trapped mem)) :
    ∃ t', ReflTransGen TStep t t' ∧ Trapped A p S N mem t' :=
  (simulationBounded A p S N hc hv D hD).toForward.traps ⟨hm, hb⟩ h

theorem diverges_bounded {s : Machine.Lir.State P} {t : MState} (hm : Match A p S N s t)
    (hb : DepthBounded p s D) (h : Machine.Lir.Diverges p s) : InfiniteTrace TStep t :=
  (simulationBounded A p S N hc hv D hD).toForward.diverges ⟨hm, hb⟩ h

end Behaviours

end Silmaril.RiscV.Backend
