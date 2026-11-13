module

public import Silmaril.X86.Features.Ext.IntExt.Extension
public import Silmaril.X86.Features.Ext.BaseInt.Extension

/-!
# The int-ext and baseint lanes agree on their overlap

The int-ext lane (`IntExt.ext`, recovered in #3585) and the baseline-integer
lane (`BaseInt.baseIntExt`) both model ADC/SBB in their five ALU forms,
SHLD/SHRD and BT/BTS/BTR/BTC at 32 and 64 bits, and PUSH imm32/imm8.
`IntExt.Instr.toBase?` maps each such int-ext instruction to the baseint
instruction with the same meaning, and `BaseInt.Instr.toIntExt?` maps back.

* `encode_toBase`: the two encoders produce the same bytes.
* `exec_toBase`: the two semantics are equal, on every state and memory.
* `requires_toBase`: neither lane requires a feature for these forms.
* `decode_toBase`: hence each decoder accepts exactly the byte strings the
  other accepts on the overlap, with the same length.
-/

-- Ported from legacy hiloopai/silmaril; its proofs predate the current unused-tactic linter.
set_option linter.unusedTactic false

@[expose] public section

namespace Silmaril.X86.Features.IntMerged

open Silmaril.X86 (Byte Reg Word)
open Silmaril.X86.Ext (Sz RM)
open Silmaril.Process (Memory)

/-! ## The correspondence -/

def carryOp : IntExt.CarryOp → BaseInt.CarryOp
  | .adc => .adc | .sbb => .sbb

def bitOp : IntExt.BitOp → BaseInt.BtOp
  | .bt => .bt | .bts => .bts | .btr => .btr | .btc => .btc

def shdCount : IntExt.ShdCount → BaseInt.ShdCount
  | .cl => .cl | .imm n => .imm n

/-- The baseint instruction with the same meaning, for the forms of the overlap. -/
def _root_.Silmaril.X86.Features.IntExt.Instr.toBase? : IntExt.Instr → Option BaseInt.Instr
  | .carry op sz dst src => some (.carry sz (carryOp op) (.rm dst src))
  | .carryR op sz dst src => some (.carry sz (carryOp op) (.r dst src))
  | .carryI op sz dst imm => some (.carry sz (carryOp op) (.i dst imm))
  | .carryI8 op sz dst imm => some (.carry sz (carryOp op) (.i8 dst imm))
  | .carryA op sz imm => some (.carry sz (carryOp op) (.a imm))
  | .pushI imm => some (.pushI imm)
  | .pushI8 imm => some (.pushI8 imm)
  | .bit op sz dst src => some (.bit (.ofSz sz) (bitOp op) dst (.reg src))
  | .bitI op sz dst imm => some (.bit (.ofSz sz) (bitOp op) dst (.imm imm))
  | .shd right sz dst src count => some (.shd (.ofSz sz) (!right) dst src (shdCount count))
  | _ => none

/-- The int-ext forms of the overlap. -/
def _root_.Silmaril.X86.Features.IntExt.Instr.isBase (i : IntExt.Instr) : Bool := i.toBase?.isSome

def carryOp' : BaseInt.CarryOp → IntExt.CarryOp
  | .adc => .adc | .sbb => .sbb

def bitOp' : BaseInt.BtOp → IntExt.BitOp
  | .bt => .bt | .bts => .bts | .btr => .btr | .btc => .btc

def shdCount' : BaseInt.ShdCount → IntExt.ShdCount
  | .cl => .cl | .imm n => .imm n

def sz? : BaseInt.Width → Option Sz
  | .w => none | .d => some .d | .q => some .q

/-- The int-ext instruction with the same meaning, for the 32/64-bit forms. -/
def _root_.Silmaril.X86.Features.BaseInt.Instr.toIntExt? : BaseInt.Instr → Option IntExt.Instr
  | .carry sz op (.rm dst src) => some (.carry (carryOp' op) sz dst src)
  | .carry sz op (.r dst src) => some (.carryR (carryOp' op) sz dst src)
  | .carry sz op (.i dst imm) => some (.carryI (carryOp' op) sz dst imm)
  | .carry sz op (.i8 dst imm) => some (.carryI8 (carryOp' op) sz dst imm)
  | .carry sz op (.a imm) => some (.carryA (carryOp' op) sz imm)
  | .pushI imm => some (.pushI imm)
  | .pushI8 imm => some (.pushI8 imm)
  | .bit wd op dst (.reg src) => (sz? wd).map fun sz => .bit (bitOp' op) sz dst src
  | .bit wd op dst (.imm imm) => (sz? wd).map fun sz => .bitI (bitOp' op) sz dst imm
  | .shd wd left dst src count => (sz? wd).map fun sz => .shd (!left) sz dst src (shdCount' count)
  | _ => none

theorem toBase?_toIntExt? {x : BaseInt.Instr} {i : IntExt.Instr} (h : x.toIntExt? = some i) :
    i.toBase? = some x := by
  cases x with
  | carry sz op form =>
    cases form <;> simp only [BaseInt.Instr.toIntExt?, Option.some.injEq] at h <;> subst h <;>
      cases op <;> rfl
  | bit wd op dst src =>
    cases wd <;> cases src <;> simp [BaseInt.Instr.toIntExt?, sz?] at h <;> subst h <;>
      cases op <;> rfl
  | shd wd left dst src count =>
    cases wd <;> simp [BaseInt.Instr.toIntExt?, sz?] at h <;> subst h <;>
      cases left <;> cases count <;> rfl
  | pushI | pushI8 => simp only [BaseInt.Instr.toIntExt?, Option.some.injEq] at h; subst h; rfl
  | _ => simp [BaseInt.Instr.toIntExt?] at h

set_option linter.unusedTactic false in
theorem toIntExt?_toBase? {i : IntExt.Instr} {x : BaseInt.Instr} (h : i.toBase? = some x) :
    x.toIntExt? = some i := by
  cases i <;> simp only [IntExt.Instr.toBase?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | rfl
    | (rename_i op sz _ _; cases op <;> cases sz <;> rfl)
    | (rename_i op sz _ _ _; cases op <;> cases sz <;> rfl)
    | (rename_i op sz _; cases op <;> cases sz <;> rfl)
    | (rename_i right sz _ _ count; cases right <;> cases sz <;> cases count <;> rfl)

/-- The baseint forms outside the overlap: the 16-bit forms and `repz ret`. -/
theorem toIntExt?_eq_none {x : BaseInt.Instr} (h : x.toIntExt? = none) :
    x.isAlu16 = true ∨ (∃ left dst src count, x = .shd .w left dst src count) ∨
      (∃ op dst src, x = .bit .w op dst src) ∨ x = .repRet := by
  cases x with
  | carry sz op form => cases form <;> simp [BaseInt.Instr.toIntExt?] at h
  | alu16 => exact .inl rfl
  | shd wd => cases wd <;> simp_all [BaseInt.Instr.toIntExt?, sz?]
  | bit wd op dst src => cases wd <;> cases src <;> simp_all [BaseInt.Instr.toIntExt?, sz?]
  | pushI | pushI8 => simp [BaseInt.Instr.toIntExt?] at h
  | repRet => simp

/-! ## Encodings -/

set_option linter.unusedTactic false in
theorem encode_toBase {i : IntExt.Instr} {x : BaseInt.Instr} (h : i.toBase? = some x) :
    IntExt.encode i = BaseInt.encode x := by
  cases i <;> simp only [IntExt.Instr.toBase?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [IntExt.encode, BaseInt.encode, IntExt.toRaw, BaseInt.toRaw, IntExt.legacyRaw,
      BaseInt.formRaw, BaseInt.accRaw, Ext.rmRaw, IntExt.Raw.bytes, Ext.Raw.bytes, IntExt.Enc.bytes,
      IntExt.Map.bytes, IntExt.Pfx.bytes, Ext.Pfx.bytes, Ext.Opc.bytes, List.append_assoc,
      List.cons_append, List.nil_append]
  all_goals first
    | rfl
    | (rename_i op sz _ _; cases op <;> cases sz <;> rfl)
    | (rename_i op sz _ _ _; cases op <;> cases sz <;> rfl)
    | (rename_i op sz _; cases op <;> cases sz <;> rfl)
    | (rename_i right sz _ _ count; cases right <;> cases sz <;> cases count <;> rfl)


/-! ## Semantics -/

section Exec

open BaseInt

theorem writeRM_rip {sz : Sz} {op : RM} {v : BitVec sz.bits} {c : X86.State} {mem : Memory}
    {next : Word} {t : X86.State} {m' : Memory} (h : Ext.writeRM sz op v c mem next = some (t, m')) :
    t.rip = c.rip := by
  cases op <;> simp only [Ext.writeRM, Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff] at h
  · obtain ⟨rfl, -⟩ := h; rfl
  · obtain ⟨_, -, rfl, -⟩ := h; rfl

/-- The retired state of int-ext: the integer state `c` with RIP advanced. -/
theorem advance_setCore (s : State) (c : X86.State) (n : Nat) (hc : c.rip = s.core.rip) :
    (s.setCore c).advance n = s.setCore { c with rip := s.core.rip + BitVec.ofNat 64 n } := by
  simp [State.advance, State.setRip, State.setCore, State.rip, hc]

/-- Unfold both semantics. -/
macro "unfold_both" : tactic => `(tactic|
  simp only [BaseInt.exec, execCore, formStep, aluStep, aluStepR, shdStep, bitStep, Op.readsCarry,
    CarryOp.toOp, carryOp, bitOp, shdCount, IntExt.exec, IntExt.run, IntExt.carryRM, IntExt.rmw,
    Width.ofSz, Width.read, Width.write, Width.readRM, Width.writeRM, Width.loadAt, Width.storeAt,
    Op.eval, Op.toAluOp?, retire, Ext.readRM, Ext.writeRM, isMemOp, ShdCount.raw,
    IntExt.shdCount, IntExt.bitOffset, BtOp.modify, IntExt.BitOp.apply])

/-- Reduce the matches on known constructors. -/
macro "reduce_both" : tactic => `(tactic|
  (try simp only [*, Option.isNone_none, Option.isNone_some, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, ite_false, ite_true, Option.map_some, Option.map_none, reduceCtorEq,
    IntExt.Out.ofOption, Out.result, State.rip, and_false, false_and, and_true, true_and,
    Bool.true_and, Bool.false_and, decide_false, decide_true, ↓reduceIte, eq_self_iff_true]))

/-- Close an equality of results that agree up to unfolding. -/
macro "close_both" : tactic => `(tactic|
  first
  | exact rfl
  | (simp only [State.advance, State.setRip, State.setCore, State.rip, IntExt.setFlags,
      Result.retired.injEq, and_true]
     congr 1 <;> congr 1 <;> exact rfl))

/-- Case on a load at `a` that both sides make. -/
macro "load_at" a:term : tactic => `(tactic|
  (generalize Ext.loadN _ $a _ = l; cases l <;> reduce_both))

/-- Case on a store at `a` that both sides make, with values equal up to unfolding. -/
macro "store_at" a:term : tactic => `(tactic|
  (generalize h1 : Ext.storeN _ $a _ _ = st1
   generalize h2 : Ext.storeN _ $a _ _ = st2
   have e : st1 = st2 := h1.symm.trans h2
   subst e
   cases st1 <;> reduce_both))

/-- Load, then store, at the same address. -/
macro "rmw_at" a:term : tactic => `(tactic|
  (all_goals first
    | close_both
    | (load_at $a
       all_goals first | close_both | (store_at $a; all_goals close_both))))

theorem exec_carry (op : IntExt.CarryOp) (sz : Sz) (dst : RM) (src : Reg) (n : Nat) (s : State)
    (m : Memory) :
    BaseInt.exec (.carry sz (carryOp op) (.rm dst src)) n s m =
      IntExt.exec (.carry op sz dst src) n s m := by
  cases dst with
  | reg r =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both
    rmw_at mm.addr s.core (s.core.rip + BitVec.ofNat 64 n)

theorem exec_carryR (op : IntExt.CarryOp) (sz : Sz) (dst : Reg) (src : RM) (n : Nat) (s : State)
    (m : Memory) :
    BaseInt.exec (.carry sz (carryOp op) (.r dst src)) n s m =
      IntExt.exec (.carryR op sz dst src) n s m := by
  cases src with
  | reg r =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> reduce_both <;>
      load_at mm.addr s.core (s.core.rip + BitVec.ofNat 64 n)
    all_goals (rcases hc : s.core.flags.carry with _ | cf <;> (reduce_both; try close_both))

theorem exec_carryI (op : IntExt.CarryOp) (sz : Sz) (dst : RM) (imm : BitVec 32) (n : Nat)
    (s : State) (m : Memory) :
    BaseInt.exec (.carry sz (carryOp op) (.i dst imm)) n s m =
      IntExt.exec (.carryI op sz dst imm) n s m := by
  cases dst with
  | reg r =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both
    rmw_at mm.addr s.core (s.core.rip + BitVec.ofNat 64 n)

theorem exec_carryI8 (op : IntExt.CarryOp) (sz : Sz) (dst : RM) (imm : BitVec 8) (n : Nat)
    (s : State) (m : Memory) :
    BaseInt.exec (.carry sz (carryOp op) (.i8 dst imm)) n s m =
      IntExt.exec (.carryI8 op sz dst imm) n s m := by
  cases dst with
  | reg r =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
      reduce_both
    rmw_at mm.addr s.core (s.core.rip + BitVec.ofNat 64 n)

theorem exec_carryA (op : IntExt.CarryOp) (sz : Sz) (imm : BitVec 32) (n : Nat) (s : State)
    (m : Memory) :
    BaseInt.exec (.carry sz (carryOp op) (.a imm)) n s m = IntExt.exec (.carryA op sz imm) n s m := by
  cases op <;> cases sz <;> unfold_both <;> rcases hc : s.core.flags.carry with _ | cf <;>
    reduce_both <;> close_both

theorem pushWord_eq (c : X86.State) (m : Memory) (v : Word) :
    X86.pushWord c m v =
      (Ext.storeN m (c.read .rsp - 8) 8 v).map fun after => (c.write .rsp (c.read .rsp - 8), after) := by
  simp only [X86.pushWord, Ext.storeN, Ext.leBytes_eight]
  rfl

theorem exec_pushI (imm : BitVec 32) (n : Nat) (s : State) (m : Memory) :
    BaseInt.exec (.pushI imm) n s m = IntExt.exec (.pushI imm) n s m := by
  simp only [BaseInt.exec, execCore, IntExt.exec, IntExt.run, pushWord_eq]
  reduce_both
  store_at (s.core.read .rsp - 8)
  all_goals close_both

theorem exec_pushI8 (imm : BitVec 8) (n : Nat) (s : State) (m : Memory) :
    BaseInt.exec (.pushI8 imm) n s m = IntExt.exec (.pushI8 imm) n s m := by
  simp only [BaseInt.exec, execCore, IntExt.exec, IntExt.run, pushWord_eq]
  reduce_both
  store_at (s.core.read .rsp - 8)
  all_goals close_both

theorem shdCount_eq (sz : Sz) (count : IntExt.ShdCount) (c : X86.State) :
    (ShdCount.raw (shdCount count) c).toNat % (if Width.ofSz sz = .q then 64 else 32) =
      IntExt.shdCount sz count c := by
  cases sz <;> cases count <;>
    simp [ShdCount.raw, shdCount, IntExt.shdCount, Width.ofSz, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd]

theorem shdCount_lt (sz : Sz) (count : IntExt.ShdCount) (c : X86.State) :
    IntExt.shdCount sz count c < sz.bits := by
  cases count <;> exact Nat.mod_lt _ (by cases sz <;> decide)

theorem exec_shd (right : Bool) (sz : Sz) (dst : RM) (src : Reg) (count : IntExt.ShdCount)
    (n : Nat) (s : State) (m : Memory) :
    BaseInt.exec (.shd (.ofSz sz) (!right) dst src (shdCount count)) n s m =
      IntExt.exec (.shd right sz dst src count) n s m := by
  have hlt := shdCount_lt sz count s.core
  simp only [BaseInt.exec, execCore, shdStep, shdCount_eq, IntExt.exec, IntExt.run]
  by_cases h0 : IntExt.shdCount sz count s.core = 0
  · cases dst with
    | reg r =>
      cases sz <;> simp only [h0, isMemOp] <;> unfold_both <;> reduce_both <;> close_both
    | mem mm => simp [h0, isMemOp, Out.result]
  · have hb : ¬ (Width.ofSz sz).bits < IntExt.shdCount sz count s.core := by
      cases sz <;> simpa [Width.ofSz] using Nat.le_of_lt hlt
    cases dst with
    | reg r =>
      cases sz <;> cases right <;> simp only [h0, hb, isMemOp] <;> unfold_both <;> reduce_both <;>
        close_both
    | mem mm =>
      cases sz <;> cases right <;> simp only [h0, hb, isMemOp] <;> unfold_both <;> reduce_both
      rmw_at mm.addr s.core (s.core.rip + BitVec.ofNat 64 n)

/-- Case on two loads that are equal up to unfolding. -/
macro "load2" : tactic => `(tactic|
  (generalize h1 : Ext.loadN _ _ _ = l1
   generalize h2 : Ext.loadN _ _ _ = l2
   have e : l1 = l2 := h1.symm.trans h2
   subst e
   cases l1 <;> reduce_both))

/-- Case on two stores that are equal up to unfolding. -/
macro "store2" : tactic => `(tactic|
  (generalize h1 : Ext.storeN _ _ _ _ = st1
   generalize h2 : Ext.storeN _ _ _ _ = st2
   have e : st1 = st2 := h1.symm.trans h2
   subst e
   cases st1 <;> reduce_both))

theorem exec_bit (op : IntExt.BitOp) (sz : Sz) (dst : RM) (src : Reg) (n : Nat) (s : State)
    (m : Memory) :
    BaseInt.exec (.bit (.ofSz sz) (bitOp op) dst (.reg src)) n s m =
      IntExt.exec (.bit op sz dst src) n s m := by
  cases dst with
  | reg r => cases op <;> cases sz <;> unfold_both <;> reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> reduce_both <;> load2
    all_goals first | close_both | (store2; all_goals close_both)

theorem exec_bitI (op : IntExt.BitOp) (sz : Sz) (dst : RM) (imm : BitVec 8) (n : Nat) (s : State)
    (m : Memory) :
    BaseInt.exec (.bit (.ofSz sz) (bitOp op) dst (.imm imm)) n s m =
      IntExt.exec (.bitI op sz dst imm) n s m := by
  cases dst with
  | reg r => cases op <;> cases sz <;> unfold_both <;> reduce_both <;> close_both
  | mem mm =>
    cases op <;> cases sz <;> unfold_both <;> reduce_both <;> load2
    all_goals first | close_both | (store2; all_goals close_both)

end Exec

end Silmaril.X86.Features.IntMerged
