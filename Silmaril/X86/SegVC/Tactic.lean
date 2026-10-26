module

public import Silmaril.X86.SegVC

/-!
# `seg_vc`: unfolding a segment's VCs by symbolic execution

`seg_vc [defs]` unfolds `SegVC.wpN` for an instance built with `Isa.ofExt` (`Isa.ext`,
`X86Sys.Isa.sys`, and any other machine whose instructions are `X86.Ext`'s) along every
path, through `Ext.exec`, leaving the arithmetic VCs (bit-vector and `Nat` facts for
`omega`, `simp` or `decide`, or an SMT fact as a labelled fallback).

Two kinds of lemma make this work, and both are reusable for any ISA variant:

* **branch splitting** (`onOk_jcc8`, `onOk_jcc`, used as `↓` pre-rewrites): a conditional
  branch is unfolded into both successors, each under its condition, *before* `Ext.exec` is
  exposed (`simp` cannot split the `match` on an unknown condition inside `exec`). They
  mention no instance, so they apply to every `Isa` whose executor is `Ext.exec`;
* **flag reading** (`eval_logic_*`, `eval_sub_*`): the flags a `test`/`and` or a `cmp`/`sub`
  leaves, read through a condition code, become a comparison of the operands.

The flag lemmas are those of `ProgramVC.X86` (projects/smt-axioms/ProgramVC/X86/Tactic.lean),
restated here so that Silmaril modules (which cannot import that project) can use them.
-/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext

theorem add_sub_self_left (b x : Word) : b + x - b = x := by bv_omega

theorem eval_logic_e {w : Nat} (r : BitVec w) :
    Cond.e.eval (logicFlagsN r) = some (r == 0#w) := rfl
theorem eval_logic_ne {w : Nat} (r : BitVec w) :
    Cond.ne.eval (logicFlagsN r) = some (!(r == 0#w)) := rfl

theorem msb_eq_slt_zero {w : Nat} (r : BitVec (w + 1)) : r.msb = r.slt 0 := by
  rw [Bool.eq_iff_iff, BitVec.slt_eq_decide, BitVec.msb_eq_toInt]
  simp

theorem sle_zero_eq {w : Nat} (r : BitVec (w + 1)) : r.sle 0 = (r == 0#(w + 1) || r.msb) := by
  rw [msb_eq_slt_zero, Bool.eq_iff_iff, BitVec.sle_eq_decide, BitVec.slt_eq_decide]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    rcases Int.lt_or_eq_of_le h with h | h
    · exact .inr h
    · exact .inl (BitVec.toInt_inj.mp (by simpa using h))
  · rintro (h | h)
    · subst h; simp
    · omega

theorem eval_logic_le {w : Nat} (r : BitVec (w + 1)) :
    Cond.le.eval (logicFlagsN r) = some (r.sle 0) := by
  rw [sle_zero_eq]
  cases hz : (r == 0#(w + 1)) <;> cases hm : r.msb <;>
    simp [Cond.eval, logicFlagsN, kOr, kXor, isZeroN, hz, hm]

theorem eval_logic_g {w : Nat} (r : BitVec (w + 1)) :
    Cond.g.eval (logicFlagsN r) = some (!r.sle 0) := by
  rw [sle_zero_eq]
  cases hz : (r == 0#(w + 1)) <;> cases hm : r.msb <;>
    simp [Cond.eval, logicFlagsN, kOr, kXor, kNot, isZeroN, hz, hm]

theorem eval_logic_s {w : Nat} (r : BitVec (w + 1)) :
    Cond.s.eval (logicFlagsN r) = some r.msb := by
  simp [Cond.eval, logicFlagsN]

theorem eval_logic_ns {w : Nat} (r : BitVec (w + 1)) :
    Cond.ns.eval (logicFlagsN r) = some (!r.msb) := by
  simp [Cond.eval, logicFlagsN, kNot]

theorem eval_sub_8 (x y : BitVec 8) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 7) x y c) := eval_subFlagsN (w := 7) x y c
theorem eval_sub_32 (x y : BitVec 32) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 31) x y c) := eval_subFlagsN (w := 31) x y c
theorem eval_sub_64 (x y : BitVec 64) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 63) x y c) := eval_subFlagsN (w := 63) x y c

/-- `exec` rebuilds a state from a written one; put the write back outside. -/
theorem mk_write (s : State) (r : Reg) (v : Word) (x : Word) (f : Flags) (fs : Word) :
    State.mk (s.write r v).regs x f fs = (State.mk s.regs x f fs).write r v := rfl

theorem regs_mk (regs : Silmaril.Machine.RegisterFile Reg Word) (x : Word) (f : Flags)
    (fs : Word) : (State.mk regs x f fs).regs = regs := rfl

theorem read_mk (regs : Silmaril.Machine.RegisterFile Reg Word) (x : Word) (f : Flags)
    (fs : Word) (q : Reg) : (State.mk regs x f fs).read q = regs q := rfl

theorem core_regs (s : State) (q : Reg) : s.regs q = s.read q := rfl

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp [BitVec.setWidth_setWidth_of_le]

theorem base_reg_value (r : Reg) (s : State) (next : Word) :
    (Base.reg r).value s next = s.read r := rfl

@[simp] theorem onOk_ok {P : State → Memory → Prop} {c : State} {m : Memory} :
    onOk P (.ok c m) = P c m := rfl
@[simp] theorem onOk_dataFault {P : State → Memory → Prop} : onOk P .dataFault = False := rfl
@[simp] theorem onOk_divideError {P : State → Memory → Prop} : onOk P .divideError = False := rfl
@[simp] theorem onOk_undefinedCondition {P : State → Memory → Prop} {c : Cond} :
    onOk P (.undefinedCondition c) = False := rfl
@[simp] theorem onOk_trap {P : State → Memory → Prop} : onOk P .trap = False := rfl

/-! ## Unfolding the path budget one instruction at a time

`wpN` is unfolded only when applied to an offset and a state, so that `simp` does not unfold
the continuation under its binder (which would evaluate the listing lookup at a symbolic
offset). -/

theorem wpN_succ {σ : Type} {I : Isa σ} {code : List Byte} {L : Listing I}
    {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))} {calls : List (Nat × Nat × Call I)}
    {base : Word} {μ : Option Nat} {k o : Nat} {s : σ} :
    wpN I code L cuts stops calls [] base μ (k + 1) o s =
      wpI I code cuts stops calls base μ (wpN I code L cuts stops calls [] base μ k) o (L.lookup o) s :=
  rfl

/-- With summaries: one is used where listed, else the instruction. -/
theorem wpN_succ_subs {σ : Type} {I : Isa σ} {code : List Byte} {L : Listing I}
    {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))} {calls : List (Nat × Nat × Call I)}
    {subs : List (Nat × Nat × Call I)} {base : Word} {μ : Option Nat} {k o : Nat} {s : σ} :
    wpN I code L cuts stops calls subs base μ (k + 1) o s =
      match subs.lookup o with
      | some (o', sb) => sb.pre s ∧ ∀ t, sb.post s t →
          (I.core t).rip = base + BitVec.ofNat 64 o' ∧ Loaded (I.mem t) base code ∧
            nextAt cuts stops μ (wpN I code L cuts stops calls subs base μ k) (o' % 2 ^ 64) t
      | none =>
        wpI I code cuts stops calls base μ (wpN I code L cuts stops calls subs base μ k) o (L.lookup o) s :=
  rfl

theorem wpN_zero {σ : Type} {I : Isa σ} {code : List Byte} {L : Listing I}
    {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))} {calls : List (Nat × Nat × Call I)}
    {base : Word} {μ : Option Nat} {o : Nat} {s : σ} {subs : List (Nat × Nat × Call I)} :
    wpN I code L cuts stops calls subs base μ 0 o s = False :=
  rfl

/-! ## Conditional branches, in the form `simp` can split

`simp` cannot split the `match` on an unknown condition inside `Ext.exec`, so the two branch
forms are rewritten *before* `Ext.exec` is unfolded: `seg_vc` uses these lemmas as
pre-rewrites (`↓`). They mention no instance, so they apply to every `SegVC.Isa` whose
executor is `Ext.exec` (`Isa.ofExt`). -/

theorem onOk_jcc8 {P : State → Memory → Prop} {c : Cond} {rel : BitVec 8} {s : State}
    {m : Memory} {l : Nat} :
    onOk P (Ext.exec (.jcc8 c rel) s m l) ↔
      (c.eval s.flags).isSome ∧
      (c.eval s.flags = some true →
        P { s with rip := s.rip + BitVec.ofNat 64 l + rel.signExtend 64 } m) ∧
      (c.eval s.flags = some false → P { s with rip := s.rip + BitVec.ofNat 64 l } m) := by
  simp only [Ext.exec]
  cases h : c.eval s.flags with
  | none => simp [onOk]
  | some b => cases b <;> simp [onOk]

theorem onOk_jcc {P : State → Memory → Prop} {c : Cond} {rel : BitVec 32} {s : State}
    {m : Memory} {l : Nat} :
    onOk P (Ext.exec (.jcc c rel) s m l) ↔
      (c.eval s.flags).isSome ∧
      (c.eval s.flags = some true →
        P { s with rip := s.rip + BitVec.ofNat 64 l + rel.signExtend 64 } m) ∧
      (c.eval s.flags = some false → P { s with rip := s.rip + BitVec.ofNat 64 l } m) := by
  simp only [Ext.exec]
  cases h : c.eval s.flags with
  | none => simp [onOk]
  | some b => cases b <;> simp [onOk]

/-! ## Stores, with the successor memory left opaque

`retire` and `Option.map` stay folded in `seg_vc`, so that a store whose success is not yet
known meets `onOk_retire_storeN`: the VC asks for the write permission and continues from
*every* memory the store may produce, named by its `storeN` equation. That equation is all
the later reasoning needs (`Stored.of_storeN`, `loadN_storeN`, `loadN_storeN_disjoint`), and
the memory term does not grow along the path. -/

theorem retire_some {next : Word} {t : State} {m : Memory} :
    retire next (some (t, m)) = .ok { t with rip := next } m := rfl

theorem retire_none {next : Word} : retire next none = .dataFault := rfl

theorem onOk_retire_storeN {P : State → Memory → Prop} {next : Word}
    {g : Memory → State × Memory} {memory : Memory} {address : Word} {k : Nat} {v : Word} :
    onOk P (retire next ((storeN memory address k v).map g)) ↔
      memory.Permitted .write address.toNat k ∧
        ∀ after, storeN memory address k v = some after → onOk P (retire next (some (g after))) := by
  constructor
  · intro h
    cases hs : storeN memory address k v with
    | none => rw [hs] at h; exact h.elim
    | some after =>
      refine ⟨?_, fun after' h' => ?_⟩
      · have := Memory.writeBytes_permitted (by simpa [storeN] using hs)
        simpa using this
      · rw [hs] at h
        cases h'
        exact h
  · rintro ⟨hp, h⟩
    obtain ⟨after, hs, _⟩ := storeN_isSome (v := v) hp
    rw [hs]
    exact h after hs

/-- `seg_vc [lemmas]`: unfold a segment's `wpN` along every path by symbolic execution.

It alternates two `simp` passes: the first normalises and splits (`onOk_jcc8`, `onOk_jcc`)
with `Ext.exec` folded; the second unfolds the `Ext.exec` of the instructions the first pass
exposed. A conditional branch is therefore always split before its `match` is exposed. -/
syntax "seg_vc " ("(" &"maxSteps" " := " num ")")? " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic

/-- One normalising pass of `seg_vc`, with `Ext.exec` folded. -/
syntax "seg_vc_pass " "(" &"maxSteps" " := " num ")" " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic

macro_rules
  | `(tactic| seg_vc_pass (maxSteps := $n) [$ls,*]) => `(tactic|
    (simp (maxSteps := $n) only [wpN_succ, wpN_succ_subs, wpN_zero, wpI, onOk_jcc8, onOk_jcc, after, nextAt,
        onOk_ok, onOk_dataFault, onOk_divideError, onOk_undefinedCondition, onOk_trap,
        mk_write, regs_mk, read_mk, core_regs, setWidth_32_64, base_reg_value,
        Option.getD_none, Option.getD_some, BitVec.reduceSetWidth, BitVec.reduceShiftLeft,
        BitVec.toNat_ofNat, BitVec.reduceToNat, Silmaril.X86.State.write_fsBase, ne_eq,
        not_false_eq_true, Silmaril.X86.State.read_write_other, BitVec.reduceSignExtend,
        Option.isSome_some, forall_const, Option.some.injEq, offOf, List.lookup_cons,
        List.lookup_nil, Nat.reduceBEq,
        retire_some, retire_none, onOk_retire_storeN,
        Option.map_none, Silmaril.X86.Ext.aluStep,
        Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
        Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.bits,
        Silmaril.X86.Ext.rip_mk, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
        Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Index.value,
        Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.writeNarrow, Silmaril.X86.Ext.writeRM8,
        Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Narrow.bytes, BitVec.xor_self,
        Silmaril.X86.Ext.Sz.bytes, Option.map_id',
        BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero, and_self,
        Silmaril.X86.State.read_write_same, Silmaril.X86.Ext.read_with_rip,
        Silmaril.X86.Ext.read_mk_regs, Silmaril.X86.Ext.read_with_flags,
        Silmaril.X86.Ext.rip_with_flags, Silmaril.X86.State.write_rip,
        Silmaril.X86.State.write_flags,
        eval_logic_e, eval_logic_ne, eval_logic_le, eval_logic_g, eval_logic_s, eval_logic_ns,
        eval_sub_8, eval_sub_32, eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
        add_sub_self_left, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMod,
        Nat.reducePow, Nat.reduceAdd, Option.map_some, true_and, and_true,
        reduceCtorEq, ite_false, ite_true, Bool.false_eq_true, Bool.cond_true, Bool.cond_false,
        reduceIte, bound, implies_true, $ls,*]))

macro_rules
  | `(tactic| seg_vc [$ls,*]) => `(tactic| seg_vc (maxSteps := 400000) [$ls,*])
  | `(tactic| seg_vc (maxSteps := $n) [$ls,*]) => `(tactic|
    (seg_vc_pass (maxSteps := $n) [$ls,*]
     repeat (simp only [Silmaril.X86.Ext.exec]; try seg_vc_pass (maxSteps := $n) [$ls,*])
     try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Narrow.bits]))

/-- `seg_read [defs]`: read registers of a symbolically executed state. -/
syntax "seg_read " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_read [$ls,*]) => `(tactic|
    (simp only [Silmaril.X86.State.read_write_same, Silmaril.X86.State.read_write_other, ne_eq,
        reduceCtorEq, not_false_eq_true, read_mk, core_regs, regs_mk, setWidth_32_64,
        Silmaril.X86.Ext.read_with_rip, Silmaril.X86.Ext.read_mk_regs,
        Silmaril.X86.Ext.read_with_flags, true_and, and_true, Bool.not_eq_true',
        Bool.not_eq_false', beq_iff_eq, beq_eq_false_iff_ne, $ls,*]))

end Silmaril.X86.SegVC
