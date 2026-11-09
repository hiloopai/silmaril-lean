module

public import Silmaril.X86.SegVC9.Defs
public import Silmaril.X86.SegVC.Tactic
public import Silmaril.X86.SegVC.Mono
public import Silmaril.X86.Open9.Thms
import Silmaril.Proofs.X86.SegVC9.Path

/-!
# `seg_vc9`: the segment VC tactic on the open machine over `Ext9`

`Open9.isa` executes `Ext9.exec`, which is `Ext8.exec` (hence `X86.Ext.exec` on `base`
forms) on `.ext8` instructions and `Ext9.execNew` on the new forms. The lemmas here put both
in the shape the `seg_vc` lemma set expects, and package two tactics:

* **dispatch** (all `rfl`): `exec9_base`, `exec9_ext8new`, `exec9_new` (to `X86.Ext.exec`,
  `Ext8.execNew`, `Ext9.execNew`); `exec9_imulI_reg`, the three-operand
  `imul r, r, imm` as `retire` of the product; `open9_exec`, `open9_core`, `open9_mem`,
  `open9_ok`, `open9_upd`, the projections of `Open9.isa`;
* `onOk_retire_pushWord`, `popWord_of_holds`, `sub_eight`: `push` and `pop` with the
  successor memory left opaque, and `rsp - 8` as an addition;
* `nextAt_cut`, `nextAt_stop`, `nextAt_cont`: `nextAt` by cases, for listings whose
  offsets the tactics should not evaluate;
* `mk_write'`: `SegVC.mk_write` with a propositional proof (see below);
* **`seg_vc9 [lemmas]`**: `seg_vc` on `Open9.isa`, with the lemmas above;
* **variable offsets**: `wpN_succ_var`, `wpN_zero_var`, `wpI_some_var`, `wpI_none_var`,
  `after_nil_var`, `wpI_some9`: equation lemmas with propositional proofs; `wpN_one`,
  `wpN_one_cont`: one instruction at a variable offset; `wpN_budget`. **`seg_vc9_var
  [lemmas]`** is `seg_vc9` over the simp sets `seg_vc9_var` and `seg_vc9_listing`
  (`SegVC9.Defs`);
* **segments with exits** (no cut points, calls or summaries): `nextAt_exits_mem`,
  `nextAt_exits_not_mem`; `seg_runsIn`, `seg_runsIn9`: **a segment VC is a
  `FnContract.RunsIn` run inside the code** to a state satisfying the exit's postcondition
  (with `FnContract.Spec.strict_of_inCode`, the run of a strict spec).

Reusable for any `Open9` segment proof; nothing here is specific to a function. Every
lemma is proved; the tactics are macros over `simp only`.
-/

@[expose] public section

namespace Silmaril.X86.SegVC9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Result retire Sz Loaded)
open Silmaril.X86.SegVC
open Silmaril.X86.FnContract (RunsIn InCode)

/-! ## Dispatch -/

theorem exec9_base (i : Silmaril.X86.Ext.Instr) (s : State) (m : Memory) (l : Nat) :
    Ext9.exec (.ext8 (.base i)) s m l = Silmaril.X86.Ext.exec i s m l := rfl

theorem exec9_ext8new (i : Silmaril.X86.Ext8.New) (s : State) (m : Memory) (l : Nat) :
    Ext9.exec (.ext8 (.new i)) s m l =
      Silmaril.X86.Ext8.execNew i s m (s.rip + BitVec.ofNat 64 l) := rfl

/-- An `Ext9` new form executes as `execNew` at the next instruction's address. -/
theorem exec9_new (i : Ext9.New) (s : State) (m : Memory) (l : Nat) :
    Ext9.exec (.new i) s m l = Ext9.execNew i s m (s.rip + BitVec.ofNat 64 l) := rfl

/-- `imul r, r, imm` (register source; the immediate is stored sign-extended to 32 bits). -/
theorem exec9_imulI_reg (sz : Sz) (dst src : Reg) (imm : BitVec 32) (s : State) (m : Memory)
    (l : Nat) :
    Ext9.exec (.new (.imulI sz dst (.reg src) imm)) s m l =
      retire (s.rip + BitVec.ofNat 64 l)
        (some ({ sz.write s dst (sz.read s src * imm.signExtend sz.bits) with
          flags := Silmaril.X86.Ext.imulFlags (sz.read s src) (imm.signExtend sz.bits) }, m)) :=
  rfl

theorem open9_exec : Open9.isa.exec = Ext9.exec := rfl
theorem open9_core : Open9.isa.core = MState.core := rfl
theorem open9_mem : Open9.isa.mem = MState.memory := rfl
theorem open9_ok (i : Ext9.Instr) (c : State) : Open9.isa.ok i c = True := rfl
theorem open9_upd (s : MState) (c : State) (m : Memory) : Open9.isa.upd s c m = ⟨c, m⟩ := rfl

/-! ## Stack -/

/-- A `push`, with the successor memory left opaque and named by its `storeN` equation
(`pushWord` writes `encodeWords [v] = leBytes v 8` at `rsp - 8`). -/
theorem onOk_retire_pushWord {P : State → Memory → Prop} {next : Word} {s : State}
    {memory : Memory} {v : Word} :
    onOk P (retire next (Silmaril.X86.pushWord s memory v)) ↔
      memory.Permitted .write (s.read .rsp - 8#64).toNat 8 ∧
        ∀ after, Silmaril.X86.Ext.storeN memory (s.read .rsp - 8#64) 8 v = some after →
          P { s.write .rsp (s.read .rsp - 8#64) with rip := next } after :=
  Silmaril.Proofs.X86.SegVC9.onOk_retire_pushWord

/-- A `pop` reads the eight bytes at `rsp` as a little-endian word. -/
theorem popWord_of_holds {s : State} {memory : Memory} {v : Word}
    (h : memory.readBytes (s.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    Silmaril.X86.popWord s memory = some (v, s.write .rsp (s.read .rsp + 8#64)) :=
  Silmaril.X86.popWord_of_readBytes h

/-- A push's `rsp - 8` as `rsp + (2^64 - 8)`, so that `rsp`-relative addresses normalise to
`rsp + c` under `BitVec.add_assoc` and literal folding. -/
theorem sub_eight (x : Word) : x - 8#64 = x + 0xfffffffffffffff8#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl

/-! ## `nextAt` by cases

The tactics below do not unfold `nextAt` (`seg_vc` does). Unfolding it definitionally leaves
the kernel a `match` on `cuts.lookup o`; when `o` is still the unevaluated offset of a
backward jump (`(base + c - base).toNat` with `c` near `2^64`), the kernel evaluates it by
unary recursion and runs out of depth. A proof supplies `nextAt` equations for the literal
offsets of its listing, from these lemmas. -/

section NextAt

variable {σ : Type} {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))}
  {μ : Option Nat} {cont : Nat → σ → Prop} {o : Nat} {s : σ}

theorem nextAt_cut {c : Cut (σ := σ)} (h : cuts.lookup o = some c) :
    nextAt cuts stops μ cont o s = (c.inv s ∧ bound μ (c.measure s)) := by
  simp only [nextAt, h]

theorem nextAt_stop {q : σ → Prop} (h1 : cuts.lookup o = none) (h2 : stops.lookup o = some q) :
    nextAt cuts stops μ cont o s = q s := by
  simp only [nextAt, h1, h2]

theorem nextAt_cont (h1 : cuts.lookup o = none) (h2 : stops.lookup o = none) :
    nextAt cuts stops μ cont o s = cont o s := by
  simp only [nextAt, h1, h2]

end NextAt

/-- `exec` rebuilds a state from a written one; put the write back outside. `SegVC.mk_write`
is the same statement proved by `rfl`, so `simp` applies it as a definitional rewrite and
leaves the kernel to re-check `State.mk (s.write r v).regs … ≡ (State.mk s.regs …).write r v`;
when `v` holds a 64-bit literal near `2^64` (a negative displacement, `rsp - 8`, …) that
check can unfold `Nat.add` on the literal and run out of recursion depth. This copy has a
propositional proof, so the kernel only instantiates it. -/
theorem mk_write' (s : State) (r : Reg) (v : Word) (x : Word) (f : Silmaril.X86.Flags)
    (fs : Word) : State.mk (s.write r v).regs x f fs = (State.mk s.regs x f fs).write r v := by
  cases s; simp only [State.write]

/-! ## `seg_vc9` -/

/-- One normalising pass of `seg_vc9`: the lemma set of `seg_vc_pass` with `mk_write'` for
`mk_write`, without `nextAt`, and with the `Open9.isa` lemmas above. -/
syntax "seg_vc9_pass " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_vc9_pass [$ls,*]) => `(tactic|
    (simp (maxSteps := 400000) only [Silmaril.X86.SegVC.wpN_succ,
        Silmaril.X86.SegVC.wpN_succ_subs, Silmaril.X86.SegVC.wpN_zero, Silmaril.X86.SegVC.wpI,
        Silmaril.X86.SegVC.onOk_jcc8, Silmaril.X86.SegVC.onOk_jcc, Silmaril.X86.SegVC.onOk_call,
        Silmaril.X86.SegVC.after, Silmaril.X86.SegVC.onOk_ok, Silmaril.X86.SegVC.onOk_dataFault,
        Silmaril.X86.SegVC.onOk_divideError, Silmaril.X86.SegVC.onOk_undefinedCondition,
        Silmaril.X86.SegVC.onOk_trap, Silmaril.X86.SegVC9.mk_write',
        Silmaril.X86.SegVC.regs_mk, Silmaril.X86.SegVC.read_mk, Silmaril.X86.SegVC.core_regs,
        Silmaril.X86.SegVC.setWidth_32_64, Silmaril.X86.SegVC.base_reg_value,
        Option.getD_none, Option.getD_some, BitVec.reduceSetWidth, BitVec.reduceShiftLeft,
        BitVec.toNat_ofNat, BitVec.reduceToNat, Silmaril.X86.State.write_fsBase, ne_eq,
        not_false_eq_true, Silmaril.X86.State.read_write_other, BitVec.reduceSignExtend,
        Option.isSome_some, forall_const, Option.some.injEq, Silmaril.X86.SegVC.offOf,
        List.lookup_cons, List.lookup_nil, Nat.reduceBEq, Silmaril.X86.SegVC.retire_some,
        Silmaril.X86.SegVC.retire_none, Silmaril.X86.SegVC.onOk_retire_storeN, Option.map_none,
        Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.write,
        Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.rip_mk, Silmaril.X86.Ext.AluOp.resultN,
        Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Index.value,
        Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.writeNarrow, Silmaril.X86.Ext.writeRM8,
        Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Narrow.bytes, BitVec.xor_self,
        Silmaril.X86.Ext.Sz.bytes, Option.map_id', BitVec.setWidth_eq, BitVec.shiftLeft_zero,
        BitVec.add_zero, and_self, Silmaril.X86.State.read_write_same,
        Silmaril.X86.Ext.read_with_rip, Silmaril.X86.Ext.read_mk_regs,
        Silmaril.X86.Ext.read_with_flags, Silmaril.X86.Ext.rip_with_flags,
        Silmaril.X86.State.write_rip, Silmaril.X86.State.write_flags,
        Silmaril.X86.SegVC.eval_logic_e, Silmaril.X86.SegVC.eval_logic_ne,
        Silmaril.X86.SegVC.eval_logic_le, Silmaril.X86.SegVC.eval_logic_g,
        Silmaril.X86.SegVC.eval_logic_s, Silmaril.X86.SegVC.eval_logic_ns,
        Silmaril.X86.SegVC.eval_sub_8, Silmaril.X86.SegVC.eval_sub_32,
        Silmaril.X86.SegVC.eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
        Silmaril.X86.SegVC.add_sub_self_left, BitVec.add_assoc, BitVec.reduceAdd,
        Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Option.map_some, true_and, and_true,
        reduceCtorEq, ite_false, ite_true, Bool.false_eq_true, Bool.cond_true, Bool.cond_false,
        reduceIte, Silmaril.X86.SegVC.bound, implies_true,
        Silmaril.X86.SegVC9.exec9_base, Silmaril.X86.SegVC9.exec9_ext8new,
        Silmaril.X86.SegVC9.exec9_imulI_reg, Silmaril.X86.SegVC9.open9_exec,
        Silmaril.X86.SegVC9.open9_core, Silmaril.X86.SegVC9.open9_mem,
        Silmaril.X86.SegVC9.open9_ok, Silmaril.X86.SegVC9.open9_upd,
        Silmaril.X86.SegVC9.onOk_retire_pushWord, Silmaril.X86.Ext.Count.raw,
        Silmaril.X86.Ext.ShiftOp.result, $ls,*]))

/-- `seg_vc9 [lemmas]`: unfold a segment's `wpN` on `Open9.isa` along every path (as
`seg_vc`: alternate a normalising pass with `Ext.exec` folded and an unfolding of the
`Ext.exec` it exposed). Pass `nextAt` (or `nextAt_*` equations) and the listing among
`lemmas`; other `Ext9` new forms go through `exec9_new` and their `Ext9.execNew` case. -/
syntax "seg_vc9 " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_vc9 [$ls,*]) => `(tactic|
    (seg_vc9_pass [$ls,*]
     repeat (simp only [Silmaril.X86.Ext.exec]; try seg_vc9_pass [$ls,*])
     try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Narrow.bits]))

/-! ## Variable offsets

A segment lemma can take its start and continuation offsets as variables with equations,
and run up to a variable path budget `K`, so that the unfolding stops at `wpN … K o t`
instead of evaluating a listing lookup or an instruction at a literal offset. The lemmas
below support this for segments with no summaries (`subs = []`), and with no contracted
calls for `after_nil_var`, `wpN_one` and `wpN_one_cont`.

Each equation lemma is the `rfl` equation composed with `Eq.trans`, so `simp` does not
classify it as an `rfl` lemma and only instantiates it; a proof may then make
`wpN`/`wpI`/`after` locally irreducible. -/

section Var

variable {σ : Type} {I : Isa σ} {code : List Byte} {L : Listing I}
  {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))}
  {calls : List (Nat × Nat × Call I)} {base : Word} {μ : Option Nat}

theorem wpN_succ_var {k o : Nat} {s : σ} :
    wpN I code L cuts stops calls [] base μ (k + 1) o s =
      wpI I code cuts stops calls base μ (wpN I code L cuts stops calls [] base μ k) o
        (L.lookup o) s :=
  Eq.trans Silmaril.X86.SegVC.wpN_succ (Eq.refl _)

theorem wpN_zero_var {o : Nat} {s : σ} :
    wpN I code L cuts stops calls [] base μ 0 o s = False :=
  Eq.trans Silmaril.X86.SegVC.wpN_zero (Eq.refl _)

theorem wpI_some_var {cont : Nat → σ → Prop} {o : Nat} {i : I.Instr} {l : Nat} {s : σ} :
    wpI I code cuts stops calls base μ cont o (some (i, l)) s =
      onOk (after I code cuts stops calls base μ cont o i s) (I.exec i (I.core s) (I.mem s) l) :=
  Eq.trans (Eq.refl _) (Eq.refl _)

theorem wpI_none_var {cont : Nat → σ → Prop} {o : Nat} {s : σ} :
    wpI I code cuts stops calls base μ cont o none s = False :=
  Eq.trans (Eq.refl _) (Eq.refl _)

theorem after_nil_var {cont : Nat → σ → Prop} {o : Nat} {i : I.Instr} {s : σ} {c : State}
    {m : Memory} :
    after I code cuts stops [] base μ cont o i s c m =
      (I.ok i c ∧ Loaded m base code ∧ nextAt cuts stops μ cont (offOf base c) (I.upd s c m)) :=
  Eq.trans (Eq.refl _) (Eq.refl _)

/-- One listed instruction that executes (`wpN` unfolded once), at a variable offset `o`. -/
theorem wpN_one {k o : Nat} {s : σ} {i : I.Instr} {l : Nat} {c : State} {m : Memory}
    (hlk : L.lookup o = some (i, l))
    (hex : I.exec i (I.core s) (I.mem s) l = .ok c m) (hok : I.ok i c)
    (hL : Loaded m base code)
    (hnext : nextAt cuts stops μ (wpN I code L cuts stops [] [] base μ k) (offOf base c)
      (I.upd s c m)) :
    wpN I code L cuts stops [] [] base μ (k + 1) o s := by
  rw [wpN_succ_var, hlk, wpI_some_var, hex, onOk_ok, after_nil_var]
  exact ⟨hok, hL, hnext⟩

/-- `wpN_one` when the instruction falls through to a variable offset `o'` that is neither a
cut point nor a stop: the path continues there with one instruction less. -/
theorem wpN_one_cont {k o o' : Nat} {s : σ} {i : I.Instr} {l : Nat} {c : State} {m : Memory}
    (hlk : L.lookup o = some (i, l))
    (hex : I.exec i (I.core s) (I.mem s) l = .ok c m) (hok : I.ok i c)
    (hL : Loaded m base code) (hrip : c.rip = base + BitVec.ofNat 64 o') (ho : o' < 2 ^ 64)
    (hcut : cuts.lookup o' = none) (hstop : stops.lookup o' = none)
    (hk : wpN I code L cuts stops [] [] base μ k o' (I.upd s c m)) :
    wpN I code L cuts stops [] [] base μ (k + 1) o s := by
  refine wpN_one hlk hex hok hL ?_
  rw [offOf_of_rip hrip, Nat.mod_eq_of_lt ho, nextAt_cont hcut hstop]
  exact hk

/-- A segment proved up to a budget holds at every larger budget. -/
theorem wpN_budget {k k' o : Nat} {s : σ} (hk : k ≤ k')
    (h : wpN I code L cuts stops calls [] base μ k o s) :
    wpN I code L cuts stops calls [] base μ k' o s :=
  Silmaril.X86.SegVC.wpN_mono hk h

end Var

/-- `wpI_some_var` on `Open9.isa`, with the instruction typed as `Ext9.Instr`: a listing
lookup lemma states its result at `Option (Ext9.Instr × Nat)`, and `simp` does not unfold
`Open9.isa.Instr` to `Ext9.Instr` when matching the generic form. -/
theorem wpI_some9 {code : List Byte} {cuts : List (Nat × Cut (σ := MState))}
    {stops : List (Nat × (MState → Prop))} {calls : List (Nat × Nat × Call Open9.isa)}
    {base : Word} {μ : Option Nat} {cont : Nat → MState → Prop} {o : Nat}
    {i : Ext9.Instr} {l : Nat} {s : MState} :
    wpI Open9.isa code cuts stops calls base μ cont o (some (i, l) : Option (Ext9.Instr × Nat)) s =
      onOk (after Open9.isa code cuts stops calls base μ cont o i s)
        (Ext9.exec i s.core s.memory l) :=
  Eq.trans (Eq.refl _) (Eq.refl _)

attribute [seg_vc9_var]
  wpI_some9 wpN_succ_var wpN_zero_var wpI_some_var wpI_none_var after_nil_var
  Silmaril.X86.SegVC.onOk_jcc8 Silmaril.X86.SegVC.onOk_jcc Silmaril.X86.SegVC.onOk_call
  Silmaril.X86.SegVC.onOk_ok Silmaril.X86.SegVC.onOk_dataFault
  Silmaril.X86.SegVC.onOk_divideError Silmaril.X86.SegVC.onOk_undefinedCondition
  Silmaril.X86.SegVC.onOk_trap mk_write' Silmaril.X86.SegVC.regs_mk
  Silmaril.X86.SegVC.read_mk Silmaril.X86.SegVC.core_regs Silmaril.X86.SegVC.setWidth_32_64
  Silmaril.X86.SegVC.base_reg_value Option.getD_none Option.getD_some BitVec.toNat_ofNat
  Silmaril.X86.State.write_fsBase ne_eq not_false_eq_true Silmaril.X86.State.read_write_other
  Option.isSome_some forall_const Option.some.injEq Silmaril.X86.SegVC.offOf List.lookup_cons
  List.lookup_nil Silmaril.X86.SegVC.retire_some Silmaril.X86.SegVC.retire_none
  Silmaril.X86.SegVC.onOk_retire_storeN Option.map_none Silmaril.X86.Ext.aluStep
  Silmaril.X86.Ext.aluStepR Silmaril.X86.Ext.readRM Silmaril.X86.Ext.writeRM
  Silmaril.X86.Ext.Sz.read Silmaril.X86.Ext.Sz.write Silmaril.X86.Ext.Sz.bits
  Silmaril.X86.Ext.rip_mk Silmaril.X86.Ext.AluOp.resultN Silmaril.X86.Ext.AluOp.flagsN
  Silmaril.X86.Ext.Mem.addr Silmaril.X86.Ext.Index.value Silmaril.X86.Ext.readNarrow
  Silmaril.X86.Ext.writeNarrow Silmaril.X86.Ext.writeRM8 Silmaril.X86.Ext.Narrow.bits
  Silmaril.X86.Ext.Narrow.bytes BitVec.xor_self Silmaril.X86.Ext.Sz.bytes Option.map_id'
  BitVec.setWidth_eq BitVec.shiftLeft_zero BitVec.add_zero and_self
  Silmaril.X86.State.read_write_same Silmaril.X86.Ext.read_with_rip
  Silmaril.X86.Ext.read_mk_regs Silmaril.X86.Ext.read_with_flags Silmaril.X86.Ext.rip_with_flags
  Silmaril.X86.State.write_rip Silmaril.X86.State.write_flags Silmaril.X86.SegVC.eval_logic_e
  Silmaril.X86.SegVC.eval_logic_ne Silmaril.X86.SegVC.eval_logic_le
  Silmaril.X86.SegVC.eval_logic_g Silmaril.X86.SegVC.eval_logic_s
  Silmaril.X86.SegVC.eval_logic_ns Silmaril.X86.SegVC.eval_sub_8 Silmaril.X86.SegVC.eval_sub_32
  Silmaril.X86.SegVC.eval_sub_64 Silmaril.X86.Ext.Cond.afterCmp
  Silmaril.X86.SegVC.add_sub_self_left BitVec.add_assoc Option.map_some true_and and_true
  ite_false ite_true Bool.false_eq_true Bool.cond_true Bool.cond_false Silmaril.X86.SegVC.bound
  implies_true exec9_base exec9_ext8new exec9_imulI_reg open9_exec open9_core open9_mem
  open9_ok open9_upd onOk_retire_pushWord Silmaril.X86.Ext.Count.raw
  Silmaril.X86.Ext.ShiftOp.result

/-- One normalising pass of `seg_vc9_var`: the simp sets `seg_vc9_var` and `seg_vc9_listing`
plus the given lemmas (the simprocs of `seg_vc9_pass` are named here: adding a simproc to a
simp set needs it at the `meta` phase). -/
syntax "seg_vc9_var_pass " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_vc9_var_pass [$ls,*]) => `(tactic|
    (simp (maxSteps := 400000) only [seg_vc9_var, seg_vc9_listing,
        BitVec.reduceSetWidth, BitVec.reduceShiftLeft, BitVec.reduceToNat, BitVec.reduceSignExtend,
        Nat.reduceBEq, BitVec.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, reduceCtorEq,
        reduceIte, $ls,*]))

/-- `seg_vc9_var [lemmas]`: `seg_vc9` over the simp sets. A proof file first adds its
listing's lookup and `nextAt` lemmas to `seg_vc9_listing` locally; segment lemmas take their
offsets and budget as variables with equations. Only the extra `lemmas` are elaborated per
pass. -/
syntax "seg_vc9_var " " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| seg_vc9_var [$ls,*]) => `(tactic|
    (seg_vc9_var_pass [$ls,*]
     repeat (simp only [Silmaril.X86.Ext.exec]; try seg_vc9_var_pass [$ls,*])
     try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Narrow.bits]))

/-! ## Segments with exits -/

section Exits

variable {σ : Type} {I : Isa σ}

/-- Arriving at an exit: the segment's postcondition. -/
theorem nextAt_exits_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∈ exits) :
    nextAt [] (segStops exits Q) μ cont o s = Q s :=
  Silmaril.Proofs.X86.SegVC9.nextAt_exits_mem h

/-- Arriving at an offset that is not an exit: the path continues there. -/
theorem nextAt_exits_not_mem {exits : List Nat} {Q : σ → Prop} {μ : Option Nat}
    {cont : Nat → σ → Prop} {o : Nat} {s : σ} (h : o ∉ exits) :
    nextAt [] (segStops exits Q) μ cont o s = cont o s :=
  Silmaril.Proofs.X86.SegVC9.nextAt_exits_not_mem h

/-- **A segment VC runs inside the code.** For a segment with no cut points, calls or
summaries, on an instance whose decoder rejects `[]`: from a live state at offset `o`, with
the code loaded, `wpN` gives a run whose every step is taken inside the code, to a state
satisfying the exits' postcondition `Q`. -/
theorem seg_runsIn (h0 : I.decode [] = none) {code : List Byte} {L : Listing I}
    {exits : List Nat} {base : Word} {Q : σ → Prop} (hv : L.valid I code = true)
    {μ : Option Nat} {k o : Nat} {s : σ}
    (h : wpN I code L [] (segStops exits Q) [] [] base μ k o s) (hlv : I.live s)
    (hl : Loaded (I.mem s) base code) (hrip : (I.core s).rip = base + BitVec.ofNat 64 o) :
    ∃ t, RunsIn I (InCode I base code.length) s t ∧ Q t :=
  Silmaril.Proofs.X86.SegVC9.seg_runsIn h0 hv h hlv hl hrip

end Exits

theorem open9_decode_nil : Open9.isa.decode [] = none := by decide

/-- `seg_runsIn` on `Open9.isa`. -/
theorem seg_runsIn9 {code : List Byte} {L : Listing Open9.isa} {exits : List Nat} {base : Word}
    {Q : MState → Prop} (hv : L.valid Open9.isa code = true) {μ : Option Nat} {k o : Nat}
    {s : MState} (h : wpN Open9.isa code L [] (segStops exits Q) [] [] base μ k o s)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o) :
    ∃ t, RunsIn Open9.isa (InCode Open9.isa base code.length) s t ∧ Q t :=
  seg_runsIn open9_decode_nil hv h trivial hl hrip

end Silmaril.X86.SegVC9
