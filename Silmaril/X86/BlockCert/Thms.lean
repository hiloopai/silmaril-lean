module

public import Silmaril.X86.BlockCert.Defs
public import Silmaril.X86.BlockCert9.Thms
public import Silmaril.X86.Open.Thms
import Silmaril.Proofs.X86.BlockCert.Bridge
import Silmaril.Proofs.X86.BlockCert.Assemble

/-!
# Bir9 block certificates on `Open`: bridge, summaries and function contracts

* `exec_rip`, `exec_mem` (`BlockCert9`'s): retired fall-through instructions continue at the
  next instruction; instructions that write no memory keep it;
* `execBlock_open`, `runL_open`: **a checked listing that executes is a run of `Open.step`**
  (one step per instruction), with the memory unchanged;
* `runL_eq_runB`: a lifted listing runs as its Bir9 block (`Bir9.liftBlock_sound`), so block
  VCs are stated over pure Bir9 terms;
* `blockSub`: a checked block as a summary (`SegVC.Call Open.isa`) for the segment VC
  generator `Silmaril.X86.SegVC`;
* `FunCert.from_block`, `FunCert.total`, `FunCert.contract`: **a function certificate whose
  VCs hold is a total System V `FnContract Open.isa`**;
* `Frame`, `Frame.step`, `Frame.pop`: the System V frame of a leaf function, and
  `addCarryN_eq_ult`, `eval_l_sub`, `eval_le_sub`: flags after `add` and `cmp` (all
  `BlockCert9`'s, re-exported here); `result_leaf`, `Frame.result_open`: its exit on `Open`;
* tactics `bir_simp` (evaluate a Bir9 block run to its final state, `simp only`) and
  `bir_close` (`simp` with the state-reading lemmas), each with optional extra lemmas.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (LInstr XState XResult execBlock Block liftBlock)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

export Silmaril.X86.BlockCert9 (exec_rip exec_mem)

/-- **The bridge**: a listing checked at the program counter of a loaded image that executes
is a run of the open machine, and the memory is unchanged. -/
theorem execBlock_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {c : State} {x : Silmaril.X86.Bir9.Xmm} {mem : Memory} {s' : XState} {mem' : Memory}
    (hok : listingAt code o L = true) (hl : Loaded mem base code)
    (hrip : c.rip = base + BitVec.ofNat 64 o) (h : execBlock L ⟨c, x⟩ mem = .ok s' mem') :
    Reaches Open.step ⟨c, mem⟩ ⟨s'.core, mem'⟩ ∧ mem' = mem :=
  Silmaril.Proofs.X86.BlockCert.execBlock_open L o c x mem s' mem' hok hl hrip h

/-- The bridge on machine states. -/
theorem runL_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    Reaches Open.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.X86.BlockCert.runL_open hok hl hrip h

/-- A lifted listing runs as its Bir9 block. -/
theorem runL_eq_runB {L : List (LInstr × Nat)} {b : Block} (h : liftBlock L = some b)
    (m : MState) : runL L m = runB b m :=
  Silmaril.Proofs.X86.BlockCert.runL_eq_runB h m

/-- **A checked block as a segment summary.** At the block's offset, with the image loaded,
the listing checked and its run successful, the machine reaches the block's result. -/
def blockSub (code : List Byte) (base : Word) (b : Blk) (P : MState → Prop) :
    Silmaril.X86.SegVC.Call Open.isa where
  pre m := Loaded m.memory base code ∧ m.core.rip = base + BitVec.ofNat 64 b.off ∧
    listingAt code b.off b.instrs = true ∧ P m ∧ (runL b.instrs m).isSome
  post m t := runL b.instrs m = some t
  runs m _ h := by
    obtain ⟨hl, hrip, hok, _, hs⟩ := h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨t, (runL_open hok hl hrip ht).1, ht⟩

namespace FunCert

/-- From every annotated block, the machine reaches the exit condition. -/
theorem from_block {F : FunCert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) {m0 : MState} {b : Blk} {m : MState} (hb : b ∈ F.blocks)
    (ha : F.ann b.off m0 m) (hrip : m.core.rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded m.memory F.base F.code) : ∃ t, Reaches Open.step m t ∧ Q m0 t :=
  Silmaril.Proofs.X86.BlockCert.from_block hc hvc m0 _ b m rfl hb ha hrip hl

/-- Arriving at an annotated block with a smaller measure. -/
theorem next_of {F : FunCert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat} (b : Blk)
    (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (ha : F.ann b.off m0 m') (hμ : F.measure b.off m0 m' < μ) : F.Next Q m0 μ m' :=
  .inr ⟨b, hb, hrip, ha, hμ⟩

/-- The VC from the VCs of the blocks. -/
theorem vc_of_blocks {F : FunCert} {Q : MState → MState → Prop}
    (h : ∀ b ∈ F.blocks, F.BlockVC Q b) : F.VC Q :=
  fun b hb => h b hb

/-- **Total correctness from a function certificate.** -/
theorem total {F : FunCert} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Silmaril.Proofs.X86.BlockCert.total S hentry hc hvc hpre

/-- **The function contract** of a certificate. -/
def contract (F : FunCert) (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    FnContract Open.isa :=
  ⟨S, total S hentry hc hvc hpre⟩

end FunCert

/-! ## Leaf functions and flags (`BlockCert9`'s) -/

export Silmaril.X86.BlockCert9 (pop_ret Frame.entry Frame.pop Frame.step leafSpec_entry
  popWord_eq popWord_frame addCarryN_eq_ult eval_l_sub eval_le_sub eval_e_test)

/-- **The exit of a leaf function** on `Open`: back at the entry's return address, `rsp`
popped past it, callee-saved registers and memory as at entry, and the functional
postcondition (`BlockCert9.result_leaf` is the same on `Open9`). -/
theorem result_leaf {S : FnContract.Spec MState} {m0 t : MState}
    (hpc : t.core.rip = FnContract.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m0.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m0.core.read r)
    (hmem : t.memory = m0.memory) (hpost : S.post m0 t) : S.Result Open.isa m0 t :=
  ⟨rfl, ⟨hpc, hsp, hcs⟩, by
    show m0.memory.WritesWithin t.memory _
    rw [hmem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _, hpost⟩

/-- The exit of a leaf function from a frame, on `Open` (`Frame.result` is the same on
`Open9`). -/
theorem Frame.result_open {S : FnContract.Spec MState} {m0 m t : MState} (h : Frame m0 m)
    (hpc : t.core.rip = FnContract.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r)
    (hmem : t.memory = m.memory) (hpost : S.post m0 t) : S.Result Open.isa m0 t :=
  result_leaf hpc (hsp.trans (by rw [h.rsp])) (fun r hr => (hcs r hr).trans (h.saved r hr))
    (hmem.trans h.mem) hpost
export Silmaril.X86.Bir9 (block_reg state_read state_rip state_flags)

/-! ## Tactics -/

/-- Evaluate a Bir9 block run (`runB`) to its final machine state: statements, conditions on
flags, the register map. Extra lemmas (the block's definition, a frame's `pop`) in brackets. -/
syntax "bir_simp" : tactic
/-- `bir_simp` with extra lemmas. -/
syntax "bir_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- `simp` with the lemmas that read a Bir9 block's final state. -/
syntax "bir_close" : tactic
/-- `bir_close` with extra lemmas. -/
syntax "bir_close" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/- Two passes: the first rewrites conditions on `cmp` flags with `eval_l_sub`/`eval_le_sub`
before the second unfolds `Cond.eval` for the remaining (`add`, `test`) flags. -/
macro_rules
  | `(tactic| bir_simp) => `(tactic| bir_simp [Silmaril.X86.BlockCert.runB])
  | `(tactic| bir_simp [$ls,*]) => `(tactic|
      simp only [$ls,*, Silmaril.X86.BlockCert.runB,
        Silmaril.X86.Bir9.Block.run, Silmaril.X86.Bir9.runStmts,
        Silmaril.X86.Bir9.Stmt.run, Silmaril.X86.BlockCert.xs,
        Silmaril.X86.Bir9.ofX, Silmaril.X86.Bir9.Env.push,
        Silmaril.X86.Bir9.E.den, Silmaril.X86.Bir9.F.den, Silmaril.X86.Ext.AluOp.flagsN,
        Silmaril.X86.Ext.addFlagsN, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
        Silmaril.X86.BlockCert9.addCarryN_eq_ult, Silmaril.X86.BlockCert9.eval_l_sub,
        Silmaril.X86.BlockCert9.eval_le_sub, Option.some.injEq, exists_eq_left',
        List.nil_append, List.cons_append, Silmaril.X86.Bir9.state_read,
        Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.lookupE,
        Silmaril.X86.sysv64_calleeSaved, Silmaril.X86.Ext.AluOp.resultN, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, reduceCtorEq, ite_true, ite_false,
        Silmaril.X86.Ext.isZeroN, List.getD_cons_zero, Option.map_some] <;>
      try simp only [$ls,*, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.BlockCert.runB,
        Silmaril.X86.Bir9.Block.run, Silmaril.X86.Bir9.runStmts,
        Silmaril.X86.Bir9.Stmt.run, Silmaril.X86.BlockCert.xs,
        Silmaril.X86.Bir9.ofX, Silmaril.X86.Bir9.Env.push,
        Silmaril.X86.Bir9.E.den, Silmaril.X86.Bir9.F.den, Silmaril.X86.Ext.AluOp.flagsN,
        Silmaril.X86.Ext.addFlagsN, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
        Silmaril.X86.BlockCert9.addCarryN_eq_ult, Silmaril.X86.BlockCert9.eval_l_sub,
        Silmaril.X86.BlockCert9.eval_le_sub, Option.some.injEq, exists_eq_left',
        List.nil_append, List.cons_append, Silmaril.X86.Bir9.state_read,
        Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.lookupE,
        Silmaril.X86.sysv64_calleeSaved, Silmaril.X86.Ext.AluOp.resultN, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, reduceCtorEq, ite_true, ite_false,
        Silmaril.X86.Ext.isZeroN, List.getD_cons_zero, Option.map_some])

macro_rules
  | `(tactic| bir_close) => `(tactic| bir_close [Silmaril.X86.Bir9.lookupE])
  | `(tactic| bir_close [$ls,*]) => `(tactic| simp [$ls,*,
      Silmaril.X86.Bir9.lookupE, Silmaril.X86.Bir9.E.den,
      Silmaril.X86.Bir9.F.den, Silmaril.X86.Ext.isZeroN, Silmaril.X86.sysv64_calleeSaved,
      Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Bir9.state_read,
      Silmaril.X86.Bir9.state_rip])

end Silmaril.X86.BlockCert
