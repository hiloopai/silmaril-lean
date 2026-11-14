module

public import Silmaril.Machine.X86.BlockCert.Defs
import Silmaril.Proofs.Machine.X86.BlockCert.Bridge
import Silmaril.Proofs.Machine.X86.BlockCert.Assemble
import Silmaril.Proofs.Machine.X86.BlockCert.Flags

/-!
# Bir block certificates: bridge, summaries and function contracts

* `exec_rip`, `exec_mem`: retired fall-through instructions continue at the next instruction;
  instructions that write no memory keep it;
* `execBlock_open`, `runL_open`: **a checked listing that executes is a run of `Open.step`**
  (one step per instruction), with the memory unchanged;
* `runL_eq_runB`: a lifted listing runs as its Bir block (`liftBlock_sound`), so block VCs are
  stated over pure Bir terms;
* `blockSub`: a checked block as a summary (`SegVC.Call Open.isa`) for the segment VC
  generator `Silmaril.X86.SegVC`;
* `FunCert.from_block`, `FunCert.total`, `FunCert.contract`: **a function certificate whose
  VCs hold is a total System V `FnContract Open.isa`**;
* `Frame`, `result_leaf`, `Frame.result`: the System V frame of a leaf function and its exit;
* `addCarryN_eq_ult`, `eval_l_sub`, `eval_le_sub`: flags after `add` and `cmp`;
* tactics `bir_simp` (evaluate a Bir block run to its final state, `simp only`) and
  `bir_close` (`simp` with the state-reading lemmas), each with optional extra lemmas.
-/

@[expose] public section

namespace Silmaril.Machine.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Lift.Bir (LInstr XState XResult execBlock Block liftBlock)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

theorem exec_rip {i : Silmaril.X86.Ext.Instr} (hf : fallsThrough i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len :=
  Silmaril.Proofs.Machine.X86.BlockCert.exec_rip hf h

theorem exec_mem {i : Silmaril.X86.Ext.Instr} (hf : noWrite i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') : mem' = mem :=
  Silmaril.Proofs.Machine.X86.BlockCert.exec_mem hf h

/-- **The bridge**: a listing checked at the program counter of a loaded image that executes
is a run of the open machine, and the memory is unchanged. -/
theorem execBlock_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {c : State} {x : Silmaril.X86.Lift.Bir.Xmm} {mem : Memory} {s' : XState} {mem' : Memory}
    (hok : listingAt code o L = true) (hl : Loaded mem base code)
    (hrip : c.rip = base + BitVec.ofNat 64 o) (h : execBlock L ⟨c, x⟩ mem = .ok s' mem') :
    Reaches Open.step ⟨c, mem⟩ ⟨s'.core, mem'⟩ ∧ mem' = mem :=
  Silmaril.Proofs.Machine.X86.BlockCert.execBlock_open L o c x mem s' mem' hok hl hrip h

/-- The bridge on machine states. -/
theorem runL_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    Reaches Open.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.Machine.X86.BlockCert.runL_open hok hl hrip h

/-- A lifted listing runs as its Bir block. -/
theorem runL_eq_runB {L : List (LInstr × Nat)} {b : Block} (h : liftBlock L = some b)
    (m : MState) : runL L m = runB b m :=
  Silmaril.Proofs.Machine.X86.BlockCert.runL_eq_runB h m

/-- `Block.reg` by decidable equality. -/
theorem block_reg (b : Block) (r : Reg) : b.reg r = lookupE r b.regs := by
  unfold Block.reg
  generalize b.regs = l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, e⟩ := p
    simp only [List.lookup_cons, lookupE]
    by_cases h : r = a
    · subst h; simp
    · have : (r == a) = false := by simpa using h
      simp [this, h, ih]

@[simp] theorem state_read (b : Block) (env : Silmaril.X86.Lift.Bir.Env) (r : Reg) :
    (b.state env).core.read r = (lookupE r b.regs).den env := by
  simp [Block.state, Silmaril.X86.State.read, block_reg]

@[simp] theorem state_rip (b : Block) (env : Silmaril.X86.Lift.Bir.Env) :
    (b.state env).core.rip = b.rip.den env := rfl

@[simp] theorem state_flags (b : Block) (env : Silmaril.X86.Lift.Bir.Env) :
    (b.state env).core.flags = b.flags.den env := rfl

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
  Silmaril.Proofs.Machine.X86.BlockCert.from_block hc hvc m0 _ b m rfl hb ha hrip hl

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
  Silmaril.Proofs.Machine.X86.BlockCert.total S hentry hc hvc hpre

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

/-! ## Leaf functions -/

/-- The return address popped at the frame's stack pointer. -/
theorem pop_ret {c : State} {mem : Memory} (h : FnContract.AbiEntry c mem) :
    (mem.readBytes (c.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? =
      some (Open.retOf c mem) := by
  rw [h.returnAddress]; simp [Silmaril.X86.wordOfBytes?_encodeWords]

theorem Frame.entry {m : MState} (h : FnContract.AbiEntry m.core m.memory) : Frame m m :=
  ⟨h, rfl, rfl, fun _ _ => rfl⟩

/-- The return address at the current stack pointer is the entry's. -/
theorem Frame.pop {m0 m : MState} (h : Frame m0 m) :
    (m.memory.readBytes (m.core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? =
      some (Open.retOf m0.core m0.memory) := by
  rw [h.mem, h.rsp]; exact pop_ret h.abi

/-- A block that keeps memory, `rsp` and the callee-saved registers keeps the frame. -/
theorem Frame.step {m0 m t : MState} (h : Frame m0 m) (hmem : t.memory = m.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r) :
    Frame m0 t :=
  ⟨h.abi, hmem.trans h.mem, hsp.trans h.rsp, fun r hr => (hcs r hr).trans (h.saved r hr)⟩

/-- **The exit of a leaf function**: back at the entry's return address, `rsp` popped past
it, callee-saved registers and memory as at entry, and the functional postcondition. -/
theorem result_leaf {S : FnContract.Spec MState} {m0 t : MState}
    (hpc : t.core.rip = Open.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m0.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m0.core.read r)
    (hmem : t.memory = m0.memory) (hpost : S.post m0 t) : S.Result Open.isa m0 t :=
  ⟨rfl, ⟨hpc, hsp, hcs⟩, by
    show m0.memory.WritesWithin t.memory _
    rw [hmem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _, hpost⟩

/-- The exit of a leaf function from a frame. -/
theorem Frame.result {S : FnContract.Spec MState} {m0 m t : MState} (h : Frame m0 m)
    (hpc : t.core.rip = Open.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r)
    (hmem : t.memory = m.memory) (hpost : S.post m0 t) : S.Result Open.isa m0 t :=
  result_leaf hpc (hsp.trans (by rw [h.rsp])) (fun r hr => (hcs r hr).trans (h.saved r hr))
    (hmem.trans h.mem) hpost

/-- The entry of a leaf spec gives the code loaded and the program counter. -/
theorem leafSpec_entry {base : Word} {code : List Byte} {off : Nat}
    {post : MState → MState → Prop} {m : MState} (h : (leafSpec base code off post).entry m) :
    Loaded m.memory base code ∧ m.core.rip = base + BitVec.ofNat 64 off := h

/-! ## Flags -/

/-- The carry of an addition is the unsigned wrap test. -/
theorem addCarryN_eq_ult {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.addCarryN x y = (x + y).ult x :=
  Silmaril.Proofs.Machine.X86.BlockCert.addCarryN_eq_ult x y

/-- `jl` after `cmp x, y` is signed less-than. -/
theorem eval_l_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .l = some (x.slt y) :=
  Silmaril.Proofs.Machine.X86.BlockCert.eval_l_sub x y

/-- `jle`/`cmovle` after `cmp x, y` is signed less-or-equal. -/
theorem eval_le_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .le = some (x.sle y) :=
  Silmaril.Proofs.Machine.X86.BlockCert.eval_le_sub x y

/-! ## Tactics -/

/-- Evaluate a Bir block run (`runB`) to its final machine state: statements, conditions on
flags, the register map. Extra lemmas (the block's definition, a frame's `pop`) in brackets. -/
syntax "bir_simp" : tactic
/-- `bir_simp` with extra lemmas. -/
syntax "bir_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- `simp` with the lemmas that read a Bir block's final state. -/
syntax "bir_close" : tactic
/-- `bir_close` with extra lemmas. -/
syntax "bir_close" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/- Two passes: the first rewrites conditions on `cmp` flags with `eval_l_sub`/`eval_le_sub`
before the second unfolds `Cond.eval` for the remaining (`add`, `test`) flags. -/
macro_rules
  | `(tactic| bir_simp) => `(tactic| bir_simp [Silmaril.Machine.X86.BlockCert.runB])
  | `(tactic| bir_simp [$ls,*]) => `(tactic|
      simp only [$ls,*, Silmaril.Machine.X86.BlockCert.runB,
        Silmaril.X86.Lift.Bir.Block.run, Silmaril.X86.Lift.Bir.runStmts,
        Silmaril.X86.Lift.Bir.Stmt.run, Silmaril.Machine.X86.BlockCert.xs,
        Silmaril.Machine.X86.BlockCert.ofX, Silmaril.X86.Lift.Bir.Env.push,
        Silmaril.X86.Lift.Bir.E.den, Silmaril.X86.Lift.Bir.F.den, Silmaril.X86.Ext.AluOp.flagsN,
        Silmaril.X86.Ext.addFlagsN, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
        Silmaril.Machine.X86.BlockCert.addCarryN_eq_ult, Silmaril.Machine.X86.BlockCert.eval_l_sub,
        Silmaril.Machine.X86.BlockCert.eval_le_sub, Option.some.injEq, exists_eq_left',
        List.nil_append, List.cons_append, Silmaril.Machine.X86.BlockCert.state_read,
        Silmaril.Machine.X86.BlockCert.state_rip, Silmaril.Machine.X86.BlockCert.lookupE,
        Silmaril.X86.sysv64_calleeSaved, Silmaril.X86.Ext.AluOp.resultN, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, reduceCtorEq, ite_true, ite_false,
        Silmaril.X86.Ext.isZeroN, List.getD_cons_zero, Option.map_some] <;>
      try simp only [$ls,*, Silmaril.X86.Ext.Cond.eval, Silmaril.Machine.X86.BlockCert.runB,
        Silmaril.X86.Lift.Bir.Block.run, Silmaril.X86.Lift.Bir.runStmts,
        Silmaril.X86.Lift.Bir.Stmt.run, Silmaril.Machine.X86.BlockCert.xs,
        Silmaril.Machine.X86.BlockCert.ofX, Silmaril.X86.Lift.Bir.Env.push,
        Silmaril.X86.Lift.Bir.E.den, Silmaril.X86.Lift.Bir.F.den, Silmaril.X86.Ext.AluOp.flagsN,
        Silmaril.X86.Ext.addFlagsN, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
        Silmaril.Machine.X86.BlockCert.addCarryN_eq_ult, Silmaril.Machine.X86.BlockCert.eval_l_sub,
        Silmaril.Machine.X86.BlockCert.eval_le_sub, Option.some.injEq, exists_eq_left',
        List.nil_append, List.cons_append, Silmaril.Machine.X86.BlockCert.state_read,
        Silmaril.Machine.X86.BlockCert.state_rip, Silmaril.Machine.X86.BlockCert.lookupE,
        Silmaril.X86.sysv64_calleeSaved, Silmaril.X86.Ext.AluOp.resultN, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, reduceCtorEq, ite_true, ite_false,
        Silmaril.X86.Ext.isZeroN, List.getD_cons_zero, Option.map_some])

macro_rules
  | `(tactic| bir_close) => `(tactic| bir_close [Silmaril.Machine.X86.BlockCert.lookupE])
  | `(tactic| bir_close [$ls,*]) => `(tactic| simp [$ls,*,
      Silmaril.Machine.X86.BlockCert.lookupE, Silmaril.X86.Lift.Bir.E.den,
      Silmaril.X86.Lift.Bir.F.den, Silmaril.X86.Ext.isZeroN, Silmaril.X86.sysv64_calleeSaved,
      Silmaril.X86.Ext.AluOp.resultN, Silmaril.Machine.X86.BlockCert.state_read,
      Silmaril.Machine.X86.BlockCert.state_rip])

end Silmaril.Machine.X86.BlockCert
