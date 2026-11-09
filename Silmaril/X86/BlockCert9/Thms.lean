module

public import Silmaril.X86.BlockCert9.Defs
public import Silmaril.X86.Bir9.Thms
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.FnContract.Thms
import Silmaril.Proofs.X86.BlockCert9.Bridge
import Silmaril.Proofs.X86.BlockCert9.Flags

/-!
# Block certificates on `Open9`: bridge, summaries and function contracts

* `runX_open9`, `Code.run_open9`: **checked block code (an `Ext9` or a Bir9 listing) whose
  run succeeds is a run of `Open9.step`**, with the memory unchanged;
* `runX_eq_runL9`, `runX_eq_runB9`, `Code.run_bir`: a Bir9 listing of `Ext` and `Ext9`
  forms runs as the `Ext9` listing it denotes, and, with the lifter's certificate, as the
  pure Bir9 block. Block VCs are therefore stated over Bir9 terms;
* `blockSub`: a checked block as a summary (`SegVC.Call Open9.isa`) for the segment VC
  generator;
* `FunCert9.total`, `FunCert9.contract`: **a certificate whose VCs hold is a total System V
  `FnContract Open9.isa`**;
* `Frame`, `result_leaf`, `Frame.result`, `popWord_frame`: the System V frame of a leaf
  function and its exit;
* `exec_rip`, `exec_mem`, `execNew_rip`, `execNew_mem`: the per-instruction facts behind the
  bridge;
* `addCarryN_eq_ult`, `eval_l_sub`, `eval_le_sub`, `eval_e_test`: flags after `add`, `cmp`
  and `test`;
* tactics `x9_simp [lemmas]` (evaluate an `Ext9` listing run by unfolding `Ext9.exec`) and
  `bir9_simp [lemmas]`, `bir9_close [lemmas]` (evaluate a Bir9 block run, `runB9`, to its
  final state, then close the register goals).
-/

@[expose] public section

namespace Silmaril.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

/-! ## Instruction facts -/

theorem exec_rip {i : Silmaril.X86.Ext.Instr} (hf : fallsThrough i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len :=
  Silmaril.Proofs.X86.BlockCert9.exec_rip hf h

theorem exec_mem {i : Silmaril.X86.Ext.Instr} (hf : noWrite i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') : mem' = mem :=
  Silmaril.Proofs.X86.BlockCert9.exec_mem hf h

theorem execNew_rip {i : Ext9.New} (hf : fallsThroughNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    s'.rip = next :=
  Silmaril.Proofs.X86.BlockCert9.execNew_rip hf h

theorem execNew_mem {i : Ext9.New} (hf : noWriteNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    mem' = mem :=
  Silmaril.Proofs.X86.BlockCert9.execNew_mem hf h

/-! ## The bridge -/

/-- **The bridge for `Ext9` listings.** -/
theorem runX_open9 {code : List Byte} {base : Word} {L : List (Ext9.Instr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt9 code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runX L m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.X86.BlockCert9.runX_open9 L o m m' hok hl hrip h

/-- **The bridge for block code.** -/
theorem Code.run_open9 {code : List Byte} {base : Word} {c : Code} {o : Nat} {m m' : MState}
    (hok : c.check code o = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : c.run m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.X86.BlockCert9.code_run_open9 hok hl hrip h

@[simp] theorem runX_nil (m : MState) : runX [] m = some m := rfl

theorem runX_cons (i : Ext9.Instr) (l : Nat) (rest : List (Ext9.Instr × Nat)) (m : MState) :
    runX ((i, l) :: rest) m =
      match Ext9.exec i m.core m.memory l with
      | .ok c mem => runX rest ⟨c, mem⟩
      | _ => none := rfl

/-- An `Ext9` listing that is the image of a Bir9 listing runs as it. -/
theorem runX_eq_runL9 {L : List (Bir9.LInstr × Nat)} {L9 : List (Ext9.Instr × Nat)}
    (h : Bir9.toX9L L = some L9) (m : MState) : runX L9 m = Bir9.runL9 L m :=
  Silmaril.Proofs.X86.BlockCert9.runX_eq_runL9 h m

/-- **An `Ext9` listing whose Bir9 preimage lifts runs as the Bir9 block.** -/
theorem runX_eq_runB9 {L : List (Bir9.LInstr × Nat)} {L9 : List (Ext9.Instr × Nat)}
    {b : Bir9.Block} (h9 : Bir9.toX9L L = some L9) (h : Bir9.liftBlock L = some b)
    (m : MState) : runX L9 m = Bir9.runB9 b m := by
  rw [runX_eq_runL9 h9, Bir9.runL9_eq_runB9 h]

/-- A Bir9 block of a certificate runs as its lift. -/
theorem Code.run_bir {L : List (Bir9.LInstr × Nat)} {b : Bir9.Block}
    (h : Bir9.liftBlock L = some b) (m : MState) : (Code.bir L).run m = Bir9.runB9 b m :=
  Bir9.runL9_eq_runB9 h m

/-- **A checked block as a segment summary.** At the block's offset, with the image loaded,
the code checked and its run successful, the machine reaches the block's result. -/
def blockSub (code : List Byte) (base : Word) (b : Blk) (P : MState → Prop) :
    Silmaril.X86.SegVC.Call Open9.isa where
  pre m := Loaded m.memory base code ∧ m.core.rip = base + BitVec.ofNat 64 b.off ∧
    b.code.check code b.off = true ∧ P m ∧ (b.code.run m).isSome
  post m t := b.code.run m = some t
  runs m _ h := by
    obtain ⟨hl, hrip, hok, _, hs⟩ := h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨t, (Code.run_open9 hok hl hrip ht).1, ht⟩

/-! ## Function contracts -/

namespace FunCert9

/-- Arriving at an annotated block with a smaller measure. -/
theorem next_of {F : FunCert9} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (b : Blk) (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (ha : F.ann b.off m0 m') (hμ : F.measure b.off m0 m' < μ) : F.Next Q m0 μ m' :=
  .inr ⟨b, hb, hrip, ha, hμ⟩

/-- From every annotated block, the machine reaches the exit condition. -/
theorem from_block {F : FunCert9} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) {m0 : MState} {b : Blk} {m : MState} (hb : b ∈ F.blocks)
    (ha : F.ann b.off m0 m) (hrip : m.core.rip = F.base + BitVec.ofNat 64 b.off)
    (hl : Loaded m.memory F.base F.code) : ∃ t, Reaches Open9.step m t ∧ Q m0 t :=
  Silmaril.Proofs.X86.BlockCert9.from_block hc hvc m0 _ b m rfl hb ha hrip hl

/-- **Total correctness from a function certificate.** -/
theorem total {F : FunCert9} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open9.isa :=
  Silmaril.Proofs.X86.BlockCert9.total S hentry hc hvc hpre

/-- **The function contract** of a certificate. -/
def contract (F : FunCert9) (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    FnContract Open9.isa :=
  ⟨S, total S hentry hc hvc hpre⟩

end FunCert9

/-! ## Leaf functions -/

/-- The return address popped at the frame's stack pointer. -/
theorem pop_ret {c : State} {mem : Memory} (h : FnContract.AbiEntry c mem) :
    (mem.readBytes (c.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? =
      some (FnContract.retOf c mem) := by
  rw [h.returnAddress]; simp [Silmaril.X86.wordOfBytes?_encodeWords]

theorem Frame.entry {m : MState} (h : FnContract.AbiEntry m.core m.memory) : Frame m m :=
  ⟨h, rfl, rfl, fun _ _ => rfl⟩

/-- The return address at the current stack pointer is the entry's. -/
theorem Frame.pop {m0 m : MState} (h : Frame m0 m) :
    (m.memory.readBytes (m.core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? =
      some (FnContract.retOf m0.core m0.memory) := by
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
    (hpc : t.core.rip = FnContract.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m0.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m0.core.read r)
    (hmem : t.memory = m0.memory) (hpost : S.post m0 t) : S.Result Open9.isa m0 t :=
  ⟨rfl, ⟨hpc, hsp, hcs⟩, by
    show m0.memory.WritesWithin t.memory _
    rw [hmem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _, hpost⟩

/-- The exit of a leaf function from a frame. -/
theorem Frame.result {S : FnContract.Spec MState} {m0 m t : MState} (h : Frame m0 m)
    (hpc : t.core.rip = FnContract.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r)
    (hmem : t.memory = m.memory) (hpost : S.post m0 t) : S.Result Open9.isa m0 t :=
  result_leaf hpc (hsp.trans (by rw [h.rsp])) (fun r hr => (hcs r hr).trans (h.saved r hr))
    (hmem.trans h.mem) hpost

/-- The entry of a leaf spec gives the code loaded and the program counter. -/
theorem leafSpec_entry {base : Word} {code : List Byte} {off : Nat}
    {post : MState → MState → Prop} {m : MState} (h : (leafSpec base code off post).entry m) :
    Loaded m.memory base code ∧ m.core.rip = base + BitVec.ofNat 64 off := h

/-- `popWord` as a lookup of the return address. -/
theorem popWord_eq (s : State) (mem : Memory) :
    Silmaril.X86.popWord s mem =
      ((mem.readBytes (s.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes?).map
        (fun v => (v, s.write .rsp (s.read .rsp + 8#64))) := by
  simp only [Silmaril.X86.popWord]
  cases mem.readBytes (s.read .rsp).toNat 8 <;> simp
  rename_i b; cases Silmaril.X86.wordOfBytes? b <;> rfl

/-- The `ret` of a leaf frame pops the entry's return address. -/
theorem popWord_frame {m0 m : MState} (hf : Frame m0 m) {s : State}
    (hs : s.read .rsp = m.core.read .rsp) :
    Silmaril.X86.popWord s m.memory =
      some (FnContract.retOf m0.core m0.memory, s.write .rsp (s.read .rsp + 8#64)) := by
  rw [popWord_eq, hs, hf.pop]; rfl

/-! ## Flags -/

/-- The carry of an addition is the unsigned wrap test. -/
theorem addCarryN_eq_ult {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.addCarryN x y = (x + y).ult x :=
  Silmaril.Proofs.X86.BlockCert9.addCarryN_eq_ult x y

/-- `jl` after `cmp x, y` is signed less-than. -/
theorem eval_l_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .l = some (x.slt y) :=
  Silmaril.Proofs.X86.BlockCert9.eval_l_sub x y

/-- `jle`/`cmovle` after `cmp x, y` is signed less-or-equal. -/
theorem eval_le_sub {w : Nat} (x y : BitVec (w + 1)) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .le = some (x.sle y) :=
  Silmaril.Proofs.X86.BlockCert9.eval_le_sub x y

/-- `je` after `test r, r` is "`r` is zero". -/
theorem eval_e_test {n : Nat} (x : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) .e =
      some (decide (x = 0#n)) := by
  by_cases h : x = 0#n <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h]

/-! ## Tactics -/

/-- Evaluate an `Ext9` listing run to its final machine state (register operands): unfold
`Code.run`/`runX`, `Ext9.exec`, `Ext.exec` and the operand helpers, then normalise register
reads and writes. Extra lemmas (the listing, branch facts, `popWord_frame`) in brackets. -/
syntax "x9_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| x9_simp [$ls,*]) => `(tactic|
      (simp only [$ls,*, Silmaril.X86.BlockCert9.Code.run, Silmaril.X86.BlockCert9.runX,
        Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext9.execNew,
        Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStep,
        Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Count.raw,
        Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false, ite_true]
       try simp [$ls,*, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]))

/-- Evaluate a Bir9 block run (`Bir9.runB9`) to its final machine state: statements, checks,
conditions on flags, the register map. Extra lemmas (the block's definition, a frame's
`pop`, branch facts) in brackets. -/
syntax "bir9_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- `simp` with the lemmas that read a Bir9 block's final state, plus extra lemmas. -/
syntax "bir9_close" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/- Two passes: the first rewrites conditions on `cmp` flags with `eval_l_sub`/`eval_le_sub`
before the second unfolds `Cond.eval` for the remaining (`add`, `test`) flags. -/
macro_rules
  | `(tactic| bir9_simp [$ls,*]) => `(tactic|
      (simp only [$ls,*, Silmaril.X86.Bir9.runB9, Silmaril.X86.Bir9.Block.run,
        Silmaril.X86.Bir9.runStmts, Silmaril.X86.Bir9.Stmt.run, Silmaril.X86.Bir9.COp.fault,
        Silmaril.X86.Bir9.ofX, Silmaril.X86.Bir9.Env.push, Silmaril.X86.Bir9.E.den,
        Silmaril.X86.Bir9.F.den, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.addFlagsN,
        Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.kNot,
        Silmaril.X86.BlockCert9.addCarryN_eq_ult, Silmaril.X86.BlockCert9.eval_l_sub,
        Silmaril.X86.BlockCert9.eval_le_sub, Option.some.injEq, exists_eq_left',
        List.nil_append, List.cons_append, Silmaril.X86.Bir9.state_read,
        Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.lookupE,
        Silmaril.X86.sysv64_calleeSaved, Silmaril.X86.Ext.AluOp.resultN, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, reduceCtorEq, ite_true, ite_false,
        Silmaril.X86.Ext.isZeroN, List.getD_cons_zero, Option.map_some] <;>
      try simp only [$ls,*, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Bir9.E.den,
        Silmaril.X86.Bir9.F.den, Silmaril.X86.Bir9.ofX, Option.some.injEq, exists_eq_left',
        Silmaril.X86.Bir9.state_read, Silmaril.X86.Bir9.state_rip, Silmaril.X86.Bir9.lookupE,
        reduceCtorEq, ite_true, ite_false, Silmaril.X86.Ext.isZeroN]))

macro_rules
  | `(tactic| bir9_close [$ls,*]) => `(tactic| simp [$ls,*,
      Silmaril.X86.Bir9.lookupE, Silmaril.X86.Bir9.E.den, Silmaril.X86.Bir9.F.den,
      Silmaril.X86.Bir9.EOp.den, Silmaril.X86.Ext.isZeroN, Silmaril.X86.sysv64_calleeSaved,
      Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Bir9.state_read,
      Silmaril.X86.Bir9.state_rip])

end Silmaril.X86.BlockCert9
