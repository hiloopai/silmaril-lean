module

public import Silmaril.Machine.X86.BlockCert9.Defs
public import Silmaril.Machine.X86.BlockCert.Thms
public import Silmaril.Machine.X86.Open9.Thms
import Silmaril.Proofs.Machine.X86.BlockCert9.Bridge

/-!
# `Ext9` block certificates: bridge and function contracts

* `runX_open9`, `Code.run_open9`: **a checked block (Bir or `Ext9` listing) whose run succeeds
  is a run of `Open9.step`**, with the memory unchanged;
* `FunCert9.total`, `FunCert9.contract`: a certificate whose VCs hold is a total System V
  `FnContract Open9.isa`;
* `Result.toOpen9`, `result_leaf9`, `Frame.result9`: the System V exit of a leaf function on
  `Open9.isa` (the results of `BlockCert`, read on the extended machine);
* `execNew_rip`, `execNew_mem`: the per-instruction facts behind the bridge;
* `popWord_frame`, `eval_e_test`: the `ret` of a leaf frame, and `test r, r; je`;
* tactic `x9_simp [lemmas]`: evaluate an `Ext9` listing run (`Code.run`/`runX`) on register
  operands to its final machine state, by unfolding `Ext.exec`/`Ext9.execNew`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

theorem execNew_rip {i : Ext9.New} (hf : fallsThroughNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    s'.rip = next :=
  Silmaril.Proofs.Machine.X86.BlockCert9.execNew_rip hf h

theorem execNew_mem {i : Ext9.New} (hf : noWriteNew i = true) {s : State} {mem : Memory}
    {next : Word} {s' : State} {mem' : Memory} (h : Ext9.execNew i s mem next = .ok s' mem') :
    mem' = mem :=
  Silmaril.Proofs.Machine.X86.BlockCert9.execNew_mem hf h

/-- **The bridge for `Ext9` listings.** -/
theorem runX_open9 {code : List Byte} {base : Word} {L : List (Ext9.Instr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt9 code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runX L m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.Machine.X86.BlockCert9.runX_open9 L o m m' hok hl hrip h

/-- **The bridge for block code.** -/
theorem Code.run_open9 {code : List Byte} {base : Word} {c : Code} {o : Nat} {m m' : MState}
    (hok : c.check code o = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : c.run m = some m') :
    Reaches Open9.step m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.Machine.X86.BlockCert9.code_run_open9 hok hl hrip h

@[simp] theorem runX_nil (m : MState) : runX [] m = some m := rfl

theorem runX_cons (i : Ext9.Instr) (l : Nat) (rest : List (Ext9.Instr × Nat)) (m : MState) :
    runX ((i, l) :: rest) m =
      match Ext9.exec i m.core m.memory l with
      | .ok c mem => runX rest ⟨c, mem⟩
      | _ => none := rfl

namespace FunCert9

/-- Arriving at an annotated block with a smaller measure. -/
theorem next_of {F : FunCert9} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (b : Blk) (hb : b ∈ F.blocks) (hrip : m'.core.rip = F.base + BitVec.ofNat 64 b.off)
    (ha : F.ann b.off m0 m') (hμ : F.measure b.off m0 m' < μ) : F.Next Q m0 μ m' :=
  .inr ⟨b, hb, hrip, ha, hμ⟩

/-- **Total correctness from a function certificate over `Ext9`.** -/
theorem total {F : FunCert9} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open9.isa :=
  Silmaril.Proofs.Machine.X86.BlockCert9.total S hentry hc hvc hpre

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

/-- A call result on the `Ext8` open machine is one on the `Ext9` open machine. -/
theorem Result.toOpen9 {S : FnContract.Spec MState} {s t : MState}
    (h : S.Result Open.isa s t) : S.Result Open9.isa s t :=
  ⟨h.silent, h.abi, h.frame, h.post⟩

/-- The exit of a leaf function on `Open9.isa`. -/
theorem result_leaf9 {S : FnContract.Spec MState} {m0 t : MState}
    (hpc : t.core.rip = Open.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m0.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m0.core.read r)
    (hmem : t.memory = m0.memory) (hpost : S.post m0 t) : S.Result Open9.isa m0 t :=
  Result.toOpen9 (BlockCert.result_leaf hpc hsp hcs hmem hpost)

/-- The exit of a leaf function from a frame, on `Open9.isa`. -/
theorem Frame.result9 {S : FnContract.Spec MState} {m0 m t : MState} (h : BlockCert.Frame m0 m)
    (hpc : t.core.rip = Open.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r)
    (hmem : t.memory = m.memory) (hpost : S.post m0 t) : S.Result Open9.isa m0 t :=
  Result.toOpen9 (h.result hpc hsp hcs hmem hpost)

/-- `popWord` as a lookup of the return address. -/
theorem popWord_eq (s : State) (mem : Memory) :
    Silmaril.X86.popWord s mem =
      ((mem.readBytes (s.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes?).map
        (fun v => (v, s.write .rsp (s.read .rsp + 8#64))) := by
  simp only [Silmaril.X86.popWord]
  cases mem.readBytes (s.read .rsp).toNat 8 <;> simp
  rename_i b; cases Silmaril.X86.wordOfBytes? b <;> rfl

/-- The `ret` of a leaf frame pops the entry's return address. -/
theorem popWord_frame {m0 m : MState} (hf : BlockCert.Frame m0 m) {s : State}
    (hs : s.read .rsp = m.core.read .rsp) :
    Silmaril.X86.popWord s m.memory =
      some (Open.retOf m0.core m0.memory, s.write .rsp (s.read .rsp + 8#64)) := by
  rw [popWord_eq, hs, hf.pop]; rfl

/-- `je` after `test r, r` is "`r` is zero". -/
theorem eval_e_test {n : Nat} (x : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) .e =
      some (decide (x = 0#n)) := by
  by_cases h : x = 0#n <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h]

/-- Evaluate an `Ext9` listing run to its final machine state (register operands): unfold
`Code.run`/`runX`, `Ext9.exec`, `Ext.exec` and the operand helpers, then normalise register
reads and writes. Extra lemmas (the listing, branch facts, `popWord_frame`) in brackets. -/
syntax "x9_simp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| x9_simp [$ls,*]) => `(tactic|
      (simp only [$ls,*, Silmaril.Machine.X86.BlockCert9.Code.run, Silmaril.Machine.X86.BlockCert9.runX,
        Silmaril.Machine.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.Machine.X86.Ext9.execNew,
        Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStep,
        Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Count.raw,
        Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false, ite_true]
       try simp [$ls,*, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read]))

end Silmaril.Machine.X86.BlockCert9
