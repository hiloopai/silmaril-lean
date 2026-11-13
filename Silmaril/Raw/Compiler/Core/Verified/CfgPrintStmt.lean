module

public import Silmaril.Compiler.Core.Verified.CfgPrint.Defs
public import Silmaril.Compiler.Core.Verified.StateLoopStep.Defs
public import Silmaril.Compiler.Core.Verified.PrintfState.Defs

/-! # An open integer print statement at a CFG boundary

The operand is computed from the current slot registers, then printed. Only the
slots and the result register must lie below 10: expression temporaries may overlap
PrintLink's scratch registers, which its prologue initializes after evaluation.
The source and target paths preserve the slot relation and append the same output.
The caller supplies the remaining output and Core allocation budgets.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPrintStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term values)
open StateMem (Local Inv Defined defsOf)
open StateLoopStep (Layout Registers)
open Spec (coreBytes)

/-- The literal parts surrounding one decimal operand. -/
def parts (d : Nat) (pre suf : List Char) : List CfgPrint.Part :=
  pre.map (fun c => .byte c.toNat.toUInt8) ++ .dec d :: suf.map (fun c => .byte c.toNat.toUInt8)

/-- Runtime operand evaluation followed by output; no slot value is inspected by the compiler. -/
def ops (regs : Key → Mir.Reg) (d : Nat) (pre suf : List Char) (t : Term) : List (Lir.Op Mir.Reg) :=
  StateExprLir.ops regs d t ++ CfgPrint.ops (parts d pre suf)

/-- Worst-case output of one signed-int conversion. -/
def room (pre suf : List Char) : Nat := pre.length + 11 + suf.length

/-- The target items denoted by the statement at its current runtime value. -/
def items (pre suf : List Char) (n : Int) : List PrintLink.Item :=
  pre.map (fun c => .byte c.toNat.toUInt8) ++ .int n :: suf.map (fun c => .byte c.toNat.toUInt8)

theorem chars_denote (fr : Lir.Frame Mir.Reg) (cs : List Char)
    {ps : List CfgPrint.Part} {is : List PrintLink.Item} (h : CfgPrint.Denote fr ps is) :
    CfgPrint.Denote fr (cs.map (fun c => .byte c.toNat.toUInt8) ++ ps)
      (cs.map (fun c => .byte c.toNat.toUInt8) ++ is) := by
  induction cs with
  | nil => exact h
  | cons c cs ih => exact .byte _ ih

theorem parts_denote {fr : Lir.Frame Mir.Reg} {d : Nat} {n : Int} (hd : d < 10)
    (hv : fr.get d = some (BitVec.ofInt 64 n)) (pre suf : List Char) :
    CfgPrint.Denote fr (parts d pre suf) (items pre suf n) := by
  apply chars_denote
  exact .dec hd hv (by simpa using chars_denote fr suf CfgPrint.Denote.nil)

theorem items_room (pre suf : List Char) (n : Int) :
    ((items pre suf n).map PrintLink.Item.room).sum = room pre suf := by
  have chars : ∀ cs : List Char,
      ((cs.map (fun c => PrintLink.Item.byte c.toNat.toUInt8)).map PrintLink.Item.room).sum = cs.length := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, PrintLink.Item.room, List.length_cons]
      rw [ih]
      omega
  simp only [items, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    PrintLink.Item.room, chars, room]
  omega

theorem items_small {n : Int} (hn : ConvInt.IsInt n) (pre suf : List Char) :
    ∀ it ∈ items pre suf n, it.small = true := by
  have hsmall : n.natAbs < 10 ^ 10 := by
    rcases hn with ⟨lo, hi⟩
    omega
  intro it hit
  simp only [items, List.mem_append, List.mem_cons] at hit
  rcases hit with hit | rfl | hit
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hit
    rfl
  · simpa [PrintLink.Item.small] using hsmall
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hit
    rfl

theorem chars_render (cs : List Char) :
    PrintLink.render (cs.map (fun c => .byte c.toNat.toUInt8)) = coreBytes (String.ofList cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simpa [PrintLink.render, PrintLink.Item.render, coreBytes] using
      congrArg (List.cons c.toNat.toUInt8) ih

theorem items_render (pre suf : List Char) (n : Int) :
    coreBytes (PrintfIntStmt.text pre suf n) = PrintLink.render (items pre suf n) := by
  simp only [items, PrintLink.render, List.flatMap_append, List.flatMap_cons]
  change coreBytes (PrintfIntStmt.text pre suf n) =
    PrintLink.render (pre.map (fun c => .byte c.toNat.toUInt8)) ++
      (PrintLink.Item.render (.int n) ++ PrintLink.render (suf.map (fun c => .byte c.toNat.toUInt8)))
  rw [chars_render, chars_render]
  simp [PrintfIntStmt.text, PrintLink.Item.render, coreBytes]

/-- The entire target print statement preserves every local register below `d`. -/
theorem ops_exec {regs : Key → Mir.Reg} {d : Nat} {σ : Key → Int} {t : Term}
    {fr : Lir.Frame Mir.Reg} {mem : Lir.Memory} {s : String} (pre suf : List Char)
    (hd : d < 10) (ok : t.Ok σ)
    (reads : ∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)))
    (out : CfgOut.OutMem mem s)
    (fit : PrintLink.outBase + (coreBytes s).length + room pre suf ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
    ∃ fr' mem', Lir.execOps (ops regs d pre suf t) fr mem = some (fr', mem') ∧
      CfgOut.OutMem mem' (s ++ PrintfIntStmt.text pre suf (t.val σ)) ∧
      ∀ r : Nat, r < d → fr'.get r = fr.get r := by
  obtain ⟨fr1, w, hx, hv, hw, keep⟩ := StateExprLir.ops_exec regs σ t d fr mem reads
  have hv' : fr1.get d = some (BitVec.ofInt 64 (t.val σ)) := by rw [← hw ok]; exact hv
  obtain ⟨fr2, mem2, hx2, out2, keep2⟩ := CfgPrint.ops_exec out (parts_denote hd hv' pre suf)
    (items_small (t.int_of_ok ok) pre suf) (by rw [items_room]; exact fit) (items_render pre suf _)
  refine ⟨fr2, mem2, ?_, out2, fun r hr => (keep2 r (by omega)).trans (keep r hr)⟩
  simp only [ops, Lir.execOps_append, hx, Option.bind_some]
  exact hx2

/-- One open printf in both machines. Overflow is a source UB escape; a defined
operand prints its runtime value, preserves all slots and consumes one allocation allowance. -/
theorem step {file : Program} {labels : Labels} {lits : List (Sym × List Int)}
    {e : EE} {pre suf : List Char} {t : Term}
    (shape : PrintfIntStmt.printfTerm file lits ∅ e = some (pre, suf, t))
    {env : Env} {m : Mem.Concrete.State} {locals : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m locals ds)
    (early : PrintfState.Earlier m locals) (defined : Defined ds t = true)
    (lit : StrLit.LitEnv lits env m) (dead : PrintfStmt.DeadBelow m)
    (n : Nat) (alloc : 64 + 32 * (n + 1 : Nat) ≤ m.lastAddress)
    {regs : Key → Mir.Reg} {d : Nat} (layout : Layout regs d locals) (hd : d < 10)
    {fr : Lir.Frame Mir.Reg} (matched : Registers regs ds fr)
    {mem : Lir.Memory} (out : CfgOut.OutMem mem m.stdout)
    (fit : PrintLink.outBase + (coreBytes m.stdout).length + room pre suf ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (ann : List Annot) (F : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr (.mk ann (.bound e)) env, F, m⟩ ∨
      ∃ m' fr' mem', t.Ok (values (defsOf ds)) ∧
        ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, F, m⟩
          ⟨.value (.loaded (.specified (.integer
            (PrintfIntStmt.text pre suf (t.val (values (defsOf ds)))).length))), F, m'⟩ ∧
        Lir.execOps (ops regs d pre suf t) fr mem = some (fr', mem') ∧
        m'.stdout = m.stdout ++ PrintfIntStmt.text pre suf (t.val (values (defsOf ds))) ∧
        CfgOut.OutMem mem' m'.stdout ∧ Inv env m' locals ds ∧ Registers regs ds fr' ∧
        PrintfState.Earlier m' locals ∧ StrLit.LitEnv lits env m' ∧ PrintfStmt.DeadBelow m' ∧
        64 + 32 * (n : Int) ≤ m'.lastAddress := by
  by_cases ok : t.Ok (values (defsOf ds))
  · obtain ⟨m', src, stdout, inv', early', lit', dead', frontier⟩ :=
      PrintfState.printf_reaches shape inv early defined ok (Fold.EnvSub.empty env)
        lit dead (by omega) ann F
    obtain ⟨fr', mem', tgt, out', keep⟩ := ops_exec pre suf hd ok
      (StateLoopStep.reads layout inv matched defined) out fit
    refine .inr ⟨m', fr', mem', ok, src, tgt, stdout, stdout.symm ▸ out', inv', ?_,
      early', lit', dead', ?_⟩
    · intro q a ha
      obtain ⟨_, l, hl, key, _⟩ := inv.defs q a ha
      rw [keep _ (by rw [← key]; exact layout.below l hl)]
      exact matched q a ha
    · push_cast at alloc
      omega
  · exact .inl (StateStmt.fails_overflows
      (PrintfIntStmt.printfTerm_fails shape ok (inv.locs defined) ann F))

end Silmaril.Compile.Core.Verified.CfgPrintStmt
