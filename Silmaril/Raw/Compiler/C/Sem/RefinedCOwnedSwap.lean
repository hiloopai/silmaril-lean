module

public import Silmaril.Compiler.C.Sem.C1Call.Defs
public import Silmaril.Compiler.C.Sem.RefinedCOwnedByte.Defs
import Mathlib.Tactic

/-! Typed-Ail execution of a two-cell unsigned-byte swap. Addresses are flat C1
addresses; the disjoint ownership footprint, rather than byte observations alone,
supplies exclusivity. The syntax is authored, not a C parser certificate. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedSwap
open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion ConcreteResources

abbrev byteType := RefinedCOwnedByte.byteType
abbrev pointerType := RefinedCOwnedByte.pointerType

def sym (n : Nat) : Sym := ⟨⟨[]⟩, n, .id (if n = 0 then "p" else if n = 1 then "q" else "tmp")⟩
def localExpr (n : Nat) (ptr : Bool) : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩
    (if ptr then .mk [] (.pointer ⟨false, false, false⟩ byteType) else byteType) false)
    [] .unknown (.ident (sym n))
def readLocal (n : Nat) (ptr : Bool) : TypedExpression :=
  .mk (.rvalue (if ptr then .pointer ⟨false, false, false⟩ byteType
    else .basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown (.rvalue (localExpr n ptr))
def cell (n : Nat) : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ byteType false) [] .unknown (.unary .indirection (readLocal n true))
def readCell (n : Nat) : TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown (.rvalue (cell n))
def assign (n : Nat) (r : TypedExpression) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) (.expr
    (.mk (.rvalue (.basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown (.assign (cell n) r)))
def declaration : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) (.declaration [(sym 2, some (readCell 0))])
def body : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) (.block []
    [declaration, assign 0 (readCell 1), assign 1 (readLocal 2 false)])
def function : C1.FunDef :=
  ⟨⟨[(0, pointerType), (1, pointerType)], .void, body,
    (({} : Std.HashMap Nat CType).insert 0 pointerType).insert 1 pointerType |>.insert 2 (.int 1 false)⟩, [], {}⟩
def fSym : Sym := ⟨⟨[]⟩, 3, .id "swap_owned_bytes"⟩
def program : C1.Prog :=
  ⟨({} : Std.HashMap Nat C1.FunDef).insert 3 function, {}, {}, [], ⟨∅, ∅⟩, none, {}, {},
    4096, 4096, 4096⟩

def callee (initial : C1.Env) (a b : Nat) : C1.Env :=
  ⟨(({} : Std.HashMap Nat Int).insert 0 a).insert 1 b, {}, initial.mem, initial.out⟩
def updated (initial : C1.Env) (m : C1.Memory) : C1.Env := {initial with mem := m}
def finalMemory (m : C1.Memory) (a b : Nat) (v w : UInt8) : C1.Memory :=
  writeByte (writeByte m a w) b v

private theorem local_place (fuel n : Nat) (ptr : Bool) (e : C1.Env)
    (hn : n < 3) :
    C1.evalL program (fuel + 1) function (localExpr n ptr) e = .ok (.reg n, e) := by
  interval_cases n <;> simp [C1.evalL, localExpr, Expression.node, function, sym]

private theorem local_read (fuel n : Nat) (ptr : Bool) (e : C1.Env) (v : Int)
    (hn : n < 3) (hv : e.regs[n]? = some v) :
    C1.evalE program (fuel + 2) function (readLocal n ptr) e = .ok (v, e) := by
  rw [C1.evalE]
  simp only [readLocal, Expression.node]
  rw [local_place fuel n ptr e hn]
  simp [C1.readPlace, hv, Bind.bind, Except.bind, pure, Except.pure]

private theorem cell_place (fuel n a : Nat) (e : C1.Env)
    (hn : n < 3) (hv : e.regs[n]? = some (a : Int)) :
    C1.evalL program (fuel + 3) function (cell n) e = .ok (.mem a, e) := by
  rw [C1.evalL]
  simp only [cell, Expression.node]
  rw [local_read fuel n true e a hn hv]
  simp [Bind.bind, Except.bind, pure, Except.pure]

private theorem cell_read (fuel n a : Nat) (e : C1.Env) (v : Int)
    (hn : n < 3) (hv : e.regs[n]? = some (a : Int))
    (load : C1.load e.mem (.int 1 false) a = .ok v) :
    C1.evalE program (fuel + 4) function (readCell n) e = .ok (v, e) := by
  rw [C1.evalE]
  simp only [readCell, Expression.node]
  rw [cell_place fuel n a e hn hv]
  change (do
    let x ← C1.load e.mem (.int 1 false) a
    pure (x, e)) = _
  rw [load]
  rfl


private theorem int_byte_conversion (v : Int) (hv : 0 ≤ v ∧ v < 256) :
    C1.convTo (.int 1 false) v = .ok v := by
  have bound : C1.inRange 1 false v = true := by
    change decide (0 ≤ v) && decide (v < 256) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hv
  change Except.ok (C1.wrap 1 false v) = Except.ok v
  unfold C1.wrap
  rw [bound]
  rfl

private theorem byte_conversion (v : UInt8) :
    C1.convTo (.int 1 false) (v.toNat : Int) = .ok (v.toNat : Int) :=
  int_byte_conversion _ ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr v.toNat_lt⟩

private theorem assignment_eval (fuel n a : Nat) (r : TypedExpression)
    (e e' : C1.Env) (v : Int) (m : C1.Memory)
    (convert : C1.convTo (.int 1 false) v = .ok v)
    (hn : n < 3) (address : e'.regs[n]? = some (a : Int))
    (rhs : C1.evalE program (fuel + 4) function r e = .ok (v, e'))
    (store : C1.store e'.mem (.int 1 false) a v = .ok m) :
    C1.evalE program (fuel + 5) function
      (.mk (.rvalue (.basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown
        (.assign (cell n) r)) e = .ok (v, updated e' m) := by
  rw [C1.evalE]
  simp only [Expression.node]
  rw [rhs]
  simp only [Bind.bind, Except.bind]
  rw [cell_place (fuel + 1) n a e' hn address]
  change (do
    let value ← C1.convTo (.int 1 false) (v : Int)
    let out ← C1.writePlace e' (.int 1 false) value (.mem a)
    pure (value, out)) = _
  rw [convert]
  simp [C1.writePlace, C1.Env.withMem, store, updated, Bind.bind, Except.bind, pure, Except.pure]

private theorem declaration_step (fuel : Nat) (initial : C1.Env) (a b : Nat)
    (v : UInt8) (k : C0.Kont)
    (read : C1.load initial.mem (.int 1 false) a = .ok v.toNat) :
    C1.step program (fuel + 5) function (some declaration) k (callee initial a b) =
      .ok (.running none k, (callee initial a b).setReg 2 v.toNat) := by
  have ptr : (callee initial a b).regs[0]? = some (a : Int) := by
    simp only [callee, Std.HashMap.getElem?_insert]
    rfl
  have run := cell_read fuel 0 a (callee initial a b) v.toNat (by decide) ptr read
  rw [C1.step]
  simp only [declaration, Statement.node]
  simp only [List.forIn_cons, List.forIn_nil, sym, callee, function,
    Std.HashMap.getElem?_empty, Std.HashMap.contains_insert, Std.HashMap.contains_empty,
    Std.HashMap.getElem?_insert]
  simp only [function, callee] at run
  simp [run, byte_conversion, Bind.bind, Except.bind, pure, Except.pure]

private theorem expr_step (fuel : Nat) (n : Nat) (r : TypedExpression)
    (e e' : C1.Env) (v : Int) (k : C0.Kont)
    (run : C1.evalE program (fuel + 1) function
      (.mk (.rvalue (.basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown
        (.assign (cell n) r)) e = .ok (v, e')) :
    C1.step program (fuel + 2) function (some (assign n r)) k e =
      .ok (.running none k, e') := by
  rw [C1.step]
  simp only [assign, Statement.node, run, Bind.bind, Except.bind, pure, Except.pure]

private theorem enter_block (fuel : Nat) (e : C1.Env) :
    C1.loop program (fuel + 20) function (some body) .stop e =
      C1.loop program (fuel + 18) function (some declaration)
        (.seq [assign 0 (readCell 1), assign 1 (readLocal 2 false)] .stop) e := by
  rw [C1.loop, C1.step]
  change C1.loop program (fuel + 19) function none
    (.seq [declaration, assign 0 (readCell 1), assign 1 (readLocal 2 false)] .stop) e = _
  rw [C1.loop, C1.step]

private theorem loop_running (fuel : Nat) (s : Option TypedStatement) (k : C0.Kont)
    (e : C1.Env) (s' : Option TypedStatement) (k' : C0.Kont) (e' : C1.Env)
    (step : C1.step program (fuel + 1) function s k e = .ok (.running s' k', e')) :
    C1.loop program (fuel + 2) function s k e =
      C1.loop program (fuel + 1) function s' k' e' := by
  rw [C1.loop, step]

private theorem next_statement (fuel : Nat) (s : TypedStatement) (ss : List TypedStatement)
    (k : C0.Kont) (e : C1.Env) :
    C1.loop program (fuel + 2) function none (.seq (s :: ss) k) e =
      C1.loop program (fuel + 1) function (some s) (.seq ss k) e := by
  rw [C1.loop, C1.step]

private theorem finish_loop (fuel : Nat) (e : C1.Env) :
    C1.loop program (fuel + 3) function none (.seq [] .stop) e = .ok (none, e) := by
  rw [C1.loop, C1.step]
  change C1.loop program (fuel + 2) function none .stop e = _
  rw [C1.loop, C1.step]

private theorem block_loop (fuel : Nat) (e e₁ e₂ e₃ : C1.Env)
    (first : C1.step program (fuel + 17) function (some declaration)
      (.seq [assign 0 (readCell 1), assign 1 (readLocal 2 false)] .stop) e =
      .ok (.running none (.seq [assign 0 (readCell 1), assign 1 (readLocal 2 false)] .stop), e₁))
    (second : C1.step program (fuel + 15) function (some (assign 0 (readCell 1)))
      (.seq [assign 1 (readLocal 2 false)] .stop) e₁ =
      .ok (.running none (.seq [assign 1 (readLocal 2 false)] .stop), e₂))
    (third : C1.step program (fuel + 13) function (some (assign 1 (readLocal 2 false)))
      (.seq [] .stop) e₂ = .ok (.running none (.seq [] .stop), e₃)) :
    C1.loop program (fuel + 20) function (some body) .stop e = .ok (none, e₃) := by
  rw [enter_block, loop_running (fuel + 16) _ _ _ _ _ _ first,
    next_statement, loop_running (fuel + 14) _ _ _ _ _ _ second,
    next_statement, loop_running (fuel + 12) _ _ _ _ _ _ third, finish_loop]

def temporary (initial : C1.Env) (a b : Nat) (v : UInt8) : C1.Env :=
  (callee initial a b).setReg 2 v.toNat

def afterFirst (initial : C1.Env) (a b : Nat) (v w : UInt8) : C1.Env :=
  updated (temporary initial a b v) (writeByte initial.mem a w)

private theorem first_assignment (fuel : Nat) (initial : C1.Env) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte initial.mem a v) (hq : OwnedByte initial.mem b w) :
    C1.step program (fuel + 15) function (some (assign 0 (readCell 1)))
      (.seq [assign 1 (readLocal 2 false)] .stop) (temporary initial a b v) =
      .ok (.running none (.seq [assign 1 (readLocal 2 false)] .stop), afterFirst initial a b v w) := by
  have rp : (temporary initial a b v).regs[0]? = some (a : Int) := by
    simp only [temporary, C1.Env.setReg, callee, Std.HashMap.getElem?_insert]
    rfl
  have rq : (temporary initial a b v).regs[1]? = some (b : Int) := by
    simp only [temporary, C1.Env.setReg, callee, Std.HashMap.getElem?_insert]
    rfl
  have run := assignment_eval (fuel + 9) 0 a (readCell 1)
    (temporary initial a b v) (temporary initial a b v) w.toNat (writeByte initial.mem a w)
    (byte_conversion w) (by decide) rp
    (cell_read (fuel + 9) 1 b _ w.toNat (by decide) rq (load_ownedByte hq))
    (store_ownedByte hp w)
  exact expr_step (fuel + 13) 0 (readCell 1) _ _ w.toNat _ run

private theorem second_assignment (fuel : Nat) (initial : C1.Env) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte initial.mem a v) (hq : OwnedByte initial.mem b w) (distinct : a ≠ b) :
    C1.step program (fuel + 13) function (some (assign 1 (readLocal 2 false)))
      (.seq [] .stop) (afterFirst initial a b v w) =
      .ok (.running none (.seq [] .stop),
        updated (afterFirst initial a b v w) (finalMemory initial.mem a b v w)) := by
  have rt : (afterFirst initial a b v w).regs[2]? = some (v.toNat : Int) := by
    simp only [afterFirst, updated, temporary, C1.Env.setReg, Std.HashMap.getElem?_insert]
    rfl
  have rq : (afterFirst initial a b v w).regs[1]? = some (b : Int) := by
    simp only [afterFirst, updated, temporary, C1.Env.setReg, callee, Std.HashMap.getElem?_insert]
    rfl
  have hq₁ := ownedByte_frame hp hq distinct w
  have store : C1.store (afterFirst initial a b v w).mem (.int 1 false) b (v.toNat : Int) =
      .ok (finalMemory initial.mem a b v w) := store_ownedByte hq₁ v
  have run := assignment_eval (fuel + 7) 1 b (readLocal 2 false)
    (afterFirst initial a b v w) (afterFirst initial a b v w) v.toNat
    (finalMemory initial.mem a b v w) (byte_conversion v) (by decide) rq
    (local_read (fuel + 9) 2 false _ v.toNat (by decide) rt) store
  exact expr_step (fuel + 11) 1 (readLocal 2 false) _ _ v.toNat _ run

private theorem swap_loop (fuel : Nat) (initial : C1.Env) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte initial.mem a v) (hq : OwnedByte initial.mem b w) (distinct : a ≠ b) :
    C1.loop program (fuel + 20) function (some body) .stop (callee initial a b) =
      .ok (none, updated (afterFirst initial a b v w) (finalMemory initial.mem a b v w)) := by
  exact block_loop fuel _ _ _ _
    (declaration_step (fuel + 12) initial a b v _ (load_ownedByte hp))
    (first_assignment fuel initial a b v w hp hq)
    (second_assignment fuel initial a b v w hp hq distinct)

private theorem pointer_wrap (a : Nat) (ha : a < 18446744073709551616) :
    C1.wrap 8 false (a : Int) = a := by
  have range : C1.inRange 8 false (a : Int) = true := by
    simp only [C1.inRange, C1.lo, C1.hi, Bool.and_eq_true, decide_eq_true_eq]
    omega
  simp only [C1.wrap, range, ite_true]

private theorem program_lookup : program.funcs[fSym.number]? = some function := by
  simp [program, fSym]
private theorem function_params : function.params = [(0, pointerType), (1, pointerType)] := rfl
private theorem function_locals : function.memLocals = [] := rfl
private theorem function_body : function.body = body := rfl
private theorem function_ret : function.ret = .void := rfl

/-- Nonrecursive call setup and return projection, with an abstract body runner. -/
private abbrev callWith := C1Call.callWith
private theorem callFn_decompose (P : C1.Prog) (fd : C1.FunDef) (g : Sym)
    (fuel : Nat) (initial : C1.Env) (args : List Int)
    (lookup : P.funcs[g.number]? = some fd) :
    C1.callFn P (fuel + 1) g args initial =
      callWith P fd.params fd.memLocals fd.ret g args initial (C1.loop P fuel fd (some fd.body) .stop) := by
  exact C1Call.callFn_decompose P fd g fuel initial args lookup

/-- Normalize two-pointer call setup with an arbitrary runner. In particular,
no simplifier traverses the concrete recursive evaluator here. -/
private theorem abstract_call_prelude (P : C1.Prog) (g : Sym)
    (initial : C1.Env) (a b : Nat) (run : C1.Env → Except C0.Stop (Option Int × C1.Env))
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    callWith P [(0, pointerType), (1, pointerType)] [] .void g [a, b] initial run = (do
      let (_, e) ← run (callee initial a b)
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) := by
  simp only [callWith, C1Call.callWith, List.length_cons, List.length_nil,
    Nat.reduceAdd, bne_self_eq_false, Bool.false_eq_true, ite_false,
    List.forIn_nil, List.forIn_cons, List.zip_cons_cons, List.zip_nil_left,
    pointerType, RefinedCOwnedByte.pointerType, C1.convTo,
    pointer_wrap a ha, pointer_wrap b hb, Std.HashMap.getElem?_empty,
    callee, Bind.bind, Except.bind, pure, Except.pure]

private theorem call_loop (fuel : Nat) (initial : C1.Env) (a b : Nat)
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    C1.callFn program (fuel + 21) fSym [a, b] initial = (do
      let (_, e) ← C1.loop program (fuel + 20) function (some body) .stop (callee initial a b)
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) := by
  rw [callFn_decompose program function fSym (fuel + 20) initial [a, b] program_lookup]
  rw [function_params, function_locals, function_ret]
  rw [abstract_call_prelude program fSym initial a b
    (C1.loop program (fuel + 20) function (some function.body) .stop) ha hb]
  rw [function_body]

private theorem restore_memory (m : C1.Memory) (saved : Nat) (sp : m.sp = saved) :
    {m with sp := saved} = m := by
  cases m
  simp_all

private theorem return_projection (initial e : C1.Env) (m : C1.Memory)
    (out : e.out = initial.out) (sp : m.sp = initial.mem.sp) :
    (do
      let (_, e) ← (Except.ok (none, updated e m) : Except C0.Stop (Option Int × C1.Env))
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) =
      .ok (0, updated initial m) := by
  simp only [Bind.bind, Except.bind, pure, Except.pure, updated]
  rw [restore_memory m initial.mem.sp sp, out]

private theorem write_sp (m : C1.Memory) (a : Nat) (v : UInt8) :
    (writeByte m a v).sp = m.sp := by unfold writeByte; rfl

private theorem final_sp (m : C1.Memory) (a b : Nat) (v w : UInt8) :
    (finalMemory m a b v w).sp = m.sp := by
  unfold finalMemory
  rw [write_sp, write_sp]
private theorem after_out (initial : C1.Env) (a b : Nat) (v w : UInt8) :
    (afterFirst initial a b v w).out = initial.out := rfl

/-- Actual C1 function-call execution, for every pair of byte values. -/
theorem swap_call (initial : C1.Env) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte initial.mem a v) (hq : OwnedByte initial.mem b w) (distinct : a ≠ b)
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    C1.callFn program 21 fSym [a, b] initial =
      .ok (0, updated initial (finalMemory initial.mem a b v w)) := by
  rw [call_loop 0 initial a b ha hb, swap_loop 0 initial a b v w hp hq distinct]
  exact return_projection initial _ _ (after_out initial a b v w) (final_sp _ _ _ _ _)

private theorem updated_mem (e : C1.Env) (m : C1.Memory) : (updated e m).mem = m := rfl
private theorem updated_regs (e : C1.Env) (m : C1.Memory) : (updated e m).regs = e.regs := rfl
private theorem updated_frame (e : C1.Env) (m : C1.Memory) : (updated e m).frame = e.frame := rfl
private theorem updated_out (e : C1.Env) (m : C1.Memory) : (updated e m).out = e.out := rfl

private theorem final_cells (m : C1.Memory) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte m a v) (hq : OwnedByte m b w) (distinct : a ≠ b) :
    OwnedByte (finalMemory m a b v w) a w ∧ OwnedByte (finalMemory m a b v w) b v := by
  have hq₁ := ownedByte_frame hp hq distinct w
  exact ⟨ownedByte_frame hq₁ (ownedByte_write hp w) (Ne.symm distinct) v,
    ownedByte_write hq₁ v⟩

private theorem final_frame (m : C1.Memory) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte m a v) (hq : OwnedByte m b w) (distinct : a ≠ b)
    (frame : Resources.Heap) (concrete : Realizes m frame)
    (outsideP : ∀ n, (a, n) ∉ frame) (outsideQ : ∀ n, (b, n) ∉ frame) :
    Realizes (finalMemory m a b v w) frame :=
  realizes_frame (ownedByte_frame hp hq distinct w) (realizes_frame hp concrete outsideP w) outsideQ v

/-- Swapped owned cells and an arbitrary exclusive finite frame survive the call.
The caller's registers, local frame, output, and stack pointer are restored. -/
theorem swap_owned (initial : C1.Env) (a b : Nat) (v w : UInt8)
    (hp : OwnedByte initial.mem a v) (hq : OwnedByte initial.mem b w) (distinct : a ≠ b)
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (frame : Resources.Heap) (concrete : Realizes initial.mem frame)
    (outsideP : ∀ n, (a, n) ∉ frame) (outsideQ : ∀ n, (b, n) ∉ frame) :
    ∃ finalState, C1.callFn program 21 fSym [a, b] initial = .ok (0, finalState) ∧
      OwnedByte finalState.mem a w ∧ OwnedByte finalState.mem b v ∧
      Realizes finalState.mem frame ∧ finalState.regs = initial.regs ∧
      finalState.frame = initial.frame ∧ finalState.out = initial.out ∧
      finalState.mem.sp = initial.mem.sp := by
  refine ⟨updated initial (finalMemory initial.mem a b v w),
    swap_call initial a b v w hp hq distinct ha hb, ?_⟩
  rw [updated_mem]
  exact ⟨(final_cells _ _ _ _ _ hp hq distinct).1,
    (final_cells _ _ _ _ _ hp hq distinct).2,
    final_frame _ _ _ _ _ hp hq distinct frame concrete outsideP outsideQ,
    updated_regs _ _, updated_frame _ _, updated_out _ _, final_sp _ _ _ _ _⟩

/-- A physically initialized two-cell witness exists for every input pair. -/
theorem pair_call (v w : UInt8) :
    C1.callFn program 21 fSym [C1.base, C1.base + 1]
      ⟨{}, {}, pairMemory v w, .empty⟩ =
      .ok (0, updated ⟨{}, {}, pairMemory v w, .empty⟩
        (finalMemory (pairMemory v w) C1.base (C1.base + 1) v w)) :=
  swap_call _ _ _ v w (pair_left v w) (pair_right v w) (Nat.ne_add_one _) (by decide) (by decide)

end Silmaril.Compile.C.Sem.RefinedCOwnedSwap
