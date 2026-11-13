module

public import Silmaril.Compiler.C.Sem.C1Call.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
public import Silmaril.Compiler.C.Sem.ConcreteResources.Defs
import Mathlib.Tactic

/-! Actual typed-Ail execution of `void increment(unsigned char *p) { (*p)++; }`.
This is an adapted owned-cell example, not an upstream parser certificate. C1 uses
its existing flat byte/init memory; allocation provenance and Iris adequacy are
separate boundaries. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedByte

open Silmaril.Cerberus Silmaril.Cerberus.Ail

def byteType : Ctype := .mk [] (.basic (.integer (.unsigned .ichar)))
def pointerType : CType := .ptr byteType

def pSym : Sym := ⟨⟨[]⟩, 0, .id "p"⟩
def fSym : Sym := ⟨⟨[]⟩, 1, .id "increment_owned_byte"⟩
def pointerLvalue : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ (.mk [] (.pointer ⟨false, false, false⟩ byteType)) false)
    [] .unknown (.ident pSym)
def pointerRead : TypedExpression :=
  .mk (.rvalue (.pointer ⟨false, false, false⟩ byteType)) [] .unknown (.rvalue pointerLvalue)
def cell : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ byteType false) [] .unknown (.unary .indirection pointerRead)
def increment : TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.unsigned .ichar))))) [] .unknown
    (.unary .postfixIncr cell)
def body : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) (.expr increment)
def function : C1.FunDef :=
  ⟨⟨[(0, pointerType)], .void, body,
      ({} : Std.HashMap Nat CType).insert 0 pointerType⟩, [], {}⟩
def program : C1.Prog :=
  ⟨({} : Std.HashMap Nat C1.FunDef).insert 1 function, {}, {}, [], ⟨∅, ∅⟩, none, {}, {},
    4096, 4096, 4096⟩

def callee (initial : C1.Env) (a : Nat) : C1.Env :=
  ⟨({} : Std.HashMap Nat Int).insert 0 a, {}, initial.mem, initial.out⟩
def updated (initial : C1.Env) (m : C1.Memory) : C1.Env :=
  { initial with mem := m }

private theorem pointer_read (fuel a : Nat) (initial : C1.Env) :
    C1.evalE program (fuel + 3) function pointerRead (callee initial a) =
      .ok (a, callee initial a) := by
  simp [C1.evalE, C1.evalL, pointerRead, pointerLvalue, Expression.node,
    function, pSym, C1.readPlace, callee, Bind.bind, Except.bind, pure, Except.pure]

private theorem cell_place (fuel a : Nat) (initial : C1.Env) :
    C1.evalL program (fuel + 4) function cell (callee initial a) =
      .ok (.mem a, callee initial a) := by
  simp only [C1.evalL, cell, Expression.node]
  rw [pointer_read]
  simp [Bind.bind, Except.bind, pure, Except.pure]

private theorem byte_arithmetic (v : Int) (hv : 0 ≤ v ∧ v < 255) :
    C1.arith .add 4 true (C1.wrap 4 true v) 1 = .ok (v + 1) ∧
      C1.convTo (.int 1 false) (v + 1) = .ok (v + 1) := by
  have hv0 : (0 : Int) ≤ v := by omega
  have hv255 : v < 255 := by omega
  have r4 : C1.inRange 4 true v = true := by
    change decide (-2147483648 ≤ v) && decide (v < 2147483648) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have r1 : C1.inRange 1 false (v + 1) = true := by
    change decide (0 ≤ v + 1) && decide (v + 1 < 256) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have w4 : C1.wrap 4 true v = v := by
    unfold C1.wrap
    rw [r4]
    rfl
  have w1 : C1.wrap 1 false (v + 1) = v + 1 := by
    unfold C1.wrap
    rw [r1]
    rfl
  have range : C1.inRange 4 true (v + 1) = true := by
    change decide (-2147483648 ≤ v + 1) && decide (v + 1 < 2147483648) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  constructor
  · rw [w4]
    simp only [C1.arith, range, ite_true]
  · exact congrArg Except.ok w1


private theorem increment_executes (fuel : Nat) (initial : C1.Env) (a : Nat) (v : Int) (m : C1.Memory)
    (hv : 0 ≤ v ∧ v < 255)
    (read : C1.load initial.mem (.int 1 false) a = .ok v)
    (write : C1.store initial.mem (.int 1 false) a (v + 1) = .ok m) :
    C1.evalE program (fuel + 5) function increment (callee initial a) =
      .ok (v, updated (callee initial a) m) := by
  rw [C1.evalE]
  simp only [increment, Expression.node]
  rw [cell_place]
  change (do
    let old ← C1.load initial.mem (.int 1 false) a
    let r ← C1.convTo (.int 1 false) (← C1.arith .add 4 true (C1.wrap 4 true old) 1)
    pure (old, ← C1.writePlace (callee initial a) (.int 1 false) r (.mem a))) = _
  rw [read]
  simp only [Bind.bind, Except.bind]
  rw [(byte_arithmetic v hv).1]
  dsimp only
  rw [(byte_arithmetic v hv).2]
  simp [C1.writePlace, C1.Env.withMem, callee, write, updated, pure, Except.pure]


private theorem program_lookup : program.funcs[fSym.number]? = some function := by
  simp [program, fSym]

private theorem function_params : function.params = [(0, pointerType)] := rfl
private theorem function_locals : function.memLocals = [] := rfl
private theorem function_body : function.body = body := rfl
private theorem function_ret : function.ret = .void := rfl

private theorem increment_loop (fuel : Nat) (initial : C1.Env) (a : Nat)
    (v : Int) (m : C1.Memory)
    (run : C1.evalE program (fuel + 5) function increment (callee initial a) =
      .ok (v, updated (callee initial a) m)) :
    C1.loop program (fuel + 7) function (some body) .stop (callee initial a) =
      .ok (none, updated (callee initial a) m) := by
  rw [C1.loop]
  change (match (do
    let (_, e) ← C1.evalE program (fuel + 5) function increment (callee initial a)
    pure (C0.Next.running none .stop, e)) with
    | .ok (.running f k, e) => C1.loop program (fuel + 6) function f k e
    | .ok (.returned r, e) => .ok (r, e)
    | .error e => .error e) = _
  rw [run]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [C1.loop, C1.step]

/-- Keep pointer conversion independent of the call/loop reduction. -/
private theorem pointer_wrap (a : Nat) (ha : a < 18446744073709551616) :
    C1.wrap 8 false (a : Int) = a := by
  have range : C1.inRange 8 false (a : Int) = true := by
    simp only [C1.inRange, C1.lo, C1.hi, Bool.and_eq_true, decide_eq_true_eq]
    omega
  simp only [C1.wrap, range, ite_true]

/-- Nonrecursive call setup and return projection, with an abstract body runner. -/
private abbrev callWith := C1Call.callWith
private theorem callFn_decompose (P : C1.Prog) (fd : C1.FunDef) (g : Sym)
    (fuel : Nat) (initial : C1.Env) (args : List Int)
    (lookup : P.funcs[g.number]? = some fd) :
    C1.callFn P (fuel + 1) g args initial =
      callWith P fd.params fd.memLocals fd.ret g args initial (C1.loop P fuel fd (some fd.body) .stop) := by
  exact C1Call.callFn_decompose P fd g fuel initial args lookup

/-- Simplification happens with an arbitrary body runner, never a recursive
C1 evaluator. Applications only substitute that evaluator after this proof. -/
private theorem abstract_call_prelude (P : C1.Prog) (g : Sym)
    (initial : C1.Env) (a : Nat) (run : C1.Env → Except C0.Stop (Option Int × C1.Env))
    (ha : a < 18446744073709551616) :
    callWith P [(0, pointerType)] [] .void g [a] initial run = (do
      let (_, e) ← run (callee initial a)
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) := by
  simp only [callWith, C1Call.callWith, List.length_cons, List.length_nil,
    Nat.reduceAdd, bne_self_eq_false, Bool.false_eq_true, ite_false,
    List.forIn_nil, List.forIn_cons, List.zip_cons_cons, List.zip_nil_left,
    pointerType, C1.convTo, pointer_wrap a ha, Std.HashMap.getElem?_empty,
    callee, Bind.bind, Except.bind, pure, Except.pure]

/-- The concrete call uses the abstract prelude without reducing its body. -/
private theorem call_loop (fuel : Nat) (initial : C1.Env) (a : Nat)
    (ha : a < 18446744073709551616) :
    C1.callFn program (fuel + 8) fSym [a] initial = (do
      let (_, e) ← C1.loop program (fuel + 7) function (some body) .stop (callee initial a)
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) := by
  rw [callFn_decompose program function fSym (fuel + 7) initial [a] program_lookup]
  rw [function_params, function_locals, function_ret]
  rw [abstract_call_prelude program fSym initial a
    (C1.loop program (fuel + 7) function (some function.body) .stop) ha]
  rw [function_body]

private theorem restore_memory (m : C1.Memory) (saved : Nat) (sp : m.sp = saved) :
    {m with sp := saved} = m := by
  cases m
  simp_all

/-- Reduce the return projection separately from the recursive evaluator. -/
private theorem return_projection (initial : C1.Env) (a : Nat) (m : C1.Memory)
    (sp : m.sp = initial.mem.sp) :
    (do
      let (_, e) ← (Except.ok (none, updated (callee initial a) m) :
        Except C0.Stop (Option Int × C1.Env))
      pure ((0 : Int), (⟨initial.regs, initial.frame,
        {e.mem with sp := initial.mem.sp}, e.out⟩ : C1.Env))) =
      .ok (0, updated initial m) := by
  simp only [Bind.bind, Except.bind, pure, Except.pure, updated, callee]
  rw [restore_memory m initial.mem.sp sp]

private theorem call_of_increment_eval (fuel : Nat) (initial : C1.Env) (a : Nat)
    (v : Int) (m : C1.Memory) (ha : a < 18446744073709551616)
    (run : C1.evalE program (fuel + 5) function increment (callee initial a) =
      .ok (v, updated (callee initial a) m))
    (sp : m.sp = initial.mem.sp) :
    C1.callFn program (fuel + 8) fSym [a] initial = .ok (0, updated initial m) := by
  rw [call_loop fuel initial a ha, increment_loop fuel initial a v m run]
  exact return_projection initial a m sp

private theorem call_of_memory (fuel : Nat) (initial : C1.Env) (a : Nat)
    (v : Int) (m : C1.Memory) (hv : 0 ≤ v ∧ v < 255) (ha : a < 18446744073709551616)
    (read : C1.load initial.mem (.int 1 false) a = .ok v)
    (write : C1.store initial.mem (.int 1 false) a (v + 1) = .ok m)
    (sp : m.sp = initial.mem.sp) :
    C1.callFn program (fuel + 8) fSym [a] initial = .ok (0, updated initial m) := by
  exact call_of_increment_eval fuel initial a v m ha
    (increment_executes fuel initial a v m hv read write) sp

open Silmaril.Cerberus.Assertion
open ConcreteResources

def successor (v : UInt8) : UInt8 := UInt8.ofNat (v.toNat + 1)

theorem successor_value (v : UInt8) (hv : v.toNat < 255) :
    ((successor v).toNat : Int) = (v.toNat : Int) + 1 := by
  have h : v.toNat + 1 < 256 := by omega
  simp [successor, UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem successor_store (initial : C1.Env) (a : Nat) (v : UInt8)
    (owned : OwnedByte initial.mem a v) (hv : v.toNat < 255) :
    C1.store initial.mem (.int 1 false) a ((v.toNat : Int) + 1) =
      .ok (writeByte initial.mem a (successor v)) := by
  simpa only [successor_value v hv] using store_ownedByte owned (successor v)

private theorem writeByte_sp (m : C1.Memory) (a : Nat) (v : UInt8) :
    (writeByte m a v).sp = m.sp := by
  unfold writeByte
  rfl

/-- Actual pointer call on arbitrary physically backed writable memory, with a
separately owned finite frame. Real byte/init writes are derived, never assumed. -/
theorem increment_owned (initial : C1.Env) (a : Nat) (v : UInt8)
    (owned : OwnedByte initial.mem a v) (hv : v.toNat < 255)
    (address : a < 18446744073709551616)
    (frame : Resources.Heap) (concreteFrame : Realizes initial.mem frame)
    (outside : ∀ n, (a, n) ∉ frame) :
    C1.callFn program 8 fSym [a] initial =
      .ok (0, updated initial (writeByte initial.mem a (successor v))) ∧
    OwnedByte (writeByte initial.mem a (successor v)) a (successor v) ∧
    Realizes (writeByte initial.mem a (successor v)) frame := by
  have hsafe : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < 255 :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hv⟩
  refine ⟨call_of_memory 0 initial a v.toNat _ hsafe address (load_ownedByte owned) (successor_store initial a v owned hv)
      (writeByte_sp _ _ _),
    ownedByte_write owned _, realizes_frame owned concreteFrame outside _⟩

def singleton (n : Int) : RefinedC.IntRefinement := ⟨.u8, some (.literal n)⟩

private theorem updated_regs (initial : C1.Env) (m : C1.Memory) :
    (updated initial m).regs = initial.regs := by unfold updated; rfl
private theorem updated_frame (initial : C1.Env) (m : C1.Memory) :
    (updated initial m).frame = initial.frame := by unfold updated; rfl
private theorem updated_out (initial : C1.Env) (m : C1.Memory) :
    (updated initial m).out = initial.out := by unfold updated; rfl
private theorem updated_sp (initial : C1.Env) (a : Nat) (v : UInt8) :
    (updated initial (writeByte initial.mem a v)).mem.sp = initial.mem.sp := by
  unfold updated
  exact writeByte_sp _ _ _

private theorem singleton_admits (n : Int) (h0 : 0 ≤ n) (h1 : n < 256)
    (ρ : Pure.Env) : (singleton n).holds ρ n := by
  simp [singleton, RefinedC.IntRefinement.holds, RefinedC.IntegerType.admits,
    RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.signed, RefinedC.IntegerType.bits, Pure.Term.eval]
  omega

/-- A concrete-memory interpretation of a RefinedC owned singleton provides the
precondition for the actual pointer function and is re-established afterward.
Arbitrary disjoint resources and all caller register/frame/output state survive. -/
theorem refinedC_owned_call (ρ : Pure.Env) (initial : C1.Env) (a : Nat) (n : Int)
    (pre : Holds ρ ((singleton n).owned a (.literal n)) initial.mem)
    (safe : n < 255) (address : a < 18446744073709551616)
    (frame : Resources.Heap) (concreteFrame : Realizes initial.mem frame)
    (outside : ∀ value, (a, value) ∉ frame) :
    ∃ finalState,
      C1.callFn program 8 fSym [a] initial = .ok (0, finalState) ∧
      Holds ρ ((singleton (n + 1)).owned a (.literal (n + 1))) finalState.mem ∧
      Realizes finalState.mem frame ∧
      finalState.regs = initial.regs ∧ finalState.frame = initial.frame ∧
      finalState.out = initial.out ∧ finalState.mem.sp = initial.mem.sp := by
  obtain ⟨_, v, value, owned⟩ := (refinedC_owned_iff _ _ _ _ _).mp pre
  change n = (v.toNat : Int) at value
  have hv : v.toNat < 255 := Int.ofNat_lt.mp (value ▸ safe)
  obtain ⟨run, after, framed⟩ := increment_owned initial a v owned hv address frame concreteFrame outside
  refine ⟨updated initial (writeByte initial.mem a (successor v)), run, ?_, framed,
    updated_regs _ _, updated_frame _ _, updated_out _ _, updated_sp _ _ _⟩
  apply (refinedC_owned_iff _ _ _ _ _).mpr
  refine ⟨?_, successor v, ?_, after⟩
  · apply singleton_admits
    · rw [value]
      exact add_nonneg (Int.natCast_nonneg _) (by decide)
    · rw [value]
      have bound : (v.toNat : Int) < 255 := Int.ofNat_lt.mpr hv
      omega
  · simp only [Pure.Term.eval, successor_value v hv, value]

/-- A two-cell initialized witness exists for every admissible input and every
frame byte; the second byte is actually loaded unchanged after the function. -/
theorem pair_call (v w : UInt8) (safe : v.toNat < 255) :
    C1.callFn program 8 fSym [C1.base] ⟨{}, {}, pairMemory v w, .empty⟩ =
      .ok (0, ⟨{}, {}, writeByte (pairMemory v w) C1.base (successor v), .empty⟩) ∧
    C1.load (writeByte (pairMemory v w) C1.base (successor v))
      (.int 1 false) (C1.base + 1) = .ok w.toNat := by
  have run := increment_owned (⟨{}, {}, pairMemory v w, .empty⟩ : C1.Env) C1.base v
    (pair_left v w) safe (by decide) [] ⟨by simp, by simp⟩ (by simp)
  exact ⟨run.1, load_ownedByte (ownedByte_frame (pair_left v w) (pair_right v w) (by omega) _)⟩

private theorem wrap_executes (fuel : Nat) (initial : C1.Env) (a : Nat) (m : C1.Memory)
    (read : C1.load initial.mem (.int 1 false) a = .ok 255)
    (write : C1.store initial.mem (.int 1 false) a 0 = .ok m) :
    C1.evalE program (fuel + 5) function increment (callee initial a) =
      .ok (255, updated (callee initial a) m) := by
  rw [C1.evalE]
  simp only [increment, Expression.node]
  rw [cell_place]
  change (do
    let old ← C1.load initial.mem (.int 1 false) a
    let r ← C1.convTo (.int 1 false) (← C1.arith .add 4 true (C1.wrap 4 true old) 1)
    pure (old, ← C1.writePlace (callee initial a) (.int 1 false) r (.mem a))) = _
  rw [read]
  simp only [Bind.bind, Except.bind]
  rw [show C1.arith .add 4 true (C1.wrap 4 true 255) 1 = .ok 256 from by rfl]
  dsimp only
  rw [show C1.convTo (.int 1 false) 256 = .ok 0 from by rfl]
  simp [C1.writePlace, C1.Env.withMem, callee, write, updated, pure, Except.pure]

private theorem wrap_call_of_memory (fuel : Nat) (initial : C1.Env) (a : Nat)
    (m : C1.Memory) (ha : a < 18446744073709551616)
    (read : C1.load initial.mem (.int 1 false) a = .ok 255)
    (write : C1.store initial.mem (.int 1 false) a 0 = .ok m)
    (sp : m.sp = initial.mem.sp) :
    C1.callFn program (fuel + 8) fSym [a] initial = .ok (0, updated initial m) := by
  exact call_of_increment_eval fuel initial a 255 m ha
    (wrap_executes fuel initial a m read write) sp


/-- Unsigned C permits255→0. This actual pointer-call boundary is deliberately
outside the mathematical no-wrap owned-refinement precondition above. -/
theorem boundary_wrap_call :
    C1.callFn program 8 fSym [C1.base] ⟨{}, {}, pairMemory 255 37, .empty⟩ =
      .ok (0, ⟨{}, {}, writeByte (pairMemory 255 37) C1.base 0, .empty⟩) ∧
    C1.load (writeByte (pairMemory 255 37) C1.base 0) (.int 1 false) C1.base = .ok 0 ∧
    C1.load (writeByte (pairMemory 255 37) C1.base 0) (.int 1 false) (C1.base + 1) = .ok 37 := by
  exact ⟨wrap_call_of_memory 0 _ _ _ (by decide)
      (load_ownedByte (pair_left 255 37)) (store_ownedByte (pair_left 255 37) 0) rfl,
    load_ownedByte (ownedByte_write (pair_left 255 37) 0),
    load_ownedByte (ownedByte_frame (pair_left 255 37) (pair_right 255 37) (by omega) 0)⟩

/-- The wrapped byte cannot satisfy the mathematical singleton256 refinement. -/
theorem wrapped_not_singleton256 (ρ : Pure.Env) :
    ¬Holds ρ ((singleton 256).owned C1.base (.literal 256))
      (writeByte (pairMemory 255 37) C1.base 0) := by
  intro h
  have hr := ((refinedC_owned_iff _ _ _ _ _).mp h).1
  norm_num [singleton, RefinedC.IntRefinement.holds, RefinedC.IntegerType.admits,
    RefinedC.IntegerType.lower, RefinedC.IntegerType.upper,
    RefinedC.IntegerType.signed, RefinedC.IntegerType.bits, Pure.Term.eval] at hr

end Silmaril.Compile.C.Sem.RefinedCOwnedByte
