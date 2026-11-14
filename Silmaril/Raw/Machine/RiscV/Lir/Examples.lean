module

public import Silmaril.Machine.RiscV.Lir.Loader.Defs
/-!
# Examples of the Lir-to-RV64 backend

* `addOne` (`x ↦ x + 1` over two physical registers) compiles
  (`addOne_compile`, checked by kernel evaluation), and its Lir run on `41`
  returns `42`. `addOne_machine` instantiates `compile_correct`, and
  `addOne_machine_exact` instantiates `compile_correct_bounded` (the program
  makes no calls): the machine run from the loaded state reaches the halt stub
  with `42` in `a0` and stops. All premises are discharged for concrete values.
* `i32Ops` exercises the 32-bit operators, byte-wise loads and stores and a
  large memory offset; it compiles.
* `chain` uses 17 virtual registers; after spilling with `firstK 12` it compiles.
* `counts` uses every bit-counting operator; it compiles.
* Rejections: nine call arguments (`tooManyArgs`) and nine returned values
  (`tooManyReturnValues`).
-/

@[expose] public section

namespace Silmaril.RiscV.Backend.Examples

open Machine.Lir (Prog Frame)
open Relation

def A2 : Assign (Fin 2) := Assign.fin 2 (by decide)

/-- `f(x) = x + 1`. -/
def addOne : Prog (Fin 2) :=
  ⟨[⟨[.reg 0], 0, [⟨[.op (.const 1 1), .op (.binary .add 0 0 1)], .ret [.reg 0]⟩]⟩]⟩

def addOneImage : Image := ⟨emitProg A2.reg (slotBound addOne) addOne, slotBound addOne⟩

theorem addOne_compile : compile A2 addOne = .ok addOneImage := rfl

theorem addOne_length : addOneImage.code.length = 15 := by decide

/-- Code at `0x1000`, stack `[0x10000, 0x20000)`, 64 bytes of linear memory at `0x40000`. -/
def space : Space := ⟨0x1000, 0x10000, 0x20000, 0x40000, 64⟩

theorem space_valid (n : Nat) (h : n ≤ 1000) : space.Valid n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [space] <;> omega

def mem : Machine.Lir.Memory := Machine.Lir.Memory.ofList 64 []

def start : Machine.Lir.State (Fin 2) :=
  ⟨⟨0, 0, 0⟩, (Frame.empty.writeAll [.reg 0] [41]).get rfl, [], mem⟩

theorem addOne_start : addOne.start 0 [41] mem = some start := rfl

theorem addOne_returns : Machine.Lir.Behaves addOne start (.returned [42] mem) :=
  Machine.Lir.run_returned (n := 5) rfl

/-- The machine running the compiled `addOne` on `41` reaches the halt stub
with `42` in `a0`, or the stack-overflow stub. -/
theorem addOne_machine :
    ∃ m, ReflTransGen TStep (loadState space addOneImage.code addOne 0 [41] mem) m ∧
      (Returned A2 addOne space addOneImage.slots [42] mem m ∨
        Overflowed A2 addOne space addOneImage.slots m) :=
  (compile_correct addOne_compile (space_valid _ (by rw [addOne_length]; decide)) rfl
    addOne_start).1 [42] mem addOne_returns

theorem addOne_no_calls : ∀ pt f a r, addOne.fetch pt ≠ some (.instr (.call f a r)) := by
  intro ⟨fn, l, i⟩ f a r h
  rcases fn with _ | fn <;> rcases l with _ | l <;> rcases i with _ | _ | _ | i <;>
    simp [Prog.fetch, Prog.block?, Prog.func?, addOne] at h

/-- `addOne` makes no calls, so the stack cannot overflow: the machine reaches
the halt stub with `42` in `a0` and stops there. -/
theorem addOne_machine_exact :
    ∃ m, ReflTransGen TStep (loadState space addOneImage.code addOne 0 [41] mem) m ∧
      Returned A2 addOne space addOneImage.slots [42] mem m ∧ m.core.read (argRegN 0) = 42 ∧
      m.step = .stopped := by
  have hv := space_valid addOneImage.code.length (by rw [addOne_length]; decide)
  obtain ⟨m, hm, hr⟩ := (compile_correct_bounded addOne_compile hv rfl addOne_start
    (depthBounded_of_no_calls addOne_no_calls start) (by decide)).1 [42] mem addOne_returns
  exact ⟨m, hm, hr, hr.2.2.2.1 0 (by decide), Returned.stopped hv hr⟩

/-- 32-bit arithmetic, a sign-extending byte-wise load and a store at a large
offset. -/
def i32Ops : Prog (Fin 3) :=
  ⟨[⟨[.reg 0, .reg 1], 0, [⟨[.op (.binary .add 2 0 1), .op (.unary .zext32 2 2),
      .op (.binary (.cmp32 .lts) 0 0 1), .op (.binary .divs32 1 2 1), .op (.binary .rotl32 0 1 0),
      .op (.binary .shrs32 0 0 1), .op (.load .b4 .sign 1 0 3), .op (.store .b2 0 5000 1)],
      .ret [.reg 2, .reg 0]⟩]⟩]⟩

theorem i32Ops_compiles : (compile (Assign.fin 3 (by decide)) i32Ops).toBool = true := by decide

/-- The bit-counting operators, selected as unrolled sums. -/
def counts : Prog (Fin 2) :=
  ⟨[⟨[.reg 0], 0, [⟨[.op (.unary .clz 1 0), .op (.unary .ctz32 1 1), .op (.unary .popcnt 1 1),
      .op (.unary .clz32 1 1), .op (.unary .ctz 1 1), .op (.unary .popcnt32 0 1)],
      .ret [.reg 0]⟩]⟩]⟩

theorem counts_compiles : (compile A2 counts).toBool = true := by decide

/-- A chain of 17 virtual registers, more than the 14 physical ones. -/
def chain : Prog Nat :=
  ⟨[⟨[.reg 0], 0, [⟨(List.range 16).map fun i => .op (.binary .add (i + 1) i 0),
      .ret [.reg 16]⟩]⟩]⟩

theorem chain_spilled_compiles :
    (compile (Assign.fin 14 (by decide)) (Machine.Lir.Alloc.spill (Machine.Lir.Alloc.firstK 12) chain)).toBool =
      true := by decide

/-! ## Rejected programs -/

def errorOf : Except Error Image → Option Error
  | .error e => some e
  | .ok _ => none

/-- Nine call arguments exceed `a0 … a7`. -/
def nineArgs : Prog (Fin 2) :=
  ⟨[⟨[.reg 0], 0, [⟨[.call 0 (List.replicate 9 (.reg 0)) []], .ret [.reg 0]⟩]⟩]⟩

theorem nineArgs_rejected : errorOf (compile A2 nineArgs) = some (.tooManyArgs 0 0 0 9) := by
  decide

/-- Nine returned values exceed `a0 … a7`. -/
def nineResults : Prog (Fin 2) :=
  ⟨[⟨[.reg 0], 0, [⟨[], .ret (List.replicate 9 (.reg 0))⟩]⟩]⟩

theorem nineResults_rejected :
    errorOf (compile A2 nineResults) = some (.tooManyReturnValues 0 0 9) := by
  decide


end Silmaril.RiscV.Backend.Examples
