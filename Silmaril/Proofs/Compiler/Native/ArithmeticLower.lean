module

public import Silmaril.Compiler.Native.Correctness.ArithmeticLower.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Thms
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 50000
namespace Silmaril.Compiler.Native.Correctness.ArithmeticLower
open Silmaril.Compile Silmaril.Machine Silmaril.Cerberus
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native Silmaril.Compiler.Native.Optimize

/-- Exact primitive target classification of the real typed-Ail tree. -/
theorem actual_type (expression : Expression) : Types.typeOf expression.ail = .int 4 true := by
  cases expression <;> rfl

/-- The registry-aware converter has the same exact primitive type for this
actual enum-free signed-int source tree in every implementation context. -/
theorem registered_actual_type (tags : Silmaril.Cerberus.Mem.Concrete.Tags)
    (expression : Expression) : Types.Registered.typeOf tags expression.ail = .int 4 true := by
  cases expression <;> rfl

/-- The actual guarded native constant decoder accepts independently bounded
source literals. Compilation of UB expressions is not an overflow check. -/
theorem constant_value (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    Types.integerConstantValue (.iconstant number .decimal none) = .ok number := by
  have lower : -(2147483648 : Int) ≤ number := bounded.1
  have upper : number < (2147483648 : Int) := bounded.2
  simp [Types.integerConstantValue, Types.constantIntegerLayout,
    Silmaril.Compile.C.constantType, lower, upper]
  rfl

private theorem literal_action (number : Int) (bounded : LiteralEmission.IsInt32 number) :
    Lower.expr (Expression.literal number).ail = (do Lower.norm (← Lower.constReg number) 4 true) := by
  rw [Lower.expr.eq_def]
  change Lower.constant (.integer (.iconstant number .decimal none)) (.int 4 true) = _
  simp only [Lower.constant, Types.Registered.integerConstantValue, constant_value number bounded]
  rfl

private theorem binary_action (operator : Operator) (left right : Expression) :
    Lower.expr (Expression.binary operator left right).ail = (do
      let a ← Lower.expr left.ail
      let b ← Lower.expr right.ail
      let first ← Lower.unop .sext32 a
      let last ← Lower.unop .sext32 b
      let result ← Lower.binop (operation operator) first last
      Lower.unop .sext32 result) := by
  funext context
  rw [Lower.expr.eq_def]
  change (show Lower.M Mir.Reg from do
    let a ← Lower.expr left.ail
    let b ← Lower.expr right.ail
    Lower.arithValues operator.ail (.int 4 true)
      (Types.Registered.typeOf context.tags left.ail)
      (Types.Registered.typeOf context.tags right.ail) a b).run context = _
  rw [registered_actual_type, registered_actual_type]
  cases operator <;> rfl

/-- Actual lowering at any function context, instruction prefix and allocator.
Only the real instruction buffer and fresh-register cursor are changed. -/
theorem expression_lowered (expression : Expression) (bounded : expression.Bounded) :
    Lower.expr expression.ail = fun _ state =>
      .ok ((plan expression state.nextReg).result, (plan expression state.nextReg).write state) := by
  induction expression with
  | literal number =>
    show Lower.expr (Expression.literal number).ail = fun _ state =>
      .ok ((plan (.literal number) state.nextReg).result, (plan (.literal number) state.nextReg).write state)
    rw [literal_action number bounded]
    funext context state
    change Except.ok (state.nextReg + 1,
      {state with
        nextReg := state.nextReg + 2,
        instrs := (state.instrs.push (.op (.const state.nextReg (BitVec.ofInt 64 number)))).push
          (.op (.unary .sext32 (state.nextReg + 1) state.nextReg))}) =
      .ok ((plan (.literal number) state.nextReg).result, (plan (.literal number) state.nextReg).write state)
    simp only [plan, ExpressionPlan.write, Array.push_eq_append, Array.append_assoc]
    rfl
  | binary operator left right leftInduction rightInduction =>
    show Lower.expr (Expression.binary operator left right).ail = fun _ state =>
      .ok ((plan (.binary operator left right) state.nextReg).result,
        (plan (.binary operator left right) state.nextReg).write state)
    have first : Lower.expr left.ail = fun _ state =>
        .ok ((plan left state.nextReg).result, (plan left state.nextReg).write state) := leftInduction bounded.1
    have last : Lower.expr right.ail = fun _ state =>
        .ok ((plan right state.nextReg).result, (plan right state.nextReg).write state) := rightInduction bounded.2.1
    rw [binary_action, first, last]
    funext context state
    let firstPlan := plan left state.nextReg
    let lastPlan := plan right firstPlan.nextReg
    change Except.ok (lastPlan.nextReg + 3,
      {state with
        nextReg := lastPlan.nextReg + 4,
        instrs := (((((state.instrs ++ firstPlan.instructions.toArray) ++ lastPlan.instructions.toArray).push
          (.op (.unary .sext32 lastPlan.nextReg firstPlan.result))).push
          (.op (.unary .sext32 (lastPlan.nextReg + 1) lastPlan.result))).push
          (.op (.binary (operation operator) (lastPlan.nextReg + 2) lastPlan.nextReg (lastPlan.nextReg + 1)))).push
          (.op (.unary .sext32 (lastPlan.nextReg + 3) (lastPlan.nextReg + 2)))}) =
      .ok ((plan (.binary operator left right) state.nextReg).result,
        (plan (.binary operator left right) state.nextReg).write state)
    simp only [plan, ExpressionPlan.write, Array.push_eq_append, Array.append_assoc, List.append_toArray,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- Exact allocator/result positions of the real instruction plan. -/
theorem plan_cursor (expression : Expression) (next : Nat) :
    (plan expression next).nextReg = next + 6 * expression.operations + 2 ∧
      (plan expression next).result + 1 = (plan expression next).nextReg ∧
      next ≤ (plan expression next).result := by
  induction expression generalizing next with
  | literal number => simp [plan, Expression.operations]
  | binary operator left right first last =>
    have firstCursor := first next
    have lastCursor := last (plan left next).nextReg
    change (plan right (plan left next).nextReg).nextReg + 4 =
        next + 6 * (1 + left.operations + right.operations) + 2 ∧
      (plan right (plan left next).nextReg).nextReg + 3 + 1 =
        (plan right (plan left next).nextReg).nextReg + 4 ∧
      next ≤ (plan right (plan left next).nextReg).nextReg + 3
    omega

theorem plan_length (expression : Expression) (next : Nat) :
    (plan expression next).instructions.length = 6 * expression.operations + 2 := by
  induction expression generalizing next with
  | literal number => rfl
  | binary operator left right first last =>
    have firstLength := first next
    have lastLength := last (plan left next).nextReg
    simp only [plan, List.length_append, List.length_cons, List.length_nil, Expression.operations]
    omega

/-- The actual native address-taken scan visits the real tree without adding
any directly addressed identifier. No analysis soundness is assumed. -/
theorem address_free (expression : Expression) (accumulator : Std.HashSet Nat) :
    Analysis.addrTakenExpression expression.ail accumulator = accumulator := by
  induction expression generalizing accumulator with
  | literal number =>
    rw [Analysis.addrTakenExpression.eq_def]
    rfl
  | binary operator left right first last =>
    rw [Analysis.addrTakenExpression.eq_def]
    change Analysis.addrTakenExpression right.ail (Analysis.addrTakenExpression left.ail accumulator) = accumulator
    rw [first, last]

theorem body_address_free (expression : Expression) (accumulator : Std.HashSet Nat) :
    Analysis.addrTakenStatement (Main.body expression) accumulator = accumulator := by
  rw [Analysis.addrTakenStatement.eq_def]
  change Analysis.addrTakenStatement
    (.mk .unknown ⟨false, none⟩ (.mk []) (.return_ expression.ail)) accumulator = accumulator
  rw [Analysis.addrTakenStatement.eq_def]
  exact address_free expression accumulator

section SymbolicLowering
private def BoundedExpression := {expression : Expression // expression.Bounded}
private def sourceSyntax (expression : BoundedExpression) : Expression := expression.val
attribute [local cbv_opaque] sourceSyntax
private def expressionOutput (expression : BoundedExpression) (next : Nat) : ExpressionPlan :=
  plan (sourceSyntax expression) next
attribute [local cbv_opaque] expressionOutput
private theorem selected_output (expression : BoundedExpression) (next : Nat) :
    plan (sourceSyntax expression) next = expressionOutput expression next := rfl
attribute [local cbv_eval] selected_output
private theorem selected_expression (expression : BoundedExpression) :
    Lower.expr (sourceSyntax expression).ail = fun _ state =>
      .ok ((expressionOutput expression state.nextReg).result,
        (expressionOutput expression state.nextReg).write state) :=
  expression_lowered (sourceSyntax expression) expression.property
attribute [local cbv_opaque] Lower.expr Expression.ail Types.typeOf Types.Registered.typeOf Analysis.addrTakenExpression
attribute [local cbv_eval] selected_expression actual_type registered_actual_type body_address_free address_free
private theorem empty_push {α : Type} (value : α) : (#[] : Array α).push value = #[value] := rfl
private theorem singleton_push {α : Type} (first last : α) : #[first].push last = #[first, last] := rfl
private theorem pair_push {α : Type} (first middle last : α) : #[first, middle].push last = #[first, middle, last] := rfl
attribute [local cbv_opaque] Array.append Array.push
attribute [local cbv_eval] empty_push singleton_push pair_push Array.empty_append Array.append_empty

set_option maxHeartbeats 200000 in
set_option cbv.maxSteps 500000 in
private theorem compile_bounded (expression : BoundedExpression) (tag : String) :
    Lower.compile tag (Main.program (sourceSyntax expression)) = .ok (artifact (sourceSyntax expression)) := by
  have allocated : 2 < (expressionOutput expression 2).nextReg.succ := by
    change 2 < (plan (sourceSyntax expression) 2).nextReg + 1
    have cursor := (plan_cursor (sourceSyntax expression) 2).1
    omega
  cbv
  simp [allocated]

/-- Actual native separate compilation of the same real typed-Ail source.
The conclusion retains its real ABI/frame metadata and reserved prologue. -/
theorem compile (expression : Expression) (bounded : expression.Bounded) (tag : String) :
    Lower.compile tag (Main.program expression) = .ok (artifact expression) :=
  compile_bounded ⟨expression, bounded⟩ tag
end SymbolicLowering

/-- Registers preceding the expression's fresh range retain their complete
partial values, including unwritten registers. -/
theorem frame_below (expression : Expression) (next : Nat) (initial : Lir.Frame Nat)
    (register : Nat) (below : register < next) :
    (frame expression next initial).get register = initial.get register := by
  induction expression generalizing next initial with
  | literal number =>
    have first : register ≠ next := by omega
    have last : register ≠ next + 1 := by omega
    simp only [frame, Lir.Frame.get_set, first, last, ite_false]
  | binary operator left right first last =>
    show (frame (.binary operator left right) next initial).get register = initial.get register
    let firstPlan := plan left next
    let lastPlan := plan right firstPlan.nextReg
    have firstCursor : firstPlan.nextReg = next + 6 * left.operations + 2 := (plan_cursor left next).1
    have lastCursor : lastPlan.nextReg = firstPlan.nextReg + 6 * right.operations + 2 :=
      (plan_cursor right firstPlan.nextReg).1
    have firstLower : next ≤ firstPlan.nextReg := by omega
    have lastLower : firstPlan.nextReg ≤ lastPlan.nextReg := by omega
    have baseLower : next ≤ lastPlan.nextReg := firstLower.trans lastLower
    have n0 : register ≠ lastPlan.nextReg := by omega
    have n1 : register ≠ lastPlan.nextReg + 1 := by omega
    have n2 : register ≠ lastPlan.nextReg + 2 := by omega
    have n3 : register ≠ lastPlan.nextReg + 3 := by omega
    change (((((frame right firstPlan.nextReg (frame left next initial)).set lastPlan.nextReg _).set
      (lastPlan.nextReg + 1) _).set (lastPlan.nextReg + 2) _).set (lastPlan.nextReg + 3) _).get register = _
    simp only [Lir.Frame.get_set, n0, n1, n2, n3, ite_false]
    exact (last firstPlan.nextReg (frame left next initial) (below.trans_le firstLower)).trans
      (first next initial below)

private theorem word_operation (operator : Operator) (left right : Int) :
    rawWord operator left right = BitVec.ofInt 64 (operator.apply left right) := by
  cases operator with
  | add => exact (BitVec.ofInt_add left right).symm
  | sub =>
    change BitVec.ofInt 64 left - BitVec.ofInt 64 right = BitVec.ofInt 64 (left - right)
    rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
    rfl
  | mul => exact (BitVec.ofInt_mul left right).symm

private theorem normalized_operation (operator : Operator) (left right : Int)
    (bounded : LiteralEmission.IsInt32 (operator.apply left right)) :
    AdditionLower.normalize (rawWord operator left right) = BitVec.ofInt 64 (operator.apply left right) := by
  rw [word_operation]
  exact LiteralEmission.word_normalized _ bounded

theorem frame_result (expression : Expression) (bounded : expression.Bounded) (next : Nat)
    (initial : Lir.Frame Nat) :
    (frame expression next initial).get (plan expression next).result = some (BitVec.ofInt 64 expression.value) := by
  cases expression with
  | literal number =>
    change ((initial.set next (BitVec.ofInt 64 number)).set (next + 1)
      (AdditionLower.normalize (BitVec.ofInt 64 number))).get (next + 1) = _
    rw [Lir.Frame.get_set]
    simp only [ite_true]
    exact congrArg some (LiteralEmission.word_normalized number bounded)
  | binary operator left right =>
    simp only [frame, plan, Lir.Frame.get_set, ite_true]
    exact congrArg some (normalized_operation operator left.value right.value bounded.2.2)

private theorem unary_instruction (summaries : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory)
    (destination input : Nat) (number : Int) (bounded : LiteralEmission.IsInt32 number)
    (read : source.get input = some (BitVec.ofInt 64 number)) :
    InstructionExec summaries (.op (.unary .sext32 destination input)) source memory
      (source.set destination (BitVec.ofInt 64 number)) memory := by
  have normalized : Lir.Unop.sext32.eval (BitVec.ofInt 64 number) = BitVec.ofInt 64 number :=
    LiteralEmission.word_normalized number bounded
  exact .op (by simp only [Lir.Op.exec, read, normalized, Option.map_some])

private theorem operation_eval (operator : Operator) (left right : Int) :
    (operation operator).eval (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) =
      some (BitVec.ofInt 64 (operator.apply left right)) := by
  cases operator with
  | add => exact congrArg some (word_operation .add left right)
  | sub => exact congrArg some (word_operation .sub left right)
  | mul => exact congrArg some (word_operation .mul left right)

private theorem binary_instructions (summaries : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory)
    (operator : Operator) (left right : Int) (first last base : Nat)
    (leftBound : LiteralEmission.IsInt32 left) (rightBound : LiteralEmission.IsInt32 right)
    (resultBound : LiteralEmission.IsInt32 (operator.apply left right))
    (readLeft : source.get first = some (BitVec.ofInt 64 left))
    (readRight : source.get last = some (BitVec.ofInt 64 right)) (earlier : last < base) :
    InstructionsExec summaries
      [.op (.unary .sext32 base first), .op (.unary .sext32 (base + 1) last),
        .op (.binary (operation operator) (base + 2) base (base + 1)),
        .op (.unary .sext32 (base + 3) (base + 2))] source memory
      ((((source.set base (BitVec.ofInt 64 left)).set (base + 1) (BitVec.ofInt 64 right)).set
        (base + 2) (BitVec.ofInt 64 (operator.apply left right))).set
        (base + 3) (BitVec.ofInt 64 (operator.apply left right))) memory := by
  have notBase : last ≠ base := by omega
  have distinct : base ≠ base + 1 := by omega
  refine .cons (unary_instruction summaries source memory base first left leftBound readLeft)
    (.cons (unary_instruction summaries _ memory (base + 1) last right rightBound ?_)
    (.cons (.op ?_) (.cons (unary_instruction summaries _ memory (base + 3) (base + 2)
      (operator.apply left right) resultBound ?_) .nil)))
  · simpa only [Lir.Frame.get_set, notBase, ite_false] using readRight
  · simp only [Lir.Op.exec, Lir.Frame.get_set, distinct, ite_false, ite_true,
      operation_eval, Option.bind_some, Option.map_some]
  · simp only [Lir.Frame.get_set, ite_true]

/-- Every selected instruction executes from an arbitrary incoming partial
frame. All actual reads are derived from earlier writes; memory is unchanged. -/
theorem expression_executed (expression : Expression) (bounded : expression.Bounded)
    (summaries : OpenCalls) (next : Nat) (initial : Lir.Frame Nat) (memory : Lir.Memory) :
    InstructionsExec summaries (plan expression next).instructions initial memory (frame expression next initial) memory := by
  induction expression generalizing next initial with
  | literal number =>
    change InstructionsExec summaries
      [.op (.const next (BitVec.ofInt 64 number)), .op (.unary .sext32 (next + 1) next)] initial memory
      ((initial.set next (BitVec.ofInt 64 number)).set (next + 1)
        (AdditionLower.normalize (BitVec.ofInt 64 number))) memory
    refine .cons (.op rfl) (.cons (.op ?_) .nil)
    simp only [Lir.Op.exec, Lir.Frame.get_set, ite_true, Option.map_some]
    rfl
  | binary operator left right first last =>
    show InstructionsExec summaries (plan (.binary operator left right) next).instructions initial memory
      (frame (.binary operator left right) next initial) memory
    let firstPlan := plan left next
    let lastPlan := plan right firstPlan.nextReg
    let middle := frame right firstPlan.nextReg (frame left next initial)
    have firstRun : InstructionsExec summaries firstPlan.instructions initial memory
        (frame left next initial) memory := first bounded.1 next initial
    have lastRun : InstructionsExec summaries lastPlan.instructions (frame left next initial) memory
        middle memory := last bounded.2.1 firstPlan.nextReg (frame left next initial)
    have beforeLast : firstPlan.result < firstPlan.nextReg := by
      have cursor : (plan left next).result + 1 = (plan left next).nextReg := (plan_cursor left next).2.1
      change (plan left next).result < (plan left next).nextReg
      omega
    have leftRead : middle.get firstPlan.result = some (BitVec.ofInt 64 left.value) :=
      (frame_below right firstPlan.nextReg (frame left next initial) firstPlan.result beforeLast).trans
        (frame_result left bounded.1 next initial)
    have rightRead : middle.get lastPlan.result = some (BitVec.ofInt 64 right.value) :=
      frame_result right bounded.2.1 firstPlan.nextReg (frame left next initial)
    have lastEarlier : lastPlan.result < lastPlan.nextReg := by
      have cursor : (plan right firstPlan.nextReg).result + 1 = (plan right firstPlan.nextReg).nextReg :=
        (plan_cursor right firstPlan.nextReg).2.1
      change (plan right firstPlan.nextReg).result < (plan right firstPlan.nextReg).nextReg
      omega
    have tail := binary_instructions summaries middle memory operator left.value right.value
      firstPlan.result lastPlan.result lastPlan.nextReg (bounded_value left bounded.1)
      (bounded_value right bounded.2.1) bounded.2.2 leftRead rightRead lastEarlier
    have post : frame (.binary operator left right) next initial =
        ((((middle.set lastPlan.nextReg (BitVec.ofInt 64 left.value)).set
          (lastPlan.nextReg + 1) (BitVec.ofInt 64 right.value)).set
          (lastPlan.nextReg + 2) (BitVec.ofInt 64 (operator.apply left.value right.value))).set
          (lastPlan.nextReg + 3) (BitVec.ofInt 64 (operator.apply left.value right.value))) := by
      have raw : rawWord operator left.value right.value = BitVec.ofInt 64 (operator.apply left.value right.value) :=
        word_operation operator left.value right.value
      simp only [frame]
      have normalized : AdditionLower.normalize (BitVec.ofInt 64 (operator.apply left.value right.value)) =
          BitVec.ofInt 64 (operator.apply left.value right.value) :=
        LiteralEmission.word_normalized _ bounded.2.2
      rw [raw, normalized]
    rw [post]
    exact (firstRun.append lastRun).append tail

/-- The real body appends its final return-width normalization to the
recursive instruction plan and returns the actual written register. -/
theorem body_executed (expression : Expression) (bounded : expression.Bounded)
    (summaries : OpenCalls) (initial : Lir.Frame Nat) (memory : Lir.Memory) :
    BlockExec summaries (body expression) initial memory (.returned [BitVec.ofInt 64 expression.value])
      (bodyFrame expression initial) memory := by
  have instructions := expression_executed expression bounded summaries 2 initial memory
  have final := unary_instruction summaries (frame expression 2 initial) memory
    (plan expression 2).nextReg (plan expression 2).result expression.value
    (bounded_value expression bounded) (frame_result expression bounded 2 initial)
  refine ⟨?_, .ret ?_⟩
  · simpa only [body, Array.toList_push, List.toList_toArray, bodyFrame] using
      instructions.append (.cons final .nil)
  · simp [bodyFrame, Lir.Frame.readAll, Lir.Frame.read]

end Silmaril.Compiler.Native.Correctness.ArithmeticLower
