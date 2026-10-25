module

public import Silmaril.Wasm.Binaryen.Syntax

@[expose] public section

/-! # Lowering and lifting: the definition of the IR

**An IR program means its lowering.** `BExpr.lower` maps a folded tree to the
Core 3.0 instruction sequence that computes it (operands first, then the
operator), `BModule.lower` maps every function body, and nothing else changes.
Every semantic notion of the IR (`Binaryen/Behaviour.lean`) is the Core 3.0
notion of the lowered module, and every pass theorem is a Core 3.0 theorem.

Lowering is total and structural. It is the composition of Binaryen's
`BinaryenIRWriter` (`src/wasm-stack.h`, `visit`/`visitBlock`, version_133) with
the stack-to-text identity, *without* its skip-after-unreachable step: that
step is the DCE pass (`Binaryen/Pass/DCE.lean`), so lowering stays exact.

Lifting:

* `liftFlat` puts every instruction in a leaf; `lower_lift` is the **exact**
  inverse property `(BModule.lift m).lower = m`, proved here.
* `liftInstrs` rebuilds structured control as tree nodes (`lowerList_liftInstrs`).
* `fold` rebuilds operand trees from arities, as Binaryen's `IRBuilder`
  (`src/wasm/wasm-ir-builder.cpp`) does; it never changes the lowering
  (`lowerList_fold`), whatever arity function it is given.
-/

namespace Silmaril.Wasm.Binaryen

mutual
/-- Lower one folded tree to Core 3.0 instructions. -/
def BExpr.lower : BExpr → List Instr
  | .op i args => BExpr.lowerList args ++ [i]
  | .block bt body => [.block bt (BExpr.lowerList body)]
  | .loop bt body => [.loop bt (BExpr.lowerList body)]
  | .if_ bt c t e => BExpr.lowerList c ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
  | .tryTable bt cs body => [.tryTable bt cs (BExpr.lowerList body)]
/-- Lower a list of trees: concatenation of the lowerings. -/
def BExpr.lowerList : List BExpr → List Instr
  | [] => []
  | e :: es => BExpr.lower e ++ BExpr.lowerList es
end

namespace BExpr

@[simp] theorem lowerList_nil : lowerList [] = [] := rfl

@[simp] theorem lowerList_cons (e : BExpr) (es : List BExpr) :
    lowerList (e :: es) = e.lower ++ lowerList es := rfl

@[simp] theorem lower_op (i : Instr) (args : List BExpr) :
    (BExpr.op i args).lower = lowerList args ++ [i] := rfl

@[simp] theorem lowerList_append (es es' : List BExpr) :
    lowerList (es ++ es') = lowerList es ++ lowerList es' := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ih, List.append_assoc]

theorem lowerList_eq_flatMap (es : List BExpr) : lowerList es = es.flatMap BExpr.lower := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ih, List.flatMap_cons]

@[simp] theorem lowerList_singleton (e : BExpr) : lowerList [e] = e.lower := by simp

end BExpr

/-! ## Flat lifting: the exact inverse -/

/-- Put a Core instruction in a leaf. -/
def liftFlat (i : Instr) : BExpr := .op i []

@[simp] theorem lower_liftFlat (i : Instr) : (liftFlat i).lower = [i] := rfl

@[simp] theorem lowerList_map_liftFlat (is : List Instr) :
    BExpr.lowerList (is.map liftFlat) = is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

/-- Lower a module: lower every function body; keep everything else. -/
def BModule.lower (m : BModule) : Module :=
  { m.base with funcs := m.funcs.map (Declaration.Func.mapBody BExpr.lowerList) }

/-- Lift a Core module to layer D with every instruction in a leaf. -/
def BModule.lift (m : Module) : BModule :=
  ⟨m, m.funcs.map (Declaration.Func.mapBody (List.map liftFlat))⟩

theorem mapBody_lift_lower (f : Func) :
    Declaration.Func.mapBody BExpr.lowerList
      (Declaration.Func.mapBody (List.map liftFlat) f) = f := by
  rcases f with ⟨t, ls, body⟩
  simp [Declaration.Func.mapBody]

/-- **Lowering inverts lifting, exactly.** Every Core 3.0 module is the lowering of
an IR module, so the IR loses no Core program. -/
theorem lower_lift (m : Module) : (BModule.lift m).lower = m := by
  cases m with
  | mk types imports tags globals memories tables funcs data elems start exports =>
    have h : (funcs.map (Declaration.Func.mapBody (List.map liftFlat))).map
        (Declaration.Func.mapBody BExpr.lowerList) = funcs := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id funcs]
      exact List.map_congr_left (fun f _ => mapBody_lift_lower f)
    simp only [BModule.lower, BModule.lift, h]

/-! ## Structured lifting -/

mutual
/-- Rebuild structured control as tree nodes; flat instructions become leaves. -/
def liftInstr : Instr → BExpr
  | .block bt body => .block bt (liftInstrs body)
  | .loop bt body => .loop bt (liftInstrs body)
  | .if_ bt t e => .if_ bt [] (liftInstrs t) (liftInstrs e)
  | .tryTable bt cs body => .tryTable bt cs (liftInstrs body)
  | i => .op i []
/-- `liftInstr` on a list. -/
def liftInstrs : List Instr → List BExpr
  | [] => []
  | i :: is => liftInstr i :: liftInstrs is
end

theorem lowerList_liftInstrs_of (is : List Instr)
    (h : ∀ j ∈ is, (liftInstr j).lower = [j]) : BExpr.lowerList (liftInstrs is) = is := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    simp only [liftInstrs, BExpr.lowerList_cons]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]
    rfl

theorem structuredList_liftInstrs_of (is : List Instr)
    (h : ∀ j ∈ is, BExpr.structured (liftInstr j) = true) :
    BExpr.structuredList (liftInstrs is) = true := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    simp only [liftInstrs, BExpr.structuredList]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]
    rfl

/-- `liftInstr` is lowering-exact, by induction on a size bound. -/
theorem lower_liftInstr_lt : ∀ (n : Nat) (i : Instr), sizeOf i < n → (liftInstr i).lower = [i]
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hb : ∀ body : List Instr, sizeOf body < sizeOf i →
        BExpr.lowerList (liftInstrs body) = body := fun body hlt =>
      lowerList_liftInstrs_of body fun j hj =>
        lower_liftInstr_lt n j (by have := List.sizeOf_lt_of_mem hj; omega)
    cases i
    case block bt body =>
      simp only [liftInstr, BExpr.lower]
      rw [hb body (by simp only [Instr.block.sizeOf_spec]; omega)]
    case loop bt body =>
      simp only [liftInstr, BExpr.lower]
      rw [hb body (by simp only [Instr.loop.sizeOf_spec]; omega)]
    case if_ bt t e =>
      simp only [liftInstr, BExpr.lower, BExpr.lowerList_nil, List.nil_append]
      rw [hb t (by simp only [Instr.if_.sizeOf_spec]; omega),
        hb e (by simp only [Instr.if_.sizeOf_spec]; omega)]
    case tryTable bt cs body =>
      simp only [liftInstr, BExpr.lower]
      rw [hb body (by simp only [Instr.tryTable.sizeOf_spec]; omega)]
    all_goals rfl

/-- `liftInstr` produces structured trees, by induction on a size bound. -/
theorem structured_liftInstr_lt :
    ∀ (n : Nat) (i : Instr), sizeOf i < n → BExpr.structured (liftInstr i) = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hb : ∀ body : List Instr, sizeOf body < sizeOf i →
        BExpr.structuredList (liftInstrs body) = true := fun body hlt =>
      structuredList_liftInstrs_of body fun j hj =>
        structured_liftInstr_lt n j (by have := List.sizeOf_lt_of_mem hj; omega)
    cases i
    case block bt body =>
      simp only [liftInstr, BExpr.structured]
      exact hb body (by simp only [Instr.block.sizeOf_spec]; omega)
    case loop bt body =>
      simp only [liftInstr, BExpr.structured]
      exact hb body (by simp only [Instr.loop.sizeOf_spec]; omega)
    case if_ bt t e =>
      simp only [liftInstr, BExpr.structured]
      rw [hb t (by simp only [Instr.if_.sizeOf_spec]; omega),
        hb e (by simp only [Instr.if_.sizeOf_spec]; omega)]
      rfl
    case tryTable bt cs body =>
      simp only [liftInstr, BExpr.structured]
      exact hb body (by simp only [Instr.tryTable.sizeOf_spec]; omega)
    all_goals rfl

theorem lower_liftInstr (i : Instr) : (liftInstr i).lower = [i] :=
  lower_liftInstr_lt _ i (Nat.lt_succ_self _)

/-- Structured lifting is lowering-exact. -/
theorem lowerList_liftInstrs (is : List Instr) : BExpr.lowerList (liftInstrs is) = is :=
  lowerList_liftInstrs_of is fun j _ => lower_liftInstr j

/-- Structured lifting produces structured trees. -/
theorem structuredList_liftInstrs (is : List Instr) :
    BExpr.structuredList (liftInstrs is) = true :=
  structuredList_liftInstrs_of is fun j _ => structured_liftInstr_lt _ j (Nat.lt_succ_self _)

/-! ## Folding (IRBuilder-style tree reconstruction) -/

/-- One step of the folding stack machine. The stack holds finished trees, most
recent first. An instruction of arity `n > 0` with `n` finished trees available
takes them as its operands. -/
def foldStep (arity : Instr → Option Nat) (stk : List BExpr) : BExpr → List BExpr
  | .op i [] =>
    match arity i with
    | some (n + 1) =>
      if n + 1 ≤ stk.length then .op i (stk.take (n + 1)).reverse :: stk.drop (n + 1)
      else .op i [] :: stk
    | _ => .op i [] :: stk
  | e => e :: stk

/-- Fold a list of trees: rebuild operand trees from `arity` (Binaryen's
`IRBuilder::pushExpression`/`pop`, `src/wasm/wasm-ir-builder.cpp`, version_133).
The validator's arities give Binaryen's trees; any other arity is still sound. -/
def fold (arity : Instr → Option Nat) (es : List BExpr) : List BExpr :=
  (es.foldl (foldStep arity) []).reverse

theorem lowerList_reverse_take_drop (stk : List BExpr) (i : Instr) (k : Nat) :
    BExpr.lowerList ((BExpr.op i (stk.take k).reverse) :: stk.drop k).reverse =
      BExpr.lowerList stk.reverse ++ [i] := by
  have h : stk.reverse = (stk.drop k).reverse ++ (stk.take k).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [h]
  simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton,
    BExpr.lower_op, List.append_assoc]

/-- One folding step appends the lowering of the folded tree. -/
theorem lowerList_foldStep (arity : Instr → Option Nat) (stk : List BExpr) (e : BExpr) :
    BExpr.lowerList (foldStep arity stk e).reverse = BExpr.lowerList stk.reverse ++ e.lower := by
  unfold foldStep
  split
  · split
    · split
      · exact lowerList_reverse_take_drop _ _ _
      · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]
    · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]
  · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]

/-- The folding invariant: the stack's (reversed) lowering followed by the rest. -/
theorem lowerList_foldl_foldStep (arity : Instr → Option Nat) (es : List BExpr)
    (stk : List BExpr) :
    BExpr.lowerList (es.foldl (foldStep arity) stk).reverse =
      BExpr.lowerList stk.reverse ++ BExpr.lowerList es := by
  induction es generalizing stk with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, lowerList_foldStep, BExpr.lowerList_cons, List.append_assoc]

/-- **Folding never changes the lowering**, for every arity function. Hence
fold/unfold is an equivalence by equality of lowerings (`Pass/Free.lean`). -/
theorem lowerList_fold (arity : Instr → Option Nat) (es : List BExpr) :
    BExpr.lowerList (fold arity es) = BExpr.lowerList es := by
  have h := lowerList_foldl_foldStep arity es []
  simpa [fold] using h

end Silmaril.Wasm.Binaryen
