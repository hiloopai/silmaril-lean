module

public import Silmaril.Compiler.Decompile.WordC.Defs
@[expose] public section
namespace Silmaril.Compiler.Decompile.WordC

open Silmaril.X86 (Word Reg MState)
open Silmaril.X86.Decompile.SemLift
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion
open Silmaril.Compile.C.Sem

theorem word_of_encode (value : Word) : BitVec.ofInt 64 (value.toNat : Int) = value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt]

theorem wrap_as_word (value : Int) :
    C0.wrap 8 false value = ((BitVec.ofInt 64 value).toNat : Int) := by
  unfold C0.wrap
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.toNat_ofInt]
  change value % 18446744073709551616 = ((value % 18446744073709551616).toNat : Int)
  exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))).symm

@[simp] theorem wrap_encode (value : Word) :
    C0.wrap 8 false (value.toNat : Int) = value.toNat := by
  rw [wrap_as_word, word_of_encode]

theorem wrap_add (left right : Word) :
    C0.wrap 8 false ((left.toNat : Int) + right.toNat) = (left + right).toNat := by
  rw [wrap_as_word, BitVec.ofInt_add, word_of_encode, word_of_encode]

theorem wrap_sub (left right : Word) :
    C0.wrap 8 false ((left.toNat : Int) - right.toNat) = (left - right).toNat := by
  rw [wrap_as_word, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    word_of_encode, word_of_encode, ← sub_eq_add_neg]

theorem wrap_mul (left right : Word) :
    C0.wrap 8 false ((left.toNat : Int) * right.toNat) = (left * right).toNat := by
  rw [wrap_as_word, BitVec.ofInt_mul, word_of_encode, word_of_encode]

@[simp] theorem wordValue_literal (values : String → Word) (value : Int) :
    wordValue values (.literal value) = BitVec.ofInt 64 value := rfl

@[simp] theorem wordValue_var (values : String → Word) (name : String) :
    wordValue values (.var name) = values name := word_of_encode _

@[simp] theorem wordValue_add (values : String → Word) (left right : Pure.Term) :
    wordValue values (.add left right) = wordValue values left + wordValue values right :=
  BitVec.ofInt_add _ _

@[simp] theorem wordValue_sub (values : String → Word) (left right : Pure.Term) :
    wordValue values (.sub left right) = wordValue values left - wordValue values right := by
  simp only [wordValue, Pure.Term.eval, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]

@[simp] theorem wordValue_mul (values : String → Word) (left right : Pure.Term) :
    wordValue values (.mul left right) = wordValue values left * wordValue values right :=
  BitVec.ofInt_mul _ _

@[simp] theorem unsignedExpr_type (node : ExpressionNode GenTypeCategory) :
    Silmaril.Compile.C.typeOf (unsignedExpr node) = .int 8 false := rfl

@[simp] theorem toAil_type (symbols : String → Sym) (term : Pure.Term) :
    Silmaril.Compile.C.typeOf (toAil symbols term) = .int 8 false := by
  cases term <;> rfl

/-- Only source variables actually used by the term require initialized locals.
Values are unsigned word observations in the actual C0 environment. -/
def Locals (symbols : String → Sym) (values : String → Word) (env : C0.Env) :
    Pure.Term → Prop
  | .literal _ => True
  | .var name => env.locals[(symbols name).number]? = some (values name).toNat
  | .add left right | .sub left right | .mul left right =>
      Locals symbols values env left ∧ Locals symbols values env right

/-- Every generated unsigned expression evaluates in the existing C0 interpreter
to its modular 64-bit value and preserves the whole environment. Unsigned
wrapping removes the signed-overflow obligations; no evaluation oracle is
assumed. This is a theorem about C0, whose full Cerberus refinement is separate. -/
theorem toAil_eval (symbols : String → Sym) (values : String → Word)
    (program : C0.Prog) (function : C0.FunDef) (env : C0.Env) (term : Pure.Term)
    (locals : Locals symbols values env term) (fuel : Nat) (enough : height term ≤ fuel) :
    C0.evalE program fuel function (toAil symbols term) env =
      .ok ((wordValue values term).toNat, env) := by
  induction term generalizing fuel with
  | literal value =>
    cases fuel with
    | zero => simp [height] at enough
    | succ fuel =>
      change (Except.ok (C0.wrap 8 false ((BitVec.ofInt 64 value).toNat : Int), env) :
        Except C0.Stop (Int × C0.Env)) =
          .ok (((BitVec.ofInt 64 value).toNat : Int), env)
      rw [wrap_encode]
  | var name =>
    cases fuel with
    | zero => simp [height] at enough
    | succ fuel =>
      have localValue : env.locals[(symbols name).number]? = some ((values name).toNat : Int) := locals
      simp [toAil, C0.evalE, unsignedExpr, Expression.node, localExpr,
        C0.lvalSym, C0.readVar, localValue, Bind.bind, Except.bind, pure, Except.pure]
  | add left right leftIH rightIH =>
    show C0.evalE program fuel function (toAil symbols (.add left right)) env =
      .ok ((wordValue values (.add left right)).toNat, env)
    cases fuel with
    | zero => simp [height] at enough
    | succ fuel =>
      show C0.evalE program (fuel + 1) function (toAil symbols (.add left right)) env =
        .ok ((wordValue values (.add left right)).toNat, env)
      have heights : max (height left) (height right) + 1 ≤ fuel + 1 := enough
      have leftFuel : height left ≤ fuel := by omega
      have rightFuel : height right ≤ fuel := by omega
      have leftRun : C0.evalE program fuel function (toAil symbols left) env =
          .ok ((wordValue values left).toNat, env) := leftIH locals.1 fuel leftFuel
      have rightRun : C0.evalE program fuel function (toAil symbols right) env =
          .ok ((wordValue values right).toNat, env) := rightIH locals.2 fuel rightFuel
      have evaluated : C0.evalE program (fuel + 1) function (toAil symbols (.add left right)) env =
          .ok (C0.wrap 8 false
            (C0.wrap 8 false ((wordValue values left).toNat : Int) +
              C0.wrap 8 false ((wordValue values right).toNat : Int)), env) := by
        conv_lhs => unfold toAil
        rw [C0.evalE]
        simp only [unsignedExpr, Expression.node]
        rw [leftRun]
        simp only [Bind.bind, Except.bind]
        rw [rightRun]
        show (Except.ok (C0.wrap 8 false
          (C0.wrap 8 false ((wordValue values left).toNat : Int) +
            C0.wrap 8 false ((wordValue values right).toNat : Int)), env) :
              Except C0.Stop (Int × C0.Env)) = _
        rfl
      rw [evaluated]
      simp only [wrap_encode, wrap_add, wordValue_add]
  | sub left right leftIH rightIH =>
    show C0.evalE program fuel function (toAil symbols (.sub left right)) env =
      .ok ((wordValue values (.sub left right)).toNat, env)
    cases fuel with
    | zero => simp [height] at enough
    | succ fuel =>
      show C0.evalE program (fuel + 1) function (toAil symbols (.sub left right)) env =
        .ok ((wordValue values (.sub left right)).toNat, env)
      have heights : max (height left) (height right) + 1 ≤ fuel + 1 := enough
      have leftFuel : height left ≤ fuel := by omega
      have rightFuel : height right ≤ fuel := by omega
      have leftRun : C0.evalE program fuel function (toAil symbols left) env =
          .ok ((wordValue values left).toNat, env) := leftIH locals.1 fuel leftFuel
      have rightRun : C0.evalE program fuel function (toAil symbols right) env =
          .ok ((wordValue values right).toNat, env) := rightIH locals.2 fuel rightFuel
      have evaluated : C0.evalE program (fuel + 1) function (toAil symbols (.sub left right)) env =
          .ok (C0.wrap 8 false
            (C0.wrap 8 false ((wordValue values left).toNat : Int) -
              C0.wrap 8 false ((wordValue values right).toNat : Int)), env) := by
        conv_lhs => unfold toAil
        rw [C0.evalE]
        simp only [unsignedExpr, Expression.node]
        rw [leftRun]
        simp only [Bind.bind, Except.bind]
        rw [rightRun]
        show (Except.ok (C0.wrap 8 false
          (C0.wrap 8 false ((wordValue values left).toNat : Int) -
            C0.wrap 8 false ((wordValue values right).toNat : Int)), env) :
              Except C0.Stop (Int × C0.Env)) = _
        rfl
      rw [evaluated]
      simp only [wrap_encode, wrap_sub, wordValue_sub]
  | mul left right leftIH rightIH =>
    show C0.evalE program fuel function (toAil symbols (.mul left right)) env =
      .ok ((wordValue values (.mul left right)).toNat, env)
    cases fuel with
    | zero => simp [height] at enough
    | succ fuel =>
      show C0.evalE program (fuel + 1) function (toAil symbols (.mul left right)) env =
        .ok ((wordValue values (.mul left right)).toNat, env)
      have heights : max (height left) (height right) + 1 ≤ fuel + 1 := enough
      have leftFuel : height left ≤ fuel := by omega
      have rightFuel : height right ≤ fuel := by omega
      have leftRun : C0.evalE program fuel function (toAil symbols left) env =
          .ok ((wordValue values left).toNat, env) := leftIH locals.1 fuel leftFuel
      have rightRun : C0.evalE program fuel function (toAil symbols right) env =
          .ok ((wordValue values right).toNat, env) := rightIH locals.2 fuel rightFuel
      have evaluated : C0.evalE program (fuel + 1) function (toAil symbols (.mul left right)) env =
          .ok (C0.wrap 8 false
            (C0.wrap 8 false ((wordValue values left).toNat : Int) *
              C0.wrap 8 false ((wordValue values right).toNat : Int)), env) := by
        conv_lhs => unfold toAil
        rw [C0.evalE]
        simp only [unsignedExpr, Expression.node]
        rw [leftRun]
        simp only [Bind.bind, Except.bind]
        rw [rightRun]
        show (Except.ok (C0.wrap 8 false
          (C0.wrap 8 false ((wordValue values left).toNat : Int) *
            C0.wrap 8 false ((wordValue values right).toNat : Int)), env) :
              Except C0.Stop (Int × C0.Env)) = _
        rfl
      rw [evaluated]
      simp only [wrap_encode, wrap_mul, wordValue_mul]

theorem ssa_add (initial : MState) (left right : Ex) :
    (Ex.alu .q .add left right).eval initial.core initial.memory =
      left.eval initial.core initial.memory + right.eval initial.core initial.memory := by
  change (((left.eval initial.core initial.memory).setWidth 64) +
    ((right.eval initial.core initial.memory).setWidth 64)).setWidth 64 = _
  simp only [BitVec.setWidth_eq]

theorem ssa_sub (initial : MState) (left right : Ex) :
    (Ex.alu .q .sub left right).eval initial.core initial.memory =
      left.eval initial.core initial.memory - right.eval initial.core initial.memory := by
  change (((left.eval initial.core initial.memory).setWidth 64) -
    ((right.eval initial.core initial.memory).setWidth 64)).setWidth 64 = _
  simp only [BitVec.setWidth_eq]

theorem ssa_shift (initial : MState) (expression : Ex) (count : Nat) :
    (Ex.shift .q .shl expression count).eval initial.core initial.memory =
      expression.eval initial.core initial.memory <<< count := by
  change (((expression.eval initial.core initial.memory).setWidth 64) <<< count).setWidth 64 = _
  simp only [BitVec.setWidth_eq]

theorem bind2_success {α β γ : Type} {left : Except String α} {right : Except String β}
    {combine : α → β → γ} {output : γ}
    (accepted : (do return combine (← left) (← right)) = .ok output) :
    ∃ a b, left = .ok a ∧ right = .ok b ∧ output = combine a b := by
  cases left <;> cases right <;>
    simp_all [Bind.bind, Except.bind, pure, Except.pure]

/-- Successful SSA regeneration preserves its unsigned word value. Every
declared name must denote the register it replaces; there are no implicit
loads, signed arithmetic choices, or stale-register assumptions. -/
theorem fromSSA_sound (inputs : Reg → Option String) (values : String → Word)
    (initial : MState)
    (represented : ∀ register name, inputs register = some name →
      values name = initial.core.read register)
    {expression : Ex} {term : Pure.Term} (accepted : fromSSA inputs expression = .ok term) :
    wordValue values term = expression.eval initial.core initial.memory := by
  induction expression generalizing term with
  | reg register =>
    show wordValue values term = (Ex.reg register).eval initial.core initial.memory
    cases named : inputs register with
    | none =>
      have impossible : False := by simp [fromSSA, named] at accepted
      exact impossible.elim
    | some name =>
      have generated : Pure.Term.var name = term := by
        simpa only [fromSSA, named, Except.ok.injEq] using accepted
      rw [← generated]
      simpa only [wordValue_var, Ex.eval_reg] using represented register name named
  | const value =>
    have generated : Pure.Term.literal value.toNat = term := by
      simpa only [fromSSA, Except.ok.injEq] using accepted
    rw [← generated]
    simpa only [wordValue_literal, Ex.eval_const] using word_of_encode value
  | ld address bytes _ =>
    have impossible : False := by simp [fromSSA] at accepted
    exact impossible.elim
  | ext size expression ih =>
    cases size with
    | d =>
      have impossible : False := by simp [fromSSA] at accepted
      exact impossible.elim
    | q =>
      simpa only [Ex.eval_ext, extW, Silmaril.X86.Ext.Sz.bits, BitVec.setWidth_eq]
        using ih accepted
  | alu size operator left right leftIH rightIH =>
    show wordValue values term = (Ex.alu size operator left right).eval initial.core initial.memory
    cases size with
    | d =>
      have impossible : False := by simp [fromSSA] at accepted
      exact impossible.elim
    | q =>
      show wordValue values term = (Ex.alu .q operator left right).eval initial.core initial.memory
      cases operator with
      | add =>
        obtain ⟨a, b, leftRun, rightRun, generated⟩ :
            ∃ a b, fromSSA inputs left = .ok a ∧ fromSSA inputs right = .ok b ∧
              term = Pure.Term.add a b :=
          bind2_success (combine := Pure.Term.add) accepted
        rw [generated, wordValue_add, leftIH leftRun, rightIH rightRun, ssa_add]
      | sub =>
        obtain ⟨a, b, leftRun, rightRun, generated⟩ :
            ∃ a b, fromSSA inputs left = .ok a ∧ fromSSA inputs right = .ok b ∧
              term = Pure.Term.sub a b :=
          bind2_success (combine := Pure.Term.sub) accepted
        rw [generated, wordValue_sub, leftIH leftRun, rightIH rightRun, ssa_sub]
      | «or» | «and» | xor | cmp =>
        have impossible : False := by simp [fromSSA] at accepted
        exact impossible.elim
  | shift size operator expression count ih =>
    show wordValue values term = (Ex.shift size operator expression count).eval initial.core initial.memory
    cases size with
    | d =>
      have impossible : False := by simp [fromSSA] at accepted
      exact impossible.elim
    | q =>
      show wordValue values term = (Ex.shift .q operator expression count).eval initial.core initial.memory
      cases operator with
      | shl =>
        show wordValue values term = (Ex.shift .q .shl expression count).eval initial.core initial.memory
        by_cases bounded : count < 64
        · show wordValue values term = (Ex.shift .q .shl expression count).eval initial.core initial.memory
          cases child : fromSSA inputs expression with
          | error why =>
            have impossible : False := by simp [fromSSA, bounded, child] at accepted
            exact impossible.elim
          | ok term' =>
            have generated : Pure.Term.mul term'
                (.literal (BitVec.twoPow 64 count).toNat) = term := by
              simpa only [fromSSA, bounded, ↓reduceIte, child, Bind.bind, Except.bind,
                pure, Except.pure, Except.ok.injEq] using accepted
            rw [← generated, wordValue_mul, wordValue_literal, word_of_encode, ih child,
              ssa_shift, BitVec.shiftLeft_eq_mul_twoPow]
        ·
          have impossible : False := by simp [fromSSA, bounded] at accepted
          exact impossible.elim
      | shr | sar | rol | ror =>
        have impossible : False := by simp [fromSSA] at accepted
        exact impossible.elim
  | un size operator expression _ =>
    have impossible : False := by simp [fromSSA] at accepted
    exact impossible.elim
  | bswap size expression _ =>
    have impossible : False := by simp [fromSSA] at accepted
    exact impossible.elim

/-- Compose the checked native SSA graph with actual generated C0 evaluation.
The result includes real machine reachability, not only expression equality.
Control transfers and the final native RET remain outside this block theorem. -/
theorem checked_output_c0 (exit base : Word) (bytes : List Silmaril.X86.Byte)
    (instructions : Nat) (summary : Summary) (checked : check bytes instructions summary = true)
    (initial : MState)
    (admitted : Silmaril.X86.Decompile.VC.BlockPre bytes base summary initial)
    (output : Reg) (expression : Ex) (live : (output, expression) ∈ summary.outs)
    (inputs : Reg → Option String) (values : String → Word)
    (represented : ∀ register name, inputs register = some name →
      values name = initial.core.read register)
    {term : Pure.Term} (lowered : fromSSA inputs expression = .ok term)
    (symbols : String → Sym) (program : C0.Prog) (function : C0.FunDef) (env : C0.Env)
    (locals : Locals symbols values env term) :
    ∃ final, Silmaril.X86.Ext.Reaches exit initial final ∧
      C0.evalE program (height term) function (toAil symbols term) env =
        .ok ((final.core.read output).toNat, env) := by
  obtain ⟨final, execution, specified⟩ :=
    (Silmaril.X86.Decompile.VC.checked_block_summary exit base bytes instructions summary
      checked).runs initial trivial admitted
  have sourceRun := toAil_eval symbols values program function env term locals _ (Nat.le_refl _)
  rw [fromSSA_sound inputs values initial represented lowered,
    ← specified.values (output, expression) live] at sourceRun
  exact ⟨final, execution, sourceRun⟩

end Silmaril.Compiler.Decompile.WordC
