module

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Single

/-!
# Soundness of the basic-instruction proof rules

Figure 6 of Watt et al., plus the numeric instructions the paper leaves to
`unop`/`binop`/`testop`/`relop`/`cvtop` schemas. Each is an instance of
`valid_single_pure`: the instruction touches neither the heap nor any variable.

The `defined(binop, τ₁, τ₂)` and `defined(cvtop, τ)` predicates of the paper
become explicit pure preconditions naming the result, which is how a
nondeterministic numeric relation — the permitted NaN results of
`Execution.Numerics.floatBinOpRel` — is pinned down.

`valid_convert` deviates from `Triple.convert` as stated in
`Silmaril/Wasm/V1/Logic/Rules.lean`. The premise there,
`convertRel op τ (ok τ')` together with the absence of a trap, only says that
`τ'` is *a* permitted result; `convertRel` is nondeterministic on NaNs, so the
execution may produce a different one and the conclusion is unsound. See
`convertRel_demote_nondeterministic` below for a machine-checked counterexample.
The premise here is the universally quantified form already used by
`valid_floatUnOp` and `valid_floatBinOp`, and `Triple.convert` needs the same
correction.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert}

/-! ## Plumbing -/

/-- `(S | emp)` is `(S | emp ∧ ⊤)`, the shape `valid_single_pure` expects. -/
private theorem stack_eq_stackIf (S : List (Term Value)) :
    Assert.stack S = Assert.stackIf S fun _ => True := by
  funext ρ vs h
  simp [Assert.stack, Assert.stackIf, Assert.mk, HAssert.empAnd, HAssert.and, HAssert.pure]

/-- Strengthening the postcondition of a valid triple: the derived instance of
`[consequence]` needed where a rule's postcondition is an existential rather
than a literal `(S | emp ∧ φ)`. -/
private theorem valid_post {P Q Q' : Assert} {code : Silmaril.Wasm.V1.Expr}
    (hv : Valid host n F L R P code Q) (ent : Assert.Entails Q Q') :
    Valid host n F L R P code Q' := by
  intro s f ρ vs vf h hf o pre disj reify run
  obtain ⟨h', ρ', disj', reify', agree, sat⟩ := hv s f ρ vs vf h hf o pre disj reify run
  refine ⟨h', ρ', disj', reify', agree, ?_⟩
  cases hres : o.result with
  | normal ws =>
    rw [hres] at sat
    obtain ⟨ws', rfl, hq⟩ := sat
    exact ⟨ws', rfl, ent _ _ _ hq⟩
  | br l ws => rw [hres] at sat; exact sat
  | ret ws => rw [hres] at sat; exact sat
  | trap => rw [hres] at sat; exact sat.elim

/-- Two values of the same numeric type are equal only if their bits are. -/
private theorem value_inj {t : NumType} {a b : BitVec t.width}
    (h : (⟨t, a⟩ : Value) = ⟨t, b⟩) : a = b := by
  injection h with _ hbits

/-- Two integer values of the same type are equal only if their bits are. -/
private theorem value_int_inj {t : IntType} {a b : BitVec t.width}
    (h : Value.int t a = Value.int t b) : a = b := value_inj h

/-- Two floating values of the same type are equal only if their bits are. -/
private theorem value_float_inj {t : FloatType} {a b : BitVec t.width}
    (h : Value.float t a = Value.float t b) : a = b := value_inj h

/-! ## Inversion of the one-instruction executions

`Execution.Plain` and `Execution.PlainTrap` are indexed by the operand list,
which at the point of use is a `List.map` rather than a variable, so each
instruction is inverted once here with its operands still general, and once
more in the shape the rule presents them. -/

private theorem nop_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    (step : Plain s f args .nop s' f' rets) :
    args.length = 0 ∧ s' = s ∧ f' = f ∧ rets = [] := by
  cases step; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem nop_noTrap {s : Store H} {f : Frame} {args : List Value} :
    ¬ PlainTrap s f args .nop := by rintro step; cases step

private theorem intConst_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : IntType} {bits : BitVec t.width} (step : Plain s f args (.intConst t bits) s' f' rets) :
    args.length = 0 ∧ s' = s ∧ f' = f ∧ rets = [Value.int t bits] := by
  cases step; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem intConst_noTrap {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {bits : BitVec t.width} : ¬ PlainTrap s f args (.intConst t bits) := by
  rintro step; cases step

private theorem floatConst_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : FloatType} {bits : BitVec t.width}
    (step : Plain s f args (.floatConst t bits) s' f' rets) :
    args.length = 0 ∧ s' = s ∧ f' = f ∧ rets = [Value.float t bits] := by
  cases step; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem floatConst_noTrap {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {bits : BitVec t.width} : ¬ PlainTrap s f args (.floatConst t bits) := by
  rintro step; cases step

private theorem drop_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    (step : Plain s f args .drop s' f' rets) :
    args.length = 1 ∧ s' = s ∧ f' = f ∧ rets = [] := by
  cases step; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem drop_noTrap {s : Store H} {f : Frame} {args : List Value} :
    ¬ PlainTrap s f args .drop := by rintro step; cases step

private theorem select_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    (step : Plain s f args .select s' f' rets) :
    args.length = 3 ∧ s' = s ∧ f' = f ∧ ∃ (a b : Value) (c : BitVec 32),
      args = [a, b, Value.int .i32 c] ∧ rets = [if c = 0 then b else a] := by
  cases step
  · exact ⟨rfl, rfl, rfl, _, _, _, rfl, rfl⟩
  · rename_i nonzero
    refine ⟨rfl, rfl, rfl, _, _, _, rfl, ?_⟩
    rw [ite_eq_right nonzero]

private theorem select_effect {s s' : Store H} {f f' : Frame} {a b : Value} {c : BitVec 32}
    {rets : List Value} (step : Plain s f [a, b, Value.int .i32 c] .select s' f' rets) :
    s' = s ∧ f' = f ∧ rets = [if c = 0 then b else a] := by
  obtain ⟨-, rfl, rfl, a', b', c', hargs, rfl⟩ := select_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ hargs
  injection hargs with h₃ _
  subst h₁; subst h₂
  obtain rfl := value_int_inj h₃
  exact ⟨rfl, rfl, rfl⟩

private theorem select_noTrap {s : Store H} {f : Frame} {args : List Value} :
    ¬ PlainTrap s f args .select := by rintro step; cases step

private theorem intUnOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : IntType} {op : Silmaril.Wasm.V1.IntUnOp} (step : Plain s f args (.intUnOp t op) s' f' rets) :
    args.length = 1 ∧ s' = s ∧ f' = f ∧ ∃ x : BitVec t.width, args = [Value.int t x] ∧
      rets = [Value.int t (Numerics.intUnOp t op.toCore x)] := by
  cases step; exact ⟨rfl, rfl, rfl, _, rfl, rfl⟩

private theorem intUnOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : IntType} {op : Silmaril.Wasm.V1.IntUnOp} {x : BitVec t.width}
    (step : Plain s f [Value.int t x] (.intUnOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ rets = [Value.int t (Numerics.intUnOp t op.toCore x)] := by
  obtain ⟨-, rfl, rfl, x', hargs, rfl⟩ := intUnOp_inv step
  injection hargs with h _
  obtain rfl := value_int_inj h
  exact ⟨rfl, rfl, rfl⟩

private theorem intUnOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {op : Silmaril.Wasm.V1.IntUnOp} : ¬ PlainTrap s f args (.intUnOp t op) := by rintro step; cases step

private theorem intBinOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : IntType} {op : IntBinOp} (step : Plain s f args (.intBinOp t op) s' f' rets) :
    args.length = 2 ∧ s' = s ∧ f' = f ∧ ∃ x y z : BitVec t.width,
      Numerics.intBinOp t op x y = .ok z ∧ args = [Value.int t x, Value.int t y] ∧
      rets = [Value.int t z] := by
  cases step
  rename_i result
  exact ⟨rfl, rfl, rfl, _, _, _, result, rfl, rfl⟩

private theorem intBinOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
    (step : Plain s f [Value.int t x, Value.int t y] (.intBinOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ ∃ z : BitVec t.width, Numerics.intBinOp t op x y = .ok z ∧
      rets = [Value.int t z] := by
  obtain ⟨-, rfl, rfl, x', y', z, result, hargs, rfl⟩ := intBinOp_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ _
  obtain rfl := value_int_inj h₁
  obtain rfl := value_int_inj h₂
  exact ⟨rfl, rfl, z, result, rfl⟩

private theorem intBinOp_trap_inv {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {op : IntBinOp} (step : PlainTrap s f args (.intBinOp t op)) :
    args.length = 2 ∧ ∃ (x y : BitVec t.width) (e : Numerics.IntTrap),
      Numerics.intBinOp t op x y = .error e ∧ args = [Value.int t x, Value.int t y] := by
  cases step
  rename_i result
  exact ⟨rfl, _, _, _, result, rfl⟩

private theorem intBinOp_trap {s : Store H} {f : Frame} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width} (step : PlainTrap s f [Value.int t x, Value.int t y]
      (.intBinOp t op)) :
    ∃ e : Numerics.IntTrap, Numerics.intBinOp t op x y = .error e := by
  obtain ⟨-, x', y', e, result, hargs⟩ := intBinOp_trap_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ _
  obtain rfl := value_int_inj h₁
  obtain rfl := value_int_inj h₂
  exact ⟨e, result⟩

private theorem intTestOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : IntType} {op : IntTestOp} (step : Plain s f args (.intTestOp t op) s' f' rets) :
    args.length = 1 ∧ s' = s ∧ f' = f ∧ ∃ x : BitVec t.width, args = [Value.int t x] ∧
      rets = [Value.int .i32 (Numerics.intTestOp t op x)] := by
  cases step; exact ⟨rfl, rfl, rfl, _, rfl, rfl⟩

private theorem intTestOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : IntType} {op : IntTestOp} {x : BitVec t.width}
    (step : Plain s f [Value.int t x] (.intTestOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ rets = [Value.int .i32 (Numerics.intTestOp t op x)] := by
  obtain ⟨-, rfl, rfl, x', hargs, rfl⟩ := intTestOp_inv step
  injection hargs with h _
  obtain rfl := value_int_inj h
  exact ⟨rfl, rfl, rfl⟩

private theorem intTestOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {op : IntTestOp} : ¬ PlainTrap s f args (.intTestOp t op) := by rintro step; cases step

private theorem intRelOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : IntType} {op : IntRelOp} (step : Plain s f args (.intRelOp t op) s' f' rets) :
    args.length = 2 ∧ s' = s ∧ f' = f ∧ ∃ x y : BitVec t.width,
      args = [Value.int t x, Value.int t y] ∧
      rets = [Value.int .i32 (Numerics.intRelOp t op x y)] := by
  cases step; exact ⟨rfl, rfl, rfl, _, _, rfl, rfl⟩

private theorem intRelOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : IntType} {op : IntRelOp} {x y : BitVec t.width}
    (step : Plain s f [Value.int t x, Value.int t y] (.intRelOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ rets = [Value.int .i32 (Numerics.intRelOp t op x y)] := by
  obtain ⟨-, rfl, rfl, x', y', hargs, rfl⟩ := intRelOp_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ _
  obtain rfl := value_int_inj h₁
  obtain rfl := value_int_inj h₂
  exact ⟨rfl, rfl, rfl⟩

private theorem intRelOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {op : IntRelOp} : ¬ PlainTrap s f args (.intRelOp t op) := by rintro step; cases step

private theorem floatUnOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : FloatType} {op : FloatUnOp} (step : Plain s f args (.floatUnOp t op) s' f' rets) :
    args.length = 1 ∧ s' = s ∧ f' = f ∧ ∃ x y : BitVec t.width,
      Numerics.floatUnOpRel t op x y ∧ args = [Value.float t x] ∧
      rets = [Value.float t y] := by
  cases step
  rename_i result
  exact ⟨rfl, rfl, rfl, _, _, result, rfl, rfl⟩

private theorem floatUnOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : FloatType} {op : FloatUnOp} {x : BitVec t.width}
    (step : Plain s f [Value.float t x] (.floatUnOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ ∃ y : BitVec t.width, Numerics.floatUnOpRel t op x y ∧
      rets = [Value.float t y] := by
  obtain ⟨-, rfl, rfl, x', y, result, hargs, rfl⟩ := floatUnOp_inv step
  injection hargs with h _
  obtain rfl := value_float_inj h
  exact ⟨rfl, rfl, y, result, rfl⟩

private theorem floatUnOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {op : FloatUnOp} : ¬ PlainTrap s f args (.floatUnOp t op) := by rintro step; cases step

private theorem floatBinOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : FloatType} {op : FloatBinOp} (step : Plain s f args (.floatBinOp t op) s' f' rets) :
    args.length = 2 ∧ s' = s ∧ f' = f ∧ ∃ x y z : BitVec t.width,
      Numerics.floatBinOpRel t op x y z ∧ args = [Value.float t x, Value.float t y] ∧
      rets = [Value.float t z] := by
  cases step
  rename_i result
  exact ⟨rfl, rfl, rfl, _, _, _, result, rfl, rfl⟩

private theorem floatBinOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width}
    (step : Plain s f [Value.float t x, Value.float t y] (.floatBinOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ ∃ z : BitVec t.width, Numerics.floatBinOpRel t op x y z ∧
      rets = [Value.float t z] := by
  obtain ⟨-, rfl, rfl, x', y', z, result, hargs, rfl⟩ := floatBinOp_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ _
  obtain rfl := value_float_inj h₁
  obtain rfl := value_float_inj h₂
  exact ⟨rfl, rfl, z, result, rfl⟩

private theorem floatBinOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {op : FloatBinOp} : ¬ PlainTrap s f args (.floatBinOp t op) := by rintro step; cases step

private theorem floatRelOp_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {t : FloatType} {op : FloatRelOp} (step : Plain s f args (.floatRelOp t op) s' f' rets) :
    args.length = 2 ∧ s' = s ∧ f' = f ∧ ∃ x y : BitVec t.width,
      args = [Value.float t x, Value.float t y] ∧
      rets = [Value.int .i32 (Numerics.floatRelOp t op x y)] := by
  cases step; exact ⟨rfl, rfl, rfl, _, _, rfl, rfl⟩

private theorem floatRelOp_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width}
    (step : Plain s f [Value.float t x, Value.float t y] (.floatRelOp t op) s' f' rets) :
    s' = s ∧ f' = f ∧ rets = [Value.int .i32 (Numerics.floatRelOp t op x y)] := by
  obtain ⟨-, rfl, rfl, x', y', hargs, rfl⟩ := floatRelOp_inv step
  injection hargs with h₁ hargs
  injection hargs with h₂ _
  obtain rfl := value_float_inj h₁
  obtain rfl := value_float_inj h₂
  exact ⟨rfl, rfl, rfl⟩

private theorem floatRelOp_noTrap {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {op : FloatRelOp} : ¬ PlainTrap s f args (.floatRelOp t op) := by rintro step; cases step

private theorem convert_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {op : Silmaril.Wasm.V1.ConvertOp} (step : Plain s f args (.convert op) s' f' rets) :
    args.length = 1 ∧ s' = s ∧ f' = f ∧ ∃ (x : Numerics.NumValue op.toCore.source)
      (y : Numerics.NumValue op.toCore.target), Numerics.convertRel op.toCore x (.ok y) ∧
      args = [⟨op.toCore.source, x⟩] ∧ rets = [⟨op.toCore.target, y⟩] := by
  cases step
  rename_i result
  exact ⟨rfl, rfl, rfl, _, _, result, rfl, rfl⟩

private theorem convert_effect {s s' : Store H} {f f' : Frame} {rets : List Value}
    {op : Silmaril.Wasm.V1.ConvertOp} {x : Numerics.NumValue op.toCore.source}
    (step : Plain s f [⟨op.toCore.source, x⟩] (.convert op) s' f' rets) :
    s' = s ∧ f' = f ∧ ∃ y : Numerics.NumValue op.toCore.target,
      Numerics.convertRel op.toCore x (.ok y) ∧ rets = [⟨op.toCore.target, y⟩] := by
  obtain ⟨-, rfl, rfl, x', y, result, hargs, rfl⟩ := convert_inv step
  injection hargs with h _
  obtain rfl := value_inj h
  exact ⟨rfl, rfl, y, result, rfl⟩

private theorem convert_trap_inv {s : Store H} {f : Frame} {args : List Value} {op : Silmaril.Wasm.V1.ConvertOp}
    (step : PlainTrap s f args (.convert op)) :
    args.length = 1 ∧ ∃ (x : Numerics.NumValue op.toCore.source) (e : Numerics.FloatTrap),
      Numerics.convertRel op.toCore x (.error e) ∧ args = [⟨op.toCore.source, x⟩] := by
  cases step
  rename_i result
  exact ⟨rfl, _, _, result, rfl⟩

private theorem convert_trap {s : Store H} {f : Frame} {op : Silmaril.Wasm.V1.ConvertOp}
    {x : Numerics.NumValue op.toCore.source}
    (step : PlainTrap s f [⟨op.toCore.source, x⟩] (.convert op)) :
    ∃ e : Numerics.FloatTrap, Numerics.convertRel op.toCore x (.error e) := by
  obtain ⟨-, x', e, result, hargs⟩ := convert_trap_inv step
  injection hargs with h _
  obtain rfl := value_inj h
  exact ⟨e, result⟩

/-! ## The rules of Figure 6 -/

theorem valid_const (v : Value) :
    Valid host n F L R (Assert.stack []) [constInstr v] (Assert.stack [Term.const v]) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  obtain ⟨t, bits⟩ := v
  cases t with
  | int t =>
    refine valid_single_pure (S := []) trivial ?_ ?_ ?_ ?_
    · exact fun _ _ _ _ _ _ step => (intConst_inv step).1
    · exact fun _ _ _ step => absurd step intConst_noTrap
    · exact fun _ _ _ _ => intConst_noTrap
    · refine fun _ _ _ _ _ _ _ step => ?_
      obtain ⟨-, rfl, rfl, rfl⟩ := intConst_inv step
      exact ⟨rfl, rfl, rfl, trivial⟩
  | float t =>
    refine valid_single_pure (S := []) trivial ?_ ?_ ?_ ?_
    · exact fun _ _ _ _ _ _ step => (floatConst_inv step).1
    · exact fun _ _ _ step => absurd step floatConst_noTrap
    · exact fun _ _ _ _ => floatConst_noTrap
    · refine fun _ _ _ _ _ _ _ step => ?_
      obtain ⟨-, rfl, rfl, rfl⟩ := floatConst_inv step
      exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_unreachable (Q : Assert) :
    Valid host n F L R (Assert.stackIf [] fun _ => False) [.unreachable] Q := by
  intro _ _ _ _ _ _ _ _ pre
  exact pre.2.2.elim

theorem valid_nop : Valid host n F L R (Assert.stack []) [.nop] (Assert.stack []) := by
  rw [stack_eq_stackIf]
  refine valid_single_pure (S := []) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (nop_inv step).1
  · exact fun _ _ _ step => absurd step nop_noTrap
  · exact fun _ _ _ _ => nop_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨-, rfl, rfl, rfl⟩ := nop_inv step
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_drop (τ : Term Value) :
    Valid host n F L R (Assert.stack [τ]) [.drop] (Assert.stack []) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  refine valid_single_pure (S := [τ]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (drop_inv step).1
  · exact fun _ _ _ step => absurd step drop_noTrap
  · exact fun _ _ _ _ => drop_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨-, rfl, rfl, rfl⟩ := drop_inv step
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_select (τ₁ τ₂ : Term Value) (c : Term (BitVec 32))
    (sameType : ∀ ρ, (τ₁ ρ).type = (τ₂ ρ).type) :
    Valid host n F L R (Assert.stack [τ₁, τ₂, Term.i32 c]) [.select]
      (Assert.ex fun x : Value => Assert.stackIf [Term.const x] fun ρ =>
        (c ρ ≠ 0 → x = τ₁ ρ) ∧ (c ρ = 0 → x = τ₂ ρ)) := by
  -- `Execution.Plain.selectZero`/`selectNonzero` carry the equal-type premise
  -- themselves, so soundness does not need the rule's `sameType` side condition.
  have _sameType := sameType
  rw [stack_eq_stackIf]
  refine valid_post (Q := Assert.stackIf [fun ρ => if c ρ = 0 then τ₂ ρ else τ₁ ρ]
    fun _ => True) ?_ ?_
  · refine valid_single_pure (S := [τ₁, τ₂, Term.i32 c]) trivial ?_ ?_ ?_ ?_
    · exact fun _ _ _ _ _ _ step => (select_inv step).1
    · exact fun _ _ _ step => absurd step select_noTrap
    · exact fun _ _ _ _ => select_noTrap
    · refine fun _ _ _ _ _ _ _ step => ?_
      obtain ⟨rfl, rfl, rfl⟩ := select_effect step
      exact ⟨rfl, rfl, rfl, trivial⟩
  · rintro ρ vs h ⟨rfl, hemp, -⟩
    refine ⟨if c ρ = 0 then τ₂ ρ else τ₁ ρ, rfl, hemp, ?_, ?_⟩
    · exact fun hne => ite_eq_right hne
    · exact fun he => ite_eq_left he

theorem valid_intUnOp (t : IntType) (op : Silmaril.Wasm.V1.IntUnOp) (x : Term (BitVec t.width)) :
    Valid host n F L R (Assert.stack [Term.int t x]) [.intUnOp t op]
      (Assert.stack [Term.int t fun ρ => Numerics.intUnOp t op.toCore (x ρ)]) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  refine valid_single_pure (S := [Term.int t x]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (intUnOp_inv step).1
  · exact fun _ _ _ step => absurd step intUnOp_noTrap
  · exact fun _ _ _ _ => intUnOp_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨rfl, rfl, rfl⟩ := intUnOp_effect step
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_intBinOp (t : IntType) (op : IntBinOp) (x y z : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.stackIf [Term.int t x, Term.int t y] fun ρ =>
        Numerics.intBinOp t op (x ρ) (y ρ) = .ok (z ρ))
      [.intBinOp t op] (Assert.stack [Term.int t z]) := by
  rw [stack_eq_stackIf]
  refine valid_single_pure (S := [Term.int t x, Term.int t y]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (intBinOp_inv step).1
  · exact fun _ _ _ step => (intBinOp_trap_inv step).1
  · refine fun _ _ ρ hφ step => ?_
    obtain ⟨e, herr⟩ := intBinOp_trap step
    rw [hφ] at herr
    simp at herr
  · refine fun _ _ _ _ ρ _ hφ step => ?_
    obtain ⟨rfl, rfl, w, hok, rfl⟩ := intBinOp_effect step
    rw [hφ] at hok
    obtain rfl := Except.ok.inj hok
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_intTestOp (t : IntType) (op : IntTestOp) (x : Term (BitVec t.width)) :
    Valid host n F L R (Assert.stack [Term.int t x]) [.intTestOp t op]
      (Assert.stack [Term.i32 fun ρ => Numerics.intTestOp t op (x ρ)]) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  refine valid_single_pure (S := [Term.int t x]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (intTestOp_inv step).1
  · exact fun _ _ _ step => absurd step intTestOp_noTrap
  · exact fun _ _ _ _ => intTestOp_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨rfl, rfl, rfl⟩ := intTestOp_effect step
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_intRelOp (t : IntType) (op : IntRelOp) (x y : Term (BitVec t.width)) :
    Valid host n F L R (Assert.stack [Term.int t x, Term.int t y]) [.intRelOp t op]
      (Assert.stack [Term.i32 fun ρ => Numerics.intRelOp t op (x ρ) (y ρ)]) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  refine valid_single_pure (S := [Term.int t x, Term.int t y]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (intRelOp_inv step).1
  · exact fun _ _ _ step => absurd step intRelOp_noTrap
  · exact fun _ _ _ _ => intRelOp_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨rfl, rfl, rfl⟩ := intRelOp_effect step
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_floatUnOp (t : FloatType) (op : FloatUnOp) (x y : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.stackIf [Term.float t x] fun ρ =>
        ∀ z, Numerics.floatUnOpRel t op (x ρ) z → z = y ρ)
      [.floatUnOp t op] (Assert.stack [Term.float t y]) := by
  rw [stack_eq_stackIf]
  refine valid_single_pure (S := [Term.float t x]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (floatUnOp_inv step).1
  · exact fun _ _ _ step => absurd step floatUnOp_noTrap
  · exact fun _ _ _ _ => floatUnOp_noTrap
  · refine fun _ _ _ _ ρ _ hφ step => ?_
    obtain ⟨rfl, rfl, w, hrel, rfl⟩ := floatUnOp_effect step
    rw [hφ w hrel]
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_floatBinOp (t : FloatType) (op : FloatBinOp) (x y z : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.stackIf [Term.float t x, Term.float t y] fun ρ =>
        ∀ w, Numerics.floatBinOpRel t op (x ρ) (y ρ) w → w = z ρ)
      [.floatBinOp t op] (Assert.stack [Term.float t z]) := by
  rw [stack_eq_stackIf]
  refine valid_single_pure (S := [Term.float t x, Term.float t y]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (floatBinOp_inv step).1
  · exact fun _ _ _ step => absurd step floatBinOp_noTrap
  · exact fun _ _ _ _ => floatBinOp_noTrap
  · refine fun _ _ _ _ ρ _ hφ step => ?_
    obtain ⟨rfl, rfl, w, hrel, rfl⟩ := floatBinOp_effect step
    rw [hφ w hrel]
    exact ⟨rfl, rfl, rfl, trivial⟩

theorem valid_floatRelOp (t : FloatType) (op : FloatRelOp) (x y : Term (BitVec t.width)) :
    Valid host n F L R (Assert.stack [Term.float t x, Term.float t y]) [.floatRelOp t op]
      (Assert.stack [Term.i32 fun ρ => Numerics.floatRelOp t op (x ρ) (y ρ)]) := by
  rw [stack_eq_stackIf, stack_eq_stackIf]
  refine valid_single_pure (S := [Term.float t x, Term.float t y]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (floatRelOp_inv step).1
  · exact fun _ _ _ step => absurd step floatRelOp_noTrap
  · exact fun _ _ _ _ => floatRelOp_noTrap
  · refine fun _ _ _ _ _ _ _ step => ?_
    obtain ⟨rfl, rfl, rfl⟩ := floatRelOp_effect step
    exact ⟨rfl, rfl, rfl, trivial⟩

/-- A binary64 arithmetic NaN: quiet, with a payload that is not the canonical
one. -/
private def demoteSrc : Numerics.NumValue (V1.ConvertOp.demote).toCore.source :=
  0x7ff8000000000001#64

/-- A binary32 arithmetic NaN. -/
private def demoteTgt₁ : Numerics.NumValue (V1.ConvertOp.demote).toCore.target := 0x7fc00000#32

/-- Another binary32 arithmetic NaN. -/
private def demoteTgt₂ : Numerics.NumValue (V1.ConvertOp.demote).toCore.target := 0x7fc00001#32

/-- `Execution.Numerics.convertRel` is not a function: demoting an arithmetic
NaN admits every arithmetic NaN of the target type. So "`τ'` is a permitted
result of `cvtop` on `τ`, and `cvtop` does not trap on `τ`" does not determine
the result, and is too weak a precondition for `valid_convert`. -/
private theorem convertRel_demote_nondeterministic :
    Numerics.convertRel (V1.ConvertOp.demote).toCore demoteSrc (.ok demoteTgt₁) ∧
    Numerics.convertRel (V1.ConvertOp.demote).toCore demoteSrc (.ok demoteTgt₂) ∧
    demoteTgt₁ ≠ demoteTgt₂ ∧
    ∀ e, ¬ Numerics.convertRel (V1.ConvertOp.demote).toCore demoteSrc (.error e) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro (_ | _) <;> decide

theorem valid_convert (op : Silmaril.Wasm.V1.ConvertOp) (x : Term (Numerics.NumValue op.toCore.source))
    (y : Term (Numerics.NumValue op.toCore.target)) :
    Valid host n F L R
      (Assert.stackIf [fun ρ => ⟨op.toCore.source, x ρ⟩] fun ρ =>
        (∀ y', Numerics.convertRel op.toCore (x ρ) (.ok y') → y' = y ρ) ∧
        ∀ e, ¬ Numerics.convertRel op.toCore (x ρ) (.error e))
      [.convert op] (Assert.stack [fun ρ => ⟨op.toCore.target, y ρ⟩]) := by
  rw [stack_eq_stackIf]
  refine valid_single_pure (S := [fun ρ => ⟨op.toCore.source, x ρ⟩]) trivial ?_ ?_ ?_ ?_
  · exact fun _ _ _ _ _ _ step => (convert_inv step).1
  · exact fun _ _ _ step => (convert_trap_inv step).1
  · refine fun _ _ ρ hφ step => ?_
    obtain ⟨e, herr⟩ := convert_trap step
    exact hφ.2 e herr
  · refine fun _ _ _ _ ρ _ hφ step => ?_
    obtain ⟨rfl, rfl, w, hrel, rfl⟩ := convert_effect step
    rw [hφ.1 w hrel]
    exact ⟨rfl, rfl, rfl, trivial⟩

end Silmaril.Wasm.Logic.V1
