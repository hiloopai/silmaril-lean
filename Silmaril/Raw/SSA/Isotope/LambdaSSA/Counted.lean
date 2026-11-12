module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Loop
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Sequence

/-! # Carried-value counted loops over an arbitrary SSA machine

The common CFG carries a represented natural counter and an arbitrary value.
Clients supply actual zero, comparison and increment terms, together with
their evaluations. The signed limit may be nonpositive. A capacity bound on
every visited increment lets clients justify their finite-width counters.

The trace retains each actual body evaluation and all intermediate machine
states. Translating it into a CFG never resets state, manufactures a successful
body, or hides a whole loop inside an instruction.
-/

@[expose] public section
universe u v a s
namespace Silmaril.Isotope.LambdaSSA.Counted
open Semantics (extend)

variable {Φ : Type u}

def offset : Tm Φ := .let₂ (.var 0) (.var 1)
def accumulator : Tm Φ := .let₂ (.var 0) (.var 0)

def next (increment body : Tm Φ) : Tm Φ :=
  .let₁ body (.pair (increment.rename Nat.succ) (.var 0))

def loop (zero initial predicate increment body : Tm Φ) : Region Φ :=
  While.region (.pair zero initial) predicate (next increment body)

def region (zero initial predicate increment body : Tm Φ) : Region Φ :=
  Region.sequence (loop zero initial predicate increment body) (.br 0 accumulator)

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem offset_typed {context : VCtx τ} (indexType accType : τ) :
    Tm.HasType (TypeFormers.product indexType accType :: context) (offset (Φ := Φ)) indexType :=
  .let₂ (.var rfl) (.var rfl)

theorem accumulator_typed {context : VCtx τ} (indexType accType : τ) :
    Tm.HasType (TypeFormers.product indexType accType :: context) (accumulator (Φ := Φ)) accType :=
  .let₂ (.var rfl) (.var rfl)

theorem next_typed {context : VCtx τ} {indexType accType : τ} {increment body : Tm Φ}
    (inc : Tm.HasType (TypeFormers.product indexType accType :: context) increment indexType)
    (step : Tm.HasType (TypeFormers.product indexType accType :: context) body accType) :
    Tm.HasType (TypeFormers.product indexType accType :: context) (next increment body)
      (TypeFormers.product indexType accType) :=
  .let₁ step (.pair (inc.weaken accType) (.var rfl))

theorem loop_typed {context : VCtx τ} {indexType accType : τ} {zero initial predicate increment body : Tm Φ}
    (hz : Tm.HasType context zero indexType) (hi : Tm.HasType context initial accType)
    (hp : Tm.HasType (TypeFormers.product indexType accType :: context) predicate
      (TypeFormers.coprod TypeFormers.unit TypeFormers.unit))
    (hn : Tm.HasType (TypeFormers.product indexType accType :: context) increment indexType)
    (hb : Tm.HasType (TypeFormers.product indexType accType :: context) body accType) :
    Region.HasType context (loop zero initial predicate increment body) [TypeFormers.product indexType accType] :=
  While.region_typed (.pair hz hi) hp (next_typed hn hb)

theorem region_typed {context : VCtx τ} {indexType accType : τ} {zero initial predicate increment body : Tm Φ}
    (hz : Tm.HasType context zero indexType) (hi : Tm.HasType context initial accType)
    (hp : Tm.HasType (TypeFormers.product indexType accType :: context) predicate
      (TypeFormers.coprod TypeFormers.unit TypeFormers.unit))
    (hn : Tm.HasType (TypeFormers.product indexType accType :: context) increment indexType)
    (hb : Tm.HasType (TypeFormers.product indexType accType :: context) body accType) :
    Region.HasType context (region zero initial predicate increment body) [accType] :=
  Region.HasType.sequence (loop_typed hz hi hp hn hb) (.br rfl (accumulator_typed indexType accType))

variable {α : Type a} {σ : Type s}

def stateValue (indexValue : Nat → Value α) (index : Nat) (acc : Value α) : Value α :=
  .pair (indexValue index) acc

def stateEnv (indexValue : Nat → Value α) (env : Nat → Value α) (index : Nat) (acc : Value α) : Nat → Value α :=
  extend env (stateValue indexValue index acc)

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem offset_eval (indexValue : Nat → Value α) (env : Nat → Value α) (index : Nat) (acc : Value α) (state : σ) :
    Semantics.Tm.Eval instr (stateEnv indexValue env index acc) offset state (indexValue index) state :=
  .let₂ .var .var

theorem accumulator_eval (indexValue : Nat → Value α) (env : Nat → Value α) (index : Nat) (acc : Value α) (state : σ) :
    Semantics.Tm.Eval instr (stateEnv indexValue env index acc) accumulator state acc state :=
  .let₂ .var .var

inductive Trace (instr : Φ → Value α → σ → Value α → σ → Prop) (indexValue : Nat → Value α)
    (env : Nat → Value α) (body : Tm Φ) (limit : Int) (stride capacity : Nat) :
    Nat → Value α → σ → Nat → Value α → σ → Prop where
  | done {index : Nat} {acc state} (stopped : limit ≤ (index : Int)) :
      Trace instr indexValue env body limit stride capacity index acc state index acc state
  | next {index : Nat} {acc value before middle last result after}
      (active : (index : Int) < limit) (incrementSafe : index + stride < capacity)
      (head : Semantics.Tm.Eval instr (stateEnv indexValue env index acc) body before value middle)
      (tail : Trace instr indexValue env body limit stride capacity (index + stride) value middle last result after) :
      Trace instr indexValue env body limit stride capacity index acc before last result after

theorem while_trace_of_trace {indexValue : Nat → Value α} {env : Nat → Value α}
    {body predicate increment : Tm Φ} {limit : Int} {stride capacity index last : Nat}
    {acc result : Value α} {before after : σ}
    (testEval : ∀ index < capacity, ∀ acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) predicate state
        (if (index : Int) < limit then .inl .unit else .inr .unit) state)
    (incEval : ∀ index acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) increment state (indexValue (index + stride)) state)
    (safe : index < capacity) (trace : Trace instr indexValue env body limit stride capacity index acc before last result after) :
    While.Trace instr env predicate (next increment body)
      (stateValue indexValue index acc) before (stateValue indexValue last result) after := by
  induction trace with
  | @done index acc state stopped =>
    apply While.Trace.done
    simpa only [stateEnv, ite_eq_right (by omega : ¬ (index : Int) < limit)] using testEval index safe acc state
  | @next index acc value before middle last result after active inRange head tail ih =>
    have test := testEval index safe acc before
    rw [ite_eq_left active] at test
    have inc := (incEval index acc middle).rename
      (env' := extend (stateEnv indexValue env index acc) value) (ρ := Nat.succ) (fun _ => rfl)
    exact .next test (.let₁ head (.pair inc .var)) (ih inRange)

theorem loop_eval {indexValue : Nat → Value α} {env : Nat → Value α}
    {zero initial body predicate increment : Tm Φ} {limit : Int} {stride capacity last : Nat}
    {acc result : Value α} {before middle after : σ}
    (zeroEval : Semantics.Tm.Eval instr env zero before (indexValue 0) before)
    (initialEval : Semantics.Tm.Eval instr env initial before acc middle)
    (testEval : ∀ index < capacity, ∀ acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) predicate state
        (if (index : Int) < limit then .inl .unit else .inr .unit) state)
    (incEval : ∀ index acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) increment state (indexValue (index + stride)) state)
    (positive : 0 < capacity) (trace : Trace instr indexValue env body limit stride capacity 0 acc middle last result after) :
    Semantics.Region.Eval instr env (loop zero initial predicate increment body) before 0
      (stateValue indexValue last result) after :=
  While.region_eval (.pair zeroEval initialEval) (while_trace_of_trace testEval incEval positive trace)

theorem region_eval {indexValue : Nat → Value α} {env : Nat → Value α}
    {zero initial body predicate increment : Tm Φ} {limit : Int} {stride capacity last : Nat}
    {acc result : Value α} {before middle after : σ}
    (zeroEval : Semantics.Tm.Eval instr env zero before (indexValue 0) before)
    (initialEval : Semantics.Tm.Eval instr env initial before acc middle)
    (testEval : ∀ index < capacity, ∀ acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) predicate state
        (if (index : Int) < limit then .inl .unit else .inr .unit) state)
    (incEval : ∀ index acc state,
      Semantics.Tm.Eval instr (stateEnv indexValue env index acc) increment state (indexValue (index + stride)) state)
    (positive : 0 < capacity) (trace : Trace instr indexValue env body limit stride capacity 0 acc middle last result after) :
    Semantics.Region.Eval instr env (region zero initial predicate increment body) before 0 result after :=
  Semantics.Region.Eval.sequence (loop_eval zeroEval initialEval testEval incEval positive trace)
    (.br (accumulator_eval indexValue env last result after))

theorem Trace.of_iterations {indexValue : Nat → Value α} {env : Nat → Value α} {body : Tm Φ}
    (limit : Int) (stride capacity start count : Nat) (acc : Nat → Value α) (state : Nat → σ)
    (active : ∀ i < count, (((start + i) * stride : Nat) : Int) < limit)
    (stopped : limit ≤ (((start + count) * stride : Nat) : Int))
    (safe : (start + count) * stride < capacity)
    (execute : ∀ i < count, Semantics.Tm.Eval instr
      (stateEnv indexValue env ((start + i) * stride) (acc (start + i))) body
      (state (start + i)) (acc (start + i + 1)) (state (start + i + 1))) :
    Trace instr indexValue env body limit stride capacity (start * stride) (acc start) (state start)
      ((start + count) * stride) (acc (start + count)) (state (start + count)) := by
  induction count generalizing start with
  | zero => exact .done (by simpa only [Nat.add_zero] using stopped)
  | succ count ih =>
    have inRange : start * stride + stride < capacity := by
      have bound := Nat.mul_le_mul_right stride (show start + 1 ≤ start + (count + 1) by omega)
      rw [Nat.add_mul, Nat.one_mul] at bound
      omega
    have head := execute 0 (by omega)
    simp only [Nat.add_zero] at head
    have tail := ih (start + 1) (by
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using active (i + 1) (by omega))
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using stopped)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using safe)
      (by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using execute (i + 1) (by omega))
    apply Trace.next (by simpa using active 0 (by omega)) inRange head
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm 1 count] using tail

end Silmaril.Isotope.LambdaSSA.Counted
