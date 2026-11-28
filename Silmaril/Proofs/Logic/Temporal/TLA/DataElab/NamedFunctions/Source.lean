module

public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Thms
import Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Thms

/-! Identify the collection evaluator's CHOOSE predicate with the checked fixed-point equation. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Proofs

open Data Data.Tagged

universe u

variable (p : Predecessor) (policy : Tagged.Policy.{u}) (invalid : Tagged.CollectionPolicy.{u})
  (sequence : SequencePolicy.{u}) (graph : Unspecified.{u})
  (endpoints : Endpoints.EndpointValuation Value.{u})

private noncomputable abbrev evaluate (e : Expr) (witnesses : Nat → Value.{u}) : Value.{u} :=
  e.eval (policy.collectionOperations invalid graph) policy.booleans
    (Sequences.external policy sequence) ⟨endpoints.rigid, endpoints.source⟩
    witnesses endpoints.target

private theorem len_apply (v : Value.{u}) :
    (Sequences.external policy sequence lenId 1 (by decide)).apply [v] = v.len sequence := by
  rw [Sequences.external_apply _ _ (op := .inr .len) (by decide), Sequences.len_apply]

private theorem range_apply (lo hi : Value.{u}) :
    (Sequences.external policy sequence rangeId 2 (by decide)).apply [lo, hi] =
      Value.interval policy.numeric lo hi := by
  rw [Sequences.external_apply _ _ (op := .inl .interval) (by decide),
    Sequences.numeric_apply, Tagged.Policy.interval_apply]

private theorem sub_apply (i j : Int) :
    (Sequences.external policy sequence subId 2 (by decide)).apply [.integer i, .integer j] =
      .integer (i - j) := by
  rw [Sequences.external_apply _ _ (op := .inl .sub) (by decide),
    Sequences.numeric_apply, Tagged.Policy.sub_apply, Value.sub_integer]

/-- At every positive declared key the interpreted subtraction produces a smaller
key in the same interval. -/
public theorem predecessor_key (n : Nat) (i : Int) (hi : 0 < i) (hn : i ≤ n) :
    let key := (Sequences.external policy sequence subId 2 (by decide)).apply [.integer i, .integer 1]
    key = .integer (i - 1) ∧ (SetData.intRange.{u} 0 n).mem key ∧ i - 1 < i := by
  dsimp only
  rw [sub_apply, SetData.integer_mem_intRange]
  exact ⟨rfl, ⟨by omega, by omega⟩, by omega⟩

private theorem isBoolean_ofProp (B : Booleans Value.{u}) (q : Prop) :
    B.IsBoolean (B.ofProp q) := by
  classical
  by_cases h : q <;> simp [Booleans.IsBoolean, Booleans.ofProp, h]

private abbrev setKey (p : Predecessor) (witnesses : Nat → Value.{u})
    (candidate : Value.{u}) (i : Value.{u}) : Nat → Value.{u} :=
  withWitness (withWitness witnesses p.self candidate) p.index i

private theorem eval_len (witnesses : Nat → Value.{u}) :
    evaluate policy invalid sequence graph endpoints p.len witnesses =
      (endpoints.source p.queue).len sequence := by
  simp only [Predecessor.len, evaluate, Term.eval, Term.evalList, len_apply]

private theorem eval_bound (entries : List Value.{u})
    (queue : endpoints.source p.queue = .tuple entries) (witnesses : Nat → Value.{u}) :
    evaluate policy invalid sequence graph endpoints p.bound witnesses =
      .set (SetData.intRange 0 entries.length) := by
  simp only [Predecessor.bound, evaluate, Term.eval, Term.evalList, range_apply,
    eval_len, queue, Value.len_tuple]
  exact Value.interval_integer _ 0 entries.length

private noncomputable abbrev fieldAt (q : Value.{u}) (i : Int) (field : String) : Value.{u} :=
  ((q.apply graph (.integer i)).apply graph (.integer 2)).apply graph (.string field)

open Classical in
private theorem eval_body (witnesses : Nat → Value.{u}) (candidate : Value.{u}) (i : Int) :
    let field := fieldAt graph (endpoints.source p.queue) i
    let previous := candidate.apply graph (.integer (i - 1))
    evaluate policy invalid sequence graph endpoints p.body (setKey p witnesses candidate (.integer i)) =
      if i = 0 then endpoints.source p.base
      else if field "op" = .string "Rd" then previous
      else previous.updatePath graph [field "adr"] (fun _ => field "val") := by
  have h := p.index_ne_self.symm
  have h' := p.index_ne_old
  simp only [Predecessor.body, Predecessor.previous, Predecessor.field, evaluate, Term.eval,
    Term.evalList, Term.evalClauses, Bool.false_eq_true, ite_false, isBoolean_ofProp, ite_true,
    Booleans.holds_ofProp, Operations.collection, cast_eq, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, withWitness, h, h',
    sub_apply, List.map_cons, List.map_nil, Value.updateClauses_cons, Value.updateClauses_nil,
    Value.integer_injective.eq_iff]
  simp only [fieldAt, show Int.ofNat 0 = (0 : Int) by decide,
    show Int.ofNat 1 = (1 : Int) by decide, show Int.ofNat 2 = (2 : Int) by decide]

private theorem eval_function (entries : List Value.{u}) (queue : endpoints.source p.queue = .tuple entries)
    (witnesses : Nat → Value.{u}) (candidate : Value.{u}) :
    evaluate policy invalid sequence graph endpoints p.function (withWitness witnesses p.self candidate) =
      .function ((vmemDefinition graph (endpoints.source p.base) entries).rhs graph candidate) := by
  let rhs := (vmemDefinition graph (endpoints.source p.base) entries).rhs graph candidate
  let domain : SetData.{u} := .intRange 0 entries.length
  let body := fun key => evaluate policy invalid sequence graph endpoints p.body (setKey p witnesses candidate key)
  change (policy.collectionOperations invalid graph).function
    (evaluate policy invalid sequence graph endpoints p.bound (withWitness witnesses p.self candidate))
    body = .function rhs
  rw [eval_bound p policy invalid sequence graph endpoints entries queue]
  simp only [Tagged.Policy.collectionOperations, Value.asSet_set]
  apply congrArg Value.function
  have hd : domain = rhs.domain := by
    apply Value.set_injective
    rw [← Value.domain_function graph rhs, vmem_rhs_domain graph sequence, Value.len_tuple]
    exact (Value.interval_integer _ _ _).symm
  apply Graph.ext_of_domain_lookup
  · simpa only [Graph.domain_ofFn] using hd
  intro key hk
  rw [Graph.domain_ofFn] at hk
  rw [Graph.lookup_ofFn hk]
  have inRhs : rhs.domain.mem key := hd ▸ hk
  cases lookup : rhs.lookup key with
  | none => exact ((Graph.lookup_eq_none.mp lookup) inRhs).elim
  | some value =>
    apply congrArg some
    rw [← Value.apply_function graph (Graph.lookup_eq_some.mp lookup)]
    obtain ⟨i, rfl, hlo, hhi⟩ := (SetData.mem_intRange 0 entries.length).mp hk
    obtain ⟨j, rfl⟩ : ∃ j : Nat, i = j := ⟨i.toNat, (Int.toNat_of_nonneg hlo).symm⟩
    cases j with
    | zero =>
      change body (.integer 0) = Value.apply graph (.function rhs) (.integer 0)
      rw [vmem_rhs_zero graph (endpoints.source p.base) entries candidate]
      simp [body, eval_body]
    | succ j =>
      have hj : j < entries.length := by omega
      have nonzero : (↑(j + 1) : Int) ≠ 0 := by omega
      rw [vmem_rhs_succ graph _ _ _ hj]
      simp only [body, eval_body, nonzero, ite_false, fieldAt]
      rw [queue]

public theorem eval_eq_choose_apply_len (checked : CheckedVMem) (entries : List Value.{u})
    (queue : endpoints.source checked.predecessor.queue = .tuple entries) :
    checked.eval policy invalid sequence graph endpoints =
      (policy.choice.choose ((vmemDefinition graph (endpoints.source checked.predecessor.base)
        entries).FixedPoint graph)).apply graph (Value.len sequence (.tuple entries)) := by
  let p := checked.predecessor
  unfold CheckedVMem.eval
  rw [checked.shape]
  change (evaluate policy invalid sequence graph endpoints p.term (fun _ => .set .empty)) = _
  simp only [Predecessor.term, evaluate, Term.eval, Operations.collection, cast_eq, Bool.false_eq_true,
    ite_false, Booleans.holds_ofProp, eval_len]
  let empty : Nat → Value.{u} := fun _ => .set .empty
  change Value.apply graph (policy.choice.choose (fun candidate =>
    withWitness empty p.self candidate p.self =
      evaluate policy invalid sequence graph endpoints p.function
        (withWitness empty p.self candidate)))
    ((endpoints.source p.queue).len sequence) = _
  have self (candidate : Value.{u}) : withWitness empty p.self candidate p.self = candidate :=
    by simp [withWitness]
  simp only [self]
  have equation : (fun candidate => candidate =
      evaluate policy invalid sequence graph endpoints p.function
        (withWitness empty p.self candidate)) =
      (vmemDefinition graph (endpoints.source p.base) entries).FixedPoint graph := by
    funext candidate
    rw [eval_function p policy invalid sequence graph endpoints entries queue]
    rfl
  rw [equation, queue]

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Proofs
