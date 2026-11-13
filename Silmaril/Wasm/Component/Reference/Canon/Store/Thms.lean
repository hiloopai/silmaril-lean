module

public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs
public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Store`: laws of the component reference

Theorems of the component reference copy `Canon.Store`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Store`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem storeMismatch {α : Type} : P.Inv I (Canon.storeMismatch : P E σ α) := internal _

theorem storeListIntoValidRangeWith (elemSize : Nat) {storeElem : Val → Nat → P E σ Unit}
    (h : ∀ e a, P.Inv I (storeElem e a)) (vs : List Val) (ptr : Nat) :
    P.Inv I (Canon.storeListIntoValidRangeWith elemSize storeElem vs ptr) :=
  forM fun _ _ => h _ _

theorem storeListIntoRangeWith (cx : LiftLowerContext E) (el : ABI.Layout)
    {storeElem : Val → Nat → P E σ Unit} (h : ∀ e a, P.Inv I (storeElem e a))
    (vs : List Val) : P.Inv I (Canon.storeListIntoRangeWith cx el storeElem vs) :=
  bind (allocate _ _ _) fun _ => bind (trapIf _ _) fun _ => bind (checkInBounds _ _ _) fun _ =>
    bind (storeListIntoValidRangeWith _ h _ _) fun _ => pure _

theorem storeListWith (cx : LiftLowerContext E) (el : ABI.Layout)
    {storeElem : Val → Nat → P E σ Unit} (h : ∀ e a, P.Inv I (storeElem e a)) (fixed : Bool)
    (vs : List Val) (ptr : Nat) (hw : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storeListWith cx el storeElem fixed vs ptr) := by
  unfold Canon.storeListWith
  split
  · exact storeListIntoValidRangeWith _ h _ _
  · exact bind (storeListIntoRangeWith cx el h vs) fun _ => bind (ptrSize cx) fun _ =>
      bind (storeInt _ _ _ _ _ (hw · _ _)) fun _ => storeInt _ _ _ _ _ (hw · _ _)

theorem storeVariantHead (cx : LiftLowerContext E) (n : Nat) (a : ABI.Alignment) (i ptr : Nat)
    (hw : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storeVariantHead cx n a i ptr : P E σ Nat) :=
  bind (storeInt _ _ _ _ _ (hw · _ _)) fun _ => pure _

theorem storeFlags (cx : LiftLowerContext E) (n : Nat) (bs : List Bool) (ptr : Nat)
    (hw : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storeFlags cx n bs ptr : P E σ Unit) :=
  storeInt _ _ _ _ _ (hw · _ _)

theorem storePrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (pt : WIT.Primitive)
    (v : Val) (ptr : Nat) (hw : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storePrim lim q cx pt v ptr : P E σ Unit) := by
  unfold Canon.storePrim
  split
  · exact storeInt _ _ _ _ _ (hw · _ _)
  · exact bind (encodeFloat _ _) fun _ => storeInt _ _ _ _ _ (hw · _ _)
  · exact bind (encodeFloat _ _) fun _ => storeInt _ _ _ _ _ (hw · _ _)
  · exact storeInt _ _ _ _ _ (hw · _ _)
  · exact storeString _ _ _ _ _ hw
  · split
    · exact storeInt _ _ _ _ _ (hw · _ _)
    · exact storeMismatch
  · exact storeMismatch

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

/-- The `option` arm of `store`, given the invariant for the payload's stores. -/
theorem storeOption (h : StorePres I) {lim : Limits} {q : Quirks} {cx : LiftLowerContext E}
    {u : WIT.ClosedType RtId}
    (hu : ∀ x a, P.Inv I (Canon.store lim q cx x u a : P E σ Unit)) (v : Val) (ptr : Nat) :
    P.Inv I (Canon.store lim q cx v (.option u) ptr : P E σ Unit) := by
  rw [Canon.store.eq_def]
  cases v <;> try first | exact storeMismatch
  rename_i i payload
  rcases i with _ | _ | i
  · exact bind (ptrType cx) fun _ => bind (storeVariantHead _ _ _ _ _ h.write) fun _ => pure _
  · refine bind (ptrType cx) fun _ => bind (storeVariantHead _ _ _ _ _ h.write) fun _ => ?_
    cases payload
    · exact storeMismatch
    · exact hu _ _
  · exact storeMismatch

/-- The `result` arm of `store`, given the invariant for both optional payload stores. -/
theorem storeResult (h : StorePres I) {lim : Limits} {q : Quirks} {cx : LiftLowerContext E}
    {ok err : Option (WIT.ClosedType RtId)}
    (hok : ∀ x a, P.Inv I (Canon.storeOpt lim q cx x ok a : P E σ Unit))
    (herr : ∀ x a, P.Inv I (Canon.storeOpt lim q cx x err a : P E σ Unit)) (v : Val)
    (ptr : Nat) : P.Inv I (Canon.store lim q cx v (.result ok err) ptr : P E σ Unit) := by
  rw [Canon.store.eq_def]
  cases v <;> try first | exact storeMismatch
  rename_i i payload
  rcases i with _ | _ | i
  · exact bind (ptrType cx) fun _ => bind (storeVariantHead _ _ _ _ _ h.write) fun _ => hok _ _
  · exact bind (ptrType cx) fun _ => bind (storeVariantHead _ _ _ _ _ h.write) fun _ => herr _ _
  · exact storeMismatch

mutual

/-- Every store update issued by `store` preserves `I` (given `StorePres I`). -/
theorem store (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (v : Val) (t : WIT.ClosedType RtId) (ptr : Nat) :
    P.Inv I (Canon.store lim q cx v t ptr : P E σ Unit) := by
  rw [Canon.store.eq_def]
  cases t with
  | prim pt => exact storePrim _ _ _ _ _ _ h.write
  | ref r => exact nomatch r
  | list u =>
    cases v <;> try first | exact storeMismatch
    exact bind (ptrType cx) fun _ =>
      storeListWith _ _ (fun e a => store h lim q cx e u a) _ _ _ h.write
  | fixedList u n =>
    cases v <;> try first | exact storeMismatch
    exact bind (ptrType cx) fun _ =>
      storeListWith _ _ (fun e a => store h lim q cx e u a) _ _ _ h.write
  | map k u =>
    cases v <;> try first | exact storeMismatch
    refine bind (ptrType cx) fun p => storeListWith _ _ (fun e a => ?_) _ _ _ h.write
    split
    · exact bind (storePrim _ _ _ _ _ _ h.write) fun _ => store h lim q cx _ u _
    · exact storeMismatch
  | record fields =>
    cases v <;> try first | exact storeMismatch
    exact storeFields h lim q cx _ fields ptr
  | tuple ts =>
    cases v <;> try first | exact storeMismatch
    exact storeTuple h lim q cx _ ts ptr
  | variant cases =>
    cases v <;> try first | exact storeMismatch
    exact bind (ptrType cx) fun _ => bind (storeVariantHead _ _ _ _ _ h.write) fun _ =>
      storeCase h lim q cx _ _ cases _
  | enum labels =>
    cases v <;> try first | exact storeMismatch
    exact ite (bind (storeVariantHead _ _ _ _ _ h.write) fun _ => pure _) storeMismatch
  | option u =>
    rw [← Canon.store.eq_def lim q cx v (.option u) ptr]
    exact storeOption h (fun x a => store h lim q cx x u a) v ptr
  | result ok err =>
    rw [← Canon.store.eq_def lim q cx v (.result ok err) ptr]
    exact storeResult h (fun x a => storeOpt h lim q cx x ok a)
      (fun x a => storeOpt h lim q cx x err a) v ptr
  | flags labels =>
    cases v <;> try first | exact storeMismatch
    exact storeFlags _ _ _ _ h.write
  | own rt =>
    cases v <;> try first | exact storeMismatch
    exact bind (lowerOwn h.allocRes h.addHandle _ _ _ _) fun _ =>
      storeInt _ _ _ _ _ (h.write · _ _)
  | borrow rt =>
    cases v <;> try first | exact storeMismatch
    exact bind (lowerBorrow h.allocRes h.addHandle h.incBorrows _ _ _ _) fun _ =>
      storeInt _ _ _ _ _ (h.write · _ _)
  | stream u =>
    cases v <;> try first | exact storeMismatch
    exact bind (lowerAsyncValue h.addHandle h.setEndOwner h.setEndIndex _ _ _ _) fun _ =>
      storeInt _ _ _ _ _ (h.write · _ _)
  | future u =>
    cases v <;> try first | exact storeMismatch
    exact bind (lowerAsyncValue h.addHandle h.setEndOwner h.setEndIndex _ _ _ _) fun _ =>
      storeInt _ _ _ _ _ (h.write · _ _)
  | errorContext =>
    cases v <;> try first | exact storeMismatch
    exact bind (lowerErrorContext h.addHandle _ _ _) fun _ =>
      storeInt _ _ _ _ _ (h.write · _ _)
termination_by sizeOf t

theorem storeFields (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vs : List Val) (fields : List (String × WIT.ClosedType RtId)) (ptr : Nat) :
    P.Inv I (Canon.storeFields lim q cx vs fields ptr : P E σ Unit) := by
  rw [Canon.storeFields.eq_def]
  match fields, vs with
  | [], [] => exact pure _
  | (_, t) :: fields, v :: vs =>
    exact bind (ptrType cx) fun _ => bind (store h lim q cx v t _) fun _ =>
      storeFields h lim q cx vs fields _
  | [], _ :: _ => exact storeMismatch
  | _ :: _, [] => exact storeMismatch
termination_by sizeOf fields

theorem storeTuple (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vs : List Val) (ts : List (WIT.ClosedType RtId)) (ptr : Nat) :
    P.Inv I (Canon.storeTuple lim q cx vs ts ptr : P E σ Unit) := by
  rw [Canon.storeTuple.eq_def]
  match ts, vs with
  | [], [] => exact pure _
  | t :: ts, v :: vs =>
    exact bind (ptrType cx) fun _ => bind (store h lim q cx v t _) fun _ =>
      storeTuple h lim q cx vs ts _
  | [], _ :: _ => exact storeMismatch
  | _ :: _, [] => exact storeMismatch
termination_by sizeOf ts

theorem storeCase (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (i : Nat) (payload : Option Val) (cases : List (String × Option (WIT.ClosedType RtId)))
    (ptr : Nat) : P.Inv I (Canon.storeCase lim q cx i payload cases ptr : P E σ Unit) := by
  rw [Canon.storeCase.eq_def]
  match cases, i with
  | [], _ => exact storeMismatch
  | (_, t) :: _, 0 => exact storeOpt h lim q cx payload t ptr
  | _ :: cases, i + 1 => exact storeCase h lim q cx i payload cases ptr
termination_by sizeOf cases

theorem storeOpt (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (payload : Option Val) (t : Option (WIT.ClosedType RtId)) (ptr : Nat) :
    P.Inv I (Canon.storeOpt lim q cx payload t ptr : P E σ Unit) := by
  rw [Canon.storeOpt.eq_def]
  match t, payload with
  | none, _ => exact pure _
  | some u, some v => exact store h lim q cx v u ptr
  | some _, none => exact storeMismatch
termination_by sizeOf t

end

theorem storeListIntoRange (h : StorePres I) (lim : Limits) (q : Quirks)
    (cx : LiftLowerContext E) (vs : List Val) (u : WIT.ClosedType RtId) :
    P.Inv I (Canon.storeListIntoRange lim q cx vs u : P E σ (Nat × Nat)) :=
  bind (ptrType cx) fun _ =>
    storeListIntoRangeWith _ _ (fun e a => store h lim q cx e u a) _

theorem storeListIntoValidRange (h : StorePres I) (lim : Limits) (q : Quirks)
    (cx : LiftLowerContext E) (vs : List Val) (ptr : Nat) (u : WIT.ClosedType RtId) :
    P.Inv I (Canon.storeListIntoValidRange lim q cx vs ptr u : P E σ Unit) :=
  bind (ptrType cx) fun _ =>
    storeListIntoValidRangeWith _ (fun e a => store h lim q cx e u a) _ _

end P.Inv

end Silmaril.Wasm.Component.Canon
