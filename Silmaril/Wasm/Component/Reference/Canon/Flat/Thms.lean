module

public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Component.Reference.Async.Codes.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Flat`: laws of the component reference

Theorems of the component reference copy `Canon.Flat`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Flat`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem next (vi : FlatCursor) (t : CoreType) :
    P.Inv I (FlatCursor.next vi t : P E σ _) := by
  unfold FlatCursor.next
  split
  · exact pure _
  · exact internal _

theorem nextN (vi : FlatCursor) (ts : List CoreType) :
    P.Inv I (FlatCursor.nextN vi ts : P E σ _) := by
  induction ts generalizing vi with
  | nil => exact pure _
  | cons t ts ih => exact bind (next vi t) fun _ => bind (ih _) fun _ => pure _

theorem flatMismatch {α : Type} : P.Inv I (Canon.flatMismatch : P E σ α) := internal _

theorem liftFlatPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (prim : WIT.Primitive) (vi : FlatCursor) :
    P.Inv I (Canon.liftFlatPrim lim q cx p prim vi : P E σ _) := by
  unfold Canon.liftFlatPrim
  cases prim
  case bool | f32 | f64 => exact bind (next _ _) fun _ => pure _
  case char => exact bind (next _ _) fun _ => bind (convertI32ToChar _) fun _ => pure _
  case string =>
    exact bind (next _ _) fun _ => bind (next _ _) fun _ =>
      bind (loadStringFromRange _ _ _ _ _) fun _ => pure _
  all_goals exact bind (next _ _) fun _ => pure _

theorem liftFlatN {f : FlatCursor → P E σ (Val × FlatCursor)} (hf : ∀ vi, P.Inv I (f vi))
    (n : Nat) (vi : FlatCursor) : P.Inv I (Canon.liftFlatN f n vi) := by
  induction n generalizing vi with
  | zero => exact pure _
  | succ n ih => exact bind (hf _) fun _ => bind (ih _) fun _ => pure _

theorem liftFlatListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, P.Inv I (f n)) (vi : FlatCursor) :
    P.Inv I (Canon.liftFlatListWith lim cx p l f vi) :=
  bind (next _ _) fun _ => bind (next _ _) fun _ =>
    bind (loadListFromRangeWith lim cx l hf _ _) fun _ => pure _

theorem liftFlatVariantWith (n : Nat) (joined : List CoreType) (wants : Nat → List CoreType)
    {payload : Nat → FlatCursor → P E σ (Option Val × FlatCursor)}
    (hp : ∀ i c, P.Inv I (payload i c)) (vi : FlatCursor) :
    P.Inv I (Canon.liftFlatVariantWith n joined wants payload vi) :=
  bind (next _ _) fun _ => bind (trapIf _ _) fun _ => bind (nextN _ _) fun _ =>
    bind (hp _ _) fun _ => pure _

mutual
  theorem liftFlatAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : WIT.ClosedType RtId) → (vi : FlatCursor) →
      P.Inv I (Canon.liftFlatAt lim q cx p t vi : P E σ _)
    | .prim prim, vi => by rw [Canon.liftFlatAt]; exact liftFlatPrim _ _ _ _ _ _
    | .ref r, _ => nomatch r
    | .list t, vi => by
      rw [Canon.liftFlatAt]; exact liftFlatListWith _ _ _ _ (loadAt h lim q cx p t) _
    | .fixedList t n, vi => by
      rw [Canon.liftFlatAt]
      exact bind (liftFlatN (liftFlatAt h lim q cx p t) _ _) fun _ => pure _
    | .record fields, vi => by
      rw [Canon.liftFlatAt]
      exact bind (liftFlatFields h lim q cx p fields vi) fun _ => pure _
    | .tuple ts, vi => by
      rw [Canon.liftFlatAt]
      exact bind (liftFlatTypes h lim q cx p ts vi) fun _ => pure _
    | .variant cases, vi => by
      rw [Canon.liftFlatAt]
      exact liftFlatVariantWith _ _ _ (liftFlatCaseAt h lim q cx p cases) _
    | .enum labels, vi => by
      rw [Canon.liftFlatAt]
      exact liftFlatVariantWith _ _ _ (fun _ _ => pure _) _
    | .flags labels, vi => by
      rw [Canon.liftFlatAt]; exact bind (next _ _) fun _ => pure _
    | .option t, vi => by
      rw [Canon.liftFlatAt]
      refine liftFlatVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact pure _
      · exact bind (liftFlatAt h lim q cx p t _) fun _ => pure _
      · exact pure _
    | .result ok err, vi => by
      rw [Canon.liftFlatAt]
      refine liftFlatVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact liftFlatOpt h lim q cx p ok _
      · exact liftFlatOpt h lim q cx p err _
      · exact pure _
    | .map k v, vi => by
      rw [Canon.liftFlatAt]
      exact liftFlatListWith _ _ _ _
        (loadMapEntryWith _ _ _ _ _ _ (loadAt h lim q cx p v)) _
    | .own rt, vi => by
      rw [Canon.liftFlatAt]
      exact bind (next _ _) fun _ => bind (liftOwn h.remove _ _ _ _) fun _ => pure _
    | .borrow rt, vi => by
      rw [Canon.liftFlatAt]
      exact bind (next _ _) fun _ => bind (liftBorrow h.lender _ _ _ _) fun _ => pure _
    | .stream t, vi => by
      rw [Canon.liftFlatAt]
      exact bind (next _ _) fun _ =>
        bind (liftAsyncValue h.remove h.release _ _ _ _ _) fun _ => pure _
    | .future t, vi => by
      rw [Canon.liftFlatAt]
      exact bind (next _ _) fun _ =>
        bind (liftAsyncValue h.remove h.release _ _ _ _ _) fun _ => pure _
    | .errorContext, vi => by
      rw [Canon.liftFlatAt]
      exact bind (next _ _) fun _ => bind (liftErrorContext _ _ _) fun _ => pure _

  theorem liftFlatFields (h : LoadPres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (fields : List (String × WIT.ClosedType RtId)) → (vi : FlatCursor) →
      P.Inv I (Canon.liftFlatFields lim q cx p fields vi : P E σ _)
    | [], _ => by rw [Canon.liftFlatFields]; exact pure _
    | (_, t) :: fields, vi => by
      rw [Canon.liftFlatFields]
      exact bind (liftFlatAt h lim q cx p t _) fun _ =>
        bind (liftFlatFields h lim q cx p fields _) fun _ => pure _

  theorem liftFlatTypes (h : LoadPres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (ts : List (WIT.ClosedType RtId)) → (vi : FlatCursor) →
      P.Inv I (Canon.liftFlatTypes lim q cx p ts vi : P E σ _)
    | [], _ => by rw [Canon.liftFlatTypes]; exact pure _
    | t :: ts, vi => by
      rw [Canon.liftFlatTypes]
      exact bind (liftFlatAt h lim q cx p t _) fun _ =>
        bind (liftFlatTypes h lim q cx p ts _) fun _ => pure _

  theorem liftFlatCaseAt (h : LoadPres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (cases : List (String × Option (WIT.ClosedType RtId))) → (i : Nat) →
      (vi : FlatCursor) →
      P.Inv I (Canon.liftFlatCaseAt lim q cx p cases i vi : P E σ _)
    | [], _, _ => by rw [Canon.liftFlatCaseAt]; exact pure _
    | (_, t) :: _, 0, vi => by rw [Canon.liftFlatCaseAt]; exact liftFlatOpt h lim q cx p t vi
    | _ :: cases, i + 1, vi => by
      rw [Canon.liftFlatCaseAt]; exact liftFlatCaseAt h lim q cx p cases i vi

  theorem liftFlatOpt (h : LoadPres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (t : Option (WIT.ClosedType RtId)) → (vi : FlatCursor) →
      P.Inv I (Canon.liftFlatOpt lim q cx p t vi : P E σ _)
    | none, _ => by rw [Canon.liftFlatOpt]; exact pure _
    | some t, vi => by
      rw [Canon.liftFlatOpt]; exact bind (liftFlatAt h lim q cx p t vi) fun _ => pure _
end

theorem liftFlatValues (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (max : Nat) (vi : FlatCursor) (ts : List (WIT.ClosedType RtId)) :
    P.Inv I (Canon.liftFlatValues lim q cx max vi ts : P E σ _) :=
  bind (ptrType cx) fun p =>
    ite (bind (next _ _) fun _ => bind (trapIf _ _) fun _ => bind (checkInBounds _ _ _)
      fun _ => bind (loadTypesAt h lim q cx p ts _) fun _ => pure _)
      (liftFlatTypes h lim q cx p ts vi)

theorem lowerFlatPrim (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (p : AddrType) (pt : WIT.Primitive) (v : Val) :
    P.Inv I (Canon.lowerFlatPrim lim q cx p pt v : P E σ _) := by
  unfold Canon.lowerFlatPrim
  split
  · exact pure _
  · exact bind (lowerFloat _ _) fun _ => pure _
  · exact bind (lowerFloat _ _) fun _ => pure _
  · exact pure _
  · exact bind (storeStringIntoRange _ _ _ _ h.write) fun _ => pure _
  · split
    · exact pure _
    · exact flatMismatch
  · exact flatMismatch

theorem coerceLowerSlots (hs ws : List CoreType) (vs : List FlatValue) :
    P.Inv I (Canon.coerceLowerSlots hs ws vs : P E σ _) := by
  induction hs generalizing ws vs with
  | nil => rw [Canon.coerceLowerSlots.eq_def]; exact pure _
  | cons h hs ih =>
    rcases ws with _ | ⟨w, ws⟩ <;> rcases vs with _ | ⟨v, vs⟩ <;>
      rw [Canon.coerceLowerSlots.eq_def]
    · exact pure _
    · exact internal _
    · exact pure _
    · exact bind (coerceLower _ _ _) fun _ => bind (ih _ _) fun _ => pure _

theorem lowerFlatVariantWith (n : Nat) (joined : List CoreType) (i : Nat)
    (haves : List CoreType) {payload : P E σ (List FlatValue)} (hp : P.Inv I payload) :
    P.Inv I (Canon.lowerFlatVariantWith n joined i haves payload) :=
  ite (bind hp fun _ => bind (coerceLowerSlots _ _ _) fun _ => pure _) flatMismatch

theorem spillPointer (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    (o : Option FlatCursor) : P.Inv I (Canon.spillPointer cx p l o : P E σ _) := by
  cases o with
  | none => exact bind (allocate _ _ _) fun _ => pure _
  | some op => exact bind (next _ _) fun _ => pure _

theorem unpackCallbackResult (packed : Nat) :
    P.Inv I (Canon.unpackCallbackResult packed : P E σ _) := orTrap _ _

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop}

mutual
  theorem lowerFlatAt (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (v : Val) → (t : WIT.ClosedType RtId) →
      P.Inv I (Canon.lowerFlatAt lim q cx p v t : P E σ _)
    | v, .prim pt => by rw [Canon.lowerFlatAt]; exact lowerFlatPrim h _ _ _ _ _ _
    | _, .ref r => nomatch r
    | v, .list u => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (storeListIntoRange h _ _ _ _ _) fun _ => pure _
    | v, .fixedList u n => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (mapM fun e _ => lowerFlatAt h lim q cx p e u) fun _ => pure _
    | v, .map k u => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (storeListIntoRange h _ _ _ _ _) fun _ => pure _
    | v, .record fields => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact lowerFlatFields h lim q cx p _ fields
    | v, .tuple ts => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact lowerFlatTypes h lim q cx p _ ts
    | v, .variant cases => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact lowerFlatVariantWith _ _ _ _ (lowerFlatCase h lim q cx p _ _ cases)
    | v, .enum labels => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact lowerFlatVariantWith _ _ _ _ (pure _)
    | v, .option u => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      rename_i i payload
      refine lowerFlatVariantWith _ _ _ _ ?_
      rcases i with _ | _ | i
      · exact pure _
      · cases payload
        · exact flatMismatch
        · exact lowerFlatAt h lim q cx p _ u
      · exact pure _
    | v, .result ok err => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      rename_i i payload
      refine lowerFlatVariantWith _ _ _ _ ?_
      rcases i with _ | _ | i
      · exact lowerFlatOpt h lim q cx p _ ok
      · exact lowerFlatOpt h lim q cx p _ err
      · exact pure _
    | v, .flags labels => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact pure _
    | v, .own rt => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (lowerOwn h.allocRes h.addHandle _ _ _ _) fun _ => pure _
    | v, .borrow rt => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (lowerBorrow h.allocRes h.addHandle h.incBorrows _ _ _ _) fun _ => pure _
    | v, .stream u => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (lowerAsyncValue h.addHandle h.setEndOwner h.setEndIndex _ _ _ _) fun _ =>
        pure _
    | v, .future u => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (lowerAsyncValue h.addHandle h.setEndOwner h.setEndIndex _ _ _ _) fun _ =>
        pure _
    | v, .errorContext => by
      rw [Canon.lowerFlatAt.eq_def]; cases v <;> try first | exact flatMismatch
      exact bind (lowerErrorContext h.addHandle _ _ _) fun _ => pure _

  theorem lowerFlatFields (h : StorePres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (vs : List Val) → (fields : List (String × WIT.ClosedType RtId)) →
      P.Inv I (Canon.lowerFlatFields lim q cx p vs fields : P E σ _)
    | [], [] => by rw [Canon.lowerFlatFields]; exact pure _
    | v :: vs, (_, t) :: fields => by
      rw [Canon.lowerFlatFields]
      exact bind (lowerFlatAt h lim q cx p v t) fun _ =>
        bind (lowerFlatFields h lim q cx p vs fields) fun _ => pure _
    | [], _ :: _ => by rw [Canon.lowerFlatFields.eq_def]; exact flatMismatch
    | _ :: _, [] => by rw [Canon.lowerFlatFields.eq_def]; exact flatMismatch

  theorem lowerFlatTypes (h : StorePres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) :
      (vs : List Val) → (ts : List (WIT.ClosedType RtId)) →
      P.Inv I (Canon.lowerFlatTypes lim q cx p vs ts : P E σ _)
    | [], [] => by rw [Canon.lowerFlatTypes]; exact pure _
    | v :: vs, t :: ts => by
      rw [Canon.lowerFlatTypes]
      exact bind (lowerFlatAt h lim q cx p v t) fun _ =>
        bind (lowerFlatTypes h lim q cx p vs ts) fun _ => pure _
    | [], _ :: _ => by rw [Canon.lowerFlatTypes.eq_def]; exact flatMismatch
    | _ :: _, [] => by rw [Canon.lowerFlatTypes.eq_def]; exact flatMismatch

  theorem lowerFlatCase (h : StorePres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) (i : Nat) (payload : Option Val) :
      (cases : List (String × Option (WIT.ClosedType RtId))) →
      P.Inv I (Canon.lowerFlatCase lim q cx p i payload cases : P E σ _)
    | [] => by rw [Canon.lowerFlatCase.eq_def]; exact flatMismatch
    | (_, t) :: cases => by
      rw [Canon.lowerFlatCase.eq_def]
      cases i with
      | zero => exact lowerFlatOpt h lim q cx p payload t
      | succ i => exact lowerFlatCase h lim q cx p i payload cases

  theorem lowerFlatOpt (h : StorePres I) (lim : Limits) (q : Quirks)
      (cx : LiftLowerContext E) (p : AddrType) (payload : Option Val) :
      (t : Option (WIT.ClosedType RtId)) →
      P.Inv I (Canon.lowerFlatOpt lim q cx p payload t : P E σ _)
    | none => by rw [Canon.lowerFlatOpt.eq_def]; exact pure _
    | some t => by
      rw [Canon.lowerFlatOpt.eq_def]
      cases payload with
      | none => exact flatMismatch
      | some v => exact lowerFlatAt h lim q cx p v t
end

theorem lowerFlatValues (h : StorePres I) (lim : Limits) (q : Quirks)
    (cx : LiftLowerContext E) (max : Nat) (vs : List Val) (ts : List (WIT.ClosedType RtId))
    (outParam : Option FlatCursor) :
    P.Inv I (Canon.lowerFlatValues lim q cx max vs ts outParam : P E σ _) :=
  bind (ptrType cx) fun p =>
    ite (bind (spillPointer _ _ _ _) fun _ => bind (trapIf _ _) fun _ =>
      bind (checkInBounds _ _ _) fun _ => bind (store h _ _ _ _ _ _) fun _ => pure _)
      (lowerFlatTypes h lim q cx p vs ts)

end P.Inv

end Silmaril.Wasm.Component.Canon
