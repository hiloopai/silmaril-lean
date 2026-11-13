module

public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs
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
# `Canon.Load`: laws of the component reference

Theorems of the component reference copy `Canon.Load`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Load`: those that other topics use through
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

theorem loadPtrWord (cx : LiftLowerContext E) (p : AddrType) (ptr : Nat) :
    P.Inv I (Canon.loadPtrWord cx p ptr : P E σ Nat) :=
  bind (loadInt _ _ _ _) fun _ => pure _

theorem loadPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (prim : WIT.Primitive) (ptr : Nat) :
    P.Inv I (Canon.loadPrim lim q cx prim ptr : P E σ Val) := by
  cases prim
  case char =>
    exact bind (loadInt _ _ _ _) fun _ => bind (convertI32ToChar _) fun _ => pure _
  case string => exact bind (loadString _ _ _ _) fun _ => pure _
  all_goals exact bind (loadInt _ _ _ _) fun _ => pure _

theorem loadListFromValidRangeWith {f : Nat → P E σ Val} (hf : ∀ n, P.Inv I (f n))
    (ptr length sz : Nat) :
    P.Inv I (Canon.loadListFromValidRangeWith f ptr length sz) :=
  mapM fun _ _ => hf _

theorem loadListFromRangeWith (lim : Limits) (cx : LiftLowerContext E) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, P.Inv I (f n)) (ptr length : Nat) :
    P.Inv I (Canon.loadListFromRangeWith lim cx l f ptr length) :=
  bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ => bind (checkInBounds _ _ _) fun _ =>
    loadListFromValidRangeWith hf _ _ _

theorem loadListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    {f : Nat → P E σ Val} (hf : ∀ n, P.Inv I (f n)) (ptr : Nat) :
    P.Inv I (Canon.loadListWith lim cx p l f ptr) :=
  bind (loadPtrWord _ _ _) fun _ => bind (loadPtrWord _ _ _) fun _ =>
    loadListFromRangeWith lim cx l hf _ _

theorem loadVariantWith (cx : LiftLowerContext E) (n : Nat) (a : Alignment)
    {payload : Nat → Nat → P E σ (Option Val)} (hp : ∀ i ptr, P.Inv I (payload i ptr))
    (ptr : Nat) : P.Inv I (Canon.loadVariantWith cx n a payload ptr) :=
  bind (loadInt _ _ _ _) fun _ => bind (trapIf _ _) fun _ => bind (hp _ _) fun _ => pure _

theorem loadFlags (cx : LiftLowerContext E) (ptr : Nat) (labels : List String) :
    P.Inv I (Canon.loadFlags cx ptr labels : P E σ Val) :=
  bind (loadInt _ _ _ _) fun _ => pure _

theorem loadMapEntryWith (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (k : WIT.KeyType) (lv : Layout) {fv : Nat → P E σ Val} (hv : ∀ n, P.Inv I (fv n))
    (ptr : Nat) : P.Inv I (Canon.loadMapEntryWith lim q cx p k lv fv ptr) :=
  bind (loadPrim _ _ _ _ _) fun _ => bind (hv _) fun _ => pure _

mutual
  theorem loadAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : WIT.ClosedType RtId) → (ptr : Nat) →
      P.Inv I (Canon.loadAt lim q cx p t ptr : P E σ Val)
    | .prim prim, ptr => by rw [Canon.loadAt]; exact loadPrim _ _ _ _ _
    | .ref r, _ => nomatch r
    | .list t, ptr => by
      rw [Canon.loadAt]
      exact bind (loadListWith _ _ _ _ (loadAt h lim q cx p t) _) fun _ => pure _
    | .fixedList t n, ptr => by
      rw [Canon.loadAt]
      exact bind (loadListFromValidRangeWith (loadAt h lim q cx p t) _ _ _) fun _ => pure _
    | .record fields, ptr => by
      rw [Canon.loadAt]
      exact bind (loadFieldsAt h lim q cx p fields ptr) fun _ => pure _
    | .tuple ts, ptr => by
      rw [Canon.loadAt]
      exact bind (loadTypesAt h lim q cx p ts ptr) fun _ => pure _
    | .variant cases, ptr => by
      rw [Canon.loadAt]
      exact loadVariantWith _ _ _ (loadCaseAt h lim q cx p cases) _
    | .enum labels, ptr => by
      rw [Canon.loadAt]
      exact loadVariantWith _ _ _ (fun _ _ => pure _) _
    | .flags labels, ptr => by rw [Canon.loadAt]; exact loadFlags _ _ _
    | .option t, ptr => by
      rw [Canon.loadAt]
      refine loadVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact pure _
      · exact bind (loadAt h lim q cx p t _) fun _ => pure _
      · exact pure _
    | .result ok err, ptr => by
      rw [Canon.loadAt]
      refine loadVariantWith _ _ _ (fun i _ => ?_) _
      rcases i with _ | _ | _
      · exact loadOptAt h lim q cx p ok _
      · exact loadOptAt h lim q cx p err _
      · exact pure _
    | .map k v, ptr => by
      rw [Canon.loadAt]
      exact bind (loadListWith _ _ _ _
        (loadMapEntryWith _ _ _ _ _ _ (loadAt h lim q cx p v)) _) fun _ => pure _
    | .own rt, ptr => by
      rw [Canon.loadAt]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftOwn h.remove _ _ _ _) fun _ => pure _
    | .borrow rt, ptr => by
      rw [Canon.loadAt]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftBorrow h.lender _ _ _ _) fun _ => pure _
    | .stream t, ptr => by
      rw [Canon.loadAt]
      exact bind (loadInt _ _ _ _) fun _ =>
        bind (liftAsyncValue h.remove h.release _ _ _ _ _) fun _ => pure _
    | .future t, ptr => by
      rw [Canon.loadAt]
      exact bind (loadInt _ _ _ _) fun _ =>
        bind (liftAsyncValue h.remove h.release _ _ _ _ _) fun _ => pure _
    | .errorContext, ptr => by
      rw [Canon.loadAt]
      exact bind (loadInt _ _ _ _) fun _ => bind (liftErrorContext _ _ _) fun _ => pure _

  theorem loadFieldsAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (fields : List (String × WIT.ClosedType RtId)) → (ptr : Nat) →
      P.Inv I (Canon.loadFieldsAt lim q cx p fields ptr : P E σ (List Val))
    | [], _ => by rw [Canon.loadFieldsAt]; exact pure _
    | (_, t) :: fields, ptr => by
      rw [Canon.loadFieldsAt]
      exact bind (loadAt h lim q cx p t _) fun _ =>
        bind (loadFieldsAt h lim q cx p fields _) fun _ => pure _

  theorem loadTypesAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (ts : List (WIT.ClosedType RtId)) → (ptr : Nat) →
      P.Inv I (Canon.loadTypesAt lim q cx p ts ptr : P E σ (List Val))
    | [], _ => by rw [Canon.loadTypesAt]; exact pure _
    | t :: ts, ptr => by
      rw [Canon.loadTypesAt]
      exact bind (loadAt h lim q cx p t _) fun _ =>
        bind (loadTypesAt h lim q cx p ts _) fun _ => pure _

  theorem loadCaseAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (cases : List (String × Option (WIT.ClosedType RtId))) → (i ptr : Nat) →
      P.Inv I (Canon.loadCaseAt lim q cx p cases i ptr : P E σ (Option Val))
    | [], _, _ => by rw [Canon.loadCaseAt]; exact pure _
    | (_, t) :: _, 0, ptr => by rw [Canon.loadCaseAt]; exact loadOptAt h lim q cx p t ptr
    | _ :: cases, i + 1, ptr => by
      rw [Canon.loadCaseAt]; exact loadCaseAt h lim q cx p cases i ptr

  theorem loadOptAt (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
      (p : AddrType) : (t : Option (WIT.ClosedType RtId)) → (ptr : Nat) →
      P.Inv I (Canon.loadOptAt lim q cx p t ptr : P E σ (Option Val))
    | none, _ => by rw [Canon.loadOptAt]; exact pure _
    | some t, ptr => by
      rw [Canon.loadOptAt]; exact bind (loadAt h lim q cx p t ptr) fun _ => pure _
end

theorem loadListFromValidRange (h : LoadPres I) (lim : Limits) (q : Quirks)
    (cx : LiftLowerContext E) (ptr length : Nat) (t : WIT.ClosedType RtId) :
    P.Inv I (Canon.loadListFromValidRange lim q cx ptr length t : P E σ (List Val)) :=
  bind (ptrType cx) fun p => loadListFromValidRangeWith (loadAt h lim q cx p t) _ _ _

end P.Inv

end Silmaril.Wasm.Component.Canon
