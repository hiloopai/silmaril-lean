module

public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Strings`: laws of the component reference

Theorems of the component reference copy `Canon.Strings`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Strings`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type}

theorem runStoreSteps_cons (cx : LiftLowerContext E) (ptr : Nat) (s : ABI.StoreStep)
    (ss : List ABI.StoreStep) :
    (runStoreSteps cx ptr (s :: ss) : P E σ Nat) =
      runStoreStep cx ptr s >>= fun p => runStoreSteps cx p ss := rfl

namespace P.Inv

variable {I : CStore E → Prop}

theorem loadStringFromRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr tagged : Nat) :
    P.Inv I (Canon.loadStringFromRange lim q cx ptr tagged : P E σ StrVal) := by
  unfold Canon.loadStringFromRange
  refine bind (ptrType cx) fun a => bind (trapIf _ _) fun _ => bind (trapIf _ _) fun _ =>
    bind (checkInBounds _ _ _) fun _ => bind (readMem _ _ _) fun bs => ?_
  split
  · exact trap _
  · exact pure _

theorem loadString (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat) :
    P.Inv I (Canon.loadString lim q cx ptr : P E σ StrVal) :=
  bind (ptrSize cx) fun _ =>
    bind (bind (readMem _ _ _) fun _ => pure _) fun _ =>
      bind (bind (readMem _ _ _) fun _ => pure _) fun _ => loadStringFromRange _ _ _ _ _

theorem runStoreStep (cx : LiftLowerContext E) (ptr : Nat) (s : ABI.StoreStep)
    (h : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.runStoreStep cx ptr s : P E σ Nat) := by
  cases s with
  | allocate => exact allocate _ _ _
  | reallocate => exact reallocate _ _ _ _ _
  | trapIfMisaligned => exact bind (trapIf _ _) fun _ => pure _
  | trapIfOutOfBounds => exact bind (checkInBounds _ _ _) fun _ => pure _
  | write => exact bind (writeMem _ _ _ (h · _ _)) fun _ => pure _
  | inflateLatin1 =>
    exact bind (readMem _ _ _) fun _ => bind (writeMem _ _ _ (h · _ _)) fun _ => pure _
  | deflateUtf16 =>
    exact bind (readMem _ _ _) fun _ => bind (writeMem _ _ _ (h · _ _)) fun _ => pure _

theorem runStoreSteps (cx : LiftLowerContext E) (ptr : Nat) (ss : List ABI.StoreStep)
    (h : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.runStoreSteps cx ptr ss : P E σ Nat) := by
  induction ss generalizing ptr with
  | nil => exact pure _
  | cons s ss ih =>
    rw [runStoreSteps_cons]
    exact bind (runStoreStep cx ptr s h) fun p => ih p

theorem storeStringIntoRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (v : StrVal) (h : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storeStringIntoRange lim q cx v : P E σ (Nat × Nat)) :=
  bind (ptrType cx) fun _ => bind (runStoreSteps _ _ _ h) fun _ => pure _

theorem storeString (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (v : StrVal)
    (ptr : Nat) (h : ∀ m p bs s, I s → I (writeMemSt m p bs s)) :
    P.Inv I (Canon.storeString lim q cx v ptr : P E σ Unit) :=
  bind (storeStringIntoRange lim q cx v h) fun _ => bind (ptrSize cx) fun _ =>
    bind (writeMem _ _ _ (h · _ _)) fun _ => writeMem _ _ _ (h · _ _)

end P.Inv

end Silmaril.Wasm.Component.Canon
