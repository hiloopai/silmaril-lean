module

public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Options.Thms

/-!
# `Canon.Context`: laws of the component reference

Theorems of the component reference copy `Canon.Context`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Context`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type} {α : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem ptrType (cx : LiftLowerContext E) : P.Inv I (Canon.ptrType cx : P E σ _) := gets _

theorem ptrSize (cx : LiftLowerContext E) : P.Inv I (Canon.ptrSize cx : P E σ _) :=
  bind (ptrType cx) fun _ => pure _

theorem memAddr (cx : LiftLowerContext E) : P.Inv I (Canon.memAddr cx : P E σ _) :=
  orTrap _ _

theorem memLen (cx : LiftLowerContext E) : P.Inv I (Canon.memLen cx : P E σ _) :=
  bind (memAddr cx) fun _ => bind getStore fun _ => orTrap _ _

theorem readMem (cx : LiftLowerContext E) (ptr len : Nat) :
    P.Inv I (Canon.readMem cx ptr len : P E σ _) :=
  bind (memAddr cx) fun _ => bind getStore fun _ => orTrap _ _

/-- `writeMem` preserves `I` when every memory write does. -/
theorem writeMem (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray)
    (h : ∀ m s, I s → I (writeMemSt m ptr bytes s)) :
    P.Inv I (Canon.writeMem cx ptr bytes : P E σ Unit) :=
  bind (memAddr cx) fun m => bind getStore fun s => by
    cases E.memWrite? s.core m ptr bytes with
    | none => exact trap _
    | some _ => exact modifyStore (h m)

theorem checkAligned (ptr align : Nat) : P.Inv I (Canon.checkAligned ptr align : P E σ _) :=
  trapIf _ _

theorem checkInBounds (cx : LiftLowerContext E) (ptr size : Nat) :
    P.Inv I (Canon.checkInBounds cx ptr size : P E σ _) :=
  bind (memLen cx) fun _ => trapIf _ _

theorem unpackEvent (cx : LiftLowerContext E) (ptr : Nat) (e : AsyncRef.EventTuple)
    (h : ∀ m p v s, I s → I (writeMemSt m p (u32Bytes v) s)) :
    P.Inv I (Canon.unpackEvent cx ptr e : P E σ Nat) :=
  bind (checkAligned _ _) fun _ => bind (checkInBounds _ _ _) fun _ =>
    bind (writeMem _ _ _ (h · _ _)) fun _ =>
      bind (writeMem _ _ _ (h · _ _)) fun _ => pure _

theorem reallocate (cx : LiftLowerContext E) (old oldLen align newLen : Nat) :
    P.Inv I (Canon.reallocate cx old oldLen align newLen : P E σ Nat) := callNat _

theorem allocate (cx : LiftLowerContext E) (align size : Nat) :
    P.Inv I (Canon.allocate cx align size : P E σ Nat) := reallocate _ _ _ _ _

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type} {α : Type}

theorem ptrTypeIn_none (s : CStore E) (cx : LiftLowerContext E) (h : cx.opts.memory = none) :
    ptrTypeIn s cx = .i32 := CanonOpts.ptrType_none _ _ h

end Silmaril.Wasm.Component.Canon
