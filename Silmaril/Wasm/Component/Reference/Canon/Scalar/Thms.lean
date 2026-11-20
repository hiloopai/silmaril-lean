module

public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Scalar`: laws of the component reference

Theorems of the component reference copy `Canon.Scalar`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Scalar`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Execution
variable {E : CoreEngine} {σ : Type}

namespace P.Inv

variable {I : CStore E → Prop} {W : σ → Prop}

theorem loadInt (cx : LiftLowerContext E) (ptr nbytes : Nat) (signed : Bool) :
    P.InvW I W (Canon.loadInt cx ptr nbytes signed : P E σ Int) :=
  bind (readMem cx ptr nbytes) fun _ => pure _

theorem storeInt (cx : LiftLowerContext E) (v : Int) (ptr nbytes : Nat) (signed : Bool) :
    P.InvW I W (Canon.storeInt cx v ptr nbytes signed : P E σ Unit) :=
  writeMem cx ptr _

theorem convertI32ToChar (i : BitVec 32) :
    P.InvW I W (Canon.convertI32ToChar i : P E σ Char) := orTrap _ _

theorem lowerFloat (t : FloatType) (x : BitVec t.width) :
    P.InvW I W (Canon.lowerFloat t x : P E σ _) := by
  unfold Canon.lowerFloat
  split
  · exact choose _
  · exact pure _

theorem encodeFloat (t : FloatType) (x : BitVec t.width) :
    P.InvW I W (Canon.encodeFloat t x : P E σ _) :=
  bind (lowerFloat t x) fun _ => pure _

theorem coerceLower (have_ want : NumType) (v : FlatValue) :
    P.InvW I W (Canon.coerceLower have_ want v : P E σ FlatValue) := by
  unfold Canon.coerceLower
  split
  · exact bind (encodeFloat _ _) fun _ => pure _
  · exact pure _
  · exact bind (encodeFloat _ _) fun _ => pure _
  · exact bind (encodeFloat _ _) fun _ => pure _
  · exact pure _

end P.Inv

end Silmaril.Wasm.Component.Canon
