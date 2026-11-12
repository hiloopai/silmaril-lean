module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary.Instructions
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary.Modules
public import Silmaril.Wasm.Lime1.Modules

/-! # Lime1 binary format: modules

The Wasm 1.0 module grammar (`Scalar.Binary.Module`, REC 5.5) over Lime1
expressions. `Encodes` is the profile (`overlong = true`); `EncodesWith false`
is the same grammar with 1.0's literal `call_indirect` byte.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Binary

open Silmaril.Wasm.Binary

/-- The Lime1 module grammar, with or without call-indirect-overlong. -/
abbrev EncodesWith (overlong : Bool) : Bytes → Lime1.Module → Prop :=
  Scalar.Binary.Module (Expr overlong)

/-- The Lime1 profile's module grammar. -/
abbrev Encodes : Bytes → Lime1.Module → Prop := EncodesWith true

theorem EncodesWith.mono {b : Bytes} {m : Lime1.Module} (h : EncodesWith false b m) :
    Encodes b m := by
  have h' := Scalar.Binary.Module.map (G := Expr false) (G' := Expr true) id
    (fun h => Expr.mono h) h
  have hf : (Declaration.Func.mapBody id : Declaration.Func V1.ValType Lime1.Expr → _) = id :=
    funext Declaration.Func.mapBody_id
  have hg : (Declaration.Global.mapInit id :
      Declaration.Global V1.GlobalType Lime1.Expr → _) = id :=
    funext Declaration.Global.mapInit_id
  simp only [hf, hg, List.map_id, id] at h'
  rwa [List.map_id'' (fun _ => rfl), List.map_id'' (fun _ => rfl)] at h'

end Silmaril.Wasm.Lime1.Binary

namespace Silmaril.Wasm.Lime1

/-- Lime1 modules use the generic scalar module type with Lime1 expressions. -/
instance : Encoding Module := ⟨Binary.Encodes⟩

theorem Binary.functional : Encoding.Functional Module := fun _ _ _ h h' =>
  Scalar.Binary.Module.functional (Binary.Expr.prefixFree true) h h'

end Silmaril.Wasm.Lime1
