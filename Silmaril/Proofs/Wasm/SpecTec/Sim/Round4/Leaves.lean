module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Multi

/-!
# Round 4: leaves of the positive typing that need no validity

`typedV_catch`: every encoded catch clause is a typed `catch` (its indices are `u32`s by
construction). This discharges what would otherwise be a field of `PosTyping`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d254)

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_catch : (simEnv B).findTyp? "catch" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d254 0))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_tagidx :
    (simEnv B).findTyp? "tagidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- A tag index and a label index, as `tagidx labelidx`. -/
theorem hasTyp_tagLabel (x : TagIdx) (l : LabelIdx) :
    HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "tagidx" (.varT "tagidx" []), .mk "labelidx" (.varT "labelidx" [])])
      (.tuple [Encode.toValue x, Encode.toValue l]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Typing.typedV_alias findTyp_tagidx (Typing.typedV_idx x) _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl,
      Typing.typedV_alias Typing.findTyp_labelidx (Typing.typedV_idx l) _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩

set_option maxRecDepth 100000 in
/-- **Every catch clause is a typed `catch`.** -/
theorem typedV_catch (c : Catch) : TypedV (simEnv B) (.varT "catch" []) (Encode.toValue c) := by
  rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
  · exact Typing.typedV_closedCase findTyp_catch rfl (hasTyp_tagLabel x l)
  · exact Typing.typedV_closedCase findTyp_catch rfl (hasTyp_tagLabel x l)
  · exact Typing.typedV_closedCase findTyp_catch rfl
      (Typing.typedV_alias Typing.findTyp_labelidx (Typing.typedV_idx l) _ ⟨rfl, rfl, rfl⟩)
  · exact Typing.typedV_closedCase findTyp_catch rfl
      (Typing.typedV_alias Typing.findTyp_labelidx (Typing.typedV_idx l) _ ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.Round4
