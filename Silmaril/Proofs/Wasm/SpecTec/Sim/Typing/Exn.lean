module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Values
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms

/-!
# Family X's typing interface `Exn.Typing`, up to block types

`exnTyping_simEnv`: every field of `Exn.Typing (simEnv B)` except `blocktype` is proved; the
`blocktype` field (every encoded `BlockType` is a `blocktype`, which needs the typing of encoded
value types, i.e. of the closed type syntax) is taken as the hypothesis `hbt`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_exninst : (simEnv B).findTyp? "exninst" = some ([], [.instD [] [] (.structT
    [.mk "TAG" (.varT "tagaddr" []) [] [], .mk "FIELDS" (.iterT (.varT "val" []) .list) [] []])]) :=
  rfl

set_option maxRecDepth 100000 in
theorem findTyp_tagaddr :
    (simEnv B).findTyp? "tagaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl

/-- An exception instance with typed fields is an `exninst`. -/
theorem typedV_exninst (e : ExnInst) (h : TypedV (simEnv B) valsT (.list (e.fields.map valV))) :
    TypedV (simEnv B) (.varT "exninst" []) (exnInstV e) := fun ρ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_exninst
    Equiv.evalArgs_nil matchArgs_nil
    (hasTypFields_cons_iff.2 ⟨_, _, rfl,
      typedV_addrAlias findTyp_tagaddr e.tag _ ⟨rfl, rfl, rfl⟩, premsOk_nil,
      hasTypFields_cons_iff.2 ⟨_, _, rfl, h _ ⟨rfl, rfl, rfl⟩, premsOk_nil,
        hasTypFields_nil_iff.2 rfl⟩⟩)

/-- **Family X's typing interface holds in every `simEnv B`, given that encoded block types are
typed.** -/
theorem exnTyping_simEnv (B : Builtins)
    (hbt : ∀ bt : BlockType, TypedV (simEnv B) Exn.blocktypeT (Encode.toValue bt)) :
    Exn.Typing (simEnv B) where
  addr := typedV_natAlias findTyp_addr
  n := typedV_natAlias findTyp_n
  m := typedV_natAlias findTyp_m
  idx x := typedV_idx x
  labelidx l := typedV_alias findTyp_labelidx (typedV_idx l)
  blocktype := hbt
  exninst e h := typedV_exninst e h
  catch_ _ _ h := typedV_list_cons_iff.1 h

end Silmaril.Wasm.SpecTec.Sim.Typing
