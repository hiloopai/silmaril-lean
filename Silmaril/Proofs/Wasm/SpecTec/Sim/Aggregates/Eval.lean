module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Proved
public import Silmaril.Wasm.SpecTec.Sim.State.Thms

/-!
# Aggregates: evaluating the aggregate state functions

The aggregate rules read and write the state through defined functions of the script:
`$type`, `$structinst`, `$arrayinst`, `$moduleinst`, `$with_struct`, `$with_array`,
`$add_structinst`, `$add_arrayinst`, and `$elem`. Each has a single premise-free clause
(`AggDefs`, proved for every `simEnv B` by computation in `aggDefs_simEnv`), so it is evaluated
here by matching that clause, as family M does for its accessors (`State.evalExp_call1`).

Consequence: three of the four fields of family R's `RStoreFuns` are **theorems**
(`rStoreFuns_moduleinst`, `rStoreFuns_arrayinst`, `rStoreFuns_structinst`, and `$elem` through
family M's `State.evalExp_elem`: `rStoreFuns_elem`); `rStoreFuns_of_instReftype` builds the
structure from the remaining field, `$inst_reftype`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (DefType)
open State (HasClause1 statePat zPat zxPat idxPayload iterVar idxV)

/-- `z, a, i, fv`, the argument pattern of `$with_struct` and `$with_array`. -/
abbrev zaifPat : List Arg :=
  [.expA (.varE "z"), .expA (.varE "a"), .expA (.varE "i"), .expA (.varE "fv")]

/-- The body of `$with_struct` / `$with_array` for the store field `Fl`:
`$sof(z)[.Fl[a].FIELDS[i] = fv]; $fof(z)`. -/
def withAggBody (Fl : AtomS) : Exp :=
  .caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
      (.idxP (.dotP (.idxP (.dotP .rootP Fl) (.varE "a")) "FIELDS") (.varE "i")) (.varE "fv"),
    .callE "fof" [.expA (.varE "z")]])

/-- The body of `$add_structinst` / `$add_arrayinst` for the store field `Fl` and element
variable `y`: `$sof(z)[.Fl =++ y*]; $fof(z)`. -/
def addAggBody (Fl : AtomS) (y ys : IL.Id) : Exp :=
  .caseE "%;%" (.tupE [.extE (.callE "sof" [.expA (.varE "z")]) (.dotP .rootP Fl) (iterVar y ys),
    .callE "fof" [.expA (.varE "z")]])

/-- The environment facts the aggregate rules evaluate through. -/
structure AggDefs (env : Env) : Prop where
  /-- `$type(z, x) = $fof(z).MODULE.TYPES[x!%.0]`. -/
  type_ : HasClause1 env "type" zxPat
    (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE") "TYPES") idxPayload)
  /-- `$structinst((s; f)) = s.STRUCTS`. -/
  structinst : HasClause1 env "structinst" statePat (.dotE (.varE "s") "STRUCTS")
  /-- `$arrayinst((s; f)) = s.ARRAYS`. -/
  arrayinst : HasClause1 env "arrayinst" statePat (.dotE (.varE "s") "ARRAYS")
  /-- `$moduleinst((s; f)) = f.MODULE`. -/
  moduleinst : HasClause1 env "moduleinst" statePat (.dotE (.varE "f") "MODULE")
  /-- `$with_struct(z, a, i, fv)`. -/
  withStruct : HasClause1 env "with_struct" zaifPat (withAggBody "STRUCTS")
  /-- `$with_array(z, a, i, fv)`. -/
  withArray : HasClause1 env "with_array" zaifPat (withAggBody "ARRAYS")
  /-- `$add_structinst(z, si*)`. -/
  addStruct : HasClause1 env "add_structinst" [.expA (.varE "z"), .expA (iterVar "si" "si*")]
    (addAggBody "STRUCTS" "si" "si*")
  /-- `$add_arrayinst(z, ai*)`. -/
  addArray : HasClause1 env "add_arrayinst" [.expA (.varE "z"), .expA (iterVar "ai" "ai*")]
    (addAggBody "ARRAYS" "ai" "ai*")

set_option maxRecDepth 100000 in
/-- `baseEnv` has the definitions `AggDefs` names. -/
theorem aggDefs_baseEnv : AggDefs baseEnv :=
  ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩,
    ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- So has every `simEnv B`. -/
theorem aggDefs_simEnv (B : Builtins) : AggDefs (simEnv B) :=
  let D := aggDefs_baseEnv
  ⟨D.type_.withBuiltins B, D.structinst.withBuiltins B, D.arrayinst.withBuiltins B,
    D.moduleinst.withBuiltins B, D.withStruct.withBuiltins B, D.withArray.withBuiltins B,
    D.addStruct.withBuiltins B, D.addArray.withBuiltins B⟩

variable {H : Type} {hn : H → String}

/-! ## The state image's fields -/

theorem stateV_eq (s : Store H) (f : Frame) : stateV hn s f = stV (storeV hn s) (frameV f) := rfl

theorem storeV_arrays (s : Store H) :
    (storeV hn s).field? "ARRAYS" = some (.list (s.arrays.map arrayInstV)) := rfl

theorem storeV_structs (s : Store H) :
    (storeV hn s).field? "STRUCTS" = some (.list (s.structs.map structInstV)) := rfl

theorem frameV_module (f : Frame) :
    (frameV f).field? "MODULE" = some (RefsGC.moduleInstToValue' f.module) := rfl

theorem moduleV_types (m : ModuleInst) :
    (RefsGC.moduleInstToValue' m).field? "TYPES" = some (.list (m.types.map CT.defType)) := rfl

/-! ## Evaluation -/

section Eval

variable {env : Env} (D : AggDefs env) (SD : State.StateDefs env) {ρ : VarEnv} {e ex : Exp}
include D

theorem evalExp_structinst (hρ : ρ.findDef? "structinst" = none) {s : Store H} {f : Frame}
    (he : EvalExp env ρ e (stateV hn s f)) :
    EvalExp env ρ (.callE "structinst" [.expA e]) (.list (s.structs.map structInstV)) :=
  State.evalExp_call1 D.structinst hρ (evalArgs_cons he evalArgs_nil) State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, storeV_structs s⟩)

theorem evalExp_arrayinst (hρ : ρ.findDef? "arrayinst" = none) {s : Store H} {f : Frame}
    (he : EvalExp env ρ e (stateV hn s f)) :
    EvalExp env ρ (.callE "arrayinst" [.expA e]) (.list (s.arrays.map arrayInstV)) :=
  State.evalExp_call1 D.arrayinst hρ (evalArgs_cons he evalArgs_nil) State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, storeV_arrays s⟩)

theorem evalExp_moduleinst (hρ : ρ.findDef? "moduleinst" = none) {s : Store H} {f : Frame}
    (he : EvalExp env ρ e (stateV hn s f)) :
    EvalExp env ρ (.callE "moduleinst" [.expA e]) (RefsGC.moduleInstToValue' f.module) :=
  State.evalExp_call1 D.moduleinst hρ (evalArgs_cons he evalArgs_nil) State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, frameV_module f⟩)

include SD in
/-- `$type(z, x)` is the image of `f.type? x`. -/
theorem evalExp_type (hρ : ρ.findDef? "type" = none) {s : Store H} {f : Frame} {x : TypeIdx}
    {d : DefType} (hd : f.type? x = some d) (he : EvalExp env ρ e (stateV hn s f))
    (hx : EvalExp env ρ ex (Encode.toValue x)) :
    EvalExp env ρ (.callE "type" [.expA e, .expA ex]) (CT.defType d) :=
  State.evalExp_call1 D.type_ hρ (evalArgs_cons he (evalArgs_cons hx evalArgs_nil))
    State.matchArgs_zxPat
    (evalExp_idxE_iff.2 ⟨_, x.toNat,
      evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_, State.evalExp_fof SD rfl (evalExp_var rfl),
        frameV_module f⟩, moduleV_types f.module⟩,
      State.evalExp_idxPayload rfl, by simp only [Frame.type?] at hd; simp [Value.idx?, hd]⟩)

end Eval

/-! ## `RStoreFuns`, discharged except for `$inst_reftype` -/

/-- A scope binding term variables only renames no definition. -/
theorem findDef_none {ρ : VarEnv} (hvo : ValsOnly ρ) (x : IL.Id) : ρ.findDef? x = none := by
  rw [VarEnv.findDef?, hvo.2.1]
  rfl

/-- **Family R's `RStoreFuns`, from its `$inst_reftype` field alone**: `$moduleinst`,
`$arrayinst`, `$structinst` and `$elem` are evaluated by their clauses. -/
theorem rStoreFuns_of_instReftype (B : Builtins)
    (hI : ∀ (ρ : VarEnv) (e₁ e₂ : Exp) (m : ModuleInst) (rt : RefType), ValsOnly ρ →
      EvalExp (simEnv B) ρ e₁ (RefsGC.moduleInstToValue' m) →
      EvalExp (simEnv B) ρ e₂ (Encode.toValue rt) →
      EvalExp (simEnv B) ρ (.callE "inst_reftype" [.expA e₁, .expA e₂])
        (CT.elemType (m.instRef rt))) :
    RefsGC.RStoreFuns (simEnv B) where
  moduleinst _ ρ _ _ _ hvo he := evalExp_moduleinst (aggDefs_simEnv B) (findDef_none hvo _) he
  arrayinst _ ρ _ _ _ hvo he := evalExp_arrayinst (aggDefs_simEnv B) (findDef_none hvo _) he
  structinst _ ρ _ _ _ hvo he := evalExp_structinst (aggDefs_simEnv B) (findDef_none hvo _) he
  elem hn ρ _ _ s f y ea ei hvo hy hz hx := by
    obtain ⟨a, ha, hb⟩ : ∃ a, f.module.elems[y.toNat]? = some a ∧ s.elems[a]? = some ei ∧ a = ea := by
      simp only [Store.elem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨a, ha, e, he, rfl, rfl⟩ := hy
      exact ⟨a, ha, he, rfl⟩
    obtain ⟨hb, rfl⟩ := hb
    exact State.evalExp_elem (a := a) (State.stateDefs_simEnv B) (findDef_none hvo _) hz hx rfl rfl rfl
      (by simp [ha]) (by simp [hb])
  instReftype := hI

end Silmaril.Wasm.SpecTec.Sim.Aggregates
