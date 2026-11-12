module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Refs

/-!
# Round 5: `Aggregates.AggTypes` on bounded types

Family A's (and track r4-fwd's) aggregate lemmas take `Aggregates.AggTypes`, whose `expand` and
`storagetype` fields quantify over every Core type and are refuted (`RefOk.not_aggTypes'`).
`AggTypesB` restates them with a bound: `expand` for a bounded defined type, `storagetype` for a
bounded storage type. The bound is an **auto-parameter** (`bnd_tac`), discharged at each use from a
local instance `Fact (Round4.ModuleBnd f.module)` and the lemma's own `f.type? x = some d` and
`Expand d ct` premises (`tyBnd_type'`, `tyBnd_arrayZt'`, `tyBnd_structZt'`,
`tyBnd_structFields'`). So the copied aggregate lemmas (`Round5Fwd/Agg*.lean`) keep their proofs
verbatim: only `AggTypes` becomes `AggTypesB` and the signatures gain the instance.

`aggTypesB_of`: `AggTypesB` for the concrete `B`, from `TypesB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV mutV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd ModuleBnd)
open Round4Int (BI)

variable {H : Type}

/-! ## Bounds from a bounded frame module -/

/-- A defined type of a bounded module is bounded. -/
theorem tyBnd_type' {f : Frame} {x : TypeIdx} {d : DefType} (hd : f.type? x = some d)
    [hM : Fact (ModuleBnd f.module)] : tyBnd d = true :=
  hM.out.1 d (List.mem_of_getElem? hd)

/-- The element storage type of an array type of a bounded module is bounded. -/
theorem tyBnd_arrayZt' {f : Frame} {x : TypeIdx} {d : DefType} {m : Mutability}
    {zt : CStorageType} (he : Expand d (.array (.field m zt))) (hd : f.type? x = some d)
    [Fact (ModuleBnd f.module)] : tyBnd zt = true :=
  tyBnd_of_expand (tyBnd_type' hd) he

/-- The fields of a structure type of a bounded module are bounded. -/
theorem tyBnd_structFields' {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    (he : Expand d (.struct fs)) (hd : f.type? x = some d) [Fact (ModuleBnd f.module)] :
    ∀ ft ∈ fs.toList, tyBnd ft = true := by
  have h : tyBnd (Ty.struct fs) = true := tyBnd_of_expand (tyBnd_type' hd) he
  have hfs : tyBnd fs = true := by
    have h' : fs.toList.length < Round4.bnd32 ∧ tyBnd fs = true := by
      simpa only [tyBnd, Bool.and_eq_true, decide_eq_true_eq] using h
    exact h'.2
  exact fun ft hft => tyBnd_of_mem hfs hft

/-- A field storage type of a structure type of a bounded module is bounded. -/
theorem tyBnd_structZt' {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
    {k : Nat} {m : Mutability} {zt : CStorageType} (he : Expand d (.struct fs))
    (hd : f.type? x = some d) (hi : fs.toList[k]? = some (.field m zt))
    [Fact (ModuleBnd f.module)] : tyBnd zt = true :=
  tyBnd_structFields' he hd _ (List.mem_of_getElem? hi)

/-- The bound of a type the aggregate rules quantify over, from the local context. -/
macro "bnd_tac" : tactic => `(tactic| first
  | assumption
  | exact tyBnd_type' (by assumption)
  | exact tyBnd_arrayZt' (by assumption) (by assumption)
  | exact tyBnd_structZt' (by assumption) (by assumption) (by assumption)
  | exact tyBnd_structFields' (by assumption) (by assumption))

/-! ## The restated structure -/

/-- **`Aggregates.AggTypes` on bounded types** (module doc). -/
structure AggTypesB (env : Env) : Prop where
  /-- SpecTec's `Expand` on the images of Core's `Expand`, for a bounded defined type. -/
  expand (d : DefType) (ct : CCompType) (he : Expand d ct)
    (hb : tyBnd d = true := by bnd_tac) :
    DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, tyV ct])
  /-- A bounded storage type is a `storagetype`. -/
  storagetype (zt : CStorageType) (ρ : VarEnv) (hρ : ValsOnly ρ)
    (hb : tyBnd zt = true := by bnd_tac) : HasTyp env ρ Aggregates.storagetypeT (tyV zt)
  /-- An encoded mutability flag is a `mut?`. -/
  mut_ : ∀ m : Mutability, TypedV env Aggregates.mutOptT (mutV m)
  /-- An array instance of a typed store is an `arrayinst`. -/
  arrayOfStore : ∀ {H : Type} (hn : H → String) (s : Store H) (ai : ArrayInst),
    TypedV env storeT (storeV hn s) → ai ∈ s.arrays → TypedV env Aggregates.arrayinstT (arrayInstV ai)
  /-- A struct instance of a typed store is a `structinst`. -/
  structOfStore : ∀ {H : Type} (hn : H → String) (s : Store H) (si : StructInst),
    TypedV env storeT (storeV hn s) → si ∈ s.structs →
    TypedV env Aggregates.structinstT (structInstV si)

/-- The typing of the `zt*` and `mut?*` bindings of a bounded field list
(`Aggregates.typed_fieldLists` on bounded fields). -/
theorem typed_fieldListsB {env : Env} (A : AggTypesB env) (fs : List CFieldType)
    (hb : ∀ ft ∈ fs, tyBnd ft = true := by bnd_tac) :
    TypedV env (.iterT Aggregates.storagetypeT .list)
        (.list (fs.map (tyV ∘ fieldStorage))) ∧
      TypedV env (.iterT Aggregates.mutOptT .list) (.list (fs.map (mutV ∘ Aggregates.fieldMut))) := by
  constructor
  · refine typedV_list_iff.2 fun v hv => ?_
    obtain ⟨ft, hft, rfl⟩ := List.mem_map.1 hv
    cases ft with
    | field m zt => exact fun ρ hρ => A.storagetype zt ρ hρ (hb _ hft)
  · refine typedV_list_iff.2 fun v hv => ?_
    obtain ⟨ft, -, rfl⟩ := List.mem_map.1 hv
    exact A.mut_ _

/-- **`AggTypesB` for the concrete `B`, from `TypesB`.** -/
theorem aggTypesB_of {hn : H → String} {P : Profile} {host : HostSemantics H}
    (TB : TypesB (simEnv (BI P hn host))) : AggTypesB (simEnv (BI P hn host)) where
  expand _ _ he hb := dderives_expandB TB _ hb he
  storagetype zt ρ hρ hb := TB.storagetype zt hb ρ hρ
  mut_ := ConfigOk.typedV_mut
  arrayOfStore hn s ai h hai := ConfigOk.arrayOfStore_simEnv hn s ai h hai
  structOfStore hn s si h hsi := ConfigOk.structOfStore_simEnv hn s si h hsi

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
