module

public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Defs
public import Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Names.Defs
public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.V1.ToCore.Types
public import Silmaril.Wasm.Validation.Types
public import Init.Data.String.Defs
public import Init.Data.Repr
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# `Validation.DefTypes`: laws of the component reference

Theorems of the component reference copy `Validation.DefTypes`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.DefTypes`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)
variable {X : Type}

private theorem typeSlotAt?_eq_ok {Γ : Ctx X} {i : Nat} {s : TypeSlot X} :
    Γ.typeSlotAt? i = .ok s ↔ Γ.types[i]? = some s := Ctx.listAt?_eq_ok

private theorem type?_eq_some {Γ : Ctx X} {i : Nat} {d : TypeDef Nat X} :
    Γ.type? i = some d ↔ ∃ s, Γ.types[i]? = some s ∧ s.def_ = d := by
  simp only [Ctx.type?, Option.map_eq_some_iff]

theorem nameFresh_of_conflict? {names : List String} {n : String}
    (h : conflict? names n = none) : NameFresh names n := by
  intro p hp heq
  have := List.find?_eq_none.mp h p hp
  simp [heq] at this

end Silmaril.Wasm.Component.Validation

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)
variable {X : Type}

theorem moduleDecl?_import_sound {hk : DeclHooks X} {outer : List (Ctx X)} {s s' : CMState X}
    {m n ty} (h : moduleDecl? hk outer s (.import_ m n ty) = .ok s') :
    ModuleDeclStep hk outer s (.import_ m n ty) s' := by
  simp only [moduleDecl?] at h
  split at h
  · cases h
  · next x hx =>
    split at h
    · cases h
    · next hd => cases h; exact .import_ hx hd

theorem moduleDecl?_aliasOuter_sound {hk : DeclHooks X} {outer : List (Ctx X)}
    {s s' : CMState X} {ct idx : Nat} (h : moduleDecl? hk outer s (.aliasOuter ct idx) = .ok s') :
    ModuleDeclStep hk outer s (.aliasOuter ct idx) s' := by
  rcases ct with _ | c
  · simp only [moduleDecl?] at h
    split at h
    · next r ht => cases h; exact .aliasSelf ht
    · cases h
    · cases h
  · simp only [moduleDecl?] at h
    split at h
    · cases h
    · next q hq =>
      split at h
      · next r ht => cases h; exact .aliasOuter hq ht
      · cases h
      · cases h

theorem moduleDecl?_export_sound {hk : DeclHooks X} {outer : List (Ctx X)} {s s' : CMState X}
    {n ty} (h : moduleDecl? hk outer s (.export_ n ty) = .ok s') :
    ModuleDeclStep hk outer s (.export_ n ty) s' := by
  simp only [moduleDecl?] at h
  split at h
  · cases h
  · next x hx =>
    split at h
    · cases h
    · next hd => cases h; exact .export_ hx hd

theorem moduleDecl?_iff {hk : DeclHooks X} {outer : List (Ctx X)} {s s' : CMState X}
    {d : Syntax.CoreModuleDecl} :
    moduleDecl? hk outer s d = .ok s' ↔ ModuleDeclStep hk outer s d s' := by
  constructor
  · intro h
    cases d with
    | import_ m n ty => exact moduleDecl?_import_sound h
    | type r =>
      simp only [moduleDecl?] at h
      split at h
      · cases h
      · next he => cases h; exact .type he
    | aliasOuter ct idx => exact moduleDecl?_aliasOuter_sound h
    | export_ n ty => exact moduleDecl?_export_sound h
  · intro h
    cases h with
    | import_ hty hdup => simp only [moduleDecl?, hty, hdup]
    | type h => simp only [moduleDecl?, h]
    | aliasSelf h => simp only [moduleDecl?, h]
    | aliasOuter hq h => simp only [moduleDecl?, hq, h]
    | export_ hty hdup => simp only [moduleDecl?, hty, hdup]

theorem moduleDecls?_iff {hk : DeclHooks X} {outer : List (Ctx X)} :
    ∀ {s s' : CMState X} {ds : List Syntax.CoreModuleDecl},
      moduleDecls? hk outer s ds = .ok s' ↔ ModuleDeclSteps hk outer s ds s'
  | s, s', [] => by
    simp only [moduleDecls?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .nil s
    · rintro ⟨⟩; rfl
  | s, s', d :: ds => by
    simp only [moduleDecls?]
    constructor
    · intro h
      split at h
      · next s1 h1 => exact .cons (moduleDecl?_iff.mp h1) (moduleDecls?_iff.mp h)
      · cases h
    · rintro (_ | ⟨h1, hs⟩)
      rw [moduleDecl?_iff.mpr h1]
      exact moduleDecls?_iff.mpr hs

/-- Soundness and completeness of `checkCoreModuleType?`. -/
theorem checkCoreModuleType?_iff {hk : DeclHooks X} {outer : List (Ctx X)}
    {ds : List Syntax.CoreModuleDecl} {mt : CoreModuleType X} :
    checkCoreModuleType? hk outer ds = .ok mt ↔ ValidCoreModuleType hk outer ds mt := by
  unfold checkCoreModuleType? ValidCoreModuleType
  constructor
  · intro h
    split at h
    · next s hs => cases h; exact ⟨s, moduleDecls?_iff.mp hs, rfl⟩
    · cases h
  · rintro ⟨s, hs, rfl⟩
    rw [moduleDecls?_iff.mpr hs]

theorem resolveDesc?_func_sound {feat : Features} {Γ : Ctx X} {i : Nat}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.func i) = .ok e) :
    ResolveDesc feat Γ (.func i) e := by
  simp only [resolveDesc?] at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · next t ht => cases h; exact .func (type?_eq_some.mpr ⟨s, typeSlotAt?_eq_ok.mp hs, ht⟩)
    · cases h

theorem resolveDesc?_component_sound {feat : Features} {Γ : Ctx X} {i : Nat}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.component i) = .ok e) :
    ResolveDesc feat Γ (.component i) e := by
  simp only [resolveDesc?] at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · next t ht => cases h; exact .component (type?_eq_some.mpr ⟨s, typeSlotAt?_eq_ok.mp hs, ht⟩)
    · cases h

theorem resolveDesc?_instance_sound {feat : Features} {Γ : Ctx X} {i : Nat}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.instance_ i) = .ok e) :
    ResolveDesc feat Γ (.instance_ i) e := by
  simp only [resolveDesc?] at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · next t ht => cases h; exact .instance_ (type?_eq_some.mpr ⟨s, typeSlotAt?_eq_ok.mp hs, ht⟩)
    · cases h

theorem resolveDesc?_coreModule_sound {feat : Features} {Γ : Ctx X} {c : Nat}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.coreModule c) = .ok e) :
    ResolveDesc feat Γ (.coreModule c) e := by
  simp only [resolveDesc?] at h
  split at h
  · cases h
  · next t ht => cases h; exact .coreModule (Ctx.listAt?_eq_ok.mp ht)
  · cases h

theorem resolveDesc?_typeEq_sound {feat : Features} {Γ : Ctx X} {i : Nat}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.type (.eq i)) = .ok e) :
    ResolveDesc feat Γ (.type (.eq i)) e := by
  simp only [resolveDesc?] at h
  split at h
  · next s hs => cases h; exact .typeEq (type?_eq_some.mpr ⟨s, typeSlotAt?_eq_ok.mp hs, rfl⟩)
  · cases h

theorem resolveDesc?_value_sound {feat : Features} {Γ : Ctx X} {b : Syntax.ValueBound}
    {e : Entity Nat X} (h : resolveDesc? feat Γ (.value b) = .ok e) :
    ResolveDesc feat Γ (.value b) e := by
  simp only [resolveDesc?] at h
  split at h
  · next hf =>
    cases b with
    | eq j =>
      simp only at h
      split at h
      · next p hp =>
        cases h
        exact .valueEq (b := p.2) hf (Ctx.listAt?_eq_ok.mp hp)
      · cases h
    | type vt =>
      simp only at h
      split at h
      · next t ht => cases h; exact .valueType hf (resolveVT?_eq_ok.mp ht)
      · cases h
  · cases h

/-- Soundness of `resolveDesc?`. -/
theorem resolveDesc?_sound {feat : Features} {Γ : Ctx X} {d : Syntax.ExternDesc}
    {e : Entity Nat X} (h : resolveDesc? feat Γ d = .ok e) : ResolveDesc feat Γ d e := by
  cases d with
  | coreModule c => exact resolveDesc?_coreModule_sound h
  | func i => exact resolveDesc?_func_sound h
  | value b => exact resolveDesc?_value_sound h
  | type b =>
    cases b with
    | eq i => exact resolveDesc?_typeEq_sound h
    | subResource => cases h; exact .subResource
  | component i => exact resolveDesc?_component_sound h
  | instance_ i => exact resolveDesc?_instance_sound h

/-- Completeness of `resolveDesc?`. -/
theorem resolveDesc?_complete {feat : Features} {Γ : Ctx X} {d : Syntax.ExternDesc}
    {e : Entity Nat X} (h : ResolveDesc feat Γ d e) : resolveDesc? feat Γ d = .ok e := by
  cases h with
  | coreModule h =>
    simp only [resolveDesc?, Ctx.coreTypeAt?, Ctx.listAt?_eq_ok.mpr h]
  | func h =>
    obtain ⟨s, hs, hd⟩ := type?_eq_some.mp h
    simp only [resolveDesc?, typeSlotAt?_eq_ok.mpr hs, hd]
  | valueEq hf h =>
    simp only [resolveDesc?, hf, Ctx.valueAt?, Ctx.listAt?_eq_ok.mpr h, ite_true]
  | valueType hf h =>
    simp only [resolveDesc?, hf, resolveVT?_eq_ok.mpr h, ite_true]
  | typeEq h =>
    obtain ⟨s, hs, hd⟩ := type?_eq_some.mp h
    simp only [resolveDesc?, typeSlotAt?_eq_ok.mpr hs, hd]
  | subResource => rfl
  | component h =>
    obtain ⟨s, hs, hd⟩ := type?_eq_some.mp h
    simp only [resolveDesc?, typeSlotAt?_eq_ok.mpr hs, hd]
  | instance_ h =>
    obtain ⟨s, hs, hd⟩ := type?_eq_some.mp h
    simp only [resolveDesc?, typeSlotAt?_eq_ok.mpr hs, hd]

/-- Soundness and completeness of `resolveDesc?`. -/
theorem resolveDesc?_iff {feat : Features} {Γ : Ctx X} {d : Syntax.ExternDesc}
    {e : Entity Nat X} : resolveDesc? feat Γ d = .ok e ↔ ResolveDesc feat Γ d e :=
  ⟨resolveDesc?_sound, resolveDesc?_complete⟩

theorem importDecl?_sound {feat : Features} {st st' : DState X} {n : Syntax.ExternName}
    {d : Syntax.ExternDesc} (h : importDecl? feat st n d = .ok st') :
    ValidImportDecl feat st n d st' := by
  unfold importDecl? at h
  split at h
  · next hn =>
    split at h
    · cases h
    · next hc =>
      split at h
      · cases h
      · next e he =>
        split at h
        · next hv =>
          cases h
          exact .mk hn (nameFresh_of_conflict? hc) (resolveDesc?_iff.mp he) hv
        · cases h
  · cases h

theorem exportDecl?_sound {feat : Features} {st st' : DState X} {n : Syntax.ExternName}
    {d : Syntax.ExternDesc} (h : exportDecl? feat st n d = .ok st') :
    ValidExportDecl feat st n d st' := by
  unfold exportDecl? at h
  split at h
  · next hn =>
    split at h
    · cases h
    · next hc =>
      split at h
      · cases h
      · next e he =>
        split at h
        · next hval =>
          simp only at h
          split at h
          · next hv =>
            cases h
            exact .mk hn (nameFresh_of_conflict? hc) (resolveDesc?_iff.mp he) hval hv
          · cases h
        · cases h
  · cases h

theorem aliasDecl?_export_sound {sc : Scopes X} {st st' : DState X} {i : Nat} {n : String}
    {s : Syntax.Sort_} (h : aliasDecl? sc st (.export_ i n s) = .ok st') :
    ValidAlias sc st (.export_ i n s) st' := by
  simp only [aliasDecl?] at h
  split at h
  · next hs =>
    split at h
    · cases h
    · next p hp =>
      split at h
      · next hso =>
        cases h
        refine .export_ ?_ hp hso
        cases s <;> simp_all
      · cases h
  · cases h

theorem aliasDecl?_outerType_sound {sc : Scopes X} {st st' : DState X} {ct idx : Nat}
    (h : aliasDecl? sc st (.outer ct idx .type) = .ok st') :
    ValidAlias sc st (.outer ct idx .type) st' := by
  simp only [aliasDecl?] at h
  split at h
  · cases h
  · next q hq =>
    split at h
    · cases h
    · next slot hslot =>
      split at h
      · cases h
      · next hc =>
        cases h
        refine .outerType hq (Ctx.listAt?_eq_ok.mp hslot) fun hcr => ?_
        simp only [hcr, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at hc
        simpa using hc

theorem aliasDecl?_outerCoreType_sound {sc : Scopes X} {st st' : DState X} {ct idx : Nat}
    (h : aliasDecl? sc st (.outer ct idx (.core .type)) = .ok st') :
    ValidAlias sc st (.outer ct idx (.core .type)) st' := by
  simp only [aliasDecl?] at h
  split at h
  · cases h
  · next q hq =>
    split at h
    · cases h
    · next slot hslot =>
      cases h
      exact .outerCoreType hq (Ctx.listAt?_eq_ok.mp hslot)

theorem aliasDecl?_sound {sc : Scopes X} {st st' : DState X} {a : Syntax.Alias}
    (h : aliasDecl? sc st a = .ok st') : ValidAlias sc st a st' := by
  cases a with
  | export_ i n s => exact aliasDecl?_export_sound h
  | coreExport _ _ _ => cases h
  | outer ct idx s =>
    cases s with
    | type => exact aliasDecl?_outerType_sound h
    | core cs =>
      cases cs with
      | type => exact aliasDecl?_outerCoreType_sound h
      | _ => cases h
    | _ => cases h

/-- Soundness and completeness of `coreTypeDecl?`. -/
theorem coreTypeDecl?_iff {hk : DeclHooks X} {sc : Scopes X} {st st' : DState X}
    {t : Syntax.CoreTypeDef} :
    coreTypeDecl? hk sc st t = .ok st' ↔ ValidCoreTypeDecl hk sc st t st' := by
  constructor
  · intro h
    cases t with
    | rec_ r =>
      simp only [coreTypeDecl?] at h
      split at h
      · cases h
      · next he => cases h; exact .rec_ he
    | module_ ds =>
      simp only [coreTypeDecl?] at h
      split at h
      · next mt hmt => cases h; exact .module_ (checkCoreModuleType?_iff.mp hmt)
      · cases h
  · intro h
    cases h with
    | rec_ h => simp only [coreTypeDecl?, h]
    | module_ h => simp only [coreTypeDecl?, checkCoreModuleType?_iff.mpr h]

theorem coreTypeDecl?_sound {hk : DeclHooks X} {sc : Scopes X} {st st' : DState X}
    {t : Syntax.CoreTypeDef} (h : coreTypeDecl? hk sc st t = .ok st') :
    ValidCoreTypeDecl hk sc st t st' := coreTypeDecl?_iff.mp h

/-- Soundness and completeness of `resourceDef?`. -/
theorem resourceDef?_sound {feat : Features} {hk : DeclHooks X} {st st' : DState X}
    {rep : AddrType} {dtor : Option Nat} (h : resourceDef? feat hk st rep dtor = .ok st') :
    ValidResourceDef feat hk st rep dtor ∧ st' = st.defineResource rep := by
  unfold resourceDef? at h
  split at h
  · next hk1 =>
    split at h
    · next hr =>
      cases dtor with
      | none => cases h; exact ⟨⟨hk1, hr, trivial⟩, rfl⟩
      | some f =>
        simp only at h
        split at h
        · cases h
        · next x hx =>
          split at h
          · next hd => cases h; exact ⟨⟨hk1, hr, x, Ctx.listAt?_eq_ok.mp hx, hd⟩, rfl⟩
          · cases h
    · cases h
  · cases h

theorem resourceDef?_iff {feat : Features} {hk : DeclHooks X} {st st' : DState X}
    {rep : AddrType} {dtor : Option Nat} :
    resourceDef? feat hk st rep dtor = .ok st' ↔
      ValidResourceDef feat hk st rep dtor ∧ st' = st.defineResource rep := by
  refine ⟨resourceDef?_sound, ?_⟩
  rintro ⟨⟨hk1, hr, hd⟩, rfl⟩
  unfold resourceDef?
  simp only [hk1, hr, ite_true]
  cases dtor with
  | none => rfl
  | some f =>
    obtain ⟨x, hx, hdx⟩ := hd
    simp only [Ctx.coreFuncAt?, Ctx.listAt?_eq_ok.mpr hx, hdx, ite_true]

section Soundness

variable {feat : Features} {hk : DeclHooks X}

mutual
  /-- Soundness of `checkDefType?`. -/
  theorem checkDefType?_sound : ∀ (d : Syntax.DefType) {sc : Scopes X} {st st' : DState X},
      checkDefType? feat hk sc st d = .ok st' → ValidDefType feat hk sc st d st'
    | .val d, sc, st, st', h => by
      simp only [checkDefType?] at h
      split at h
      · next t ht => cases h; exact .val (checkDefValType?_sound ht)
      · cases h
    | .func ft, sc, st, st', h => by
      simp only [checkDefType?] at h
      split at h
      · next t ht => cases h; exact .func (checkFuncType?_sound ht)
      · cases h
    | .resource rep dtor, sc, st, st', h => by
      simp only [checkDefType?] at h
      obtain ⟨hv, rfl⟩ := resourceDef?_iff.mp h
      exact .resource hv
    | .instance_ ds, sc, st, st', h => by
      simp only [checkDefType?] at h
      split at h
      · next ch hch => cases h; exact .instance_ (checkInstanceDecls?_sound ds hch)
      · cases h
    | .component ds, sc, st, st', h => by
      simp only [checkDefType?] at h
      split at h
      · next ch hch => cases h; exact .component (checkComponentDecls?_sound ds hch)
      · cases h

  /-- Soundness of `checkInstanceDecl?`. -/
  theorem checkInstanceDecl?_sound : ∀ (d : Syntax.InstanceDecl) {sc : Scopes X}
      {st st' : DState X},
      checkInstanceDecl? feat hk sc st d = .ok st' → ValidInstanceDecl feat hk sc st d st'
    | .coreType _, _, _, _, h => .coreType (coreTypeDecl?_sound h)
    | .type t, _, _, _, h => .type (checkDefType?_sound t h)
    | .alias _, _, _, _, h => .alias (aliasDecl?_sound h)
    | .export_ _ _, _, _, _, h => .export_ (exportDecl?_sound h)

  /-- Soundness of `checkComponentDecl?`. -/
  theorem checkComponentDecl?_sound : ∀ (d : Syntax.ComponentDecl) {sc : Scopes X}
      {st st' : DState X},
      checkComponentDecl? feat hk sc st d = .ok st' → ValidComponentDecl feat hk sc st d st'
    | .import_ _ _, _, _, _, h => .import_ (importDecl?_sound h)
    | .decl d, _, _, _, h => .decl (checkInstanceDecl?_sound d h)

  /-- Soundness of `checkInstanceDecls?`. -/
  theorem checkInstanceDecls?_sound : ∀ (ds : List Syntax.InstanceDecl) {sc : Scopes X}
      {st st' : DState X},
      checkInstanceDecls? feat hk sc st ds = .ok st' → ValidInstanceDecls feat hk sc st ds st'
    | [], sc, st, st', h => by
      simp only [checkInstanceDecls?, Except.ok.injEq] at h
      subst h; exact .nil
    | d :: ds, sc, st, st', h => by
      simp only [checkInstanceDecls?] at h
      split at h
      · next st1 h1 =>
        exact .cons (checkInstanceDecl?_sound d h1) (checkInstanceDecls?_sound ds h)
      · cases h

  /-- Soundness of `checkComponentDecls?`. -/
  theorem checkComponentDecls?_sound : ∀ (ds : List Syntax.ComponentDecl) {sc : Scopes X}
      {st st' : DState X},
      checkComponentDecls? feat hk sc st ds = .ok st' → ValidComponentDecls feat hk sc st ds st'
    | [], sc, st, st', h => by
      simp only [checkComponentDecls?, Except.ok.injEq] at h
      subst h; exact .nil
    | d :: ds, sc, st, st', h => by
      simp only [checkComponentDecls?] at h
      split at h
      · next st1 h1 =>
        exact .cons (checkComponentDecl?_sound d h1) (checkComponentDecls?_sound ds h)
      · cases h
end

end Soundness

end Silmaril.Wasm.Component.Validation
