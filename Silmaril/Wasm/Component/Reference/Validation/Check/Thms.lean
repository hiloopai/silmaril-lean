module

public import Silmaril.Wasm.Component.Reference.Validation.Check.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Builder.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Thms
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Defs.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# `Validation.Check`: laws of the component reference

Theorems of the component reference copy `Validation.Check`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.Check`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)

section Helpers

variable {X : Type}

theorem mapE_ok {α β : Type} {f : α → Option β} {err : α → ValidationError} :
    ∀ {l : List α} {bs : List β}, mapE f err l = .ok bs → l.mapM f = some bs
  | [], bs, h => by cases h; rfl
  | a :: as, bs, h => by
    simp only [mapE] at h
    split at h
    · cases h
    · next b hb =>
      split at h
      · next bs' hbs =>
        cases h
        simp [List.mapM_cons, hb, mapE_ok hbs]
      · cases h

theorem consumeValues?_sound :
    ∀ {Γ : Ctx X} {is : List Nat} {ts : List (Types.ValType Nat)} {Γ' : Ctx X},
      consumeValues? Γ is = .ok (ts, Γ') → ConsumeValues Γ is ts Γ'
  | Γ, [], ts, Γ', h => by cases h; exact .nil Γ
  | Γ, i :: is, ts, Γ', h => by
    simp only [consumeValues?] at h
    split at h
    · cases h
    · cases h
    · next t hv =>
      split at h
      · next ts' Γ'' hr =>
        cases h
        exact .cons hv (consumeValues?_sound hr)
      · cases h

theorem extSub?_sound {P : DefProfile X} {a b : X} (h : extSub? P a b = .ok ()) :
    P.XSub a b := by
  unfold extSub? at h
  split at h
  · assumption
  · cases h

end Helpers

section Leaves

variable {X : Type} {M : Type} {feat : Features} {P : DefProfile X}
  {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}

theorem checkCoreModule?_sound {s s' : DefState X} {m : M}
    (h : checkCoreModule? validCore s m = .ok s') :
    ValidDef feat P validCore sc s (.coreModule m) s' := by
  unfold checkCoreModule? at h
  split at h
  · next mt hm => cases h; exact .coreModule hm
  · cases h

theorem coreImportOk?_sound {Γ : Ctx X} {args : List (String × Nat)}
    {imp : (String × String) × X} (h : coreImportOk? P Γ args imp = .ok ()) :
    ∃ i ex y, args.lookup imp.1.1 = some i ∧ Γ.coreInstance? i = some ex ∧
      ex.lookup imp.1.2 = some y ∧ P.extSub y imp.2 = true := by
  unfold coreImportOk? at h
  split at h
  · cases h
  · next i hi =>
    split at h
    · cases h
    · next ex hex =>
      split at h
      · cases h
      · next y hy =>
        split at h
        · next hs => exact ⟨i, ex, y, hi, hex, hy, hs⟩
        · cases h

theorem forallE_ok {α : Type} {f : α → Except ValidationError Unit} :
    ∀ {l : List α}, forallE f l = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, _, h => nomatch h
  | a :: as, h, b, hb => by
    simp only [forallE] at h
    split at h
    · next hfa =>
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hfa
      · exact forallE_ok h b hb
    · cases h

theorem checkInstanceExports?_sound {s s' : DefState X}
    {items : List (Syntax.ExternName × Syntax.SortIdx Syntax.Sort_)}
    (h : checkInstanceExports? s items = .ok s') :
    ValidDef feat P validCore sc s (.instance_ (.exports items)) s' := by
  unfold checkInstanceExports? at h
  split at h
  · next hv =>
    split at h
    · next hu =>
      split at h
      · cases h
      · next ents he =>
        split at h
        · cases h
        · next ts Γc hc =>
          cases h
          exact .instanceExports hv hu (mapE_ok he) (consumeValues?_sound hc)
    · cases h
  · split at h <;> cases h

theorem checkCanon?_sound {s s' : DefState X} {c : Syntax.Canon}
    (h : checkCanon? feat P s c = .ok s') :
    ValidDef feat P validCore sc s (.canon c) s' := by
  cases c with
  | builtin b =>
    simp only [checkCanon?] at h
    split at h
    · next x Γ' hb => cases h; exact .builtin (checkBuiltin?_sound hb)
    · cases h
  | lift callee opts t =>
    simp only [checkCanon?] at h
    split at h
    · next e he => cases h; exact .canon (checkLiftLower?_sound he)
    · cases h
  | lower f opts =>
    simp only [checkCanon?] at h
    split at h
    · next e he => cases h; exact .canon (checkLiftLower?_sound he)
    · cases h

theorem checkStart?_sound {s s' : DefState X} {f : Nat} {args : List Nat} {results : Nat}
    (h : checkStart? feat s f args results = .ok s') :
    ValidDef feat P validCore sc s (.start f args results) s' := by
  unfold checkStart? at h
  split at h
  · next hf =>
    split at h
    · cases h
    · next ft hft =>
      split at h
      · cases h
      · next ts Γc hc =>
        split at h
        · next ha =>
          split at h
          · next hr =>
            cases h
            exact .start hf (Ctx.listAt?_eq_ok.mp hft) (consumeValues?_sound hc) ha hr
          · cases h
        · cases h
  · cases h

theorem checkValue?_sound {s s' : DefState X} {t : Syntax.VT} {payload : List UInt8}
    (h : checkValue? feat s t = .ok s') :
    ValidDef feat P validCore sc s (.value t payload) s' := by
  unfold checkValue? at h
  split at h
  · next hf =>
    split at h
    · cases h
    · next ty hty =>
      split at h
      · next hok => cases h; exact .value hf (resolveVT?_eq_ok.mp hty) hok
      · cases h
  · cases h

end Leaves

end Silmaril.Wasm.Component.Validation

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)

section Helpers

variable {X : Type}

theorem entSub?_sound {P : DefProfile X} {a b : Entity Nat X} (h : entSub? P a b = .ok ()) :
    Entity.Sub P.XSub a b :=
  Entity.sub?_sound (fun _ _ hx => extSub?_sound hx) h

/-- An `Except` value that is no error is a success. -/
theorem exists_ok_of_ne_error {ε α : Type} {x : Except ε α} (h : ∀ e, x ≠ .error e) :
    ∃ a, x = .ok a := by
  cases x with
  | error e => exact absurd rfl (h e)
  | ok a => exact ⟨a, rfl⟩

end Helpers

section Leaves

variable {X : Type} {M : Type} {feat : Features} {P : DefProfile X}
  {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}

theorem checkCoreInstance?_instantiate_sound {s s' : DefState X} {mod : Nat}
    {args : List (String × Nat)} (h : checkCoreInstance? P s (.instantiate mod args) = .ok s') :
    ValidDef feat P validCore sc s (.coreInstance (.instantiate mod args)) s' := by
  obtain ⟨mt, hmt⟩ : ∃ mt, s.ctx.coreModuleAt? mod = .ok mt :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkCoreInstance?, hx])
  have hn : (args.map (·.1)).Nodup := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkCoreInstance?, hmt, hne])
  have ha : ∀ a ∈ args, a.2 < s.ctx.coreInstances.length := by
    refine Decidable.byContradiction fun hne => absurd h ?_
    simp only [checkCoreInstance?, hmt, ite_eq_left_of_eq_true _ _ (eq_true hn),
      ite_eq_right_of_eq_false _ _ (eq_false hne)]
    split <;> simp
  have hi : forallE (coreImportOk? P s.ctx args) mt.imports = .ok () := by
    cases hx : forallE (coreImportOk? P s.ctx args) mt.imports with
    | error _ => exact absurd h (by
      simp [checkCoreInstance?, hmt, hn, ite_eq_left_of_eq_true _ _ (eq_true ha), hx])
    | ok u => rfl
  have hs' : s.step (s.st.withCtx (s.ctx.pushCoreInstance mt.exports).2) = s' := by
    simpa [checkCoreInstance?, hmt, hn, ite_eq_left_of_eq_true _ _ (eq_true ha), hi] using h
  rw [← hs']
  exact .coreInstantiate (Ctx.listAt?_eq_ok.mp hmt) hn ha
    (fun imp himp => coreImportOk?_sound (forallE_ok hi imp himp))

theorem checkCoreInstance?_exports_sound {s s' : DefState X}
    {items : List (String × Syntax.SortIdx Syntax.CoreSort)}
    (h : checkCoreInstance? P s (.exports items) = .ok s') :
    ValidDef feat P validCore sc s (.coreInstance (.exports items)) s' := by
  have hn : (items.map (·.1)).Nodup := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkCoreInstance?, hne])
  simp only [checkCoreInstance?, ite_eq_left_of_eq_true _ _ (eq_true hn)] at h
  split at h
  · cases h
  · next ex hex =>
    cases h
    exact .coreInstanceExports hn (mapE_ok hex)

theorem checkCoreInstance?_sound {s s' : DefState X} {e : Syntax.CoreInstanceExpr}
    (h : checkCoreInstance? P s e = .ok s') :
    ValidDef feat P validCore sc s (.coreInstance e) s' := by
  cases e with
  | instantiate mod args => exact checkCoreInstance?_instantiate_sound h
  | exports items => exact checkCoreInstance?_exports_sound h

theorem checkInstantiate?_sound {s s' : DefState X} {c : Nat}
    {args : List (String × Syntax.SortIdx Syntax.Sort_)}
    (h : checkInstantiate? P s c args = .ok s') :
    ValidDef feat P validCore sc s (.instance_ (.instantiate c args)) s' := by
  obtain ⟨ct, hct⟩ : ∃ ct, s.ctx.componentAt? c = .ok ct :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkInstantiate?, hx])
  have hn : (args.map (·.1)).Nodup := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkInstantiate?, hct, hne])
  obtain ⟨argEs, hargs⟩ : ∃ argEs, mapE (fun a => (itemEntity? s.ctx a.2).map (a.1, ·))
      (fun a => itemError a.2) args = .ok argEs :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkInstantiate?, hct, hn, hx])
  obtain ⟨rm, hrm⟩ : ∃ rm, openInstanceType? (entSub? P) argEs ct.imported ct.imports
      "import" = .ok rm :=
    exists_ok_of_ne_error fun _ hx =>
      absurd h (by simp [checkInstantiate?, hct, hn, hargs, hx])
  obtain ⟨⟨ts, Γc⟩, hc⟩ : ∃ r, consumeValues? s.ctx (valueIdxs (args.map (·.2))) = .ok r :=
    exists_ok_of_ne_error fun _ hx =>
      absurd h (by simp [checkInstantiate?, hct, hn, hargs, hrm, hx])
  have hs' : s.step ((s.st.withCtx Γc).instantiate ct (rm.apply ct.imported)) = s' := by
    simpa [checkInstantiate?, hct, hn, hargs, hrm, hc] using h
  rw [← hs']
  exact .instantiate (Ctx.listAt?_eq_ok.mp hct) hn (mapE_ok hargs)
    (fun _ hr => Remapping.apply_of_not_mem rm hr)
    (openInstanceType?_sound (fun _ _ hs => entSub?_sound hs) hrm)
    (consumeValues?_sound hc)

/-- An outer alias first resolves its enclosing scope. -/
theorem checkAlias?_outer {s s' : DefState X} {ct idx : Nat} {so : Syntax.Sort_}
    (h : checkAlias? P sc s (.outer ct idx so) = .ok s') :
    ∃ q, Scopes.outer? sc s.ctx ct = .ok q := by
  refine exists_ok_of_ne_error fun _ hx => absurd h ?_
  cases so with
  | core cs => cases cs <;> simp [checkAlias?, hx]
  | _ => simp [checkAlias?, hx]

theorem checkAlias?_export_sound {s s' : DefState X} {i : Nat} {n : String}
    {so : Syntax.Sort_} (h : checkAlias? P sc s (.export_ i n so) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.export_ i n so)) s' := by
  obtain ⟨p, hp⟩ : ∃ p, s.ctx.aliasInstanceExport? i n = .ok p :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hx])
  have hs : exportSortOk s.ctx i n so = true := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkAlias?, hp, hne])
  have hs' : s.step (s.st.withCtx p.2) (aliasReq s.ctx i n) (aliasReq s.ctx i n) = s' := by
    simpa [checkAlias?, hp, hs] using h
  exact hs' ▸ .aliasExport hp hs

theorem checkAlias?_coreExport_sound {s s' : DefState X} {i : Nat} {n : String}
    {so : Syntax.CoreSort} (h : checkAlias? P sc s (.coreExport i n so) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.coreExport i n so)) s' := by
  obtain ⟨ex, hex⟩ : ∃ ex, s.ctx.coreInstanceAt? i = .ok ex :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hx])
  obtain ⟨x, hx⟩ : ∃ x, ex.lookup n = some x := Option.ne_none_iff_exists'.mp fun hx =>
    absurd h (by simp [checkAlias?, hex, hx])
  have hs : P.coreSort x = so := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkAlias?, hex, hx, hne])
  have hs' : s.step (s.st.withCtx (pushCoreItem s.ctx so x)) = s' := by
    simpa [checkAlias?, hex, hx, hs] using h
  exact hs' ▸ .aliasCoreExport (Ctx.listAt?_eq_ok.mp hex) hx hs

theorem checkAlias?_outerType_sound {s s' : DefState X} {ct idx : Nat}
    (h : checkAlias? P sc s (.outer ct idx .type) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.outer ct idx .type)) s' := by
  obtain ⟨q, hq⟩ := checkAlias?_outer h
  obtain ⟨slot, hslot⟩ : ∃ slot, q.typeSlotAt? idx = .ok slot :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hq, hx])
  have hres : crossesComponent sc s.ctx ct = true → slot.def_.fv = [] := fun hcr =>
    Decidable.byContradiction fun hne => absurd h (by simp [checkAlias?, hq, hslot, hcr, hne])
  have hs' : s.step (s.st.withCtx (s.ctx.pushTypeSlot slot).2) = s' := by
    by_cases hcr : crossesComponent sc s.ctx ct = true
    · simpa [checkAlias?, hq, hslot, hcr, hres hcr] using h
    · simpa [checkAlias?, hq, hslot, hcr] using h
  exact hs' ▸ .aliasOuterType hq (Ctx.listAt?_eq_ok.mp hslot) hres

theorem checkAlias?_outerComponent_sound {s s' : DefState X} {ct idx : Nat}
    (h : checkAlias? P sc s (.outer ct idx .component) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.outer ct idx .component)) s' := by
  obtain ⟨q, hq⟩ := checkAlias?_outer h
  obtain ⟨t, ht⟩ : ∃ t, q.componentAt? idx = .ok t :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hq, hx])
  have hs' : s.step (s.st.withCtx (s.ctx.pushComponent t).2) = s' := by
    simpa [checkAlias?, hq, ht] using h
  exact hs' ▸ .aliasOuterComponent hq (Ctx.listAt?_eq_ok.mp ht)

theorem checkAlias?_outerCoreType_sound {s s' : DefState X} {ct idx : Nat}
    (h : checkAlias? P sc s (.outer ct idx (.core .type)) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.outer ct idx (.core .type))) s' := by
  obtain ⟨q, hq⟩ := checkAlias?_outer h
  obtain ⟨slot, hslot⟩ : ∃ slot, q.coreTypeAt? idx = .ok slot :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hq, hx])
  have hs' : s.step (s.st.withCtx (s.ctx.pushCoreType slot).2) = s' := by
    simpa [checkAlias?, hq, hslot] using h
  exact hs' ▸ .aliasOuterCoreType hq (Ctx.listAt?_eq_ok.mp hslot)

theorem checkAlias?_outerCoreModule_sound {s s' : DefState X} {ct idx : Nat}
    (h : checkAlias? P sc s (.outer ct idx (.core .module_)) = .ok s') :
    ValidDef feat P validCore sc s (.alias (.outer ct idx (.core .module_))) s' := by
  obtain ⟨q, hq⟩ := checkAlias?_outer h
  obtain ⟨mt, hm⟩ : ∃ mt, q.coreModuleAt? idx = .ok mt :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkAlias?, hq, hx])
  have hs' : s.step (s.st.withCtx (s.ctx.pushCoreModule mt).2) = s' := by
    simpa [checkAlias?, hq, hm] using h
  exact hs' ▸ .aliasOuterCoreModule hq (Ctx.listAt?_eq_ok.mp hm)

theorem checkAlias?_sound {s s' : DefState X} {a : Syntax.Alias}
    (h : checkAlias? P sc s a = .ok s') :
    ValidDef feat P validCore sc s (.alias a) s' := by
  cases a with
  | export_ i n so => exact checkAlias?_export_sound h
  | coreExport i n so => exact checkAlias?_coreExport_sound h
  | outer ct idx so =>
    cases so with
    | type => exact checkAlias?_outerType_sound h
    | component => exact checkAlias?_outerComponent_sound h
    | core cs =>
      cases cs with
      | type => exact checkAlias?_outerCoreType_sound h
      | module_ => exact checkAlias?_outerCoreModule_sound h
      | _ => exact absurd h (by simp [checkAlias?])
    | _ => exact absurd h (by simp [checkAlias?])

theorem ascribe?_sound {Γ : Ctx X} {e e' : Entity Nat X} {asc : Option Syntax.ExternDesc}
    (h : ascribe? feat P Γ e asc = .ok e') : Ascribe feat P Γ e asc e' := by
  cases asc with
  | none => cases h; exact .none
  | some d =>
    simp only [ascribe?] at h
    split at h
    · next hd =>
      subst hd
      split at h
      · next r => cases h; exact .subResource
      · cases h
    · next hd =>
      split at h
      · cases h
      · next e1 he =>
        split at h
        · next hs => cases h; exact .desc hd (resolveDesc?_iff.mp he) (entSub?_sound hs)
        · cases h

theorem checkExport?_sound {s s' : DefState X} {n : Syntax.ExternName}
    {it : Syntax.SortIdx Syntax.Sort_} {asc : Option Syntax.ExternDesc}
    (h : checkExport? feat P s n it asc = .ok s') :
    ValidDef feat P validCore sc s (.export_ n it asc) s' := by
  have hn : n.valid = true := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkExport?, hne])
  have hc : conflict? (s.ctx.exports.map (·.1)) n.name = none :=
    Option.eq_none_iff_forall_ne_some.mpr fun _ hp => absurd h (by simp [checkExport?, hn, hp])
  obtain ⟨e, he⟩ : ∃ e, itemEntity? s.ctx it = some e := Option.ne_none_iff_exists'.mp fun hx =>
    absurd h (by simp [checkExport?, hn, hc, hx])
  obtain ⟨e', ha⟩ : ∃ e', ascribe? feat P s.ctx e asc = .ok e' :=
    exists_ok_of_ne_error fun _ hx => absurd h (by simp [checkExport?, hn, hc, he, hx])
  have hval : exportValueOk e' = true := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkExport?, hn, hc, he, ha, hne])
  have hvis : (exportReq s it asc).eval (s.ctx.importedTokens ++ s.ctx.exportedTokens) = true :=
    Decidable.byContradiction fun hne =>
      absurd h (by simp [checkExport?, hn, hc, he, ha, hval, hne])
  have hres : resNamed s.ctx e' = true := Decidable.byContradiction fun hne =>
    absurd h (by simp [checkExport?, hn, hc, he, ha, hval, hvis, hne])
  obtain ⟨⟨ts, Γc⟩, hcons⟩ : ∃ r, consumeValues? s.ctx (valueIdxs [it]) = .ok r :=
    exists_ok_of_ne_error fun _ hx =>
      absurd h (by simp [checkExport?, hn, hc, he, ha, hval, hvis, hres, hx])
  have hs' : s.step ((s.st.withCtx Γc).exportItem n.name it e') (exportReq s it asc)
      (exportReq s it asc) = s' := by
    simpa [checkExport?, hn, hc, he, ha, hval, hvis, hres, hcons] using h
  rw [← hs']
  exact .export_ hn (nameFresh_of_conflict? hc) he (ascribe?_sound ha) hval hvis hres
    (consumeValues?_sound hcons)

end Leaves

section Checker

variable {X : Type} {M : Type}
variable {feat : Features} {P : DefProfile X} {validCore : M → Option (CoreModuleType X)}

mutual
  /-- Soundness of `checkDef?` against `ValidDef`. -/
  theorem checkDef?_sound : ∀ (d : Syntax.Definition M) {sc : Scopes X} {s s' : DefState X},
      checkDef? feat P validCore sc s d = .ok s' → ValidDef feat P validCore sc s d s'
    | .coreModule _, _, _, _, h => checkCoreModule?_sound h
    | .coreInstance _, _, _, _, h => checkCoreInstance?_sound h
    | .coreType t, sc, s, s', h => by
      simp only [checkDef?] at h
      split at h
      · next st' hst => cases h; exact .coreType (coreTypeDecl?_sound hst)
      · cases h
    | .component defs, sc, s, s', h => by
      simp only [checkDef?] at h
      split at h
      · cases h
      · next ch hch =>
        split at h
        · next hd => cases h; exact .component (checkDefs?_sound defs hch) hd
        · cases h
    | .instance_ (.instantiate _ _), _, _, _, h => checkInstantiate?_sound h
    | .instance_ (.exports _), _, _, _, h => checkInstanceExports?_sound h
    | .alias _, _, _, _, h => checkAlias?_sound h
    | .type t, sc, s, s', h => by
      simp only [checkDef?] at h
      split at h
      · next st' hst => cases h; exact .type (checkDefType?_sound t hst)
      · cases h
    | .canon _, _, _, _, h => checkCanon?_sound h
    | .start _ _ _, _, _, _, h => checkStart?_sound h
    | .import_ n d, sc, s, s', h => by
      simp only [checkDef?] at h
      split at h
      · next st' hst => cases h; exact .import_ (importDecl?_sound hst)
      · cases h
    | .export_ _ _ _, _, _, _, h => checkExport?_sound h
    | .value _ _, _, _, _, h => checkValue?_sound h

  /-- Soundness of `checkDefs?` against `ValidDefs`. -/
  theorem checkDefs?_sound : ∀ (ds : List (Syntax.Definition M)) {sc : Scopes X}
      {s s' : DefState X},
      checkDefs? feat P validCore sc s ds = .ok s' → ValidDefs feat P validCore sc s ds s'
    | [], _, _, _, h => by cases h; exact .nil
    | d :: ds, sc, s, s', h => by
      simp only [checkDefs?] at h
      split at h
      · next s1 hs1 => exact .cons (checkDef?_sound d hs1) (checkDefs?_sound ds h)
      · cases h
end

/-- **Soundness of the executable validator**: an accepted component is valid with the
returned type. -/
theorem check?_sound {c : Syntax.Component M} {ct : ComponentType Nat X}
    (h : check? feat P validCore c = .ok ct) : ValidComponent feat P validCore c ct := by
  unfold check? at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · next hd => cases h; exact ⟨s, checkDefs?_sound c hs, hd, rfl⟩
    · cases h

end Checker

theorem checkCore3?_valid {feat : Features} {c : Syntax.Component Wasm.Module}
    {ct : ComponentType Nat Core3Extern} (h : checkCore3? feat c = .ok ct) :
    ValidComponent feat core3Profile core3ModuleType? c ct := check?_sound h

/-- Soundness of `checkCore3?` (no hypothesis: every core module is validated by `validate?`,
so it is `ModuleValid`). -/
theorem checkCore3?_sound {feat : Features} {c : Syntax.Component Wasm.Module}
    {ct : ComponentType Nat Core3Extern} (h : checkCore3? feat c = .ok ct) :
    ValidComponentCore3 feat c ct :=
  validComponentCore3_iff.mpr (checkCore3?_valid h)

end Silmaril.Wasm.Component.Validation
