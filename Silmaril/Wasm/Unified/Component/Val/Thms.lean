module

public import Silmaril.Wasm.Unified.Component.Val.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Thms

/-!
# Canonical-ABI value types as features: the institution `vinst`

* `ValWithin.mono`, `FTyWithin.mono`, `CProg.UsesVals.mono`: value features are monotone;
  `compFTys_map`, `CProg.UsesVals.map`: renaming opcodes keeps the value types.
* `VSen.map`, `vinstitution : VSig ⥤ Room`, `vinst`: translation renames the opcodes of the
  programs and includes the features; **`vsat_map_iff`**: the satisfaction condition (from
  `toC_map`, forgetting value features commutes with translation, and `cinst`'s
  `sat_map_iff`).
* **`fromV : Inst.CoHom vinst cinst`**: forgetting the value features is a comorphism with
  identity model translation, so it is model-expansive (`fromV_modelExpansive`) and consequence
  is borrowed from `cinst` (`fromV_entails_iff`).
* `sat_vals_iff`: including features (value features in particular) keeps satisfaction.
* `valWithin_univ`: every value type is within all features; `toV : Inst.CoHom cinst vinst`
  (`cinst` signatures with every value feature) is a comorphism too, model-expansive, with
  `fromV`-then-`toV` sentences unchanged up to their programs.
* Feature inclusion is strict on programs: `pairComp` (an export taking a pair of `u32`) uses
  `withRecords` but not `scalarVals` (`pairComp_usesVals`, `pairComp_not_scalar`).
* `valWithin_diff_string`: no value type of the flat-only IR needs `string`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas Silmaril.Wasm.Resource
open Silmaril.Wasm.Component Silmaril.Wasm.Unified

/-! ## Monotonicity and renaming -/

theorem ValWithin.mono {V V' : Set ValFeat} (h : V ≤ V') {t : ValTy} (ht : ValWithin V t) :
    ValWithin V' t := by
  induction ht with
  | scalar hs hv => exact .scalar hs (h hv)
  | record hv _ ih => exact .record (h hv) ih
  | variant hv _ ih => exact .variant (h hv) ih

theorem FTyWithin.mono {V V' : Set ValFeat} (h : V ≤ V') {ft : FuncTy} (hf : FTyWithin V ft) :
    FTyWithin V' ft :=
  ⟨fun t ht => (hf.1 t ht).mono h, fun t ht => (hf.2 t ht).mono h⟩

variable {S S' S'' : FSig}

theorem CProg.UsesVals.mono {V V' : Set ValFeat} (h : V ≤ V') {x : CProg S}
    (hx : x.UsesVals V) : x.UsesVals V' :=
  ⟨fun ft hft => (hx.1 ft hft).mono h, fun im him a ha ft hft => (hx.2 im him a ha ft hft).mono h⟩

mutual
theorem compFTys_map (σ : S ⟶ S') : ∀ c : Comp (UMod S), compFTys (mapComp σ c) = compFTys c
  | .mk I ns xs => by rw [mapComp, compFTys, compFTys, nodesFTys_map σ ns]

theorem nodesFTys_map (σ : S ⟶ S') :
    ∀ ns : List (Node (UMod S)), nodesFTys (mapNodes σ ns) = nodesFTys ns
  | [] => by rw [mapNodes, nodesFTys, nodesFTys]
  | n :: ns => by rw [mapNodes, nodesFTys, nodesFTys, nodeFTys_map σ n, nodesFTys_map σ ns]

theorem nodeFTys_map (σ : S ⟶ S') : ∀ n : Node (UMod S), nodeFTys (mapNode σ n) = nodeFTys n
  | .core m args => by rw [mapNode, nodeFTys, nodeFTys]
  | .inst c args => by rw [mapNode, nodeFTys, nodeFTys, compFTys_map σ c]
end

/-- Renaming opcodes keeps the function types. -/
theorem ftys_map (σ : S ⟶ S') (x : CProg S) : (x.map σ).ftys = x.ftys := by
  cases x with
  | core m => rfl
  | comp c => exact compFTys_map σ c

theorem CProg.UsesVals.map {V : Set ValFeat} (σ : S ⟶ S') {x : CProg S} (hx : x.UsesVals V) :
    (x.map σ).UsesVals V := by
  unfold CProg.UsesVals
  rw [ftys_map, impls_map]
  exact hx

/-! ## Translation -/

/-- Translate a program along a signature morphism. -/
def VProgIn.map {T T' : VSig} (f : T ⟶ T') (x : VProgIn T) : VProgIn T' :=
  ⟨x.1.map f.1, (x.2.1.map f.1).mono (XSig.cm_mono (leOfHom f.2)),
    (x.2.2.map f.1).mono (XSig.vals_mono (leOfHom f.2))⟩

/-- Translate a call along a signature morphism. -/
def VCall.map {T T' : VSig} (f : T ⟶ T') (x : VCall T) : VCall T' := (x.1.map f, x.2)

/-- Sentence translation. -/
def VSen.map {T T' : VSig} (f : T ⟶ T') : VSen T → VSen T'
  | .beh φ => .beh (φ.rename (VCall.map f))
  | .res x d hd r => .res (x.map f) d (leOfHom f.2 hd) r
  | .and φ ψ => .and (VSen.map f φ) (VSen.map f ψ)

theorem VProgIn.map_id {T : VSig} (x : VProgIn T) : x.map (𝟙 T) = x :=
  Subtype.ext (CProg.map_id x.1)

theorem VProgIn.map_comp {T T' T'' : VSig} (f : T ⟶ T') (g : T' ⟶ T'') (x : VProgIn T) :
    x.map (f ≫ g) = (x.map f).map g :=
  Subtype.ext (CProg.map_comp f.1 g.1 x.1)

theorem VSen.map_id {T : VSig} (φ : VSen T) : φ.map (𝟙 T) = φ := by
  induction φ with
  | beh φ =>
    have h : VCall.map (𝟙 T) = id := funext fun x => Prod.ext (VProgIn.map_id x.1) rfl
    rw [VSen.map, h, BSen.rename_id]
  | res x d hd r => rw [VSen.map, VProgIn.map_id]
  | and φ ψ ih₁ ih₂ => rw [VSen.map, ih₁, ih₂]

theorem VSen.map_comp {T T' T'' : VSig} (f : T ⟶ T') (g : T' ⟶ T'') (φ : VSen T) :
    φ.map (f ≫ g) = (φ.map f).map g := by
  induction φ with
  | beh φ =>
    have h : VCall.map (f ≫ g) = fun x => VCall.map g (VCall.map f x) :=
      funext fun x => Prod.ext (VProgIn.map_comp f g x.1) rfl
    rw [VSen.map, VSen.map, VSen.map, BSen.rename_rename, h]
  | res x d hd r => rw [VSen.map, VSen.map, VSen.map, VProgIn.map_comp]
  | and φ ψ ih₁ ih₂ => rw [VSen.map, VSen.map, VSen.map, ih₁, ih₂]

/-- Forgetting value features commutes with translation. -/
theorem toC_map {T T' : VSig} (f : T ⟶ T') (φ : VSen T) :
    (φ.map f).toC = φ.toC.map (forgetV.map f) := by
  induction φ with
  | beh φ =>
    rw [VSen.map, VSen.toC, VSen.toC, CSen.map, BSen.rename_rename, BSen.rename_rename]
    rfl
  | res x d hd r => rfl
  | and φ ψ ih₁ ih₂ => rw [VSen.map, VSen.toC, VSen.toC, CSen.map, ih₁, ih₂]

/-- **The satisfaction condition** of `vinst`. -/
theorem vsat_map_iff {T T' : VSig} (f : T ⟶ T') (M : PModel T'.1) (φ : VSen T) :
    VSat M (φ.map f) ↔ VSat (M.reduct f.1) φ := by
  unfold VSat
  rw [toC_map]
  exact sat_map_iff (forgetV.map f) M φ.toC

/-- The room of a signature. -/
def vroom (T : VSig) : Room.{0, 0, 1} := ⟨VSen T, Cat.of (PModel T.1), VSat⟩

/-- The corridor of a signature morphism. -/
def vcorridor {T T' : VSig} (f : T ⟶ T') : vroom T ⟶ vroom T' :=
  ⟨VSen.map f, reductF f.1, fun M φ => vsat_map_iff f M φ⟩

/-- **The component institution with value-type features**, as a functor into rooms. -/
def vinstitution : VSig ⥤ Room.{0, 0, 1} where
  obj := vroom
  map := vcorridor
  map_id _ := Room.hom_ext (funext fun φ => VSen.map_id φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_id M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (funext fun φ => VSen.map_comp f g φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_comp f.1 g.1 M) (fun _ _ _ => rfl))

/-- The component institution with value-type features, bundled. -/
def vinst : Inst.{0, 0, 0, 0, 1} := ⟨VSig, vinstitution⟩

/-! ## Forgetting value features: a comorphism into `cinst` -/

/-- The corridor of `fromV` at a signature. -/
def fromVCorridor (T : VSig) : vinstitution.obj T ⟶ cinstitution.obj (forgetV.obj T) :=
  ⟨VSen.toC, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- **Forgetting value features**: a comorphism `vinst → cinst`. -/
def fromV : Inst.CoHom vinst cinst where
  Φ := forgetV
  ρ :=
    { app := fromVCorridor
      naturality := fun {_ _} f => Room.hom_ext (funext fun φ => toC_map f φ)
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

theorem fromV_modelExpansive : fromV.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- **Borrowing along `fromV`.** -/
theorem fromV_entails_iff (T : VSig) (Γ : Set (VSen T)) (φ : VSen T) :
    (vinstitution.obj T).Entails Γ φ ↔
      (cinstitution.obj (forgetV.obj T)).Entails (VSen.toC '' Γ) φ.toC :=
  fromV.entails_iff fromV_modelExpansive T Γ φ

/-- Including features (value features in particular) keeps satisfaction. -/
theorem sat_vals_iff {S : FSig} {X X' : XSig} (h : X ≤ X') (M : PModel S) (φ : VSen (S, X)) :
    VSat (T := (S, X')) M (φ.map ((𝟙 S, homOfLE h) : (S, X) ⟶ (S, X'))) ↔
      VSat (T := (S, X)) M φ :=
  (vsat_map_iff ((𝟙 S, homOfLE h) : (S, X) ⟶ (S, X')) M φ).trans (by rw [Model.reduct_id])

/-! ## Every value type is within all features: `cinst` into `vinst` -/

/-- Every value type is within all value features. -/
theorem valWithin_univ : ∀ t : ValTy, ValWithin Set.univ t
  | .record fs => .record trivial fun t _ht => valWithin_univ t
  | .variant cs => .variant trivial fun c _hc t _ht => valWithin_univ t
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .s64 | .u64 | .f32 | .f64 | .char =>
    .scalar trivial trivial
decreasing_by
  all_goals simp_wf
  · have h : sizeOf t < sizeOf fs := List.sizeOf_lt_of_mem _ht
    omega
  · have hct : c = some t := _ht
    have h : sizeOf c < sizeOf cs := List.sizeOf_lt_of_mem _hc
    have h' : sizeOf (some t) < sizeOf cs := hct ▸ h
    have hs : sizeOf (some t) = 1 + sizeOf t := rfl
    omega

theorem FTyWithin.of_within {V V' : Set ValFeat} (h : ∀ t, ValWithin V t → ValWithin V' t)
    {ft : FuncTy} (hf : FTyWithin V ft) : FTyWithin V' ft :=
  ⟨fun t ht => h t (hf.1 t ht), fun t ht => h t (hf.2 t ht)⟩

theorem CProg.UsesVals.of_within {V V' : Set ValFeat} (h : ∀ t, ValWithin V t → ValWithin V' t)
    {x : CProg S} (hx : x.UsesVals V) : x.UsesVals V' :=
  ⟨fun ft hft => (hx.1 ft hft).of_within h,
    fun im him a ha ft hft => (hx.2 im him a ha ft hft).of_within h⟩

/-- Every program uses only value types within all features. -/
theorem CProg.usesVals_univ (x : CProg S) : x.UsesVals Set.univ :=
  ⟨fun _ _ => ⟨fun t _ => valWithin_univ t, fun t _ => valWithin_univ t⟩,
    fun _ _ _ _ _ _ => ⟨fun t _ => valWithin_univ t, fun t _ => valWithin_univ t⟩⟩

theorem le_xsig_cm (K : CMSig) (V : Set ValFeat) : K ≤ (xsig K V).cm :=
  fun f hf => Or.inl ⟨f, hf, rfl⟩

theorem xsig_mono {K K' : CMSig} (h : K ≤ K') (V : Set ValFeat) : xsig K V ≤ xsig K' V :=
  Set.union_subset_union_left _ (Set.image_mono h)

/-- `cinst` signatures with every value feature. -/
def toVSig : CSig ⥤ VSig where
  obj T := (T.1, xsig T.2 allVals)
  map f := (f.1, homOfLE (xsig_mono (leOfHom f.2) allVals))

/-- A program of `T` as a program of `toVSig.obj T`. -/
def CProgIn.toV {T : CSig} (x : CProgIn T) : VProgIn (toVSig.obj T) :=
  ⟨x.1, x.2.mono (le_xsig_cm _ _), x.1.usesVals_univ.mono fun v _ => Or.inr ⟨v, trivial, rfl⟩⟩

/-- A call of `T` as a call of `toVSig.obj T`. -/
def CCall.toV {T : CSig} (x : CCall T) : VCall (toVSig.obj T) := (x.1.toV, x.2)

/-- `cinst` sentences as `vinst` sentences. -/
def CSen.toV {T : CSig} : CSen T → VSen (toVSig.obj T)
  | .beh φ => .beh (φ.rename CCall.toV)
  | .res x d hd r => .res x.toV d (le_xsig_cm _ _ hd) r
  | .and φ ψ => .and φ.toV ψ.toV

theorem toV_sat {T : CSig} (M : PModel T.1) (φ : CSen T) :
    VSat (T := toVSig.obj T) M φ.toV ↔ CSat M φ := by
  induction φ with
  | beh φ =>
    show (BSen.rename VCall.toC (φ.rename CCall.toV)).Sat _ ↔ _
    rw [BSen.rename_rename]
    exact BSen.sat_rename _ _ φ
  | res x d hd r => exact Iff.rfl
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem toV_map {T T' : CSig} (f : T ⟶ T') (φ : CSen T) :
    (φ.map f).toV = φ.toV.map (toVSig.map f) := by
  induction φ with
  | beh φ =>
    rw [CSen.map, CSen.toV, CSen.toV, VSen.map, BSen.rename_rename, BSen.rename_rename]
    rfl
  | res x d hd r => rfl
  | and φ ψ ih₁ ih₂ => rw [CSen.map, CSen.toV, CSen.toV, VSen.map, ih₁, ih₂]

/-- The corridor of `toV` at a signature. -/
def toVCorridor (T : CSig) : cinstitution.obj T ⟶ vinstitution.obj (toVSig.obj T) :=
  ⟨CSen.toV, 𝟭 _, fun M φ => toV_sat M φ⟩

/-- **`cinst` into `vinst`**: every value feature, identity on models. -/
def toV : Inst.CoHom cinst vinst where
  Φ := toVSig
  ρ :=
    { app := toVCorridor
      naturality := fun {_ _} f => Room.hom_ext (funext fun φ => toV_map f φ)
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

theorem toV_modelExpansive : toV.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- **Borrowing along `toV`**: `vinst` is a conservative extension of `cinst`. -/
theorem toV_entails_iff (T : CSig) (Γ : Set (CSen T)) (φ : CSen T) :
    (cinstitution.obj T).Entails Γ φ ↔
      (vinstitution.obj (toVSig.obj T)).Entails (CSen.toV '' Γ) φ.toV :=
  toV.entails_iff toV_modelExpansive T Γ φ

/-! ## Inclusion is strict on programs; strings are inert -/

theorem scalarVals_le_withRecords : scalarVals ≤ withRecords := fun _ h => Or.inl h

theorem withRecords_le_withVariants : withRecords ≤ withVariants := by
  rintro _ (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem withVariants_le_allVals : withVariants ≤ allVals := fun _ _ => trivial

/-- A component exporting a function that takes a pair of `u32`s (and traps). -/
def pairComp : Comp (UMod S) := .mk [] [] [⟨"pair", ⟨[.record [.u32, .u32]], []⟩, .trap⟩]

theorem pair_within : ValWithin withRecords (.record [.u32, .u32]) :=
  .record (Or.inr rfl) fun t ht => by
    have h : t = .u32 := by simpa using ht
    exact h ▸ .scalar trivial (Or.inl rfl)

theorem not_within_scalar_record (fs : List ValTy) : ¬ ValWithin scalarVals (.record fs) := by
  intro h
  cases h with
  | scalar ht _ => exact ht
  | record hv _ => exact absurd (hv : ValFeat.record = .scalar) (fun h => nomatch h)

theorem pairComp_ftys : (CProg.comp (pairComp (S := S))).ftys = [⟨[.record [.u32, .u32]], []⟩] :=
  rfl

theorem pairComp_impls : (CProg.comp (pairComp (S := S))).impls = [Impl.trap] := rfl

/-- `pairComp` is a program of every signature with records. -/
theorem pairComp_usesVals : (CProg.comp (pairComp (S := S))).UsesVals withRecords := by
  constructor
  · intro ft hft
    have h : ft = ⟨[.record [.u32, .u32]], []⟩ := List.mem_singleton.1 (pairComp_ftys ▸ hft)
    rw [h]
    exact ⟨fun t ht => (List.mem_singleton.1 ht) ▸ pair_within, fun t ht => absurd ht List.not_mem_nil⟩
  · intro im him a ha
    have h : im = Impl.trap := List.mem_singleton.1 (pairComp_impls ▸ him)
    have ha' : a ∈ (Impl.trap).chain := h ▸ ha
    exact absurd ha' List.not_mem_nil

/-- `pairComp` is not a program of a signature with scalars only. -/
theorem pairComp_not_scalar : ¬ (CProg.comp (pairComp (S := S))).UsesVals scalarVals := fun h =>
  not_within_scalar_record _
    ((h.1 _ (pairComp_ftys ▸ List.mem_singleton_self _)).1 _ (List.mem_singleton_self _))

/-- No value type of the flat-only IR needs `string`. -/
theorem valWithin_diff_string {V : Set ValFeat} {t : ValTy} (ht : ValWithin V t) :
    ValWithin (V \ {.string}) t := by
  induction ht with
  | scalar hs hv => exact .scalar hs ⟨hv, fun h => nomatch (h : ValFeat.scalar = .string)⟩
  | record hv _ ih => exact .record ⟨hv, fun h => nomatch (h : ValFeat.record = .string)⟩ ih
  | variant hv _ ih => exact .variant ⟨hv, fun h => nomatch (h : ValFeat.variant = .string)⟩ ih

/-- Removing (or adding) `string` changes no set of programs. -/
theorem usesVals_diff_string {V : Set ValFeat} (x : CProg S) :
    x.UsesVals (V \ {.string}) ↔ x.UsesVals V :=
  ⟨fun h => h.mono Set.sdiff_subset, fun h => h.of_within fun _ => valWithin_diff_string⟩

end Silmaril.Wasm.Unified.Component
