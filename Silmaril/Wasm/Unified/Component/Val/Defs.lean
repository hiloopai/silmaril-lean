module

public import Silmaril.Wasm.Unified.Component.Inst.Defs

/-!
# Canonical-ABI value types as Component Model features

The CM feature signatures of `Silmaril.Wasm.Unified.Component.Feat` constrain the adapters and
resource types of a program, not the value types crossing its interfaces. This module adds the
**value-type features** of the canonical ABI and the institution `vinst` whose signatures also
constrain them.

* `ValFeat`: `scalar` (`bool`, the integers, the floats, `char`), `record` (records and
  tuples), `variant` (variants, enums, options, results) and `string`.
* `ValWithin V t`: the value type `t` uses only features in `V` (nested types included);
  `FTyWithin V ft`: so do the parameters and results of a function type.
* `CProg.ftys x`: the component-level function types of a program: the imports and exports of
  every component (nested ones included); `adFTy a`: the function type of a canonical-ABI
  adapter (`flatCheck` has core types only). `CProg.UsesVals V x`: every one of them, and every
  adapter type of the wiring, uses only value features in `V`.
* `XFeature`: a CM feature (`cm f`, `Silmaril.Wasm.Unified.Component.CMFeature`) or a value feature
  (`val v`); `XSig := Set XFeature`, ordered by inclusion. `X.cm`, `X.vals`: the two parts.
  Named points: `xsig K V`; `scalarVals ⊆ withRecords ⊆ withVariants ⊆ allVals`.
* **The institution** `vinst`: signatures `VSig := FSig × XSig`; programs of `(S, X)` are
  programs over `S` using only adapters in `X.cm` and value types in `X.vals` (`VProgIn`);
  sentences `VSen` (behaviour sentences about calls, client/provider resource sentences of
  resource types declared in `X.cm`, conjunctions); models the unified models `PModel S`.
  Satisfaction is that of `cinst` after forgetting the value-type constraint (`VSen.toC`, into
  the signature `forgetV.obj (S, X) = (S, X.cm)`); the satisfaction condition is proved in
  `Silmaril.Wasm.Unified.Component.Val.Thms`.

**Strings.** The component IR (`Silmaril.Wasm.Component.ValTy`) is flat-only: it has no `string`
or `list` types, which the canonical ABI passes through linear memory (`realloc`). The feature
`string` is a signature feature no value type of this IR uses (`valWithin_diff_string`), so
including it changes no set of programs; it is there so that signatures can name it.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm.Atlas Silmaril.Wasm.Resource Silmaril.Wasm.Component Silmaril.Wasm.Unified

/-- Canonical-ABI value-type features. -/
inductive ValFeat where
  /-- `bool`, the integers, the floats and `char`. -/
  | scalar
  /-- Records and tuples. -/
  | record
  /-- Variants, enums, options and results. -/
  | variant
  /-- Strings (not in the flat-only IR). -/
  | string
  deriving DecidableEq, Repr

/-- A scalar value type. -/
def _root_.Silmaril.Wasm.Component.ValTy.IsScalar : ValTy → Prop
  | .record _ => False
  | .variant _ => False
  | _ => True

/-- The value type uses only the value features in `V`. -/
inductive ValWithin (V : Set ValFeat) : ValTy → Prop
  /-- A scalar type. -/
  | scalar {t : ValTy} (ht : t.IsScalar) (hv : ValFeat.scalar ∈ V) : ValWithin V t
  /-- A record of types within `V`. -/
  | record {fs : List ValTy} (hv : ValFeat.record ∈ V) (hf : ∀ t ∈ fs, ValWithin V t) :
      ValWithin V (.record fs)
  /-- A variant whose payload types are within `V`. -/
  | variant {cs : List (Option ValTy)} (hv : ValFeat.variant ∈ V)
      (hc : ∀ c ∈ cs, ∀ t ∈ c, ValWithin V t) : ValWithin V (.variant cs)

/-- The parameter and result types of a function type use only value features in `V`. -/
def FTyWithin (V : Set ValFeat) (ft : FuncTy) : Prop :=
  (∀ t ∈ ft.params, ValWithin V t) ∧ ∀ t ∈ ft.results, ValWithin V t

/-- The component-level function type of an adapter. -/
def adFTy : Adapter → Option FuncTy
  | .lift ft => some ft
  | .lower ft => some ft
  | .canon ft => some ft
  | .check ft => some ft
  | .flatCheck _ _ => none

variable {M : Type} {S S' : FSig}

mutual
/-- The function types of the imports and exports of a component, nested ones included. -/
def compFTys : Comp M → List FuncTy
  | .mk I ns xs => I.map Prod.snd ++ nodesFTys ns ++ xs.map Silmaril.Wasm.Component.Export.ty

/-- `compFTys` on nodes. -/
def nodesFTys : List (Node M) → List FuncTy
  | [] => []
  | n :: ns => nodeFTys n ++ nodesFTys ns

/-- `compFTys` on a node (a core instance has core types only). -/
def nodeFTys : Node M → List FuncTy
  | .core _ _ => []
  | .inst c _ => compFTys c
end

/-- The component-level function types of a program (a core module has none). -/
def CProg.ftys : CProg S → List FuncTy
  | .core _ => []
  | .comp c => compFTys c

/-- `x` uses only value types with features in `V`, at its interfaces and in its adapters. -/
def CProg.UsesVals (V : Set ValFeat) (x : CProg S) : Prop :=
  (∀ ft ∈ x.ftys, FTyWithin V ft) ∧ ∀ im ∈ x.impls, ∀ a ∈ im.chain, ∀ ft ∈ adFTy a, FTyWithin V ft

/-! ## Extended feature signatures -/

/-- A Component Model feature or a value-type feature. -/
inductive XFeature where
  /-- A feature of `CMSig` (adapter kind or resource type). -/
  | cm (f : CMFeature)
  /-- A value-type feature. -/
  | val (v : ValFeat)

/-- Extended feature signatures, ordered by inclusion. -/
abbrev XSig : Type := Set XFeature

/-- The CM features of an extended signature. -/
def XSig.cm (X : XSig) : CMSig := {f | XFeature.cm f ∈ X}

/-- The value features of an extended signature. -/
def XSig.vals (X : XSig) : Set ValFeat := {v | XFeature.val v ∈ X}

theorem XSig.cm_mono {X X' : XSig} (h : X ≤ X') : X.cm ≤ X'.cm := fun _ hf => h hf

theorem XSig.vals_mono {X X' : XSig} (h : X ≤ X') : X.vals ≤ X'.vals := fun _ hv => h hv

/-- The extended signature with CM features `K` and value features `V`. -/
def xsig (K : CMSig) (V : Set ValFeat) : XSig := XFeature.cm '' K ∪ XFeature.val '' V

/-- Scalars only. -/
def scalarVals : Set ValFeat := {.scalar}

/-- Scalars and records. -/
def withRecords : Set ValFeat := {.scalar, .record}

/-- Scalars, records and variants: every value type of the flat-only IR. -/
def withVariants : Set ValFeat := {.scalar, .record, .variant}

/-- Every value feature, strings included. -/
def allVals : Set ValFeat := Set.univ

/-! ## The institution -/

/-- Signatures: core opcodes and extended features. -/
abbrev VSig : Type := FSig × XSig

/-- Programs of a signature: over its opcodes, with its adapters and value types. -/
abbrev VProgIn (T : VSig) : Type := {x : CProg T.1 // x.Uses T.2.cm ∧ x.UsesVals T.2.vals}

/-- Calls of a signature. -/
abbrev VCall (T : VSig) : Type := VProgIn T × Nat × Payload

/-- Forget the value features: the `cinst` signature. -/
def forgetV : VSig ⥤ CSig where
  obj T := (T.1, T.2.cm)
  map f := (f.1, homOfLE (XSig.cm_mono (leOfHom f.2)))

/-- A program of `T` as a program of `forgetV.obj T`. -/
def VProgIn.toC {T : VSig} (x : VProgIn T) : CProgIn (forgetV.obj T) := ⟨x.1, x.2.1⟩

/-- A call of `T` as a call of `forgetV.obj T`. -/
def VCall.toC {T : VSig} (x : VCall T) : CCall (forgetV.obj T) := (x.1.toC, x.2)

/-- Sentences. -/
inductive VSen (T : VSig) : Type where
  /-- A behaviour sentence about calls. -/
  | beh (φ : BSen (VCall T) (Option Payload))
  /-- The program follows the handle protocol of a declared resource type, in role `r`. -/
  | res (x : VProgIn T) (d : ResDecl) (hd : XFeature.cm (.resource d) ∈ T.2) (r : Role)
  /-- Conjunction. -/
  | and (φ ψ : VSen T)

/-- Forget the value-type constraint of a sentence. -/
def VSen.toC {T : VSig} : VSen T → CSen (forgetV.obj T)
  | .beh φ => .beh (φ.rename VCall.toC)
  | .res x d hd r => .res x.toC d hd r
  | .and φ ψ => .and φ.toC ψ.toC

/-- **Satisfaction**: that of `cinst`. -/
def VSat {T : VSig} (M : PModel T.1) (φ : VSen T) : Prop := CSat M φ.toC

end Silmaril.Wasm.Unified.Component
