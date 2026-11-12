module

public import Silmaril.Wasm.Unified.Component.Core.Defs
public import Silmaril.Wasm.Resource.Handle.Defs

/-!
# Component Model feature signatures: canonical ABI and resources

Feature sets of the component layer, ordered by inclusion (a thin category, as the core
feature signatures `Silmaril.Wasm.Unified.FSig` are under `FSig.Sub`).

* `CMFeature`: a canonical-ABI adapter kind (`adapter k`: `canon lift`, `canon lower`, a fused
  `canon` or `check`, a core-to-core `flatCheck`; see `Silmaril.Wasm.Component.Adapter`), or a
  **resource type** (`resource d`) given by its declaration `ResDecl`: the import indices of
  its canonical built-ins `resource.new`, `resource.drop` and `resource.rep`.
* `CMSig := Set CMFeature`. Named points: `coreOnly` (no adapters: plain core wiring),
  `flatAbi` (core-to-core canonical ABI: fused `canon` and `flatCheck`), `canonAbi` (every
  adapter), `withRes K ds` (`K` and the resource types `ds`).
* `CProg.Uses K x`: every adapter in the wiring of `x` (nested components included) has its kind
  in `K`. Renaming opcodes does not change wiring (`impls_map`), so uses are preserved.
  Resource types are not read off the syntax (the IR has no resource types; built-ins are
  ordinary imports); they enter through the resource sentences, which may only mention declared
  resource types.
* `resEv d`: the classifier reading moves of a strategy over `sigU` as handle events of the
  resource `d` (`Silmaril.Wasm.Resource.Handle.HEv`, handles are single flat values): the answer
  `[h]` of a call of `new` is `alloc h`, a call of `drop` (resp. `rep`) with `[h]` is `free h`
  (resp. `use h`), anything else is `skip`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Wasm.Component Silmaril.Wasm.Unified Silmaril.Wasm.Resource
open Silmaril.Games (Move)

/-- Kinds of canonical-ABI adapters. -/
inductive AdKind where
  | lift | lower | canon | check | flatCheck
  deriving DecidableEq, Repr

/-- The kind of an adapter. -/
def adKind : Adapter → AdKind
  | .lift _ => .lift
  | .lower _ => .lower
  | .canon _ => .canon
  | .check _ => .check
  | .flatCheck _ _ => .flatCheck

/-- A resource type: the import indices of its canonical built-ins. -/
structure ResDecl where
  /-- `resource.new`: representation to fresh handle. -/
  new : Nat
  /-- `resource.drop`: drop an owned handle. -/
  drop : Nat
  /-- `resource.rep`: the representation of a handle. -/
  rep : Nat
  deriving DecidableEq, Repr

/-- A Component Model feature. -/
inductive CMFeature where
  /-- Canonical-ABI adapters of a kind. -/
  | adapter (k : AdKind)
  /-- A resource type. -/
  | resource (d : ResDecl)
  deriving DecidableEq

/-- Component Model feature signatures, ordered by inclusion. -/
abbrev CMSig : Type := Set CMFeature

/-- No adapters: plain core wiring. -/
def coreOnly : CMSig := ∅

/-- The core-to-core canonical ABI: fused `canon` adapters and flat checks. -/
def flatAbi : CMSig := {.adapter .canon, .adapter .flatCheck}

/-- The whole canonical ABI (every adapter kind). -/
def canonAbi : CMSig := Set.range CMFeature.adapter

/-- A feature signature with the resource types `ds`. -/
def withRes (K : CMSig) (ds : Set ResDecl) : CMSig := K ∪ CMFeature.resource '' ds

theorem coreOnly_le_flatAbi : coreOnly ≤ flatAbi := Set.empty_subset _

theorem flatAbi_le_canonAbi : flatAbi ≤ canonAbi := by
  rintro _ (rfl | rfl)
  · exact ⟨.canon, rfl⟩
  · exact ⟨.flatCheck, rfl⟩

theorem le_withRes (K : CMSig) (ds : Set ResDecl) : K ≤ withRes K ds := Set.subset_union_left

/-! ## Uses of adapters -/

variable {M : Type} {S S' : FSig}

mutual
/-- Every wiring program of a component, nested components included. -/
def compImpls : Comp M → List Impl
  | .mk _ ns xs => nodesImpls ns ++ xs.map Silmaril.Wasm.Component.Export.impl

/-- `compImpls` on nodes. -/
def nodesImpls : List (Node M) → List Impl
  | [] => []
  | n :: ns => nodeImpls n ++ nodesImpls ns

/-- `compImpls` on a node. -/
def nodeImpls : Node M → List Impl
  | .core _ args => args
  | .inst c args => args ++ compImpls c
end

/-- The wiring programs of a program (a core module has none). -/
def CProg.impls : CProg S → List Impl
  | .core _ => []
  | .comp c => compImpls c

/-- `x` uses only adapters of kinds in `K`. -/
def CProg.Uses (K : CMSig) (x : CProg S) : Prop :=
  ∀ im ∈ x.impls, ∀ a ∈ im.chain, CMFeature.adapter (adKind a) ∈ K

theorem CProg.Uses.mono {K K' : CMSig} (h : K ≤ K') {x : CProg S} (hx : x.Uses K) :
    x.Uses K' :=
  fun im him a ha => h (hx im him a ha)

/-- A core module uses no adapters. -/
theorem CProg.uses_core (K : CMSig) (m : UMod S) : (CProg.core m).Uses K :=
  fun _ him => absurd him List.not_mem_nil

mutual
theorem compImpls_map (σ : S ⟶ S') : ∀ c : Comp (UMod S), compImpls (mapComp σ c) = compImpls c
  | .mk I ns xs => by rw [mapComp, compImpls, compImpls, nodesImpls_map σ ns]

theorem nodesImpls_map (σ : S ⟶ S') :
    ∀ ns : List (Node (UMod S)), nodesImpls (mapNodes σ ns) = nodesImpls ns
  | [] => by rw [mapNodes, nodesImpls, nodesImpls]
  | n :: ns => by rw [mapNodes, nodesImpls, nodesImpls, nodeImpls_map σ n, nodesImpls_map σ ns]

theorem nodeImpls_map (σ : S ⟶ S') : ∀ n : Node (UMod S), nodeImpls (mapNode σ n) = nodeImpls n
  | .core m args => by rw [mapNode, nodeImpls, nodeImpls]
  | .inst c args => by rw [mapNode, nodeImpls, nodeImpls, compImpls_map σ c]
end

/-- Renaming opcodes keeps the wiring. -/
theorem impls_map (σ : S ⟶ S') (x : CProg S) : (x.map σ).impls = x.impls := by
  cases x with
  | core m => rfl
  | comp c => exact compImpls_map σ c

theorem CProg.Uses.map {K : CMSig} (σ : S ⟶ S') {x : CProg S} (hx : x.Uses K) :
    (x.map σ).Uses K := by
  unfold CProg.Uses
  rw [impls_map]
  exact hx

/-! ## Resource events -/

/-- Moves of a strategy over `sigU` read as handle events of the resource `d`. -/
def resEv (d : ResDecl) : Move sigU sigU → HEv Flat
  | .inl (.ask (i, .flat [h])) => if i = d.drop then .free h else if i = d.rep then .use h else .skip
  | .inl (.ans (i, _) (some (.flat [h]))) => if i = d.new then .alloc h else .skip
  | _ => .skip

end Silmaril.Wasm.Unified.Component
