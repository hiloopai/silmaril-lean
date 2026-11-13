module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Setup
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Closed

/-!
# The linked module of a setup is a spec instance

`linked_isSpecInstanceAt`: in the scalar fragment, the linked module prepared by the
specification into `base` is a spec instance (`IsSpecInstanceAt S.base [] S.linked mt I X.cl`)
whose instance `I` is the setup's linked instance at the spec store. The export types come from
the well-formedness of the setup's linked instance at the once store (`FnType.ofDefType?` is
the inverse of `FnType.toComp` on expansions, `ofDefType?_of_expand`), transported along the
embedding (function types are unchanged).

The provider and consumer instances of a setup are not spec instances of their modules in this
sense: their exports are the stub set and the linked exports (`Setup.providerI`,
`Setup.consumerI`), not their modules' own exports.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Linking Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC

theorem mapM_ofC?_map (l : List ScalarType) : (l.map ScalarType.toC).mapM ScalarType.ofC? = some l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, List.mapM_cons, ScalarType.ofC?_toC, ih,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- `FnType.ofDefType?` inverts `FnType.toComp` on expansions. -/
theorem ofDefType?_of_expand {d : DefType} {ft : FnType} (h : Expand d ft.toComp) :
    FnType.ofDefType? d = some ft := by
  have he : d.expand? = some ft.toComp := Expand.iff.1 h
  have hf : d.funcType? = some (ft.params.map ScalarType.toC, ft.results.map ScalarType.toC) := by
    simp only [DefType.funcType?, he, FnType.toComp, Ty.toList_ofList]
  simp only [FnType.ofDefType?, hf, mapM_ofC?_map, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

variable {S : Setup}

/-- The export conditions of the linked instance at the spec store. -/
theorem linked_exportTypes (hS : S.Scalar) (X : S.SpecStores) :
    List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, X.cl.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) S.linkedI.addrs S.linkedI.exports := by
  obtain ⟨-, -, ⟨ι, -, he, -, -⟩⟩ := SetupSpec.specStores_emb X
  have hw : S.linkedI.WellFormed S.sl := hS.linked
  refine List.forall₂_iff_get.2 ⟨hw.addrs_length, fun i h₁ h₂ => ?_⟩
  obtain ⟨fi, hfi, hex⟩ := hw.export_type ⟨i, h₂⟩
  have ha : S.linkedI.addr ⟨i, h₂⟩ = S.linkedI.addrs.get ⟨i, h₁⟩ := by
    simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      Option.getD_some, List.get_eq_getElem]
  rw [ha] at hfi
  exact ⟨function ι fi, he.func_lookup hfi, ofDefType?_of_expand hex⟩

/-- **The linked module prepared by the specification is a spec instance** of the setup's
linked instance at the spec store. -/
theorem linked_isSpecInstanceAt (hS : S.Scalar) (X : S.SpecStores) :
    ∃ mt, IsSpecInstanceAt S.base (Preparation.imports []) S.linked mt
      { S.linkedI with store := X.cl.store } X.cl := by
  obtain ⟨mt, hmt⟩ := link?_validate S.link
  have hli : mt.imports = [] := by
    have h := Recipe.validation_imports_length hmt
    rw [S.assembly.output] at h
    exact List.length_eq_zero_iff.mp h
  obtain ⟨-, -, ⟨ι, -, -, hf, -⟩⟩ := SetupSpec.specStores_emb X
  have hx : exportFuncAddrs X.cl.frame.module = S.linkedI.addrs := by
    rw [hf]
    exact exportFuncAddrs_moduleView ι S.fl.module
  refine ⟨mt, ⟨hmt, S.baseOk, by rw [hli]; exact .nil, ?_,
    ⟨X.cl, none, X.linked, rfl, rfl, hx⟩, linked_exportTypes hS X⟩⟩
  intro a fi h hf hc
  obtain ⟨g, hg⟩ := S.baseHostFree fi (List.mem_of_getElem? hf)
  rw [hg] at hc
  cases hc

/-- The closed program of a spec configuration with no code is the one of the once store,
running the start call from the once frame. -/
theorem closedSpec_emb (I : ScalarInstance) (P : Silmaril.Wasm.Numerics.Profile)
    {ι : Nat → Nat} (hinj : Function.Injective ι) {c : Config Nat} {s' : Store Nat} {f' : Frame}
    (he : Emb ι Univ s' c.store) (hframe : c.frame = frame ι f') (hcode : c.code = [])
    (st : Option FuncIdx) (K : Silmaril.Wasm.Game.Env I.E) :
    I.closedSpec P (c.withStart st) K =
      I.closedInstT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) K := by
  have hth := configThread_withStart (s' := s') hframe hcode st
  show I.closedInstT P (c.withStart st).store (configThread (c.withStart st)) K = _
  rw [hth, withStart_store]
  exact (closedInstT_emb I P hinj he _ K).symm

namespace SetupSpec

theorem provider_closedSpec (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile)
    (K : Silmaril.Wasm.Game.Env S.providerI.E) :
    S.providerI.closedSpec P X.cp K =
      S.providerI.closedInstT P S.sp (configThread ⟨S.sp, S.fp, []⟩) K := by
  obtain ⟨⟨ι, hinj, he, hf, hc⟩, -, -⟩ := specStores_emb X
  exact closedSpec_emb S.providerI P hinj he hf hc none K

theorem consumer_closedSpec (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile)
    (K : Silmaril.Wasm.Game.Env S.consumerI.E) :
    S.consumerI.closedSpec P X.ccs K =
      S.consumerI.closedInstT P S.scs (configThread ⟨S.scs, S.fcs, []⟩) K := by
  obtain ⟨-, ⟨ι, hinj, he, hf, hc⟩, -⟩ := specStores_emb X
  exact closedSpec_emb S.consumerI P hinj he hf hc none K

theorem linked_closedSpec (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile)
    (K : Silmaril.Wasm.Game.Env S.linkedI.E) :
    S.linkedI.closedSpec P X.cl K =
      S.linkedI.closedInstT P S.sl (configThread ⟨S.sl, S.fl, []⟩) K := by
  obtain ⟨-, -, ⟨ι, hinj, he, hf, hc⟩⟩ := specStores_emb X
  exact closedSpec_emb S.linkedI P hinj he hf hc none K

theorem linked_closedD (X : S.SpecStores) (P : Silmaril.Wasm.Numerics.Profile)
    (K : Silmaril.Wasm.Game.Env S.linkedI.E) :
    S.linkedI.closedD P X.cl.store K = S.linkedI.closedD P S.sl K := by
  obtain ⟨-, -, ⟨ι, hinj, he, -, -⟩⟩ := specStores_emb X
  exact (closedD_emb S.linkedI P hinj he K).symm

end SetupSpec

end Silmaril.Proofs.Wasm.Game.SpecGlobals

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core

namespace StoreIrrel

variable (I : ScalarInstance) (st : Store Nat)

/-- Transport hidden states to the instance with another recorded store. -/
def toJ : I.HState → ({ I with store := st } : ScalarInstance).HState
  | .idle s => .idle s
  | .running f s t => .running f s t
  | .waiting f s t e => .waiting f s t e

def ofJ : ({ I with store := st } : ScalarInstance).HState → I.HState
  | .idle s => .idle s
  | .running f s t => .running f s t
  | .waiting f s t e => .waiting f s t e

variable {I st} {P : Silmaril.Wasm.Numerics.Profile}

theorem toJ_step {x x' : I.HState} {l : Option (Move I.E I.F)} (h : I.DTrans P x l x') :
    ({ I with store := st } : ScalarInstance).DTrans P (toJ I st x) l (toJ I st x') := by
  cases h with
  | call s f => exact ScalarInstance.DTrans.call (I := ({ I with store := st } : ScalarInstance)) s f
  | tau hi => exact .tau hi
  | ucall callout op => exact .ucall callout op
  | uret v => exact ScalarInstance.DTrans.uret (I := ({ I with store := st } : ScalarInstance)) v
  | oret final answer => exact .oret final answer

theorem ofJ_step {x x' : ({ I with store := st } : ScalarInstance).HState}
    {l : Option (Move I.E I.F)} (h : ({ I with store := st } : ScalarInstance).DTrans P x l x') :
    I.DTrans P (ofJ I st x) l (ofJ I st x') := by
  cases h with
  | call s f => exact ScalarInstance.DTrans.call (I := I) s f
  | tau hi => exact .tau hi
  | ucall callout op => exact .ucall callout op
  | uret v => exact ScalarInstance.DTrans.uret (I := I) v
  | oret final answer => exact .oret final answer

theorem ofJ_toJ (x : I.HState) : ofJ I st (toJ I st x) = x := by cases x <;> rfl

theorem toJ_ofJ (x : ({ I with store := st } : ScalarInstance).HState) :
    toJ I st (ofJ I st x) = x := by cases x <;> rfl

/-- `I` to the instance with another recorded store. -/
def fwd (s : Store Nat) :
    LTS.DivSimulation (I.dlts P s) (({ I with store := st } : ScalarInstance).dlts P s) where
  R x y := y = toJ I st x
  init := rfl
  step hR h := by subst hR; exact ⟨_, LTS.Run.of_step (toJ_step h), rfl⟩
  lt := fun _ _ => False
  wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  tau hR h := by subst hR; exact .inl ⟨_, .single (toJ_step h), rfl⟩

/-- Back. -/
def bwd (s : Store Nat) :
    LTS.DivSimulation (({ I with store := st } : ScalarInstance).dlts P s) (I.dlts P s) where
  R x y := y = ofJ I st x
  init := rfl
  step hR h := by subst hR; exact ⟨_, LTS.Run.of_step (ofJ_step h), rfl⟩
  lt := fun _ _ => False
  wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  tau hR h := by subst hR; exact .inl ⟨_, .single (ofJ_step h), rfl⟩

end StoreIrrel

/-- The strategy from a store does not depend on the instance's recorded store. -/
theorem dstrategy_with_store (I : ScalarInstance) (st : Store Nat)
    (P : Silmaril.Wasm.Numerics.Profile) (s : Store Nat) :
    ({ I with store := st } : ScalarInstance).dstrategy P s = I.dstrategy P s :=
  le_antisymm (StoreIrrel.bwd (I := I) (st := st) s).ofLTS_le
    (StoreIrrel.fwd (I := I) (st := st) s).ofLTS_le

end Silmaril.Proofs.Wasm.Game.SpecGlobals
