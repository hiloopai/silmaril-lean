module

public import Silmaril.Proofs.Wasm.Component.Reference.InstCore
public import Silmaril.Proofs.Wasm.Component.Reference.CoreRun
public import Silmaril.Wasm.Component.Lime1Ref.Defs

/-!
# The engine-run half over Core 3.0

Proofs for `Silmaril.Wasm.Component.FXRef.Thms`.

* `instOf_core3P_inst`: for a component whose module is instantiated as the IR assumes
  (`Simple.Inst`), the `core3P P` engine instance of its module (`instOf`, empty store, exports
  by name) is the `IsInst` instance `I` up to the host type, and export `k` is the function
  `I.addrs.getD k 0` (the names of `Simple.Inst` and the core lookup `lookup_funcExport`);
* `specSub_core3P`: **the engine-run half for Core 3.0**: `exportSpecE (core3P P)
  NumModule.mod c x vs ⊆ exportSpec P c x vs` for every `Simple.Inst` component. A returned,
  trapping or diverging engine run of the export is a Core run of the `IsInst` instance
  (`coreRun_values`, `coreRun_trap`, `coreRun_diverges`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Lime1Ref (SpecSubOn)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- The entry of a list related pointwise to an entry of the other list. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → ∀ {k : Nat} {b : β}, r[k]? = some b →
      ∃ a, l[k]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | a :: _, _, .cons hab _, 0, _, h => ⟨a, rfl, (Option.some.inj h) ▸ hab⟩
  | _ :: _, _ :: _, .cons _ hr, k + 1, _, h => forall₂_getElem? hr h

/-- `prepare?` of `core3P P` on an import-free, start-free module, in a store over `Nat`. -/
theorem prepare_core3P_nat {m : Module} {mt : Validation.CModuleType} {cs : Store Nat}
    {f' : Frame} (hv : Validation.validate? m = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store Nat) m [] = some (cs, f', none)) :
    (core3P P).prepare? ((core3P P).empty Nat) m [] = some (cs, f'.module, none) := by
  show Silmaril.Wasm.Component.Engine.Core3.prepareE? {} m [] = _
  simp only [Silmaril.Wasm.Component.Engine.Core3.prepareE?, hv, hmt, ho, externAddrsOk?,
    ite_true]
  rfl

/-- **The `core3P P` instance of a `Simple.Inst` module is its `IsInst` instance**, up to the
host type, with export `k` at `I.addrs.getD k 0`. -/
theorem instOf_core3P_inst {c : Simple} (hi : c.Inst) {J : EInstance (core3P P)}
    (hJ : instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some J) :
    ∃ I : Silmaril.Wasm.Game.ScalarInstance, c.mod.IsInst I ∧
      Store.mapH (fun _ => (0 : Nat)) J.store = I.store ∧
      ∀ k a, J.addrs[k]? = some a → a = I.addrs.getD k 0 := by
  obtain ⟨I, mt, cs, f', hI, hv, hmt, ho, hs, ha⟩ := inst_once (H := Nat) (fun _ => 0) hi
  have hp := prepare_core3P_nat (P := P) hv hmt ho
  have he : instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      (exportAddrs (core3P P) f'.module c.mod.exports).map fun addrs => ⟨cs, addrs⟩ := by
    show instOf (core3P P) c.mod.mod [] c.mod.exports = _
    unfold instOf
    simp only [allocHosts, List.map_nil]
    rw [hp]
  rw [he] at hJ
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 hJ
  refine ⟨I, hI, hs, fun k a hk => ?_⟩
  obtain ⟨⟨n, ft⟩, hx, hfa⟩ := forall₂_getElem? (mapM_forall₂ hL) hk
  have hlk := lookup_funcExport hi hv ho ha hx
  rw [← exports_core3P P] at hlk
  exact (Option.some.inj
    ((congrArg (fun o => Option.bind o (core3P P).asFunc?) hlk).symm.trans hfa)).symm

/-- An engine outcome of an export call of the `core3P P` instance is a `coreOut` outcome. -/
theorem engineOut_coreOut {c : Simple} (hi : c.Inst) {J : EInstance (core3P P)}
    (hJ : instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some J) {k : Nat} {xs : List Flat} {r : Option (List Flat)}
    (hr : r ∈ engineOut (core3P P) J k xs) : r ∈ coreOut P c.mod k xs := by
  obtain ⟨a, s', t', hk, hrun, hst⟩ := hr
  obtain ⟨I, hI, hs, haddr⟩ := instOf_core3P_inst hi hJ
  have ha : a = I.addrs.getD k 0 := haddr _ _ hk
  have hinv : invoke (Store.mapH (fun _ => (0 : Nat)) J.store) a (xs.map SingleThreaded.ofFlat) =
      invoke I.store (I.addrs.getD k 0) (xs.map SingleThreaded.ofFlat) := by rw [hs, ha]
  rcases hst with ⟨ys, hys, rfl⟩ | ⟨htr, rfl⟩
  · obtain ⟨c', res, run, hc, hm⟩ := coreRun_values (fun _ => (0 : Nat)) hrun hys
    exact ⟨I, hI, c', res, hinv ▸ run, hc, hm.symm⟩
  · obtain ⟨c', res, run, hc, hm⟩ := coreRun_trap (fun _ => (0 : Nat)) hrun htr
    exact ⟨I, hI, c', res, hinv ▸ run, hc, hm.symm⟩

/-- A divergence of an export call of the `core3P P` instance is a `coreDiverges` divergence. -/
theorem engineDiverges_coreDiverges {c : Simple} (hi : c.Inst) {J : EInstance (core3P P)}
    (hJ : instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some J) {k : Nat} {xs : List Flat} (hd : engineDiverges (core3P P) J k xs) :
    coreDiverges P c.mod k xs := by
  obtain ⟨a, hk, hd⟩ := hd
  obtain ⟨I, hI, hs, haddr⟩ := instOf_core3P_inst hi hJ
  have ha : a = I.addrs.getD k 0 := haddr _ _ hk
  have hd' : Diverges P (noHostH Nat)
      (invoke (Store.mapH (fun _ => (0 : Nat)) J.store) a (xs.map SingleThreaded.ofFlat)) :=
    coreRun_diverges (P := P) (fun _ => (0 : Nat)) hd
  rw [hs, ha] at hd'
  exact ⟨I, hI, hd'⟩

/-- **The engine-run half for Core 3.0**: for a `Simple.Inst` component, the canonical-ABI
specification over `core3P P` is contained in the Core 3.0 specification `exportSpec P`. -/
theorem specSub_core3P : SpecSubOn (core3P P) NumModule.mod P fun _ => True := by
  intro c _ _ hi x _ vs
  unfold exportSpecE exportSpec
  cases checkLower x.ty.params vs with
  | none => exact fun _ h => h
  | some xs =>
    rintro b (⟨J, hJ, r, hr, rfl⟩ | ⟨rfl, J, hJ, hd⟩)
    · exact Or.inl ⟨r, engineOut_coreOut hi hJ hr, rfl⟩
    · exact Or.inr ⟨rfl, engineDiverges_coreDiverges hi hJ hd⟩

end Silmaril.Proofs.Wasm.Component.FXRef
