module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.InstCore

/-!
# Core 3.0 engines with a smaller internal step: definitions

`core3R P V I` is the Core 3.0 engine `core3P P` with its validity replaced by `V` and its
internal step replaced by `I`. Every other field (stores, threads, instantiation, memories,
tables, status, resumption) is `core3P P`'s, so the types of the component machine over
`core3R P V I` are built from the same data as over `core3P P`. Two instances matter:

* `core3P P` itself is `core3R P (core3P P).Valid (core3P P).Internal` (definitionally);
* the restriction `restrict (core3P P) r` is `core3R P (fun m => _ ∧ r.Mod m)
  (fun c c' => InternalP P c c' ∧ r.Rt c')` (definitionally).

The reference-machine half `refToSpec_of_arity` was proved for `core3P P` by symbolic execution.
The engine-specific parts of that proof (the instantiation phase `InstRun`/`InstExport`/`InstCore`
and the call phase `CallPath`/`CallRun`, about 1.5k lines) are re-run here over `core3R P V I`
for every `V` and every `I` contained in `InternalP P` (`Sub`). The engine-generic lemmas of
`Silmaril.Proofs.Wasm.Component.Reference` are reused unchanged. This file holds the engine, the
phase statements over it (copied from `Reference.Phases`) and the engine facts of
`Reference.InstCore` (section `Engine`).

Provenance: the definitions and proofs of the `Core3R` modules are copies of
`Silmaril.Proofs.Wasm.Component.Reference.{Phases,InstCore,InstExport,InstRun,CallPath,CallRun,
RefToSpec}` (the `core3P`-specific sections) with `core3P P` replaced by `core3R P V I`; the only
proof changes are where a core step is read as an `InternalP P` step (through `Sub`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- A Core 3.0 store and single-threaded thread at host type `H`. -/
abbrev Cfg3 (H : Type) : Type :=
  Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread

/-- **The Core 3.0 engine at profile `P` with validity `V` and internal step `I`.** -/
noncomputable abbrev core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop) : Engine :=
  { core3P P with Valid := V, Internal := I }

instance core3R_decExternSub (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop) (a b : (core3R P V I).ExternType) :
    Decidable ((core3R P V I).ExternSub a b) :=
  core3P_decExternSub P a b

/-- The internal step `I` is contained in the Core 3.0 step `InternalP P`. -/
def Sub (P : Profile) (I : {H : Type} → Cfg3 H → Cfg3 H → Prop) : Prop :=
  ∀ {H : Type} {x y : Cfg3 H}, I x y → Silmaril.Wasm.Game.InternalP P x y

theorem core3P_eq_core3R (P : Profile) :
    core3P P = core3R P (core3P P).Valid (core3P P).Internal := rfl

theorem sub_core3P (P : Profile) : Sub P (core3P P).Internal := fun h => h

/-- The reference host over `core3R P V I`. -/
noncomputable def refHostR (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop) : Host (core3R P V I) Unit :=
  { hr := fun _ _ => false, impl := Silmaril.Wasm.Component.Canon.HostImpl.none }

/-! ## The two phases (`Reference.Phases`) over `core3R P V I` -/

/-- The lifted functions of the exports of `c`, at the core addresses `addr x.core`. -/
noncomputable def liftedFuncs (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop) (addr : Nat → Nat) (c : Simple) :
    List (CFuncInst (core3R P V I)) :=
  c.exports.map fun x => .lifted (addr x.core) (liftedFt x)
    {} ⟨0⟩

/-- The configuration after instantiation, in host state `h`. -/
noncomputable def afterInstH {σ : Type} (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop)
    (cs : (core3R P V I).Store (CanonHost (core3R P V I)))
    (fs : List (CFuncInst (core3R P V I))) (h : σ) : Machine.Config (core3R P V I) σ :=
  Silmaril.Wasm.Execution.Core.Config.init { core := cs, insts := [{}], funcs := fs } h

/-- The configuration after instantiation, with the host state `()`. -/
noncomputable abbrev afterInst (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (I : {H : Type} → Cfg3 H → Cfg3 H → Prop)
    (cs : (core3R P V I).Store (CanonHost (core3R P V I)))
    (fs : List (CFuncInst (core3R P V I))) : Machine.Config (core3R P V I) Unit :=
  afterInstH P V I cs fs ()


/-- **The instantiation phase** over `core3R P V I` (`Reference.InstPhase`). -/
def InstPhase : Prop :=
  ∀ (P : Profile) (V : Silmaril.Wasm.Module → Prop) (I : {H : Type} → Cfg3 H → Cfg3 H → Prop)
    (prof : ProfileKind) (c : Simple), c.Good → c.Inst →
    ∃ (J : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3R P V I).Store (CanonHost (core3R P V I))),
      c.mod.IsInst J ∧ Store.mapH (fun _ => 0) cs = J.store ∧
      ∀ r ∈ instBehaviours prof (refHostR P V I) (initConfig ()) c.toRef [],
        r = .instance (afterInst P V I cs (liftedFuncs P V I (fun k => J.addrs.getD k 0) c)) ⟨0⟩
          (exportMap c)

/-- **The call phase** over `core3R P V I` (`Reference.CallPhase`), for `I` contained in
`InternalP P`. -/
def CallPhase : Prop :=
  ∀ (P : Profile) (V : Silmaril.Wasm.Module → Prop) (I : {H : Type} → Cfg3 H → Cfg3 H → Prop),
    Sub P I → ∀ (prof : ProfileKind) (c : Simple), c.Good → c.FloatFree → c.Arity →
    ∀ (J : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3R P V I).Store (CanonHost (core3R P V I))),
      c.mod.IsInst J → Store.mapH (fun _ => 0) cs = J.store →
      ∀ (j : Nat) (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
        ValTy.checkList c.exports[j].ty.params vs = true →
        callBehaviours prof (refHostR P V I)
            (afterInst P V I cs (liftedFuncs P V I (fun k => J.addrs.getD k 0) c)) ⟨0⟩ ⟨j⟩
            (vs.map toRefVal) ⊆
          exportSpec P c c.exports[j] vs

/-! ## The engine (`Reference.InstCore`, section `Engine`) -/

section Engine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable (P : Profile) {V : Silmaril.Wasm.Module → Prop} {I : {H : Type} → Cfg3 H → Cfg3 H → Prop}

/-- `prepare?` of `core3R P V I` on an import-free, start-free module. -/
theorem prepare_core3R {m : Module} {mt : Validation.CModuleType}
    {cs : Store (Silmaril.Wasm.Component.Runtime.CanonHost (core3R P V I))} {f' : Frame}
    (hv : Validation.validate? m = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (Silmaril.Wasm.Component.Runtime.CanonHost (core3R P V I))) m [] =
      some (cs, f', none)) :
    (core3R P V I).prepare? ((core3R P V I).empty _) m [] = some (cs, f'.module, none) := by
  show Core3.prepareE? {} m [] = _
  simp only [Core3.prepareE?, hv, hmt, ho, externAddrsOk?, ite_true]
  rfl

/-- `importTypes` of `core3R P V I` on an import-free module. -/
theorem importTypes_core3R {m : Module} {mt : Validation.CModuleType}
    (hv : Validation.validate? m = some mt) (hmt : mt.imports = []) :
    (core3R P V I).importTypes m = [] := by
  show Core3.importTypesE m = []
  unfold Core3.importTypesE
  split
  next mt' hv' =>
    have he : mt' = mt := Option.some.inj (hv'.symm.trans hv)
    subst he
    simp only [hmt, List.attachWith_nil, List.zip_nil_right, List.map_nil]
  next hv' => rfl

/-- The exports of a core instance of `core3R P V I`. -/
theorem exports_core3R (mi : ModuleInst) :
    (core3R P V I).exports mi = mi.exports.map fun x => (x.name, x.addr) := rfl

end Engine

end Silmaril.Proofs.Wasm.Component.Param.Core3R
