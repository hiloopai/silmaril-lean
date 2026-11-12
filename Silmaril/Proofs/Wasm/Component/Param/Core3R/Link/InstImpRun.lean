module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstImpRun` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstImpRun` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3R Pf V IR) σ}
  {inst : InstId} {outer : List (Frame (core3R Pf V IR))} {args : Exports (core3R Pf V IR)}

/-! ## The export definitions, shifted -/

/-- What the frame holds before export `i`: the core instance `es₀` at index `ix`, `base + i`
core functions and `base + 2i` component functions. -/
structure ExpInvAt (es₀ : List (String × (core3R Pf V IR).ExternVal)) (ix base i : Nat)
    (f : Frame (core3R Pf V IR)) : Prop where
  ci : f.coreInstance? ix = some es₀
  cf : f.coreFuncs.length = base + i
  fn : f.funcs.length = base + 2 * i

theorem _root_.Silmaril.Proofs.Wasm.Component.Reference.PureTys.expInvAtR {sc sc' : Scope (core3R Pf V IR)}
    {ds : List (Syntax.Definition (core3R Pf V IR).Module)} {n ix base i : Nat}
    {es₀ : List (String × (core3R Pf V IR).ExternVal)} (h : PureTys R inst outer args sc ds sc' n)
    (hi : ExpInvAt es₀ ix base i sc.frame) : ExpInvAt es₀ ix base i sc'.frame := by
  obtain ⟨-, ⟨new, hf⟩, -⟩ := h
  rw [hf]
  exact ⟨hi.ci, hi.cf, hi.fn⟩

theorem exportDefsAt_eq (names : CoreIface) (ix base i : Nat) (x : SimpleExport) (n : Nat) :
    (SimpleI.exportDefsAt names ix base i x n :
      List (Syntax.Definition (core3R Pf V IR).Module) × Nat) =
      ((emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.1 ++
        (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).1,
                        result := (emitTys (M := (core3R Pf V IR).Module) x.ty.results
                          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport ix (((names[x.core]?).map (·.1)).getD "") .func),
         .canon (.lift (base + i) [] (emitTys (M := (core3R Pf V IR).Module) x.ty.results
           (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, base + 2 * i⟩ none],
        (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.2 + 1) := by
  simp only [SimpleI.exportDefsAt]
  rfl

/-! ## The `canon lower` definitions -/

theorem _root_.Silmaril.Proofs.Wasm.Component.Reference.TRuns.getObjR {Id α : Type} (F : ArenaField (core3R Pf V IR) Id α) (i : Id) {x : α}
    (m : Machine.Config (core3R Pf V IR) σ) (h : F.get? m.store i = some x) :
    TRuns (Canon.getObj F i : P (core3R Pf V IR) σ α) m x m := by
  refine .get ?_
  show TRuns (match F.get? m.store i with
    | some x => Pure.pure x | none => internal "dangling arena id") m x m
  rw [h]
  exact TRuns.pure x m

theorem _root_.Silmaril.Proofs.Wasm.Component.Reference.TRuns.allocCoreHostR (h : CanonHost (core3R Pf V IR)) (m : Machine.Config (core3R Pf V IR) σ) :
    TRuns (Instantiate.allocCoreHost h : P (core3R Pf V IR) σ _) m
      ((core3R Pf V IR).allocHost m.store.core (h.coreType (addrTypesOf m.store)) h).2
      { m with store := allocHostSt (h.coreType (addrTypesOf m.store)) h m.store } :=
  (TRuns.getStore m).bind ((TRuns.modifyStore
    (f := allocHostSt (h.coreType (addrTypesOf m.store)) h) (fun _ => rfl) m).bind
    (TRuns.pure _ _))

/-- `canon lower` of component function `fid` without options allocates its trampoline. -/
theorem lower_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ) {k : Nat}
    {fid : FuncId} {fi : CFuncInst (core3R Pf V IR)} {ty : Silmaril.Wasm.V1.FuncType}
    (hf : sc.frame.funcs[k]? = some fid) (hs : ArenaField.funcs.get? cfg.store fid = some fi)
    (hty : (CanonHost.lowered fid fi.ft {} inst).coreType (addrTypesOf cfg.store) = ty) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lower k []))) cfg
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++
                             [((core3R Pf V IR).allocHost cfg.store.core ty (.lowered fid fi.ft {} inst)).2] } }
      { cfg with store := allocHostSt ty (.lowered fid fi.ft {} inst) cfg.store } := by
  have hr : resolveLower? sc.frame k [] = some (fid, {}) := by
    simp only [resolveLower?, Frame.func?, hf, resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind]
  have ha := TRuns.allocCoreHostR (σ := σ) (CanonHost.lowered fid fi.ft {} inst) cfg
  rw [hty] at ha
  refine (TRuns.getObjR ArenaField.funcs fid cfg hs).bind (ha.bind ?_)
  simp only [pushEntry, Frame.push, need, orTrap, pure_bind]
  exact TRuns.pure _ _

/-- Natural numbers as core function addresses of `core3R Pf V IR`. -/
def addrList (Pf : Silmaril.Wasm.Numerics.Profile) (l : List Nat) : List (core3R Pf V IR).FuncAddr := l

theorem lowers_eq (ims : Iface) :
    (ims.mapIdx fun k _ => (.canon (.lower k []) : Syntax.Definition (core3R Pf V IR).Module)) =
      (List.range' 0 ims.length).map fun j => .canon (.lower j []) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp

/-! ## The core instances -/

/-- `core instance (instantiate 0 (with "env" 0))` of a start-free instantiation. -/
theorem instantiateEnv_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ)
    {m : Silmaril.Wasm.Module} {xas : List (core3R Pf V IR).ExternVal}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hm : sc.frame.coreModules = [m])
    (himp : coreImportsFor? cfg.store.core m [("env", 0)] sc.frame = some xas)
    (hp : (core3R Pf V IR).prepare? cfg.store.core m xas = some (cs, ci, none)) :
    TRuns (instantiateDef R inst outer args sc (.coreInstance (.instantiate 0 [("env", 0)])))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [(core3R Pf V IR).exports ci] } }
      { cfg with store := setCoreSt cs cfg.store } := by
  have hmod : sc.frame.coreModule? 0 = some m := by rw [Frame.coreModule?, hm]; rfl
  have hc : TRuns (instantiateCore inst sc.frame 0 [("env", 0)] : P (core3R Pf V IR) σ _) cfg
      ((core3R Pf V IR).exports ci) { cfg with store := setCoreSt cs cfg.store } := by
    unfold instantiateCore
    rw [hmod]
    refine (TRuns.pure _ cfg).bind ((TRuns.getStore cfg).bind ?_)
    rw [himp]
    refine (TRuns.pure _ cfg).bind ?_
    dsimp only
    rw [hp]
    exact (TRuns.modifyStore (f := setCoreSt cs) (fun _ => rfl) cfg).bind (TRuns.pure _ _)
  exact hc.bind (TRuns.pure _ _)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
