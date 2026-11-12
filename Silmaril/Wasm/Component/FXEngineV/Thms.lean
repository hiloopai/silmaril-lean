module

public import Silmaril.Wasm.Component.FXEngineV.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms
public import Silmaril.Wasm.Component.FXExample.Thms
import Silmaril.Proofs.Wasm.Component.FXEngineV.Lawful
import Silmaril.Proofs.Wasm.Component.FXEngineV.Vals
import Silmaril.Proofs.Wasm.Component.FXEngineV.Incl

/-!
# A WasmFX component engine whose code can suspend: laws and game engine

* **`fxEV_lawful P : (fxEV P).Lawful`**: the engine with `StepFX'`, `CtxV` parking and FX
  functions in the function index space satisfies the engine laws (the argument of
  `fxE_lawful`, `Silmaril.Proofs.Wasm.Component.FXEngineV.Lawful`).
* **`fxXGV P : GameEngine`**: its game engine over IR modules carrying FX functions
  (`FXNumModule`, as `fxXG P`).
* `statusV_vals`: an FX thread at Core values has returned them (as in `fxE P`).
* **`fxXG_le_fxXGV`**: on a module without FX functions, every play of `fxXG P` is a play of
  `fxXGV P`; with `fxXG_noFX`, **`core3G_le_fxXGV`**: every Core 3.0 play of a numeric module is
  a play of the engine with suspension. The engine-level fact is a simulation on the same
  instance (`Silmaril.Proofs.Wasm.Component.FXEngineV.Incl`), and holds for every instance; only
  the instantiation of FX functions differs between the engines. The converse is not proved
  (it needs that a store without FX functions keeps every thread a Core thread).
* `prepareFXV?_noFX`: on a module without FX functions, instantiation is that of `fxE P`.
* `fxEV_suspend`: `suspend` under a handler with clause `(on x l)` is an internal step, and,
  unlike in `fxE P`, the branch that follows carries the continuation out of the handler
  (`fxEV_suspend_br`).

That the code of a module can actually suspend inside a play is
`Silmaril.Wasm.Component.FXSuspend.fxXGV_suspend_play`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXEngineV

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Proofs.Wasm.Component.FXEngineV
open Silmaril.Wasm.Numerics (Profile)

/-- **The WasmFX engine with suspension is lawful.** -/
instance fxEV_lawful (P : Profile) : (fxEV P).Lawful where
  flatType?_ofFlatType := (L₀).flatType?_ofFlatType
  returned_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusV P _ _ = _ from h).symm.trans e) _
  callout_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusV P _ _ = _ from h).symm.trans e) _
  stuck_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusV P _ _ = _ from h).symm.trans e) _
  externSub_refl := (L₀).externSub_refl
  externSub_trans := (L₀).externSub_trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := Grows.extendsV (internalV_grows h)
  prepare_extends h := Grows.extendsV (prepareFXV?_grows h)
  allocHost_extends h :=
    Grows.extendsV (Silmaril.Wasm.Component.Engine.Core3.allocHost_grows h)
  allocHost_fresh h := (L₀).allocHost_fresh h
  allocHost_frame h := (L₀).allocHost_frame h
  allocHost_funcType h := (L₀).allocHost_funcType h
  allocHost_callout h hn := statusV_allocHost_callout h hn
  memWrite_extends h :=
    Grows.extendsV (Silmaril.Wasm.Component.Engine.Core3.memWrite?_grows h)
  memWrite_memSize h := (L₀).memWrite_memSize h
  memWrite_memAddrType h := (L₀).memWrite_memAddrType h
  memWrite_read h := (L₀).memWrite_read h
  memWrite_read_other h := (L₀).memWrite_read_other h
  memRead_isSome_iff := (L₀).memRead_isSome_iff
  memRead_size h := (L₀).memRead_size h
  memWrite_isSome_iff := (L₀).memWrite_isSome_iff
  memAddrType_isSome_iff := (L₀).memAddrType_isSome_iff

/-- **The WasmFX game engine with suspension** over IR modules with FX functions. -/
noncomputable def fxXGV (P : Profile) : GameEngine where
  E := fxEV P
  lawful := fxEV_lawful P
  abi := AbiLawful.ofLawful _
  M := FXNumModule
  core := inferInstance
  emb := FXNumModule.mod

/-- The FX instance of an instance with no FX functions to add is the instance itself. -/
theorem fxInst_zero (i : Silmaril.Wasm.Execution.Core.ModuleInst) (n : Nat) :
    fxInst i n 0 = i := by
  simp [fxInst]

/-- **On a module without FX functions, instantiation is that of `fxE P`.** -/
theorem prepareFXV?_noFX {H : Type} (s : Silmaril.Wasm.Execution.Core.Store (FXCode H))
    (m : Silmaril.Wasm.Module)
    (xas : List Silmaril.Wasm.Execution.Core.ExternAddr) :
    prepareFXV? s ⟨m, []⟩ xas = prepareFX? s ⟨m, []⟩ xas := by
  unfold prepareFXV? prepareFX?
  rfl

open Silmaril.Wasm.Models.FX in
open Silmaril.Wasm.Models.FXV in
/-- **`suspend` is an internal step**: an FX thread whose handler has clause `(on x l)` around
`suspend x` captures the empty context as a new continuation and branches to `l` with it. -/
theorem fxEV_suspend (P : Profile) {H : Type} {s : Silmaril.Wasm.Execution.Core.Store (FXCode H)}
    {K : List (Option ContFX)} {f : Silmaril.Wasm.Execution.Core.Frame}
    {x : Silmaril.Wasm.TagIdx} {ta : Nat} {ti : Silmaril.Wasm.Execution.Core.TagInst}
    {l : Silmaril.Wasm.LabelIdx} (ht : s.tag? f x = some (ta, ti)) :
    (fxEV P).Internal (s, ThreadV.fx K f [.handler [.onLabel ta l] [.fx (.suspend x)]])
      (s, ThreadV.fx (K ++ [some ⟨CtxV.hole.plug⟩]) f
        [.contRef K.length, .core (.plain (.br l))]) :=
  Or.inl ⟨_, _, _, rfl, StepFX'.suspend (E := .hole) (vs := []) ht (by simp [CtxV.Handles])
    (by simp [HClause.tag])⟩

open Silmaril.Wasm.Models.FX in
open Silmaril.Wasm.Models.FXV in
/-- **The branch after a suspension carries the continuation**: a label of arity one around a
continuation reference and `br 0` steps to the continuation reference (in `fxE P` this
configuration is stuck: `suspend_to_label_stuck`). -/
theorem fxEV_suspend_br (P : Profile) {H : Type}
    {s : Silmaril.Wasm.Execution.Core.Store (FXCode H)} {K : List (Option ContFX)}
    {f : Silmaril.Wasm.Execution.Core.Frame} {k : List InstrFX} {j : Nat}
    {rest : List AdminFX} :
    (fxEV P).Internal (s, ThreadV.fx K f [.label 1 k ([.contRef j, .core (.plain (.br ⟨0⟩))] ++
        rest)])
      (s, ThreadV.fx K f (.contRef j :: k.map InstrFX.toAdmin)) :=
  Or.inl ⟨_, _, _, rfl, StepFX'.brLabelZero (vs' := []) (vs := [.cont j]) (by rfl) rfl⟩

/-- **An FX thread at values has returned them**: it takes no internal step, and its status is
that of `fxE P` (`statusFX_vals`). -/
theorem statusV_vals (P : Profile) {H : Type} (s : Silmaril.Wasm.Execution.Core.Store (FXCode H))
    (K : List (Option Silmaril.Wasm.Models.FX.ContFX)) (f : Silmaril.Wasm.Execution.Core.Frame)
    (vs : List Silmaril.Wasm.Execution.Core.Val) :
    statusV P s (.fx K f (Silmaril.Wasm.Models.FX.cvals vs)) =
      match vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | some fvs => .returned (.values fvs)
      | none => .stuck :=
  Silmaril.Proofs.Wasm.Component.FXEngineV.statusV_vals' s K f vs

/-- The host functions of the imports are allocated alike by the two engines. -/
theorem allocHosts_eq (P : Profile) :
    ∀ (s : Silmaril.Wasm.Execution.Core.Store (FXCode Nat)) (i : Nat) (imps : CoreIface),
      allocHosts (fxEV P) s i imps = allocHosts (fxE P) s i imps
  | _, _, [] => rfl
  | s, i, _ :: imps => by
    simp only [allocHosts]
    erw [allocHosts_eq P _ (i + 1) imps]
    rfl

/-- **On a module without FX functions, the two engines have the same instance.** -/
theorem instOf_noFX (P : Profile) (c : Silmaril.Wasm.Module) (imps exps : CoreIface) :
    instOf (fxEV P) ⟨c, []⟩ imps exps =
      (instOf (fxE P) ⟨c, []⟩ imps exps).map fun I => ⟨I.store, I.addrs⟩ := by
  unfold instOf
  rw [show allocHosts (fxEV P) ((fxEV P).empty Nat) 0 imps =
    allocHosts (fxE P) ((fxE P).empty Nat) 0 imps from allocHosts_eq P {} 0 imps]
  rcases allocHosts (fxE P) ((fxE P).empty Nat) 0 imps with ⟨s, as⟩
  dsimp only
  rw [show (fxEV P).prepare? s ⟨c, []⟩ (as.map (fxEV P).ofFunc) =
      prepareFX? s ⟨c, []⟩ (as.map .func) from prepareFXV?_noFX _ _ _]
  rw [show (fxE P).prepare? s ⟨c, []⟩ (as.map (fxE P).ofFunc) =
      prepareFX? s ⟨c, []⟩ (as.map .func) from rfl]
  rcases prepareFX? s ⟨c, []⟩ (as.map .func) with _ | ⟨s', inst, _ | st⟩
  · rfl
  · show Option.map _ (exportAddrs (fxEV P) inst exps) =
      Option.map _ (Option.map _ (exportAddrs (fxE P) inst exps))
    rw [Option.map_map]
    rfl
  · rfl

/-- The game semantics over the two engines, on a module with the same instances. -/
theorem engineSem_le (P : Profile) {M : Type} [CoreModule M] (emb : M → ModuleFX) (m : M)
    (hI : ∀ imps exps, instOf (fxEV P) (emb m) imps exps =
      (instOf (fxE P) (emb m) imps exps).map fun I => ⟨I.store, I.addrs⟩) :
    (engineSem (fxE P) M emb).sem m ≤ (engineSem (fxEV P) M emb).sem m := by
  unfold engineSem
  dsimp only
  rw [hI]
  split
  next I hE =>
    rw [hE]
    exact Silmaril.Proofs.Wasm.Component.FXEngineV.engineStrategy_le I _ _
  next hE =>
    rw [hE]
    exact le_rfl

/-- **On a module without FX functions, every play of `fxXG P` is a play of `fxXGV P`.** -/
theorem fxXG_le_fxXGV (P : Profile) (c : Silmaril.Wasm.Module) (exps : CoreIface) :
    (fxXG P).sem.sem ⟨⟨c, []⟩, exps⟩ ≤ (fxXGV P).sem.sem ⟨⟨c, []⟩, exps⟩ :=
  engineSem_le P (M := FXNumModule) FXNumModule.mod ⟨⟨c, []⟩, exps⟩ (instOf_noFX P c)

/-- **Every Core 3.0 play of a numeric module is a play of the engine with suspension.** -/
theorem core3G_le_fxXGV (P : Profile) (m : NumModule) :
    (core3G P).sem.sem m ≤ (fxXGV P).sem.sem ⟨ofNum m, m.exports⟩ :=
  (Silmaril.Wasm.Component.FXExample.fxXG_noFX P m).symm.le.trans (fxXG_le_fxXGV P m.mod m.exports)

end Silmaril.Wasm.Component.FXEngineV
