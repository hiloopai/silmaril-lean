module

public import Silmaril.Wasm.Component.FXEngine.Defs
public import Silmaril.Wasm.Component.Lime1G.Thms
import Silmaril.Proofs.Wasm.Component.FXEngine.Lawful
import Silmaril.Proofs.Wasm.Component.FXEngine.Sim
import Silmaril.Proofs.Wasm.Component.FXEngine.Spec
public import Silmaril.Wasm.Component.Reference.Sound.Thms

/-!
# A component engine over WasmFX: laws, game engines, and the shared construction

* **`fxE_lawful P : (fxE P).Lawful`**: the WasmFX engine satisfies the engine laws of
  `CoreEngine.Lawful`. Internal steps (Core steps, `StepFX` steps, parking) grow the store;
  growth is store extension, because callouts of Core threads persist (the Core 3.0 argument)
  and parked threads are callouts whatever the store; a thread whose status is not `running`
  takes no step; an allocated host function is a callout. The memory, table and type laws are
  those of `core3P P` at host type `FXCode H`.
* **`fxG P : GameEngine`**: the WasmFX game engine over the IR's numeric modules (`ofNum`, no FX
  functions), and **`fxXG P : GameEngine`** over IR modules that carry FX functions
  (`FXNumModule`); `fxXG_ofNum`: on a numeric module the two agree.
* **The parametrized construction.** `NumEngine` is a lawful engine with a map from the IR's
  numeric modules; `NumEngine.toGameEngine` is the game engine and `NumEngine.den` the IR
  component semantics `Comp.den` over its game semantics `engineSem`. The Core 3.0, Lime1,
  Core-3.0-restricted-to-Lime1 and WasmFX instances are `core3N P`, `lime1N`, `core3LN P` and
  `fxN P`, and their game engines are exactly `core3G P`, `lime1G`, `core3LG P` and `fxG P`
  (`core3N_toGameEngine`, …, `fxN_toGameEngine`, all by `rfl`): the four component models are
  one construction applied to four core models.

**Behaviour.**

* **`fxG_sem_eq_core3G`**: on numeric modules the WasmFX game semantics is the Core 3.0 game
  semantics (`(fxG P).sem = (core3G P).sem`). The FX instance of a module without FX functions is
  its Core 3.0 instance with host code `h` read as `FXCode.host h`, and the two instance
  transition systems simulate each other move for move
  (`Silmaril.Proofs.Wasm.Component.FXEngine.Sim`). Hence `fxN_den_eq_core3N` (equal component
  semantics), `fxG_sem_eq_modSem` (the bridge to `modSem P`, under `SameInst`), and
  **`Simple.sound_fxG`**: soundness of the IR over `fxG P` for the reference machine over Core
  3.0, assuming the bridge hypothesis of `core3G_sem_eq_modSem_of` for every module;
* `exportSpecE_ofNum`: on numeric modules the canonical-ABI specification over the FX engine is
  the one over Core 3.0 (`exportSpecE (fxE P) ofNum = exportSpecE (core3P P) NumModule.mod`):
  the export calls of the two instances have the same outcomes and diverge together
  (`Silmaril.Proofs.Wasm.Component.FXEngine.Spec`);
* `Simple.specToIR_fx`: the IR half over the FX engine itself: terminating outcomes of the
  canonical-ABI specification run on `fxE P` are plays of the IR denotation over `fxG P`;
* the engine has stack switching: `fxE_suspend` (`suspend` under a handler is an internal step
  capturing a continuation) and `fxE_status_fx_call` (a Core call of an FX function is not a
  callout; the engine runs it).

See `docs/projects/wasm-components.md` (track compfx).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXEngine

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Proofs.Wasm.Component.FXEngine
open Silmaril.Wasm.Numerics (Profile)

/-- **The WasmFX engine is lawful.** -/
instance fxE_lawful (P : Profile) : (fxE P).Lawful where
  flatType?_ofFlatType := (L₀).flatType?_ofFlatType
  returned_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusFX P _ _ = _ from h).symm.trans e) _
  callout_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusFX P _ _ = _ from h).symm.trans e) _
  stuck_no_step h := no_step_of_ne_running (P := P)
    (fun e => by cases (show statusFX P _ _ = _ from h).symm.trans e) _
  externSub_refl := (L₀).externSub_refl
  externSub_trans := (L₀).externSub_trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := Grows.extendsFX (internalFX_grows h)
  prepare_extends h := Grows.extendsFX (prepareFX?_grows h)
  allocHost_extends h :=
    Grows.extendsFX (Silmaril.Wasm.Component.Engine.Core3.allocHost_grows h)
  allocHost_fresh h := (L₀).allocHost_fresh h
  allocHost_frame h := (L₀).allocHost_frame h
  allocHost_funcType h := (L₀).allocHost_funcType h
  allocHost_callout h hn := statusFX_allocHost_callout h hn
  memWrite_extends h :=
    Grows.extendsFX (Silmaril.Wasm.Component.Engine.Core3.memWrite?_grows h)
  memWrite_memSize h := (L₀).memWrite_memSize h
  memWrite_memAddrType h := (L₀).memWrite_memAddrType h
  memWrite_read h := (L₀).memWrite_read h
  memWrite_read_other h := (L₀).memWrite_read_other h
  memRead_isSome_iff := (L₀).memRead_isSome_iff
  memRead_size h := (L₀).memRead_size h
  memWrite_isSome_iff := (L₀).memWrite_isSome_iff
  memAddrType_isSome_iff := (L₀).memAddrType_isSome_iff

/-- **The WasmFX game engine** over the IR's numeric modules (no FX functions). -/
noncomputable def fxG (P : Profile) : GameEngine where
  E := fxE P
  lawful := fxE_lawful P
  abi := AbiLawful.ofLawful _
  M := NumModule
  core := inferInstance
  emb := ofNum

/-- **The WasmFX game engine over IR modules with FX functions.** -/
noncomputable def fxXG (P : Profile) : GameEngine where
  E := fxE P
  lawful := fxE_lawful P
  abi := AbiLawful.ofLawful _
  M := FXNumModule
  core := inferInstance
  emb := FXNumModule.mod

theorem fxG_sem (P : Profile) : (fxG P).sem = engineSem (fxE P) NumModule ofNum := rfl

/-- On a numeric module, the two WasmFX game engines agree. -/
theorem fxXG_ofNum (P : Profile) (m : NumModule) :
    (fxXG P).sem.sem ⟨ofNum m, m.exports⟩ = (fxG P).sem.sem m := rfl

/-! ## The parametrized construction -/

/-- **A core model for the component construction**: a lawful engine with a map from the IR's
numeric core modules. -/
structure NumEngine where
  /-- The engine. -/
  E : Engine
  /-- Its laws. -/
  lawful : E.Lawful
  /-- The engine module of a numeric IR module. -/
  emb : NumModule → E.Module

/-- The game engine of a core model. -/
def NumEngine.toGameEngine (N : NumEngine) : GameEngine where
  E := N.E
  lawful := N.lawful
  abi := @AbiLawful.ofLawful N.E N.lawful
  M := NumModule
  core := inferInstance
  emb := N.emb

/-- **The component semantics over a core model**: the IR denotation `Comp.den` over the game
semantics `engineSem` of the engine. -/
def NumEngine.den (N : NumEngine) (c : Comp NumModule) :=
  c.den (engineSem N.E NumModule N.emb)

theorem NumEngine.den_eq (N : NumEngine) (c : Comp NumModule) :
    N.den c = c.den N.toGameEngine.sem := rfl

/-- Core 3.0 as a core model. -/
noncomputable def core3N (P : Profile) : NumEngine := ⟨core3P P, core3P_lawful P, NumModule.mod⟩

/-- Core 3.0 restricted to `lime1` as a core model. -/
noncomputable def core3LN (P : Profile) : NumEngine :=
  ⟨restrict (core3P P) (Lime1G.lime1R P), restrict_lawful, NumModule.mod⟩

/-- The Lime1 engine as a core model. -/
def lime1N : NumEngine :=
  ⟨Silmaril.Wasm.Component.Engine.Lime1.lime1, Silmaril.Wasm.Component.Engine.Lime1.lawful,
    Lime1G.lime1Emb⟩

/-- WasmFX as a core model. -/
noncomputable def fxN (P : Profile) : NumEngine := ⟨fxE P, fxE_lawful P, ofNum⟩

theorem core3N_toGameEngine (P : Profile) : (core3N P).toGameEngine = core3G P := rfl

theorem core3LN_toGameEngine (P : Profile) : (core3LN P).toGameEngine = Lime1G.core3LG P := rfl

theorem lime1N_toGameEngine : lime1N.toGameEngine = Lime1G.lime1G := rfl

theorem fxN_toGameEngine (P : Profile) : (fxN P).toGameEngine = fxG P := rfl

/-- **Lime1 and WasmFX arise from the same construction**: the component semantics of the
Lime1, Core-3.0-restricted-to-Lime1 and WasmFX component models are `NumEngine.den` of their
core models, and the restricted model refines Core 3.0. -/
theorem lime1_fx_same_construction (P : Profile) (c : Comp NumModule) :
    c.den Lime1G.lime1G.sem = lime1N.den c ∧ c.den (Lime1G.core3LG P).sem = (core3LN P).den c ∧
      c.den (fxG P).sem = (fxN P).den c ∧ (core3LN P).den c ≤ (core3N P).den c :=
  ⟨rfl, rfl, rfl, den_restrict_le (E := core3P P) (r := Lime1G.lime1R P) NumModule.mod c⟩

/-! ## Behaviour: on Core modules the WasmFX engine is Core 3.0 -/

/-- **On numeric modules the WasmFX game semantics is the Core 3.0 game semantics.** The FX
instance of a module without FX functions is its Core 3.0 instance (host code renamed into
`FXCode`), and the two instance transition systems simulate each other move for move. -/
theorem fxG_sem_eq_core3G (P : Profile) : (fxG P).sem = (core3G P).sem := by
  show engineSem (fxE P) NumModule ofNum = engineSem (core3P P) NumModule NumModule.mod
  unfold engineSem
  congr 1
  funext m
  rw [show instOf (fxE P) (ofNum m) (CoreModule.imports m) (CoreModule.exports m) =
      (instOf (core3P P) m.mod (CoreModule.imports m) (CoreModule.exports m)).map
        fun I => ⟨SFX I.store, I.addrs⟩ from instOf_ofNum m]
  cases instOf (core3P P) m.mod (CoreModule.imports m) (CoreModule.exports m) with
  | none => rfl
  | some I => exact engineStrategy_SFX I _ _

/-- **The WasmFX and Core 3.0 component semantics agree** on every component of numeric modules. -/
theorem fxN_den_eq_core3N (P : Profile) (c : Comp NumModule) : (fxN P).den c = (core3N P).den c :=
  congrArg (fun C => c.den C) (fxG_sem_eq_core3G P)

/-- **The bridge for the WasmFX game engine**: on a module whose engine instance is its `IsInst`
instance, `(fxG P).sem` is `modSem P`. -/
theorem fxG_sem_eq_modSem (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hS : SameInst P m I) : (fxG P).sem.sem m = (modSem P).sem m := by
  rw [fxG_sem_eq_core3G]
  exact core3G_sem_eq_modSem P hI hS

theorem CoreSem.ext' {M : Type} [CoreModule M] {C D : CoreSem M} (h : C.sem = D.sem) : C = D := by
  cases C
  cases D
  cases h
  rfl

/-- **On numeric modules the canonical-ABI specification over the WasmFX engine is the one over
Core 3.0.** -/
theorem exportSpecE_ofNum (P : Profile) (c : Simple) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) :
    exportSpecE (fxE P) ofNum c x vs = exportSpecE (core3P P) NumModule.mod c x vs :=
  Silmaril.Proofs.Wasm.Component.FXEngine.exportSpecE_ofNum c x vs

/-- **The IR half of soundness over the WasmFX engine**: every terminating outcome of the
canonical-ABI specification over `fxE P` (lower, run the export on the FX engine instance, lift)
of an export call of a simple component is a play of its IR denotation over `fxG P`. -/
theorem Simple.specToIR_fx (P : Profile) (c : Simple) (hc : c.Good) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (b : Outcome)
    (hb : b ∈ exportSpecE (fxE P) ofNum c c.exports[j] vs) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (fxG P).sem)
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.specToIRE (E := fxE P) ofNum c hc j vs b hb

/-- **Soundness of the IR over the WasmFX game engine** for the reference Component Model
semantics over Core 3.0: when every numeric module has the same instance on the engine and
`modSem` sides (or none on either), every behaviour of a simple component in the reference
machine is matched by its IR denotation over `fxG P`. -/
theorem Simple.sound_fxG (P : Profile)
    (hB : ∀ m : NumModule, (∃ I, m.IsInst I ∧ SameInst P m I) ∨
      (instOf (core3P P) m.mod [] m.exports = none ∧ ¬ ∃ I, m.IsInst I))
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (fxG P).sem)
      ⟨j, by simp [Simple.toComp]⟩ vs b := by
  have hsem : (fxG P).sem.sem = (modSem P).sem := funext fun m =>
    (congrArg (fun C : CoreSem NumModule => C.sem m) (fxG_sem_eq_core3G P)).trans
      (core3G_sem_eq_modSem_of P hB m)
  have he : (fxG P).sem = modSem P := CoreSem.ext' hsem
  rw [he]
  exact Reference.Simple.sound P prof c hc hf hi ha j vs hvs b hb

/-! ## The engine has stack switching -/

open Silmaril.Wasm.Models.FX in
/-- **`suspend` is an internal step of the FX engine**: an FX thread whose handler has clause
`(on x l)` around `suspend x` captures the empty context as a new continuation and branches to
`l` with it. -/
theorem fxE_suspend (P : Profile) {H : Type} {s : Silmaril.Wasm.Execution.Core.Store (FXCode H)}
    {K : List (Option ContFX)} {f : Silmaril.Wasm.Execution.Core.Frame}
    {x : Silmaril.Wasm.TagIdx} {ta : Nat} {ti : Silmaril.Wasm.Execution.Core.TagInst}
    {l : Silmaril.Wasm.LabelIdx} (ht : s.tag? f x = some (ta, ti)) :
    (fxE P).Internal (s, ThreadFX.fx K f [.handler [.onLabel ta l] [.fx (.suspend x)]])
      (s, ThreadFX.fx (K ++ [some ⟨Ctx.hole.plug⟩]) f [.contRef K.length, .core (.plain (.br l))]) :=
  Or.inl ⟨_, _, _, rfl, suspend_step ht⟩

/-- **A Core thread calling an FX function is running**: the FX engine does not report the call
as a callout (the next step enters the FX function). -/
theorem fxE_status_fx_call (P : Profile) {H : Type}
    {s : Silmaril.Wasm.Execution.Core.Store (FXCode H)} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {F : Silmaril.Wasm.Models.FX.FuncFX} {args : List Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Game.statusP P s t = .callout (.fx F) args) :
    (fxE P).status s (ThreadFX.core t) = .running := by
  show liftR _ = _
  rw [h]
  rfl

end Silmaril.Wasm.Component.FXEngine
