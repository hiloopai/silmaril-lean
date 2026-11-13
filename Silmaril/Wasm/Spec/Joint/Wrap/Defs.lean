module

public import Silmaril.Wasm.Spec.Joint.Defs
public import Silmaril.Wasm.Spec.Wasm.Thms
public import Silmaril.Wasm.Spec.Component.Ground.Defs

@[expose] public section

/-!
# Modules and components together: wrapping a core module as a component

The module institutions of `Silmaril.Wasm.Spec` (over `wasmSem P`, scalar Core 3.0 instances) and
the component ones (`Silmaril.Wasm.Spec.Component`) are related by the **wrapping** of a numeric
core module as a component: each core export is `canon lift`ed at the component function type
that reads `i32`/`i64` as `u32`/`u64` and keeps `f32`/`f64`.

* `NIface := Iface CoreFuncTy`: interfaces of numeric core functions;
  `numSem P := (wasmSem P).restrict fnOf`: the scalar Core 3.0 semantics at numeric interfaces
  (programs are `WasmProg (X.map fnOf)`).
* The change of base (`Silmaril.Wasm.Spec.Joint.Base`): `wrapFn : CoreFuncTy → CFn` (injective),
  arguments by `wrapVal` (`i32 x ↦ u32 x`, …) and results by `wrapOut` (`returns vs ↦
  returns (some …)`, traps and uncaught exceptions ↦ `traps`, as the canonical ABI's
  `call_and_trap_on_throw`; `diverges ↦ diverges`).
* `wrapSem P := (numSem P).push wrapFn (List.map wrapVal) wrapOut`: wrapped modules as component
  programs, with their Core traces read as component events.
* **The comorphism** `wrapCoHom L P : inst (L.pull wrapFn …) (numSem P) → inst L (wrapSem P)`
  for every component logic `L` (model-expansive, so entailment is borrowed:
  `push_entails_iff`).
* **Joint institutions.** At component interfaces, `jointSem P C := (wrapSem P).sum (irSem C)`:
  models are wrapped modules or IR components (`sumInlCoHom`, `sumInrCoHom`). At module
  interfaces, `modCompLogic Lm Lc := Lm.sum (Lc.pull wrapFn …)`: module formulas and component
  formulas side by side, with `LogicMap.inl/inr`.

**Soundness w.r.t. the boundary adapters** (`Silmaril.Wasm.Spec.Joint.Wrap.Thms`). The wrapped
traces are *defined* by translation. That this is what the canonical-ABI adapters do is proved
against Silmaril's IR: `wrapSimple m` is the component of the IR (one core instance of `m`, each
export lifted at `liftTy`) whose interface is the image (`cface_wrapSimple`), and every
terminating first call of a Core 3.0 instance of `m` is, translated, a trace of `wrapSimple m`
in `irSem (modSem P)` (`wrap_sound`), through `Reference.specToIR`. Given
`Simple.RefSound` it is also the reference machine's.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Wasm.Component (CoreFuncTy ValTy FuncTy)
open Silmaril.Wasm.Component.Reference (fnOf NumModule Simple SimpleExport toRefVal)
open Silmaril.Wasm.Spec.Component
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Execution.Core (Val)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.Institution

/-! ## Numeric module interfaces -/

/-- Interfaces of numeric core functions. -/
abbrev NIface : Type := Iface CoreFuncTy

/-- **Scalar Core 3.0 modules at numeric interfaces**, at profile `P`. -/
noncomputable abbrev numSem (P : Profile) :
    Semantics CoreFuncTy (List Val) (Silmaril.Wasm.Behaviour Val) :=
  (wasmSem P).restrict fnOf

/-! ## The change of base -/

/-- The component type of a wrapped core type. -/
def wrapNum : NumType → CTy
  | .int .i32 => .prim .u32
  | .int .i64 => .prim .u64
  | .float .f32 => .prim .f32
  | .float .f64 => .prim .f64

/-- The component function type of a wrapped core function type. -/
def wrapFn (ft : CoreFuncTy) : CFn := ⟨ft.params.map wrapNum, ft.results.map wrapNum⟩

/-- The component value of a numeric Core value (`i32 x ↦ u32 x`, `i64 x ↦ u64 x`, floats by
their bits). Non-numeric values do not occur at numeric interfaces; they map to a junk value. -/
def wrapVal : Val → RVal
  | .num ⟨.int .i32, b⟩ => .int .u32 b.toNat
  | .num ⟨.int .i64, b⟩ => .int .u64 b.toNat
  | .num ⟨.float .f32, b⟩ => .f32 b
  | .num ⟨.float .f64, b⟩ => .f64 b
  | _ => .errorContext ⟨0⟩

/-- The component outcome of a Core behaviour: uncaught exceptions trap at the component
boundary. -/
def wrapOut : Silmaril.Wasm.Behaviour Val → Outcome
  | .returns vs => .returns (some (vs.map wrapVal))
  | .traps => .traps
  | .throws _ => .traps
  | .diverges => .diverges

theorem wrapNum_injective : Function.Injective wrapNum := by
  intro a b h
  rcases a with (_ | _) | (_ | _) <;> rcases b with (_ | _) | (_ | _) <;>
    first | rfl | cases h

theorem wrapFn_injective : Function.Injective wrapFn := by
  rintro ⟨p, r⟩ ⟨p', r'⟩ h
  simp only [wrapFn, CFn.mk.injEq] at h
  rw [List.map_injective_iff.2 wrapNum_injective h.1,
    List.map_injective_iff.2 wrapNum_injective h.2]

/-- **Wrapped modules as component programs.** -/
noncomputable abbrev wrapSem (P : Profile) : Semantics CFn (List RVal) Outcome :=
  (numSem P).push wrapFn (List.map wrapVal) wrapOut

/-- **The comorphism of wrapping**: from pulled component specifications of modules to component
specifications of wrapped modules. -/
noncomputable def wrapCoHom (L : Logic CFn (List RVal) Outcome) (P : Profile) :
    Inst.CoHom (inst (L.pull wrapFn (List.map wrapVal) wrapOut) (numSem P)) (inst L (wrapSem P)) :=
  pushCoHom L (numSem P) (List.map wrapVal) wrapOut wrapFn_injective

/-- **Joint models at component interfaces**: wrapped modules and IR components. -/
noncomputable abbrev jointSem {M : Type} [Silmaril.Wasm.Component.CoreModule M] (P : Profile)
    (C : Silmaril.Wasm.Component.CoreSem M) : Semantics CFn (List RVal) Outcome :=
  (wrapSem P).sum (irSem C)

/-- **Joint logics at module interfaces**: module formulas and component formulas. -/
abbrev modCompLogic (Lm : Logic CoreFuncTy (List Val) (Silmaril.Wasm.Behaviour Val))
    (Lc : Logic CFn (List RVal) Outcome) :
    Logic CoreFuncTy (List Val) (Silmaril.Wasm.Behaviour Val) :=
  Lm.sum (Lc.pull wrapFn (List.map wrapVal) wrapOut)

/-! ## The wrapping component in the IR -/

/-- The IR type of a wrapped core type. -/
def numVT : NumType → ValTy
  | .int .i32 => .u32
  | .int .i64 => .u64
  | .float .f32 => .f32
  | .float .f64 => .f64

/-- The IR function type at which a core function is lifted. -/
def liftTy (ft : CoreFuncTy) : FuncTy := ⟨ft.params.map numVT, ft.results.map numVT⟩

/-- The IR value of a numeric Core value. -/
def numToIR : Val → Silmaril.Wasm.Component.Val
  | .num ⟨.int .i32, b⟩ => .u32 b
  | .num ⟨.int .i64, b⟩ => .u64 b
  | .num ⟨.float .f32, b⟩ => .f32 b
  | .num ⟨.float .f64, b⟩ => .f64 b
  | _ => .bool false

/-- **The wrapping of a numeric module** as a component of the IR: one instance, each core
export `canon lift`ed at `liftTy`. -/
def wrapSimple (m : NumModule) : Simple :=
  ⟨m, m.exports.mapIdx fun k p => ⟨p.1, liftTy p.2, k⟩⟩

/-- The numeric interface of a module: no imports, its exports. -/
def numIface (m : NumModule) : NIface := ⟨[], m.exports.map Prod.snd⟩

/-- The module program of an instance of `m`. -/
def numProg (P : Profile) (m : NumModule) (I : Silmaril.Wasm.Game.ScalarInstance) :
    (numSem P).Prog (numIface m) :=
  ⟨I.addrs, I.store⟩

/-- Export `j` of `m` at the numeric interface. -/
def numExp (m : NumModule) (j : Fin m.exports.length) : (numIface m).Exp :=
  ⟨j, by simp [numIface]⟩

/-- Export `j` of `m` in the wrapping component. -/
def wrapExp (m : NumModule) (j : Fin m.exports.length) : Fin (wrapSimple m).exports.length :=
  ⟨j, by simp [wrapSimple]⟩

end Silmaril.Wasm.Spec
