module

public import Silmaril.Wasm.Det.Component.Defs
public import Silmaril.Wasm.Det.Core.Component.Thms
public import Silmaril.Proofs.Wasm.Det.Component.Leaf
public import Silmaril.Proofs.Wasm.Det.Component.Scratch

/-!
# Components: determinism and statelessness modulo traps and imports across calls: theorems

Every statement holds at an **arbitrary** silmaril-lean profile `P`, and at every component
choice profile.

**One export call on the reference machine** (`core3P P`, the reference host without host
functions):

* `exportDet_of_coreDet`: for a float-free simple component within the flat arities whose
  module is instantiated as the IR assumes, `CoreDet` of export `x` (its core function is
  `DetCall` on all flat arguments) makes the export call deterministic modulo traps
  (`ExportDet`). The proof goes through `refToSpec_of_arity`.
* `coreDet_of_instLeafCheck`, and the tactic `export_det`: `CoreDet` from the kernel-evaluated
  leaf check of the instantiated module.
* `CompDet.exportDet`: the shared `CompDet` implies `ExportDet`.

**Sessions** (one core instance, many canonical-ABI export calls, the core store persisting):

* `SStatelessAt.history`: the non-trapping output of a call after any history of calls is the
  output of the same call in the initial state.
* `sStatelessAt_of_obs` (**unwinding**): an observable-state PER `Obs` with `Obs s₀ s₀`,
  confinement (`Confined`) and observation (`ObsDetermines`) give `SStatelessAt`.
* `abi_confined`: confinement from the per-export `ConfVC`s. `runs_obs` is per-step confinement
  (`StepConfined`) along Core runs, used to discharge the `ConfVC` fields.
* `abi_obsDetermines`: observation from the phase VCs `ReallocVC`, `WriteVC`, `CoreVC` (the
  scratch discipline).
* `sReach_funcs`: call states keep the function instances.
* `sStatelessAt_of_obsAgree`: a flat-result export whose `realloc` and core function agree on
  outputs (`ObsAgree`) across stores with the session's function instances is stateless. This is
  the lift of the core `StatelessFn` notion; the `list<u8>` argument is written into memory and
  read by the core function in the same call.
* `sDetAt_of_detCalls`: determinism from `DetCall` of `realloc`, the core function and
  `post-return`. This is the lift of the core `DetFn` notion.
* `sStatelessAt_of_abiLeafCheck`, `sDetAt_of_abiLeafCheck`, and the tactics `abi_stateless`,
  `abi_det`: by kernel evaluation of `abiLeafCheck`.

**The scratch region and the Hoare logic**:

* `scratchEq_refl`, `isPER_scratchEq`: "equal except on the scratch bytes" is an observable-state
  PER;
* `memWrite_scratchEq`: the canonical ABI's write of a `list<u8>` argument inside the scratch
  region is confined (the `write` field of `ConfVC` for `ScratchEq`, when `realloc` returns a
  scratch pointer);
* `obsAgree_of_hwp`: two invocations without import calls whose every-run specifications
  `HWP … (RetOrTrap F)` (Silmaril's Hoare logic, `Silmaril.Wasm.Logic.Hoare`) return the same values
  agree on outputs. With `F` depending only on the arguments, `sStatelessAt_of_hwp` makes the
  export stateless.

Proofs: `Silmaril.Proofs.Wasm.Det.Component.{Ref,Session,Leaf,Scratch}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core

/-! ## One export call on the reference machine -/

section Ref

open Silmaril.Wasm.Component.Reference (Simple SimpleExport refHost toRefVal)

/-- **Lifting core determinism to an export call of the reference machine.** -/
theorem exportDet_of_coreDet (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    {x : SimpleExport} (hx : x ∈ c.exports) (hD : CoreDet P c x)
    {vs : List Silmaril.Wasm.Component.Val}
    (hvs : Silmaril.Wasm.Component.ValTy.checkList x.ty.params vs = true) :
    ExportDet prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) :=
  Silmaril.Proofs.Wasm.Det.Component.exportDet_of_coreDet P prof c hc hf hi ha hx hD hvs

/-- **`CoreDet` from the leaf check** of the instantiated core module, at every profile. -/
theorem coreDet_of_instLeafCheck {P : Profile} {c : Simple} {x : SimpleExport}
    (h : instLeafCheck c.mod.mod x.core = true) : CoreDet P c x :=
  Silmaril.Proofs.Wasm.Det.Component.coreDet_of_instLeafCheck h

end Ref

section Shared

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host Engine)

/-- The shared component-level determinism implies `ExportDet` for every export call. -/
theorem CompDet.exportDet {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]
    {prof : ProfileKind} {h : Host E σ} {σ0 : σ} {comp : Syntax.Component E.Module}
    {args : Instantiate.Exports E} (hD : Silmaril.Wasm.Det.Core.Component.CompDet prof h σ0 comp args)
    (name : String) (vals : List Value.Val) : ExportDet prof h σ0 comp args name vals :=
  fun _ _ h₁ h₂ => Silmaril.Wasm.Det.Core.Component.exportBehaviours_returns_eq hD h₁ h₂

end Shared

/-- Closes `CoreDet P c x` for a simple component whose lifted core export is a store-free
native leaf function, by kernel evaluation of `instLeafCheck`. -/
macro "export_det" : tactic =>
  `(tactic| exact Silmaril.Wasm.Det.Component.coreDet_of_instLeafCheck (by decide +kernel))

/-! ## Sessions -/

section Session

variable {ι α β : Type} {C : ι → CallSem α β} {s₀ : Store Nat}

/-- **Statelessness: earlier calls do not affect later non-trapping outputs.** -/
theorem SStatelessAt.history {i : ι} (hS : SStatelessAt C s₀ i) {s : Store Nat}
    (hs : SReach C s₀ s) {v : α} {tr : List Call} {t₀ t : Store Nat} {w₀ w : β}
    (h₀ : C i s₀ v tr t₀ (some w₀)) (h : C i s v tr t (some w)) : w = w₀ :=
  hS s s₀ hs .init v tr t t₀ w w₀ h h₀

/-- **Determinism: same call state, same non-trapping output and store.** -/
theorem SDetAt.out {i : ι} (hD : SDetAt C s₀ i) {s : Store Nat} (hs : SReach C s₀ s) {v : α}
    {tr : List Call} {t₁ t₂ : Store Nat} {w₁ w₂ : β} (h₁ : C i s v tr t₁ (some w₁))
    (h₂ : C i s v tr t₂ (some w₂)) : w₁ = w₂ ∧ t₁ = t₂ :=
  hD s hs v tr t₁ t₂ w₁ w₂ h₁ h₂

/-- **Unwinding**: an observable-state PER, confinement and observation give statelessness. -/
theorem sStatelessAt_of_obs {Obs : Store Nat → Store Nat → Prop} (hP : IsPER Obs)
    (h₀ : Obs s₀ s₀) (hC : Confined C s₀ Obs) {i : ι} (hO : ObsDetermines C Obs i) :
    SStatelessAt C s₀ i :=
  Silmaril.Proofs.Wasm.Det.Component.sStatelessAt_of_obs hP h₀ hC hO

/-- Under confinement every call state is `Obs`-related to the initial one. -/
theorem sReach_obs {Obs : Store Nat → Store Nat → Prop} (hP : IsPER Obs) (h₀ : Obs s₀ s₀)
    (hC : Confined C s₀ Obs) {s : Store Nat} (hs : SReach C s₀ s) : Obs s₀ s :=
  Silmaril.Proofs.Wasm.Det.Component.sReach_obs hP h₀ hC hs

end Session

/-- **Per-step confinement along Core runs**: an invariant closed under steps on which every
step keeps the store `Obs`-related gives `Obs` between the start and the end of every run. -/
theorem runs_obs {P : Profile} {Obs : Store Nat → Store Nat → Prop} {J : Config Nat → Prop}
    (hS : StepConfined P Obs J) (hP : IsPER Obs) (hr : ∀ s, Obs s s) {c d : Config Nat}
    {tr : List Call} (hc : J c) (h : Runs P c tr d) : Obs c.store d.store :=
  Silmaril.Proofs.Wasm.Det.Component.runs_obs hS hP hr hc h

/-- **Confinement of a canonical-ABI session** from the per-export `ConfVC`s. -/
theorem abi_confined {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat}
    {Obs : Store Nat → Store Nat → Prop} (hP : IsPER Obs) (hr : ∀ s, Obs s s)
    (hV : ∀ i, ConfVC P Obs (X i)) : Confined (abiSem P X) s₀ Obs :=
  Silmaril.Proofs.Wasm.Det.Component.abi_confined hP hr hV

/-- **Observation for a canonical-ABI export** from the phase VCs of the scratch discipline:
lowering from `Obs`-related stores gives `Arg`-related stores (directly for flat arguments;
through the `realloc` VC and the write VC for a `list<u8>`), and the core VC gives equal
results and equal lifted outputs. -/
theorem abi_obsDetermines {P : Profile} {ι : Type} (X : ι → AbiFn) (i : ι)
    {Obs Mid Arg : Store Nat → Store Nat → Prop}
    (hflat : (X i).argBuf = none → ∀ s₁ s₂, Obs s₁ s₂ → Arg s₁ s₂)
    (hbuf : ∀ ra m, (X i).argBuf = some (ra, m) → ReallocVC P Obs Mid ra ∧ WriteVC Mid Arg m)
    (hC : CoreVC P Arg (X i)) : ObsDetermines (abiSem P X) Obs i :=
  Silmaril.Proofs.Wasm.Det.Component.abi_obsDetermines X i hflat hbuf hC

/-- Call states of a canonical-ABI session hold the initial function instances. -/
theorem sReach_funcs {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ s : Store Nat}
    (hs : SReach (abiSem P X) s₀ s) : s.funcs = s₀.funcs :=
  Silmaril.Proofs.Wasm.Det.Component.sReach_funcs hs

/-- **Lifting core statelessness to a session export** (flat result). -/
theorem sStatelessAt_of_obsAgree {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat}
    {i : ι} (hres : (X i).resBuf = none)
    (hR : ∀ ra m, (X i).argBuf = some (ra, m) → ∀ t₁ t₂ n, FuncsAt s₀.funcs t₁ t₂ →
      ObsAgree P (invoke t₁ ra (reallocArgs n)) (invoke t₂ ra (reallocArgs n)))
    (hC : ∀ t₁ t₂ args, FuncsAt s₀.funcs t₁ t₂ → Nums args →
      ObsAgree P (invoke t₁ (X i).fn args) (invoke t₂ (X i).fn args)) :
    SStatelessAt (abiSem P X) s₀ i :=
  Silmaril.Proofs.Wasm.Det.Component.sStatelessAt_of_obsAgree hres hR hC

/-- **Lifting core determinism to a session export.** -/
theorem sDetAt_of_detCalls {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (hR : ∀ ra m, (X i).argBuf = some (ra, m) → ∀ t n, t.funcs = s₀.funcs →
      DetCall P t ra (reallocArgs n))
    (hC : ∀ t args, t.funcs = s₀.funcs → Nums args → DetCall P t (X i).fn args)
    (hp : ∀ pr, (X i).post = some pr → ∀ t ws, t.funcs = s₀.funcs → DetCall P t pr ws) :
    SDetAt (abiSem P X) s₀ i :=
  Silmaril.Proofs.Wasm.Det.Component.sDetAt_of_detCalls hR hC hp

/-- **The leaf check gives statelessness** of a session export, at every profile. -/
theorem sStatelessAt_of_abiLeafCheck {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat}
    {i : ι} (h : abiLeafCheck s₀ (X i) = true) : SStatelessAt (abiSem P X) s₀ i :=
  Silmaril.Proofs.Wasm.Det.Component.sStatelessAt_of_abiLeafCheck h

/-- **The leaf check gives determinism** of a session export without `post-return`, at every
profile. -/
theorem sDetAt_of_abiLeafCheck {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat}
    {i : ι} (h : abiLeafCheck s₀ (X i) = true) (hpost : (X i).post = none) :
    SDetAt (abiSem P X) s₀ i :=
  Silmaril.Proofs.Wasm.Det.Component.sDetAt_of_abiLeafCheck h hpost

/-! ## The scratch region and the Hoare logic -/

theorem scratchEq_refl (m lo hi : Nat) (s : Store Nat) : ScratchEq m lo hi s s :=
  Silmaril.Proofs.Wasm.Det.Component.scratchEq_refl m lo hi s

theorem isPER_scratchEq (m lo hi : Nat) : IsPER (ScratchEq m lo hi) :=
  Silmaril.Proofs.Wasm.Det.Component.isPER_scratchEq m lo hi

/-- **Writes into the scratch region are confined**: writing bytes inside `[lo, hi)` of memory
`m` keeps the store `ScratchEq m lo hi`-related. -/
theorem memWrite_scratchEq {m lo hi p : Nat} {bs : List UInt8} {s t : Store Nat}
    (hp : lo ≤ p) (hq : p + bs.length ≤ hi) (h : memWrite s m p bs = some t) :
    ScratchEq m lo hi s t :=
  Silmaril.Proofs.Wasm.Det.Component.memWrite_scratchEq hp hq h

/-- **Output agreement from every-run specifications** of the Hoare logic. -/
theorem obsAgree_of_hwp {P : Profile} {s₁ s₂ : Store Nat} {a : Nat} {vs : List Silmaril.Wasm.Execution.Core.Val}
    {F₁ F₂ : List Silmaril.Wasm.Execution.Core.Val} (hnc₁ : NoCalls P (invoke s₁ a vs)) (hnc₂ : NoCalls P (invoke s₂ a vs))
    (h₁ : Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost s₁ {} (invoke s₁ a vs).code (RetOrTrap F₁))
    (h₂ : Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost s₂ {} (invoke s₂ a vs).code (RetOrTrap F₂))
    (hF : F₁ = F₂) : ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs) :=
  Silmaril.Proofs.Wasm.Det.Component.obsAgree_of_hwp hnc₁ hnc₂ h₁ h₂ hF

/-- **Statelessness from functional specifications** in the Hoare logic: if, in every store
with the session's function instances, `realloc` and the core function make no import calls
and return values depending only on their arguments (or trap), the flat-result export is
stateless. -/
theorem sStatelessAt_of_hwp {P : Profile} {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (hres : (X i).resBuf = none) (GR : Nat → List Silmaril.Wasm.Execution.Core.Val) (G : List Silmaril.Wasm.Execution.Core.Val → List Silmaril.Wasm.Execution.Core.Val)
    (hR : ∀ ra m, (X i).argBuf = some (ra, m) → ∀ t n, t.funcs = s₀.funcs →
      NoCalls P (invoke t ra (reallocArgs n)) ∧
        Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost t {} (invoke t ra (reallocArgs n)).code
          (RetOrTrap (GR n)))
    (hC : ∀ t args, t.funcs = s₀.funcs → Nums args → NoCalls P (invoke t (X i).fn args) ∧
      Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost t {} (invoke t (X i).fn args).code
        (RetOrTrap (G args))) :
    SStatelessAt (abiSem P X) s₀ i :=
  sStatelessAt_of_obsAgree hres
    (fun ra m hx t₁ t₂ n ho => obsAgree_of_hwp (hR ra m hx t₁ n ho.1).1 (hR ra m hx t₂ n ho.2).1
      (hR ra m hx t₁ n ho.1).2 (hR ra m hx t₂ n ho.2).2 rfl)
    (fun t₁ t₂ args ho hn => obsAgree_of_hwp (hC t₁ args ho.1 hn).1 (hC t₂ args ho.2 hn).1
      (hC t₁ args ho.1 hn).2 (hC t₂ args ho.2 hn).2 rfl)

/-- Closes `SStatelessAt (abiSem P X) s₀ i` for a concrete export whose core function (and
`realloc`) are store-free native leaf functions, by kernel evaluation of `abiLeafCheck`. -/
macro "abi_stateless" : tactic =>
  `(tactic| exact Silmaril.Wasm.Det.Component.sStatelessAt_of_abiLeafCheck (by decide +kernel))

/-- Closes `SDetAt (abiSem P X) s₀ i` likewise, for an export without `post-return`. -/
macro "abi_det" : tactic =>
  `(tactic| exact Silmaril.Wasm.Det.Component.sDetAt_of_abiLeafCheck (by decide +kernel) rfl)

end Silmaril.Wasm.Det.Component
