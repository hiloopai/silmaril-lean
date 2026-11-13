module

public import Silmaril.Wasm.Models.V2CoreSpec.Defs
public import Silmaril.Wasm.Models.V2CoreInst.Thms
public import Silmaril.Wasm.Game.SpecGlobals.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff

/-!
# Single allocation is included in the spec's double allocation, without host calls

* `coreRun_complete`: the relational run of `$instantiate` (`CoreRun`, no validity premise) is
  computed by `instantiate? evalConst?` when the initialisers are constant (the proof of
  silmaril-lean's `instantiate?_complete`, with the constancy given directly);
* `once_prepare`: so a single-allocation instantiation `CoreInstantiateOnce` is
  `$evalglobals` (computed by `evalGlobals?`) followed by the preparation of the global-free
  residue (computed by `prepare?`), with the start call;
* **`once_sub_spec`**: without host calls, every single-allocation instantiation run `C` has a
  spec `$instantiate` run `C'` (double allocation) with the same behaviours, at every profile,
  for a store whose functions name only existing globals (`GlobalsNamed`). The behaviours are
  transported by `Silmaril.Wasm.Game.spec_behaviours_eq_residue` (global-address embedding);
* **`coreInstObsOnce_sub_spec`**: hence single-allocation instantiation observations are spec
  instantiation observations at host-free points;
* `liftHost_noHost`: the empty 2.0 host lifts to the empty Core host;
* **`instObs_sub_spec`**: 2.0 instantiation observations of any module with a Core image,
  defined globals included, are spec (`coreInstObs`) observations of the image, at host-free
  points whose Core store satisfies `GlobalsNamed`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The relational run of `$instantiate` is computed**, for constant initialisers. -/
theorem coreRun_complete {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreRun P host s m xas c)
    (hcG : ∀ e ∈ m.globals.map Global.init, ConstExpr e)
    (hcT : ∀ e ∈ m.tables.map Table.init, ConstExpr e)
    (hcE : ∀ es ∈ m.elems.map Elem.init, ∀ e ∈ es, ConstExpr e) :
    instantiate? evalConst? s m xas = some c := by
  obtain ⟨hb, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT, hE, hM, rfl⟩ := h
  have hev : EvalComplete P host (evalConst? (H := H)) := evalConst?_evalComplete
  unfold instantiate?
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  simp only [evalGlobals?_complete hev hG hcG, evalExprs?_complete hev hT hcT,
    evalExprss?_complete hev hE hcE, hM]
  rfl

/-- **A single-allocation instantiation is `$evalglobals`, then the residue's preparation.** -/
theorem once_prepare {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
    {xas : List ExternAddr} {C : Config H}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ (s₁ : Store H) (f₁ : Frame) (vs : List Val) (c₁ : Config H) (st : Option FuncIdx),
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st) ∧
      C = c₁.withStart st := by
  obtain ⟨⟨xtE, xtI, hmod, -⟩, s₁, f₁, vs, hG, hrun⟩ := h
  obtain ⟨hcG, hcT, hcE⟩ := hmod.initConst
  have hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, vs) :=
    evalGlobals?_complete evalConst?_evalComplete hG hcG
  have hi : instantiate? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some C :=
    coreRun_complete hrun (by simp) hcT hcE
  rw [prepare?_instantiate?] at hi
  obtain ⟨⟨c₁, st⟩, hp, hC⟩ := Option.map_eq_some_iff.mp hi
  exact ⟨s₁, f₁, vs, c₁, st, hg, hp, hC.symm⟩

/-- **Without host calls, single allocation is included in the spec's double allocation**, with
the same behaviours at every profile. -/
theorem once_sub_spec {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    (hs : GlobalsNamed s) {m : Module} {xas : List ExternAddr} {C : Config Nat}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' noHostC C' = behavioursOf P' noHostC C := by
  obtain ⟨xtE, xtI, -, hxas⟩ := h.1
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, rfl⟩ := once_prepare h
  obtain ⟨c, hc, hbeh⟩ := Silmaril.Wasm.Game.spec_behaviours_eq_residue hs hxas hg hp
  have hI : Instantiate P host s m xas (c.withStart st) :=
    (prepare?_iff h.1).mp (by rw [hc]; rfl)
  exact ⟨c.withStart st, hI, hbeh⟩

/-- **Host-free single-allocation instantiation observations are spec observations.** -/
theorem coreInstObsOnce_sub_spec (P : Profile) {s : Store Nat} (hs : GlobalsNamed s)
    (cm : Module) (cxas : List ExternAddr) :
    Silmaril.Proofs.Wasm.Models.V2CoreInst.coreInstObsOnce P (s, noHostC) (cm, cxas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (s, noHostC) (cm, cxas) := by
  rintro b ⟨C, hC, hb⟩
  obtain ⟨C', hC', hbeh⟩ := once_sub_spec hs hC
  have hb' : b ∈ behavioursOf P noHostC C' := by
    rw [hbeh P]
    exact hb
  exact ⟨C', hC', hb'⟩

/-- The empty 2.0 host lifts to the empty Core host. -/
theorem liftHost_noHost :
    liftHost (fun _ _ _ _ => False : VHost H) = (noHostC : CHost H) := by
  funext h S args out
  simp [liftHost, noHostC]

/-- **2.0 instantiation observations are spec observations of the image, defined globals
included**, at host-free points whose Core store satisfies `GlobalsNamed`. -/
theorem instObs_sub_spec (P : Profile) {p : Pt Nat} (hp : dom p)
    (hhost : p.2 = fun _ _ _ _ => False) (hs : GlobalsNamed (ptCore p).1)
    {m : Silmaril.Wasm.V2.Module} {cm : Module}
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr) :
    Silmaril.Proofs.Wasm.Models.V2Core.instObs P p (m, xas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
  have hpt : ptCore p = ((ptCore p).1, noHostC) := by
    rw [ptCore, hhost, liftHost_noHost]
  have hsub := Silmaril.Proofs.Wasm.Models.V2CoreInst.instObs_sub_once P hp hcm xas
  rw [hpt] at hsub ⊢
  exact hsub.trans (coreInstObsOnce_sub_spec P hs _ _)

end Silmaril.Proofs.Wasm.Models.V2CoreSpec
