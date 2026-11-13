module

public import Silmaril.Wasm.FnInst.Ground.Link.Defs
public import Silmaril.Wasm.FnInst.Ground.Forced.Thms
public import Silmaril.Wasm.FnInst.Ground.Check.Thms

@[expose] public section

/-! # `checkInst` sentences from the code simulations of the bridges

`modRefines_of_baseSim` (any silmaril `BaseSim` at a lawful rank) and
`modRefines_of_deferred` (any `DeferredBaseSim`): when the computed instances are related
(`InstRel`), every invocation of export `j` of `m` is transported to `m'` by the closure
(`closure_run_transport`, `deferred_closure_run_transport` and the divergence transports), so
`ModRefines (· = ·) P m m' j` holds at every profile `P`.
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.Verify (instOf)

variable {P : Profile} {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

/-- The closed host is wasm-check's host. -/
theorem closedHost_eq_noHost : (closedHost (H := ℕ)) = SingleThreaded.Det.noHost := rfl

theorem addrOf_eq {m m' : Module} (hI : InstRel BI m m') (j : ℕ) : addrOf m' j = addrOf m j := by
  simp only [addrOf, hI.2]

/-- Invocations of related instances: runs and divergence transported by any closure. -/
theorem modRefines_of_transport {m m' : Module} (hI : InstRel BI m m') (j : ℕ)
    (hrun : ∀ {c d c' : Config ℕ} {r : Result}, CfgRel (FuncRel BI) (AdminsRel BI B) c d →
      Steps P closedHost c c' → c'.code = r.toAdmin →
      ∃ d', Steps P closedHost d d' ∧ d'.code = r.toAdmin)
    (hdiv : ∀ {c d : Config ℕ}, CfgRel (FuncRel BI) (AdminsRel BI B) c d →
      Diverges P closedHost c → Diverges P closedHost d) :
    ModRefines (· = ·) P m m' j := by
  intro vs _ b hb
  have hcfg : CfgRel (FuncRel BI) (AdminsRel BI B) (invoke (instOf m).store (addrOf m j) vs)
      (invoke (instOf m').store (addrOf m' j) vs) := by
    rw [addrOf_eq hI j]
    exact Silmaril.Wasm.Binaryen.Deferred.invoke_cfgRel _ _ hI.1
  rcases hb with ⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩
  · obtain ⟨d', hd', hdc⟩ := hrun hcfg hs hc
    exact ⟨_, Or.inl ⟨d', r, hd', hdc, rfl⟩, rfl⟩
  · exact ⟨_, Or.inr ⟨rfl, hdiv hcfg hd⟩, rfl⟩

/-- **A code simulation gives the `checkInst` sentence `m ⊑ m'`**, at every profile. -/
theorem modRefines_of_baseSim {rank : List Admin → Nat} [LawfulCodeRank rank]
    (hB : BaseSim P (closedHost (H := ℕ)) (FuncRel BI) BI B rank) {m m' : Module} (hI : InstRel BI m m')
    (j : ℕ) : ModRefines (· = ·) P m m' j :=
  have hhost : HostRespects (FuncRel BI) (closedHost (H := ℕ)) :=
    closedHost_codeParametric.respects (fun f => FuncRel.refl f)
  modRefines_of_transport hI j
    (fun h hs hc => (closure_run_transport (fun _ _ h => h) hhost hB h hs hc).imp
      fun _ h => ⟨h.1, h.2.1⟩)
    (fun h hd => closure_diverges_transport (fun _ _ h => h) hhost hB h hd)

/-- **A deferred simulation gives the `checkInst` sentence `m ⊑ m'`**, at every profile. -/
theorem modRefines_of_deferred
    (hB : Silmaril.Wasm.Binaryen.Deferred.DeferredBaseSim P (FuncRel (H := ℕ) BI) BI B)
    {m m' : Module} (hI : InstRel BI m m') (j : ℕ) : ModRefines (· = ·) P m m' j :=
  have hhost : HostRespects (FuncRel BI) (closedHost (H := ℕ)) :=
    closedHost_codeParametric.respects (fun f => FuncRel.refl f)
  modRefines_of_transport hI j
    (fun h hs hc => (Silmaril.Wasm.Binaryen.Deferred.deferred_closure_run_transport
      (fun _ _ h => h) hhost hB h hs hc).imp fun _ h => ⟨h.1, h.2.1⟩)
    (fun h hd => Silmaril.Wasm.Binaryen.Deferred.deferred_closure_diverges_transport
      (fun _ _ h => h) hhost hB h hd)

/-- `InstRel` is monotone in the source base relation. -/
theorem InstRel.mono {BI' : List Instr → List Instr → Prop} (h : ∀ x y, BI x y → BI' x y)
    {m m' : Module} (hI : InstRel BI m m') : InstRel BI' m m' := by
  refine ⟨hI.1.mono fun fi gi hf => ⟨hf.1, hf.2.1, ?_⟩, hI.2⟩
  obtain ⟨-, -, hc⟩ := hf
  revert hc
  cases fi.code <;> cases gi.code <;> simp only [FuncCodeRel] <;> try exact id
  exact fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, GuardSim.InstrsRel.mono h h₃⟩

/-- Refinement both ways is the `checkInst` equivalence. -/
theorem modEquiv_of_refines {m m' : Module} {j : ℕ} (h₁ : ModRefines (· = ·) P m m' j)
    (h₂ : ModRefines (· = ·) P m' m j) : ModEquiv (· = ·) P m m' j := by
  refine ⟨h₁, fun vs hok b hb => ?_⟩
  obtain ⟨b', hb', rfl⟩ := h₂ vs hok b hb
  exact ⟨b, hb', rfl⟩

end Silmaril.Wasm.FnInst.Ground.Check
