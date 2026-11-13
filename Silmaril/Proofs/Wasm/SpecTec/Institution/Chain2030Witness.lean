module

public import Silmaril.Wasm.SpecTec.Institution.Chain2030One.Defs
public import Silmaril.Wasm.SpecTec.Institution.Chain2030.Thms
public import Silmaril.Wasm.SpecTec.Institution.Cover.Thms

/-!
# The chain wasm-2.0 → wasm-3.0: concrete points of its domain

`nop nop` and `nop` on the empty store, in V2 and in Core, host-free (`Det.noHost`):

* `sim_nop`, `sim_nop1`, `sim_done`: the Core configurations simulate the V2 ones (`Sim`).
* `step_nop_inv`: host-free, `nop` in front of `rest` steps only to `rest`, through Silmaril's
  `Step.head_inv` (as an earlier `succ_boundedSel_nanCfg`).
* `domDet_coreNop`, `domDet_coreNop1`: both Core configurations are in `Wasm30.DomDet` at every
  profile: typed, `BoundedSel`, with one `BoundedSel` successor.
* `pairDom_nop`, `pairDom_nop1`: **concrete points of `PairDom`**.
* `pairDom1_nop1`: `nop` is in the one-step sub-fragment `PairDom1` at any V2 host compatible
  with `noHost` (for instance `hostCompatible_none`). Its V2 step is matched through
  `Step.toCore` and Core's determinism at `nop`; no V2 inversion is needed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Chain2030

open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type}

/-! ## `Sim` at the witnesses -/

/-- The empty V2 configuration of code `code` is well formed when its code is plain. -/
theorem configWF_plain (code : List Silmaril.Wasm.V2.Execution.Admin)
    (h : Silmaril.Wasm.V2.Execution.Admin.listWF ({} : Silmaril.Wasm.V2.Execution.Store H) code) :
    Silmaril.Wasm.V2.Execution.ConfigWF (⟨{}, {}, code⟩ : Silmaril.Wasm.V2.Execution.Config H) :=
  ⟨by simp [Silmaril.Wasm.V2.Execution.StoreWF],
    by simp [Silmaril.Wasm.V2.Execution.ModWF], h⟩

theorem sim_nop : Silmaril.Wasm.V2.Execution.Sim (Wasm20.nopCfg (H := H)) coreNop :=
  ⟨rfl, configWF_plain _ (by simp [Silmaril.Wasm.V2.Execution.Admin.listWF,
    Silmaril.Wasm.V2.Execution.Admin.WF])⟩

theorem sim_nop1 : Silmaril.Wasm.V2.Execution.Sim (v2Nop1 (H := H)) coreNop1 :=
  ⟨rfl, configWF_plain _ (by simp [Silmaril.Wasm.V2.Execution.Admin.listWF,
    Silmaril.Wasm.V2.Execution.Admin.WF])⟩

theorem sim_done : Silmaril.Wasm.V2.Execution.Sim (v2Done (H := H)) coreDone :=
  ⟨rfl, configWF_plain _ (by simp [Silmaril.Wasm.V2.Execution.Admin.listWF])⟩

/-! ## Core at `nop` -/

open Silmaril.Wasm.SingleThreaded.Det (FamShape) in
/-- A family left-hand side ending in `nop` is parametric. -/
theorem famShape_nop {k : Silmaril.Wasm.SingleThreaded.Det.Fam} {args : List Val}
    (h : FamShape k (vals args ++ [.plain .nop])) : k = .parametric := by
  obtain ⟨a', e', he, -, hk⟩ := h
  obtain rfl := List.singleton_inj.1 (List.append_inj' he rfl).2
  exact hk.symm

open Silmaril.Wasm.SingleThreaded.Det in
/-- **A head step at `nop` without operands** empties the code. -/
theorem head_nop {P : Profile} {s : Store H} {f : Frame} {c₀ : Config H}
    (h : Head P s f [] (.plain .nop) c₀) : c₀ = ⟨s, f, []⟩ := by
  cases h with
  | parametric h =>
    generalize hl : vals [] ++ [Admin.plain .nop] = l at h
    cases h <;> simp [Val.toAdmin] at hl ⊢
  | numeric h => exact absurd (famShape_nop (NumericStep.shape h)) (by decide)
  | vector h => exact absurd (famShape_nop (VectorStep.shape h)) (by decide)
  | «variable» h => exact absurd (famShape_nop (VariableStep.shape h)) (by decide)
  | table h => exact absurd (famShape_nop (TableStep.shape h)) (by decide)
  | memory h => exact absurd (famShape_nop (MemoryStep.shape h)) (by decide)
  | reference h => exact absurd (famShape_nop (RefStep.shape h)) (by decide)
  | aggregate h => exact absurd (famShape_nop (AggregateStep.shape h)) (by decide)
  | callRefFunc _ hc => exact hc.elim

/-- **Host-free, `nop` in front of `rest` steps only to `rest`.** -/
theorem step_nop_inv {P : Profile} {s : Store H} {f : Frame} {rest : List Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, Admin.plain .nop :: rest⟩ c) : c = ⟨s, f, rest⟩ := by
  have h' : Step P noHost ⟨s, f, vals [] ++ Admin.plain .nop :: rest⟩ c := h
  obtain ⟨pre, args, c₀, hw, hh, rfl⟩ := Step.head_inv h' rfl (by simp) (by simp)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hw.symm
  obtain rfl := head_nop hh
  rfl


/-- Core steps from `nop nop` to `nop`, at every host. -/
theorem step_coreNop (P : Profile) (host : HostSemantics H) :
    Step P host (coreNop (H := H)) coreNop1 := by
  show Step P host ⟨{}, ⟨[], {}⟩, vals [] ++ [.plain .nop] ++ [.plain .nop]⟩
    ⟨{}, ⟨[], {}⟩, vals [] ++ [] ++ [.plain .nop]⟩
  exact Step.ctxtInstrs (.parametric .nop) (Or.inr (List.cons_ne_nil _ _))

/-- Core steps from `nop` to the empty code, at every host. -/
theorem step_coreNop1 (P : Profile) (host : HostSemantics H) :
    Step P host (coreNop1 (H := H)) coreDone :=
  .parametric .nop

/-- The empty code does not step, at any host. -/
theorem not_step_coreDone {P : Profile} {host : HostSemantics H} {c : Config H} :
    ¬ Step P host (coreDone (H := H)) c :=
  Silmaril.Wasm.Execution.Core.Step.not_vals (vs := [])

/-- Host-free, `nop nop` steps only to `nop`. -/
theorem step_coreNop_iff {P : Profile} {c : Config H} :
    Step P noHost (coreNop (H := H)) c ↔ c = coreNop1 :=
  ⟨step_nop_inv, fun h => h ▸ step_coreNop P noHost⟩

/-- Host-free, `nop` steps only to the empty code. -/
theorem step_coreNop1_iff {P : Profile} {c : Config H} :
    Step P noHost (coreNop1 (H := H)) c ↔ c = coreDone :=
  ⟨step_nop_inv, fun h => h ▸ step_coreNop1 P noHost⟩

/-! ## The Core witnesses are in `DomDet` -/

/-- `nop nop` and `nop` code are bounded, export-free and free of `FloatMissel` code. -/
theorem boundedSel_nops (n : Nat) :
    Round5.Target.BoundedSel (⟨{}, ⟨[], {}⟩, List.replicate n (Admin.plain .nop)⟩ : Config H) := by
  refine Cover.boundedSel_empty ?_ ?_ ?_ <;> induction n <;>
    simp_all [List.replicate_succ, Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd,
      Round5.Pos.AdminsNE, Round5.Pos.AdminNE, Round5.Target.AdminsSel, Round5.Target.AdminSel,
      Round5.Target.instrSel, Round5.SimdTy.FloatMissel]

/-- `⊢ nop nop : ε`. -/
theorem configOk_coreNop : ConfigOk (coreNop (H := H)) [] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .cons (.plain (.parametric .nop)) (by simp) (.single (.plain (.parametric .nop)))⟩

/-- `⊢ nop : ε`. -/
theorem configOk_coreNop1 : ConfigOk (coreNop1 (H := H)) [] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .single (.plain (.parametric .nop))⟩

/-- **`nop nop` is in the deterministic domain**, host-free, at every profile. -/
theorem domDet_coreNop (P : Profile) :
    Wasm30.DomDet P (noHost (H := H)) coreNop :=
  ⟨⟨⟨_, configOk_coreNop⟩, boundedSel_nops 2, fun _ h => step_coreNop_iff.1 h ▸ boundedSel_nops 1⟩,
    fun _ _ h₁ h₂ => (step_coreNop_iff.1 h₁).trans (step_coreNop_iff.1 h₂).symm⟩

/-- **`nop` is in the deterministic domain**, host-free, at every profile. -/
theorem domDet_coreNop1 (P : Profile) :
    Wasm30.DomDet P (noHost (H := H)) coreNop1 :=
  ⟨⟨⟨_, configOk_coreNop1⟩, boundedSel_nops 1, fun _ h => step_coreNop1_iff.1 h ▸ boundedSel_nops 0⟩,
    fun _ _ h₁ h₂ => (step_coreNop1_iff.1 h₁).trans (step_coreNop1_iff.1 h₂).symm⟩

/-! ## Points of `PairDom` and `PairDom1` -/

/-- **A concrete point of `PairDom`**: `nop nop` in V2 and Core, host-free, at every profile. -/
theorem pairDom_nop (P : Profile) : PairDom P (noHost (H := H)) nopPair :=
  ⟨Wasm20.domS_nopCfg, sim_nop, domDet_coreNop P⟩

/-- `nop` in V2 and Core is a point of `PairDom`. -/
theorem pairDom_nop1 (P : Profile) : PairDom P (noHost (H := H)) nop1Pair :=
  ⟨Wasm20.domS_nop1Cfg, sim_nop1, domDet_coreNop1 P⟩

/-- The V2 host with no behaviour is compatible with the host-free Core semantics. -/
theorem hostCompatible_none :
    Silmaril.Wasm.V2.Execution.HostCompatible (fun _ _ _ _ => False) (noHost (H := H)) :=
  ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- V2 steps from `nop` to the empty code. -/
theorem v2_step_nop1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H) :
    Silmaril.Wasm.V2.Execution.Step P host (v2Nop1 (H := H)) v2Done :=
  .pure .nop

/-- **`nop` is in the one-step sub-fragment**: its only V2 step is matched by its only Core
step, through `Step.toCore` and Core's determinism there. -/
theorem pairDom1_nop1 (P : Profile) {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
    (hc : Silmaril.Wasm.V2.Execution.HostCompatible host noHost) :
    PairDom1 P host (noHost (H := H)) nop1Pair := by
  refine ⟨pairDom_nop1 P, fun c' hs => ?_, fun cc' hs => ?_⟩
  · obtain ⟨cc', hrun, hsim⟩ := Silmaril.Wasm.V2.Execution.Step.toCore hc hs sim_nop1
    rcases Relation.TransGen.head'_iff.1 hrun with ⟨c₁, h₁, hrest⟩
    obtain rfl := step_coreNop1_iff.1 h₁
    rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨c₂, h₂, -⟩
    · exact ⟨_, h₁, hsim⟩
    · exact absurd h₂ not_step_coreDone
  · obtain rfl := step_coreNop1_iff.1 hs
    exact ⟨_, v2_step_nop1 P host, sim_done⟩

end Silmaril.Wasm.SpecTec.Institution.Chain2030
