module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Refute.CoreInv
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Refute.TestSpec
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 6: `Round5.Task.wholeStepValidSel` is false

The witness is `testCfg`: `null` and `ref.test (ref null any)` on the empty store, in a frame over
the empty module.

* It is valid (`configOk_testCfg : ConfigOk testCfg [i32]`), bounded, export-free and free of
  `FloatMissel` instructions (`boundedSel_testCfg`), so it is typed in every `simEnv B`.
* SpecTec's `Ref_ok` types `null` at `REF NULL BOT` only (`Round5.RefOk.eq_bot_of_dderives_null`,
  because `Reftype_ok` is never derivable), so `ref.test-true` cannot fire and the `otherwise`
  rule `ref.test-false` steps to `i32.const 0` (`sstep_testCfg`), in every `simEnv B`.
* Core types `null` at `REF NULL ANY` (`Round5.RefOk.refOk_nullAny`), so its only step goes to
  `i32.const 1` (`step_testCfg_inv`).

No Core successor of `testCfg` is `ConfigEq` to `testZero` (`not_configEq_testOne`), so the
backward conjunct of `Round5.Task.wholeStepValidSel` fails at `testCfg` for every `B`, encoding,
profile and host (`not_backwardSel_testCfg`): **`Round5.Task.wholeStepValidSel` is false**
(`not_wholeStepValidSel`). The forward conjunct is argued to fail there too (no SpecTec rule
reaches `i32.const 1`), but that needs an inversion of every rule and is not formalised.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Refute

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## The witness is valid and `BoundedSel` -/

/-- `ref null any`, instantiated in the empty module, is `REF NULL ANY`. -/
theorem instRef_nullAnyR : ({} : ModuleInst).instRef nullAnyR = Round5.RefOk.nullAny := rfl

/-- **The witness is valid**: `⊢ testCfg : i32`. -/
theorem configOk_testCfg : ConfigOk (testCfg (H := H)) [.num (.int .i32)] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .cons (.ref (Round5.RefOk.refOk_nullAny _)) (by simp)
      (.single (.plain (.reference (.refTest (.ref (.abs .any)) (.ref (.abs .any))
        (.refNull .heapRefl)))))⟩

/-- `i32.const b` on the empty state is valid. -/
theorem configOk_const (b : BitVec 32) :
    ConfigOk (⟨{}, ⟨[], {}⟩, [constI32 b]⟩ : Config H) [.num (.int .i32)] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .single (.plain (.numeric (.intConst _ _)))⟩

/-- A code on the empty state is `BoundedSel` when it is bounded, export-free and `AdminsSel`. -/
theorem boundedSel_empty {code : List Admin} (hb : Round4.AdminsBnd code)
    (he : Round5.Pos.AdminsNE code) (hs : Round5.Target.AdminsSel code) :
    Round5.Target.BoundedSel (⟨{}, ⟨[], {}⟩, code⟩ : Config H) :=
  ⟨⟨Round5.Target.bounded_empty hb, Round5.Target.noExports_empty he⟩,
    ⟨by simp [Round5.Target.StoreSel], hs⟩⟩

/-- **The witness is `BoundedSel`.** -/
theorem boundedSel_testCfg : Round5.Target.BoundedSel (testCfg (H := H)) :=
  boundedSel_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd])
    (by simp [Round5.Pos.AdminsNE, Round5.Pos.AdminNE])
    (by simp [Round5.Target.AdminsSel, Round5.Target.AdminSel, Round5.Target.instrSel,
      Round5.SimdTy.FloatMissel])

/-- `i32.const b` on the empty state is `BoundedSel`. -/
theorem boundedSel_const (b : BitVec 32) :
    Round5.Target.BoundedSel (⟨{}, ⟨[], {}⟩, [constI32 b]⟩ : Config H) :=
  boundedSel_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, constI32, Val.i32, Val.toAdmin,
      Round4.instrBnd])
    (by simp [Round5.Pos.AdminsNE, Round5.Pos.AdminNE, constI32, Val.i32, Val.toAdmin])
    (by simp [Round5.Target.AdminsSel, Round5.Target.AdminSel, constI32, Val.i32, Val.toAdmin,
      Round5.Target.instrSel, Round5.SimdTy.FloatMissel])

/-! ## SpecTec steps to `i32.const 0` -/

/-- SpecTec's `Ref_ok` does not type `null` at `REF NULL ANY`, under any reading of
`otherwise`. -/
theorem not_refOk_null_nullAny (B : Builtins) (hn : H → String) (O : ElseI) :
    ¬ DDerives (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn ({} : Store H), refToValue .null, CT.elemType Round5.RefOk.nullAny]) :=
  fun hd => absurd (Round5.RefOk.eq_bot_of_dderives_null B O _ Round5.RefOk.nullAny hd)
    (by simp [Round5.RefOk.nullAny])

/-- **SpecTec steps from the witness to `i32.const 0`**, in every `simEnv B`. -/
theorem sstep_testCfg (B : Builtins) (hn : H → String) :
    SStep (simEnv B) (configV hn (testCfg (H := H))) (configV hn (testZero (H := H))) :=
  fwdP_refTest0 B (s := {}) (f := ⟨[], {}⟩) (r := .null) (rt := nullAnyR)
    (not_refOk_null_nullAny B hn)
    (Round5.Target.typed_of_configOk_sel B hn configOk_testCfg boundedSel_testCfg)
    (Round5.Target.typed_of_configOk_sel B hn (configOk_const 0) (boundedSel_const 0))

/-! ## Core steps to `i32.const 1` only -/

/-- **Core's only step from the witness goes to `i32.const 1`**, under every profile and host. -/
theorem step_testCfg_inv {P : Profile} {host : HostSemantics H} {c' : Config H}
    (h : Step P host testCfg c') : c' = testOne :=
  (step_refTest_inv h rfl).elim (fun h₁ => h₁.1)
    (fun h₀ => absurd (Round5.RefOk.refOk_nullAny _) h₀.2)

/-- Core does step from the witness. -/
theorem step_testCfg (P : Profile) (host : HostSemantics H) :
    Step P host (testCfg (H := H)) testOne :=
  .reference (.testTrue (Round5.RefOk.refOk_nullAny _))

/-- `i32.const 1` agrees, up to call annotations, only with itself. -/
theorem codeEq_constI32 {b : BitVec 32} {js : List Admin}
    (h : Bwd.CodeEq [constI32 b] js) : js = [constI32 b] := by
  cases h with
  | cons ha hn =>
    cases hn
    cases ha with
    | refl => rfl
    | call h₁ _ => exact absurd h₁ (by simp [Admin.IsCallRef, constI32, Val.i32, Val.toAdmin])

/-- **No configuration `ConfigEq` to `i32.const 1` has the image of `i32.const 0`.** -/
theorem not_configEq_testOne (hn : H → String) {d : Config H} (he : Bwd.ConfigEq testOne d)
    (hw : configV hn (testZero (H := H)) = configV hn d) : False := by
  have hd : d.code = [constI32 1] := codeEq_constI32 he.2.2
  have hc : adminsToV [constI32 0] = adminsToV [constI32 1] := hd ▸ (Bwd.cfgV_inj hw).2
  have hv : adminToV (constI32 0) = adminToV (constI32 1) := List.head_eq_of_cons_eq hc
  rw [Sim.adminToV_constI32, Sim.adminToV_constI32] at hv
  simp [Silmaril.SpecTec.Equiv.Execution.pctV] at hv

/-! ## The refutation -/

/-- **The backward conjunct of `Round5.Task.wholeStepValidSel` fails at the witness**, for
every `B`, encoding, profile and host. -/
theorem not_backwardSel_testCfg (B : Builtins) (P : Profile) (host : HostSemantics H)
    (hn : H → String) :
    ¬ ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
      Round5.Target.BoundedSel c → SStep (simEnv B) (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' := fun h => by
  obtain ⟨c', d', he, hw, hs⟩ := h testCfg _ _ configOk_testCfg boundedSel_testCfg
    (sstep_testCfg B hn)
  have hc' : c' = testOne := step_testCfg_inv hs
  exact not_configEq_testOne hn (hc' ▸ he) hw

/-- **`Round5.Task.wholeStepValidSel` is false.** -/
theorem not_wholeStepValidSel : ¬ Round5.Task.wholeStepValidSel := fun h => by
  obtain ⟨B, -, hb⟩ := h Unit Round5.Pos.hnU Round5.Pos.hnU_injective Round5.Pos.divHost
    Round5.Pos.hostFinite_divHost Round5.Pos.hostOk_divHost false {}
  exact not_backwardSel_testCfg B _ Round5.Pos.divHost Round5.Pos.hnU hb

end Silmaril.Wasm.SpecTec.Sim.Round6.Refute
