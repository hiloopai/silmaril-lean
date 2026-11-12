module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdBytes
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble11
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdWhole

/-!
# One set of builtins for both 1.0 halves: `bytesB10` (round 4, pass 2)

Round 2 proved the backward half at `floatIntB` (`Task.wholeStepBwd10`), where `$bytes_`,
`$ibytes_` and `$growmemory` are inert, and pass 1 proved the forward half at
`fwdB10 nd r = bytesB10 (Profile.spec nd r)`, which answers them. This module proves the backward
half at `fwdB10 nd r` too, so one environment carries both halves.

* The rules inert at `floatIntB` are real obligations at `bytesB10`: `load-num-val`,
  `load-pack-val` and `memory.grow-succeed` are V1 steps backwards (`BwdBytes`).
* `store-num-val` and `store-pack-val` (`Step` 8, 10) still cannot be matched: no 1.0 `STORE` is
  IL-typed (`not_typedV_store10`). The backward recursion therefore runs under `GoodT10`:
  `GoodV1` and a typed code image. `GoodT10` passes to label and frame bodies and to infixes
  (`cfgInv_goodT10`, by `label_inv10`, `frame_inv10`), and at typed code the two store rules do
  not fire (`not_fires_storeTyped10`). The forward half covers stores only vacuously for the same
  reason (`FwdStoreVac`).
* **`Task.wholeStepBwd10B`** (frozen, proved by `wholeStepBwd10B`): the backward half at
  `fwdB10 nd r`, from a typed image of a `GoodV1` configuration. It is the statement of
  `Task.wholeStepBwd10` with `floatIntB` replaced by `bytesB10`.
* **`wholeStep10_both`**: at `fwdB10 nd r`, from a typed, `GoodV1`, `Plain10`, aligned
  configuration, a step of the 1.0 script to `w` exists exactly when V1 steps to a configuration
  whose image is `w` (given `hn` injective).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GoodV1 GSetOk)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-! ## The invariant -/

/-- `GoodV1` and a typed code image. -/
def GoodT10 (B : Builtins) (c : Config H) : Prop :=
  GoodV1 c ∧ TypedV (simEnv10 B) adminsT (.list (adminsToV c.code))

/-- **`GoodT10` passes to label and frame bodies and to infixes.** -/
theorem cfgInv_goodT10 (B : Builtins) : CfgInv10 (GoodT10 (H := H) B) where
  label s f n cont body h := by
    have ha : TypedV (simEnv10 B) adminT10 (adminToV (.label n cont body)) :=
      typedV_admin_of_mem10 h.2 (List.mem_singleton_self _)
    exact ⟨cfgInv_goodV1.label s f n cont body h.1, (label_inv10 ha).2.2⟩
  frame s f n fi body h := by
    have ha : TypedV (simEnv10 B) adminT10 (adminToV (.frame n fi body)) :=
      typedV_admin_of_mem10 h.2 (List.mem_singleton_self _)
    exact ⟨cfgInv_goodV1.frame s f n fi body h.1, (frame_inv10 ha).2.2⟩
  mid s f l₁ l l₂ h := by
    refine ⟨cfgInv_goodV1.mid s f l₁ l l₂ h.1, typedV_admins_of10 fun a ha => ?_⟩
    exact typedV_admin_of_mem10 h.2 (List.mem_append_left _ (List.mem_append_right _ ha))

/-! ## The store rules at typed code -/

theorem hasRuleAt10_storeLhs (B : Builtins) {k : Nat} (hk : k = 8 ∨ k = 10) :
    ∃ nm qs e₁ e₂ args rh prems, HasRuleAt (simEnv10 B) "Step" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z",
        .listE [e₁, e₂, .caseE "STORE" args]]), rh]) prems) := by
  rcases hk with rfl | rfl
  · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩

/-- **`store-num-val` and `store-pack-val` do not fire at typed code**, at every builtins. -/
theorem not_fires_storeTyped10 {B : Builtins} {k : Nat} (hk : k = 8 ∨ k = 10) {c : Config H}
    {w : Value} (hc : TypedV (simEnv10 B) adminsT (.list (adminsToV c.code)))
    (hf : Fires (simEnv10 B) "Step" k (.tuple [configV hn c, w])) : False := by
  obtain ⟨nm, qs, e₁, e₂, args, rh, prems, hr⟩ := hasRuleAt10_storeLhs B hk
  obtain ⟨σ, -, -, hes, -, -⟩ := firesCfg10_inv hr hf
  obtain ⟨a₁, a₂, a₃, hcode, -, -, h₃⟩ := codes10_three hes
  rw [hcode] at hc
  rcases head10_store (head10_of_caseE h₃) with ⟨t, p, ao, rfl⟩ | ⟨t, ao, rfl⟩
  · exact not_typed_store3 ⟨_, rfl⟩ hc
  · exact not_typed_store3 ⟨_, rfl⟩ hc

/-! ## The per-rule obligations at `bytesB10` -/

/-- The rules discharged by the generic chain of `Assemble*`, at `bytesB10`. -/
theorem bwdRest10g_bytesB10 (nd : Bool) (r : RelaxedChoice) (hn : H → String)
    (host : HostSemantics H) : BwdRest10g (bytesB10 (Profile.spec nd r)) hn host :=
  bwdRest10g_of_rest8 (bwdRest10h_of_rest9
    { pure := fun _ hi _ _ _ _ _ hf => bwd10_num (numAgree10_bytesB10 _) hi hf
      callIndirectTrap := (bwdRest10j _ hn host).callIndirectTrap })

/-- The `Step_pure` obligations at `bytesB10`. -/
theorem bwdPure10_bytesB10 {nd : Bool} {r : RelaxedChoice} {host : HostSemantics H} (i : Nat)
    (c : Config H) (w : List Value) (hg : GoodV1 c)
    (hc : Sim20.TypedSome (simEnv10 (fwdB10 nd r)) adminsT (.list (adminsToV c.code)))
    (hw : Sim20.TypedSome (simEnv10 (fwdB10 nd r)) adminsT (.list w))
    (hf : Fires (simEnv10 (fwdB10 nd r)) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    ∃ code', w = adminsToV code' ∧ PureStep c.code code' := by
  by_cases hlt : i < 29
  · by_cases hd : i ∈ pureDone10
    · exact pureDone10_bwd hd hg hf
    · by_cases ho : i ∈ pureOpen10f
      · exact (bwdRest10g_bytesB10 nd r (fun _ : H => "") host).pure i ho c w hg hc hw hf
      · have hi' : i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨
            i = 17 := by
          simp only [pureDone10, pureOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at hd ho
          omega
        rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [bwd10_labelVals hf, bwd10_brZero hf, bwd10_brSucc hf, bwd10_brTableLt hf,
          bwd10_brTableGe hf, bwd10_frameVals hf, bwd10_returnFrame hf, bwd10_returnLabel hf,
          bwd10_trapVals hf]
  · exact absurd hf (not_firesPure10_ge (by omega))

/-- The `Step_read` obligations at `bytesB10`. -/
theorem bwdRead10_bytesB10 {nd : Bool} {r : RelaxedChoice} {host : HostSemantics H} (i : Nat)
    (c : Config H) (w : List Value) (hg : GoodV1 c)
    (hc : Sim20.TypedSome (simEnv10 (fwdB10 nd r)) adminsT (.list (adminsToV c.code)))
    (hw : Sim20.TypedSome (simEnv10 (fwdB10 nd r)) adminsT (.list w))
    (hf : Fires (simEnv10 (fwdB10 nd r)) "Step_read" i (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  by_cases hlt : i < 13
  · by_cases ho : i ∈ readOpen10g
    · exact (bwdRest10g_bytesB10 nd r hn host).read i ho c w hg hc hw hf
    · have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by
        simp only [readOpen10g, List.mem_cons, List.mem_nil_iff, or_false] at ho
        omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [bwd10_block hf, bwd10_loop hf, bwd10_call hg hf, bwd10_localGet hg hf,
        bwd10_globalGet hg hf, bwd10_loadNumTrap hg hf, bwd10_loadNumVal hg hf,
        bwd10_loadPackTrap hg hf, bwd10_loadPackVal hg hf]
  · exact absurd hf (not_firesRead10_ge (by omega))

/-- The `Step` obligations at `bytesB10`, at `GoodT10`. -/
theorem bwdStep10_bytesB10 {nd : Bool} {r : RelaxedChoice} {host : HostSemantics H} (i : Nat)
    (hi : 5 ≤ i) (c : Config H) (w : Value) (hg : GoodT10 (fwdB10 nd r) c)
    (hf : Fires (simEnv10 (fwdB10 nd r)) "Step" i (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  by_cases hlt : i < 13
  · have hi' : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bwd10_localSet hg.1 hf
    · exact bwd10_globalSet hg.1 hf
    · exact bwd10_storeNumTrap hg.1 hf
    · exact (not_fires_storeTyped10 (.inl rfl) hg.2 hf).elim
    · exact bwd10_storePackTrap hg.1 hf
    · exact (not_fires_storeTyped10 (.inr rfl) hg.2 hf).elim
    · exact bwd10_memGrowSucceed hg.1 hf
    · exact bwd10_memGrowFail hg.1 hf
  · exact absurd hf (not_firesStep10_ge (by omega))

/-- **The per-rule obligations of the 1.0 backward half at `bytesB10`**, under `GoodT10`. -/
theorem bwdParts10_bytesB10 (nd : Bool) (r : RelaxedChoice) (hn : H → String)
    (host : HostSemantics H) : BwdParts10 (GoodT10 (fwdB10 nd r)) (fwdB10 nd r) hn host where
  pure i c w hg hc hw hf := bwdPure10_bytesB10 (host := host) i c w hg.1 hc hw hf
  read i c w hg hc hw hf := bwdRead10_bytesB10 i c w hg.1 hc hw hf
  step i hi c w hg hf := bwdStep10_bytesB10 i hi c w hg hf

/-! ## The target -/

/-- **The backward half of the 1.0 whole step at the forward half's builtins** (frozen; proved
below): `Task.wholeStepBwd10` with `floatIntB` replaced by `fwdB10 nd r = bytesB10 (spec nd r)`. -/
def Task.wholeStepBwd10B : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) (c : Config H) (w : Value),
      Typed10 (simEnv10 (fwdB10 nd r)) hn c → GoodV1 c →
      SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) w →
      ∃ c', w = configV hn c' ∧ Step host c c'

/-- **`Task.wholeStepBwd10B` holds.** -/
theorem wholeStepBwd10B : Task.wholeStepBwd10B := by
  intro H hn _ host nd r c w hc hg hs
  exact backward10_of_parts (bwdParts10_bytesB10 nd r hn host) (cfgInv_goodT10 _) c w
    ⟨hg, typedV_code_of_typed10 hc⟩ hs

/-- **Both halves at one set of builtins**: at `fwdB10 nd r`, from a typed, `GoodV1`, `Plain10`
configuration with aligned memories, the 1.0 script steps to `w` exactly when V1 steps to a
configuration whose image is `w`. -/
theorem wholeStep10_both {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    {c : Config H} (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c) (hg : GoodV1 c)
    (hpl : Plain10 c.code) (hal : MemsAligned10 c.store) (w : Value) :
    SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) w ↔
      ∃ c', w = configV hn c' ∧ Step host c c' := by
  constructor
  · exact wholeStepBwd10B H hn hinj host nd r c w hc hg
  · rintro ⟨c', rfl, h⟩
    exact (wholeStepFwd10 H hn host nd r c c' hc hpl hg.2.2.2 hal h).2

end Silmaril.Wasm.SpecTec.Sim10.Whole
