module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact

/-!
# Store-changing `Step` facts at `Wasm30.builtins`

What is known of `Wasm30.builtins` is that on `DomDet` Core's successor is a `Step` fact of
`stepModel builtins` up to `CfgRel` (`FwdX30Fin.stepObs_builtins`). For a store-changing redex of
fixed arity (`StoreW`) this fact is already a `Step` fact; the question is which rule produced
it. At a checked flat redex (`stepOk`), it can only be a head rule of `Step` from rule 6 on at the
whole redex: `Step/pure` and `Step/read` are refuted at the whole code, `ctxt-instrs` at its
proper infixes, and the three other context rules by their constructors. So the `Step` fact at
`builtins` is the conclusion of a store-changing rule of the pinned script, whatever the
primitives. The successors are rigid (`[]`, `[TRAP]` or one value), so it is exact.

* `sstep_head_flat`: at every evaluator with the wasm-3.0 tables, a `Step` fact from `z; l`, for
  `l` of shape `FlatK k t` with `stepOk k t`, is a rule of `Step` from rule 6 on, fired at the
  whole of `z; l`.
* `stepCombos_ok`, `storeW_flat`, `StoreW.step`: the check holds at every shape of `StoreW`.
* `storeW_builtins`, `storeW_two_sided`: on `DomDet`, at a `StoreW` redex, a rule of `Step`
  from rule 6 on fires at the image of the configuration (under the reading of `stepModel`) with
  a conclusion `CfgRel`-related to Core's successor; every `Step` fact there is that successor
  up to `CfgRel`.
* `storeW_rigid`, `storeW_exact`: the conclusion is the image of Core's successor itself.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

variable {H : Type}

/-! ## The inversion -/

/-- A row of `Step` rules 3–5 that passes `chkFull` refutes a `FlatK` code. -/
theorem not_fires_ctx3 {env : Env} (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hf3 : chkFull k t (stepRestT.take 3) = true) {i : Nat} (hi3 : 3 ≤ i)
    (hi : i < 6) {z w : Value} : ¬ Fires env "Step" i (.tuple [cfgV z l, w]) := by
  refine not_fires_of_row Tb.stepT fun row hrow => ⟨_, _, .inr ⟨z, l, rfl, hl.tagsIn, rfl⟩,
    blk_full hl hf3 row (List.mem_of_getElem? (i := i - 3) ?_)⟩
  rw [List.getElem?_take_of_lt (by omega), stepRestT, List.getElem?_drop,
    Nat.add_sub_cancel' hi3]
  exact hrow

/-- `Step/pure` does not fire at a `FlatK` code whose `Step_pure` rows pass `chkFull`. -/
theorem not_pure_full {env : Env} (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hfp : chkFull k t pureInfoT = true) {z w : Value} :
    ¬ Fires env "Step" 0 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z', is, js, h₁, -, hq⟩ := inv_pure Tb.rules.pure hf
  obtain ⟨tp, rp, hrelp⟩ := Tb.pure
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
  have hl' : l = is := (cfgV_inj h₁).2
  exact not_fires_of_blk Tb.pureT (Nat.zero_le j) (fun row hrow =>
    ⟨_, _, .inl ⟨l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfp row hrow⟩) (hl' ▸ hj)

/-- `Step/read` does not fire at a `FlatK` code whose `Step_read` rows pass `chkFull`. -/
theorem not_read_full {env : Env} (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hfr : chkFull k t readInfoT = true) {z w : Value} :
    ¬ Fires env "Step" 1 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z', is, js, h₁, -, hq⟩ := inv_read Tb.rules.read hf
  obtain ⟨tr, rr, hrelr⟩ := Tb.read
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelr).1 hq
  have hl' : l = is := (cfgV_inj h₁).2
  exact not_fires_of_blk Tb.readT (Nat.zero_le j) (fun row hrow =>
    ⟨_, _, .inr ⟨z', l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfr row hrow⟩) (hl' ▸ hj)

/-- A `Step` fact fires some rule of `Step`. -/
theorem fires_of_sstep {env : Env} (Tb : Tables env) {v w : Value} (hs : SStep env v w) :
    ∃ i, Fires env "Step" i (.tuple [v, w]) := by
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  exact (dderives_iff_fires hrel).1 hs

/-- **Inversion at a checked store-changing redex**: at every evaluator with the wasm-3.0
tables, a `Step` fact from `z; l`, for `l` of shape `FlatK k t` with `stepOk k t`, is a rule of
`Step` from rule 6 on, fired at the whole of `z; l`. -/
theorem sstep_head_flat {env : Env} (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hok : stepOk k t = true) {z w : Value} (hs : SStep env (cfgV z l) w) :
    ∃ i, 6 ≤ i ∧ Fires env "Step" i (.tuple [cfgV z l, w]) := by
  obtain ⟨⟨⟨⟨⟨hp, hr⟩, hst⟩, hfp⟩, hfr⟩, hf3⟩ : ((((chkProper k t pureInfoT = true ∧
      chkProper k t readInfoT = true) ∧ chkProper k t stepRestT = true) ∧
      chkFull k t pureInfoT = true) ∧ chkFull k t readInfoT = true) ∧
      chkFull k t (stepRestT.take 3) = true := by
    simpa only [stepOk, Bool.and_eq_true] using hok
  obtain ⟨i, hf⟩ : ∃ i, Fires env "Step" i (.tuple [cfgV z l, w]) := fires_of_sstep Tb hs
  match i, hf with
  | 0, hf => exact absurd hf (not_pure_full Tb hl hfp)
  | 1, hf => exact absurd hf (not_read_full Tb hl hfr)
  | 2, hf => exact (not_ctxt Tb (fun A M C h hne => inert_of_flat Tb hl hp hr hst h hne) hf).elim
  | 3, hf => exact absurd hf (not_fires_ctx3 Tb hl hf3 (by omega) (by omega))
  | 4, hf => exact absurd hf (not_fires_ctx3 Tb hl hf3 (by omega) (by omega))
  | 5, hf => exact absurd hf (not_fires_ctx3 Tb hl hf3 (by omega) (by omega))
  | n + 6, hf => exact ⟨n + 6, by omega, hf⟩

/-! ## The check at the store-changing shapes -/

/-- `stepOk` is `stepOkN`. -/
theorem stepOk_eq (k : Nat) (t : MixopS) : stepOk k t = stepOkN k t := by
  simp only [stepOk, stepOkN, stepRestT, chkProper_eq, chkFull_eq, List.map_drop, List.map_take,
    nvT_eq]

/-- **`stepOk` at every shape of `stepCombos`**, by kernel `decide` on the `nonV` tables. -/
theorem stepCombos_ok {k : Nat} {t : MixopS} (h : (k, t) ∈ stepCombos) : stepOk k t = true := by
  have hall : stepCombos.all (fun p => stepOkN p.1 p.2) = true := by decide +kernel
  rw [stepOk_eq]
  exact List.all_eq_true.1 hall (k, t) h

/-- **Every `StoreW` redex is a checked flat redex.** -/
theorem storeW_flat {P : Profile} {c c' : Config H} (h : StoreW P c c') :
    ∃ k t, (k, t) ∈ stepCombos ∧ FlatA k t c.code := by
  cases h with
  | var h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | flat_tac
  | table h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | flat_tac
  | memory h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | flat_tac
  | aggregate h hl =>
    cases h <;> first
      | exact absurd hl (not_lastIs_of rfl rfl)
      | exact absurd hl (not_lastIs_of List.getLast?_concat rfl)
      | flat_tac

/-- A `StoreW` step is a Core step. -/
theorem StoreW.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : StoreW P c c') :
    Step P host c c' := by
  cases h with
  | var h => exact .variable h
  | table h => exact .table h
  | memory h => exact .memory h
  | aggregate h => exact .aggregate h

/-- **The successors of `StoreW` steps are rigid**: `[]`, `[TRAP]` or one value. -/
theorem storeW_rigid {P : Profile} {c c' : Config H} (h : StoreW P c c') :
    RigidV (adminsToV c'.code) := by
  cases h with
  | var h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | rigid_tac
  | table h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | rigid_tac
  | memory h hl => cases h <;> first | exact absurd hl (not_lastIs_of rfl rfl) | rigid_tac
  | aggregate h hl =>
    cases h <;> first
      | exact absurd hl (not_lastIs_of rfl rfl)
      | exact absurd hl (not_lastIs_of List.getLast?_concat rfl)
      | rigid_tac

/-! ## At `Wasm30.builtins` -/

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- **Store-changing `Step` facts at `builtins`**: on `DomDet`, at a `StoreW` redex, a rule of
`Step` from rule 6 on fires at the image of the configuration, under the reading of
`stepModel`, with a conclusion `CfgRel`-related to Core's successor. -/
theorem storeW_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (h : StoreW (Profile.spec nd r) c c') :
    ∃ i, 6 ≤ i ∧ ∃ w, Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, w]) ∧
      SpecTec.CfgRel hn (configV hn c') w := by
  obtain ⟨⟨w, hw, hrel⟩, -⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h.step
  obtain ⟨k, t, hm, hfl⟩ := storeW_flat h
  have hw' : SStep EB (configV hn c) w :=
    (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hfl.2 w).1 hw
  rw [Bwd.configV_eq] at hw'
  obtain ⟨i, hi, hfi⟩ := sstep_head_flat (tables_simEnv _) hfl.1 (stepCombos_ok hm) hw'
  rw [← Bwd.configV_eq] at hfi
  exact ⟨i, hi, w, (Round6.Reading.firesB_step_iff _ (.inr hi)).2 hfi, hrel⟩

/-- **Two-sided**: on `DomDet`, at a `StoreW` redex, a head rule of `Step` fires to Core's
successor up to `CfgRel`, and every `Step` fact of `stepModel builtins` from the configuration
is that successor up to `CfgRel`. -/
theorem storeW_two_sided {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (h : StoreW (Profile.spec nd r) c c') :
    (∃ i, 6 ≤ i ∧ ∃ w, Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, w]) ∧
      SpecTec.CfgRel hn (configV hn c') w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn c') w :=
  ⟨storeW_builtins hc h,
    (FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h.step).2⟩

/-- **Store-changing `Step` facts at `builtins`, exactly**: on `DomDet`, at a `StoreW` redex, a
rule of `Step` from rule 6 on fires at the image of the configuration with the image of Core's
successor as its conclusion, and that is the only `Step` fact there. -/
theorem storeW_exact {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (h : StoreW (Profile.spec nd r) c c') :
    (∃ i, 6 ≤ i ∧ Round6.Reading.FiresB EB "Step" i (.tuple [configV hn c, configV hn c'])) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) → w = configV hn c' := by
  obtain ⟨⟨i, hi, w, hfi, hrel⟩, hall⟩ := storeW_two_sided (hinj := hinj) (hf := hf) (hh := hh) hc h
  refine ⟨⟨i, hi, cfgRel_exact hrel (storeW_rigid h) ▸ hfi⟩, fun w' hw' => ?_⟩
  exact cfgRel_exact (hall w' hw') (storeW_rigid h)

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
