module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.TypBwd
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms

/-!
# Round 7, moving derivations across erasure: at the swap set of a configuration (unrefined)

The hypotheses of the transfers, discharged at round 6's primitives and the swap set `QC c` of a
configuration with `StripInj c` whose export names are within SpecTec's bound (`NamesBnd c`):

* `qExp_QC`: the export lists of the records of `QC c` are typed, at one fuel for all of them
  (`QExp`), from `Round7.hasTyp_exportinst`;
* `hQA_QC`: the records of `QC c` are in the swap set;
* `hyps_eImg_BI`: the evaluator-level hypotheses at the erasure image `EImg (QC c)`.

Then `dderivesB_QC_fwd` and `dderivesB_QC_bwd`: **the transfers across erasure hold without
hypotheses for every relation of the checked part (`grE`)**, `otherwise` read as SpecTec reads it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (moduleInstToValue exportInstToValue)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps grE gdE InAI)

variable {H : Type}

/-! ## Export names -/

mutual
theorem modsAdmin_nb : ∀ (a : Admin), AdminNB a → ∀ m ∈ modsAdmin a, ModNamesBnd m
  | .label _ _ body, h, m, hm => modsAdmins_nb body h m hm
  | .handler _ _ body, h, m, hm => modsAdmins_nb body h m hm
  | .frame _ f body, h, m, hm => by
    simp only [modsAdmin, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact h.1
    · exact modsAdmins_nb body h.2 m hm
  | .plain _, _, m, hm => by simp [modsAdmin] at hm
  | .ref _, _, m, hm => by simp [modsAdmin] at hm
  | .callRefType _, _, m, hm => by simp [modsAdmin] at hm
  | .returnCallRefType _, _, m, hm => by simp [modsAdmin] at hm
  | .trap, _, m, hm => by simp [modsAdmin] at hm

theorem modsAdmins_nb : ∀ (l : List Admin), AdminsNB l → ∀ m ∈ modsAdmins l, ModNamesBnd m
  | [], _, m, hm => by simp [modsAdmins] at hm
  | a :: l, h, m, hm => by
    simp only [modsAdmins, List.mem_append] at hm
    rcases hm with hm | hm
    · exact modsAdmin_nb a h.1 m hm
    · exact modsAdmins_nb l h.2 m hm
end

theorem modNamesBnd_of_mods {c : Config H} (hnb : NamesBnd c) {m : ModuleInst} (hm : m ∈ mods c) :
    ModNamesBnd m := by
  simp only [mods, List.mem_append, List.mem_map, List.mem_cons] at hm
  rcases hm with ⟨fi, hfi, rfl⟩ | rfl | hm
  · exact hnb.store fi hfi
  · exact hnb.frame
  · exact modsAdmins_nb _ hnb.code m hm

theorem hasTyp_exports (B : Builtins) {m : ModuleInst} (hm : ModNamesBnd m) :
    HasTyp (utf8Env B) VarEnv.empty expT (.list (m.exports.map exportInstToValue)) := by
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_exportinst B ⟨rfl, rfl, rfl⟩ e (hm e he)

theorem exists_fuel (B : Builtins) :
    ∀ l : List ModuleInst, (∀ m ∈ l, ModNamesBnd m) → ∃ K, 2 ≤ K ∧ ∀ m ∈ l,
      hasTyp K (utf8Env B) VarEnv.empty expT (.list (m.exports.map exportInstToValue)) = .ok true
  | [], _ => ⟨2, le_refl _, fun _ hm => by cases hm⟩
  | m :: l, h => by
    obtain ⟨K, hK, hl⟩ := exists_fuel B l fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    obtain ⟨k, hk⟩ := hasTyp_exports B (h m List.mem_cons_self)
    refine ⟨max K k, le_trans hK (le_max_left _ _), fun m' hm' => ?_⟩
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact hasTyp_ok_of_le (le_max_right _ _) hk
    · exact hasTyp_ok_of_le (le_max_left _ _) (hl m' hm')

theorem exports_mem {m : ModuleInst} {gs : List (IL.AtomS × Value)}
    (hgs : moduleInstToValue Sim.CT m = .struct gs) {u : Value} (hu : ("EXPORTS", u) ∈ gs) :
    u = .list (m.exports.map exportInstToValue) := by
  simp only [moduleInstToValue, Value.struct.injEq] at hgs
  subst hgs
  simp at hu
  exact hu

theorem hasTyp_nil_expT {B : Builtins} {K : Nat} (hK : 2 ≤ K) :
    hasTyp K (utf8Env B) VarEnv.empty expT (.list []) = .ok true := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  simp [hasTyp, Value.asList?, hasTypList]

/-- **The export lists of the swap set are typed**, at one fuel. -/
theorem qExp_QC (B : Builtins) {c : Config H} (hnb : NamesBnd c) : ∃ K, QExp B K (QC c) := by
  obtain ⟨K, hK, hl⟩ := exists_fuel B (mods c) fun m hm => modNamesBnd_of_mods hnb hm
  refine ⟨K, fun r hr gs hgs u hu => ?_⟩
  rcases hr with ⟨m, hm, rfl⟩ | ⟨m, hm₀, rfl, -⟩
  · rw [exports_mem hgs hu]; exact hl m hm
  · rw [exports_mem hgs hu, hm₀]; exact hasTyp_nil_expT hK

/-- **The records of the swap set are in the swap set.** -/
theorem hQA_QC {c : Config H} : ∀ r, QC c r → AllIn (QC c) r := by
  intro r hr
  rcases hr with ⟨m, hm, rfl⟩ | ⟨m, hm₀, rfl, hm⟩
  · exact allIn_moduleInstToValue (Or.inl ⟨m, hm, rfl⟩)
  · exact allIn_moduleInstToValue (Or.inr ⟨m, hm₀, rfl, hm⟩)

/-- **The evaluator-level hypotheses at the erasure image**, at round 6's primitives. -/
theorem hyps_eImg_BI {c : Config H} (hinj : StripInj c) (P : Silmaril.Wasm.Numerics.Profile)
    (hn : H → String) (host : HostSemantics H) :
    Hyps (EImg (QC c)) grE gdE (utf8Env (Round4Int.BI P hn host)) :=
  hyps_eImg (EraseAll.hyps_BI hinj P hn host) (EraseAll.qShape_QC c)
    (EraseAll.biErase_BI P hn host fun _ hx => EraseAll.gdE_ne hx)

/-! ## The transfers at a configuration -/

section
variable {c : Config H} (hinj : StripInj c) (hnb : NamesBnd c)
  (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String) (host : HostSemantics H)
include hinj hnb

/-- **A derivation of a checked relation at a swap-set input goes to the erased side.** -/
theorem dderivesB_QC_fwd {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : grE x = true) (hin : InAI (QC c) v)
    (h : Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
      (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op args v) :
    Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
        (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op (args.map eraseA)
        (eraseV v) ∧ AllIn (QC c) v := by
  have H := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  exact dderivesB_erase_fwd gFacts_E H (hyps_eImg_BI hinj P hn host) (typFwd_utf8Env H)
    (typBwd_utf8Env H hK) hQA_QC hx hin h

/-- **A derivation of a checked relation on the erased side at an erased input comes back.** -/
theorem dderivesB_QC_bwd {x : IL.Id} {op : MixopS} {args' : List ArgV} {v' : Value}
    (hx : grE x = true) (hin : InAI (EImg (QC c)) v')
    (h : Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
      (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op args' v') :
    args' = [] ∧ Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
        (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op []
        (unerase (QC c) v') ∧ AllIn (EImg (QC c)) v' := by
  have H := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  exact dderivesB_erase_bwd gFacts_E H (hyps_eImg_BI hinj P hn host) (typFwd_utf8Env H)
    (typBwd_utf8Env H hK) hQA_QC hx hin h

end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
