module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.QC

/-!
# Round 7, moving derivations across erasure: `Step_read` at a configuration (unrefined)

The transfers of `Round7.EraseDer.dderivesB_QC_fwd`/`_bwd`, at the enlarged checked part `grB`
(`grE` with `Step_read`, definitions `gdB`: `gdE` with `$blocktype_`). The ingredients:

* `Round7.EraseAll.hyps_B` and its erasure image `hyps_eImg_B`;
* typing (`TypFwd`, `TypBwd`) at `gdE`, which does not depend on the definition set
  (`typFwd_gd`, `typBwd_gd`), since a rule instance's scope binds no definitions;
* the mode analysis at `grB` (`dderivesB_AIg` with `gFacts_B`).

`sReadB_QC_fwd`, `sReadB_QC_bwd`: SpecTec's `Step_read` commutes with erasure on the swap set.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps grB gdB InAI)

variable {H : Type}

/-- **The evaluator-level hypotheses at the erasure image**, on the enlarged checked part. -/
theorem hyps_eImg_B {c : Config H} (hinj : StripInj c) (P : Silmaril.Wasm.Numerics.Profile)
    (hn : H → String) (host : HostSemantics H) :
    Hyps (EImg (QC c)) grB gdB (utf8Env (Round4Int.BI P hn host)) :=
  hyps_eImg (EraseAll.hyps_B hinj P hn host) (EraseAll.qShape_QC c)
    (EraseAll.biErase_BI' P hn host fun _ hx => EraseAll.gdB_ne hx)

theorem grB_stepRead : grB "Step_read" = true := by simp [grB]

section
variable {c : Config H} (hinj : StripInj c) (hnb : NamesBnd c)
  (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String) (host : HostSemantics H)
include hinj hnb

/-- **A derivation of a relation of `grB` at a swap-set input goes to the erased side.** -/
theorem dderivesB_QCB_fwd {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : grB x = true) (hin : InAI (QC c) v)
    (h : Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
      (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op args v) :
    Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
        (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op (args.map eraseA)
        (eraseV v) ∧ AllIn (QC c) v := by
  have H := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  exact dderivesB_erase_fwd gFacts_B (EraseAll.hyps_B hinj P hn host)
    (hyps_eImg_B hinj P hn host) (typFwd_gd (typFwd_utf8Env H)) (typBwd_gd (typBwd_utf8Env H hK))
    hQA_QC hx hin h

/-- **A derivation of a relation of `grB` on the erased side at an erased input comes back.** -/
theorem dderivesB_QCB_bwd {x : IL.Id} {op : MixopS} {args' : List ArgV} {v' : Value}
    (hx : grB x = true) (hin : InAI (EImg (QC c)) v')
    (h : Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
      (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op args' v') :
    args' = [] ∧ Round6.Reading.DDerivesB (utf8Env (Round4Int.BI P hn host))
        (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) x op []
        (unerase (QC c) v') ∧ AllIn (EImg (QC c)) v' := by
  have H := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  exact dderivesB_erase_bwd gFacts_B (EraseAll.hyps_B hinj P hn host)
    (hyps_eImg_B hinj P hn host) (typFwd_gd (typFwd_utf8Env H)) (typBwd_gd (typBwd_utf8Env H hK))
    hQA_QC hx hin h

/-- **`Step_read` goes to the erased side** on the swap set. -/
theorem sReadB_QC_fwd {z : Value} {js : List Value} (hz : AllIn (QC c) z)
    (h : Round6.Reading.SReadB (utf8Env (Round4Int.BI P hn host)) z js) :
    Round6.Reading.SReadB (utf8Env (Round4Int.BI P hn host)) (eraseV z) (js.map eraseV) ∧
      ∀ j ∈ js, AllIn (QC c) j := by
  obtain ⟨h₁, h₂⟩ := dderivesB_QCB_fwd hinj hnb P hn host grB_stepRead
    (inAI_of_pair hz) h
  refine ⟨?_, fun j hj => ?_⟩
  · simpa [Round6.Reading.SReadB, eraseV, eraseVs_eq_map] using h₁
  · exact EraseAll.ai_list.1 (EraseAll.ai_tuple.1 h₂ _ (by simp)) j hj

end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
