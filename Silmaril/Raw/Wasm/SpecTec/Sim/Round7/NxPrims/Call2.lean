module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxPrims.Call

/-!
# Round 7, REH route 2: `BuiltinsVT` at round 4's primitives (unrefined)
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {H : Type}

theorem floatCall_hostcall (P : Numerics.Profile) (ws : List ArgV) :
    Floats.floatCall P "hostcall" ws = none := by
  unfold Floats.floatCall
  simp [Floats.floatNames]

theorem intCall_hostcall (ws : List ArgV) : IntNumeric.intCall "hostcall" ws = none := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_3
  simp only [String.reduceEq, ↓reduceDIte]

theorem call_hostcall (P : Numerics.Profile) (hn : H → String) (host : HostSemantics H)
    (ws : List ArgV) : Prims.call P hn host "hostcall" ws = Prims.hostcallCall hn host ws := by
  unfold Prims.call
  rw [floatCall_hostcall, intCall_hostcall]
  delta Prims.call.match_1
  simp only [↓reduceDIte]

theorem floatCall_blocktype (P : Numerics.Profile) (ws : List ArgV) :
    Floats.floatCall P "blocktype_" ws = none := by
  unfold Floats.floatCall
  simp [Floats.floatNames]

theorem intCall_blocktype (ws : List ArgV) : IntNumeric.intCall "blocktype_" ws = none := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_3
  simp only [String.reduceEq, ↓reduceDIte]

/-- An optional answer that is export-free when present. -/
structure NA (o : Option Value) : Prop where
  ok : ∀ v, o = some v → nxB v = true

theorem na_none : NA none := ⟨fun _ h => by cases h⟩

theorem na_dite {c : Prop} {inst : Decidable c} {t : c → Option Value}
    {e : ¬c → Option Value} (ht : ∀ h, NA (t h)) (he : ∀ h, NA (e h)) : NA (dite c t e) := by
  cases inst with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

theorem na_cast {α : Sort _} {a b : α} {m : Option Value} (h : b = a) (hm : NA m) :
    NA (Eq.ndrec_symm (motive := fun _ => Option Value) m h) := by
  cases h; exact hm

/-- Walk a decision tree of `dite`, casts and sparse case analyses for `NA`. -/
syntax "na_tree " tacticSeq : tactic
macro_rules
  | `(tactic| na_tree $leaf) => `(tactic| repeat' (first
      | exact na_none
      | contradiction
      | (apply na_dite <;> intro _)
      | (refine na_cast (by assumption) ?_)
      | xs_sc
      | ($leaf)))

theorem na_blocktypeCall (z xv : Value) : NA (Prims.blocktypeCall z xv) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Prims.blocktypeCall, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hv
  obtain ⟨_, _, _, _, _, _, _, _, p, _, rfl⟩ := hv
  simp [Exn.instrTypeV, nxB, nxBs]

section
attribute [local irreducible] Prims.hostcallCall Prims.unrolldtCall Prims.blocktypeCall
  Prims.growtableCall Prims.growmemCall FwdMem.nbytesCall FwdMem.ibytesCall ZBytes.zbytesCall
  FwdSimdAgg.vvCall Round5.Simd.lanesCall Round5.Simd.invLanesCall Round5.Simd.vecOpCall

set_option maxHeartbeats 1000000 in
theorem na_blocktype (P : Numerics.Profile) (hn : H → String) (host : HostSemantics H)
    {x : IL.Id} (hx : x = "blocktype_") (ws : List ArgV) :
    NA (Prims.call P hn host x ws) := by
  have hf : Floats.floatCall P x ws = none := hx ▸ floatCall_blocktype P ws
  have hi : IntNumeric.intCall x ws = none := hx ▸ intCall_blocktype ws
  unfold Prims.call
  rw [hf, hi]
  delta Prims.call.match_1
  na_tree (first | exact na_blocktypeCall _ _ | (exfalso; subst hx; contradiction))
end

theorem resV_hostcall (ws : List ArgV) :
    resV sigX tsigFixed "hostcall" ws = .iter (.name "hostcallresult" []) := by
  have hg : (tsigFixed.gres.lookup "hostcall").isNone = true := by decide
  have hr : atEq ((sigX.results.lookup "hostcall").getD .unk)
      (.iter (.name "hostcallresult" [])) = true := by decide
  unfold resV
  split
  · rename_i h; rw [h] at hg; cases hg
  · exact (atEq_iff _ _).1 hr

/-- **The primitives of `envBI` conform.** -/
theorem builtinsVT_BI (P : Numerics.Profile) (hn : H → String) (host : HostSemantics H) :
    BuiltinsVT sigX tsigFixed (envBI P hn host) := by
  intro f pts ws v _ _ hc
  have hb : (envBI P hn host).builtins.call f ws =
      if f = "utf8" then Round6.MemSimd.utf8Call ws else Prims.call P hn host f ws := rfl
  rw [hb] at hc
  by_cases hu : f = "utf8"
  · simp only [hu, ite_true] at hc
    exact vtB_of_nxB _ _ _ ((EraseAll.oks_utf8Call ws).ok v hc).1
  simp only [hu, ite_false] at hc
  by_cases hh : f = "hostcall"
  · subst hh
    rw [call_hostcall] at hc
    unfold Prims.hostcallCall at hc
    split at hc
    · cases hc
      rw [resV_hostcall, vtB_list_iter (b := .name "hostcallresult" []) (by decide)
        (by simp [unf, unalias]), vtL_iff]
      intro w hw
      obtain ⟨o, _, rfl⟩ := List.mem_map.1 hw
      exact vtB_outcomeV hn o
    · cases hc
  by_cases hbt : f = "blocktype_"
  · exact vtB_of_nxB _ _ _ ((na_blocktype P hn host hbt ws).ok v hc)
  by_cases hs : f = "sx"
  · subst hs
    rw [EraseAll.call_sx] at hc
    rw [EraseAll.vvCall_sx_val hc]
    exact vtB_of_nxB _ _ _ (by simp [nxB])
  · exact vtB_of_nxB _ _ _ ((EraseAll.oks_call P hn host hh hbt hs ws).ok v hc).1

end Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims
