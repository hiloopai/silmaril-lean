module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.PrimsVec

/-!
# Round 7, the whole-evaluator erasure: `BIErase` for round 6's primitives, assembled (unrefined)

The memory, type and lane primitives are strict (`oks_*`); `Prims.call` is strict away from
`$hostcall`, `$blocktype_` and `$sx` (`oks_call`); `$sx` ignores its argument and is compared
directly (`call_sx_erase`); `$utf8` is strict (`oks_utf8Call`). So `biErase_BI`: the builtins of
`utf8Env (Round4Int.BI P hn host)` satisfy `BIErase Q gd` whenever `gd` names neither `$hostcall`
nor `$blocktype_`, and `hyps_BI` puts it into `hyps_utf8Env`.
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-! ## The memory, type and lane primitives -/

theorem nxB_leBytesV (k n : Nat) : nxB (.list (FwdMem.leBytesV k n)) = true := by
  simp only [FwdMem.leBytesV, FwdMem.bytesV]
  exact nxB_list_map _ fun _ => rfl

theorem oks_unrolldtCall (v : Value) : OKS [.val v] (Prims.unrolldtCall v) := by
  refine ⟨fun w hw => ?_⟩
  simp only [Prims.unrolldtCall] at hw
  xs_bind hw
  obtain ⟨d, hd, st, -, rfl⟩ := hw
  exact ⟨nxB_tyV _, by simp [tyInv_nx hd]⟩

theorem oks_growtableCall (tv nv rv : Value) :
    OKS [.val tv, .val nv, .val rv] (Prims.growtableCall tv nv rv) := by
  refine ⟨fun w hw => ?_⟩
  unfold Prims.growtableCall at hw
  split at hw
  · rename_i h
    obtain ⟨p, h₁, h₂, h₃⟩ := h
    xs_bind hw
    obtain ⟨t, -, rfl⟩ := hw
    refine ⟨by simp [tableInstToValue, CT], ?_⟩
    subst h₁ h₂ h₃
    simp [tableInstToValue, CT]
  · cases hw

theorem oks_growmemCall (mv nv : Value) : OKS [.val mv, .val nv] (Prims.growmemCall mv nv) := by
  refine ⟨fun w hw => ?_⟩
  unfold Prims.growmemCall at hw
  split at hw
  · rename_i h
    obtain ⟨p, h₁, h₂⟩ := h
    xs_bind hw
    obtain ⟨t, -, rfl⟩ := hw
    refine ⟨by simp [memInstToValue], ?_⟩
    subst h₁ h₂
    simp [memInstToValue]
  · cases hw

theorem oks_nbytesCall (nt c : Value) : OKS [.val nt, .val c] (FwdMem.nbytesCall nt c) := by
  refine ⟨fun w hw => ?_⟩
  simp only [FwdMem.nbytesCall] at hw
  xs_bind hw
  obtain ⟨t, ht, b, hb, rfl⟩ := hw
  exact ⟨nxB_leBytesV _ _, by simp [decNumType_nx ht, decNum_nx hb]⟩

theorem oks_ibytesCall (N c : Value) : OKS [.val N, .val c] (FwdMem.ibytesCall N c) := by
  refine ⟨fun w hw => ?_⟩
  unfold FwdMem.ibytesCall at hw
  split at hw
  · cases hw
    exact ⟨nxB_leBytesV _ _, by simp⟩
  · cases hw

theorem oks_zbytesCall (zt c : Value) : OKS [.val zt, .val c] (ZBytes.zbytesCall zt c) := by
  refine ⟨fun w hw => ?_⟩
  unfold ZBytes.zbytesCall at hw
  split at hw
  all_goals first
    | exact (oks_nbytesCall zt c).ok w hw
    | (obtain ⟨h₁, h₂⟩ := (oks_ibytesCall _ c).ok w hw
       simp only [valsNx_cons_val] at h₂
       exact ⟨h₁, by simp [h₂.2.1]⟩)

theorem oks_lanesCall (sv v : Value) : OKS [.val sv, .val v] (Round5.Simd.lanesCall sv v) := by
  refine ⟨fun w hw => ?_⟩
  unfold Round5.Simd.lanesCall at hw
  split at hw
  · rename_i h
    obtain ⟨p, h₁, h₂⟩ := h
    cases hw
    refine ⟨?_, by subst h₁ h₂; simp [nxB_pctV]⟩
    simp only [Round5.Simd.lanesV]
    refine nxB_list_map _ fun x => ?_
    unfold Round5.Simd.laneV
    split
    · rfl
    · exact nxB_floatV _ _
    · exact nxB_floatV _ _
  · cases hw

theorem nxB_lanesV (sh : Silmaril.Wasm.Shape) (a : Silmaril.Wasm.Numerics.V128) :
    nxB (.list (Round5.Simd.lanesV sh a)) = true := by
  simp only [Round5.Simd.lanesV]
  refine nxB_list_map _ fun x => ?_
  unfold Round5.Simd.laneV
  split
  · rfl
  · exact nxB_floatV _ _
  · exact nxB_floatV _ _

theorem oks_invLanesCall (sv lv : Value) :
    OKS [.val sv, .val lv] (Round5.Simd.invLanesCall sv lv) := by
  refine ⟨fun w hw => ?_⟩
  unfold Round5.Simd.invLanesCall at hw
  split at hw
  · rename_i h
    obtain ⟨p, h₁, h₂⟩ := h
    cases hw
    refine ⟨rfl, ?_⟩
    subst h₁ h₂
    simp only [valsNx_cons_val, nxB_shapeV, nxB_lanesV, valsNx_nil, and_self]
  · cases hw


/-! ## `$utf8` -/

theorem charCodes_nx : ∀ (cs : List Value) (ns : List Nat),
    cs.mapM Round6.MemSimd.charCode? = some ns → ∀ c ∈ cs, nxB c = true
  | [], _, _, c, hc => by cases hc
  | a :: cs, ns, h, c, hc => by
    rw [List.mapM_cons] at h
    xs_bind h
    obtain ⟨n, hn, ns', hns', -⟩ := h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact charCode?_nx hn
    · exact charCodes_nx cs ns' hns' c hc

theorem oks_utf8Call (ws : List ArgV) : OKS ws (Round6.MemSimd.utf8Call ws) := by
  refine ⟨fun w hw => ?_⟩
  unfold Round6.MemSimd.utf8Call at hw
  split at hw
  · rename_i cs
    xs_bind hw
    obtain ⟨ns, hns, rfl⟩ := hw
    refine ⟨?_, ?_⟩
    · simp only [nxB_list, nxBs_eq_all, List.all_eq_true, List.mem_flatMap]
      rintro u ⟨n, -, hu⟩
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hu
      rfl
    · simp only [valsNx_cons_val, nxB_list, nxBs_eq_all, valsNx_nil, and_true,
        List.all_eq_true]
      exact charCodes_nx cs ns hns
  · cases hw

/-! ## All of round 6's primitives -/

section
attribute [local irreducible] Prims.hostcallCall Prims.unrolldtCall Prims.blocktypeCall
  Prims.growtableCall Prims.growmemCall FwdMem.nbytesCall FwdMem.ibytesCall ZBytes.zbytesCall
  FwdSimdAgg.vvCall Round5.Simd.lanesCall Round5.Simd.invLanesCall Round5.Simd.vecOpCall

theorem oks_call {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {x : IL.Id} (h₁ : x ≠ "hostcall")
    (h₂ : x ≠ "blocktype_") (h₃ : x ≠ "sx") (ws : List ArgV) :
    OKS ws (Prims.call P hn host x ws) := by
  unfold Prims.call
  split
  · rename_i v hv
    exact ⟨fun w hw => by cases hw; exact (oks_floatCall P x ws).ok v hv⟩
  · split
    · rename_i v hv
      exact ⟨fun w hw => by cases hw; exact (oks_intCall x ws).ok v hv⟩
    · delta Prims.call.match_1
      xs_tree (first
        | exact oks_unrolldtCall _
        | exact oks_growtableCall _ _ _
        | exact oks_growmemCall _ _
        | exact oks_nbytesCall _ _
        | exact oks_ibytesCall _ _
        | exact oks_zbytesCall _ _
        | exact oks_vvCall (by decide) _
        | exact oks_lanesCall _ _
        | exact oks_invLanesCall _ _
        | exact oks_vecOpCall _ _ _)
end

/-! ## `$sx` -/

theorem floatCall_sx (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    Floats.floatCall P "sx" ws = none := by
  unfold Floats.floatCall
  simp [Floats.floatNames]

theorem intCall_sx (ws : List ArgV) : IntNumeric.intCall "sx" ws = none := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_3
  simp only [String.reduceEq, ↓reduceDIte]

theorem call_sx {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (ws : List ArgV) :
    Prims.call P hn host "sx" ws = FwdSimdAgg.vvCall "sx" ws := by
  unfold Prims.call
  rw [floatCall_sx, intCall_sx]
  delta Prims.call.match_1
  simp only [String.reduceEq, ↓reduceDIte]

theorem vvCall_sx_erase (ws : List ArgV) :
    FwdSimdAgg.vvCall "sx" (ws.map eraseA) = FwdSimdAgg.vvCall "sx" ws := by
  unfold FwdSimdAgg.vvCall
  delta FwdSimdAgg.vvCall.match_1
  simp only [String.reduceEq, ↓reduceDIte]
  rcases ws with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try cases a
  all_goals rfl

theorem vvCall_sx_val {ws : List ArgV} {v : Value} (h : FwdSimdAgg.vvCall "sx" ws = some v) :
    v = .opt none := by
  unfold FwdSimdAgg.vvCall at h
  delta FwdSimdAgg.vvCall.match_1 at h
  simp only [String.reduceEq, ↓reduceDIte] at h
  rcases ws with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try cases a
  all_goals first | (cases h; rfl) | cases h


/-! ## `BIErase` -/

/-- **Round 6's primitives commute with erasure**, in the round-7 environment, at every `gd` that
names neither `$hostcall` nor `$blocktype_`. -/
theorem biErase_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {Q : Value → Prop} {gd : String → Bool}
    (hgd : ∀ x, gd x = true → x ≠ "hostcall" ∧ x ≠ "blocktype_") :
    BIErase Q gd (utf8Env (Round4Int.BI P hn host)) := by
  intro x ws hx _
  have hb : ∀ ws, (utf8Env (Round4Int.BI P hn host)).builtins.call x ws =
      if x = "utf8" then Round6.MemSimd.utf8Call ws else Prims.call P hn host x ws := fun _ => rfl
  rw [hb, hb]
  by_cases hu : x = "utf8"
  · rw [ite_eq_left hu, ite_eq_left hu]
    exact erase_of_oks oks_utf8Call
  · rw [ite_eq_right hu, ite_eq_right hu]
    by_cases hs : x = "sx"
    · subst hs
      rw [call_sx, call_sx, vvCall_sx_erase]
      refine ⟨?_, fun u hu => by rw [vvCall_sx_val hu]; trivial⟩
      cases h : FwdSimdAgg.vvCall "sx" ws with
      | none => rfl
      | some v => rw [vvCall_sx_val h]; rfl
    · exact erase_of_oks (oks_call P hn host (hgd x hx).1 (hgd x hx).2 hs)

/-- `gdE` names neither `$hostcall` nor `$blocktype_`: both are `excluded`. -/
theorem gdE_ne {x : String} (h : gdE x = true) : x ≠ "hostcall" ∧ x ≠ "blocktype_" := by
  unfold gdE stepReachE at h
  have hm := (List.mem_filter.1 (List.contains_iff_mem.1 h)).2
  constructor <;> rintro rfl <;> revert hm <;> decide

/-- **The hypotheses of `eraseAt` at round 6's primitives**, in the round-7 environment, at the
swap set of a configuration with `StripInj`. -/
theorem hyps_BI {H : Type} {c : Silmaril.Wasm.Execution.Core.Config H} (hinj : StripInj c)
    (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    Hyps (QC c) grE gdE (utf8Env (Round4Int.BI P hn host)) :=
  hyps_utf8Env hinj _ (biErase_BI P hn host fun _ => gdE_ne)

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
