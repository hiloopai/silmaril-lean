module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.EAll
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.Thms

/-!
# the 2.0 primitives commute with re-encoding export lists (unrefined)

`biSwap_storeB`: the primitives of `utf8Env20T (storeB P)` (round 6's `storeB P` with `$utf8`
answered by its UTF-8 encoding) satisfy `BIErase` at every name, for `swapX`. The argument is
round 3's strictness (`Round7.EraseAll.OKS`, read with `Round7.Swap.nxB`, "no `EXPORTS`
record"): every primitive answers only at arguments without `EXPORTS` records, with such a value,
and `swapX` keeps an `EXPORTS` record (`nxB_swapX`). Round 3 proved strictness for the float and
integer primitives and `$utf8` (`oks_floatCall'`, `oks_intCall`, `oks_utf8Call`); the 2.0 layers
`$growtable`/`$growmemory`, `$vbytes_`, `$lanes_`, `$ibytes_` and `$nbytes_` answer at images of
V2 encoders, which have no `EXPORTS` record (`Sim20.Utf8Swap.nxB_*`).

`allIn_true`: every value is in the swap set `fun _ => True`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (OKS ValsNx oks_dite oks_none valsNx_cons_val
  valsNx_nil)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## `nxX` is round 3's `nxB` -/

mutual
theorem nxX_eq_nxB : ∀ v : Value, nxX v = nxB v
  | .bool _ | .num _ | .text _ | .opt none => rfl
  | .tuple vs => nxXs_eq_nxBs vs
  | .case _ w => nxX_eq_nxB w
  | .struct gs => nxXf_eq_nxBf gs
  | .list vs => nxXs_eq_nxBs vs
  | .opt (some w) => nxX_eq_nxB w

theorem nxXs_eq_nxBs : ∀ vs : List Value, nxXs vs = nxBs vs
  | [] => rfl
  | v :: vs => by
    simp only [nxXs, nxBs]
    rw [nxX_eq_nxB v, nxXs_eq_nxBs vs]

theorem nxXf_eq_nxBf : ∀ gs : List (IL.AtomS × Value), nxXf gs = nxBf gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [nxXf, nxBf]
    rw [nxX_eq_nxB v, nxXf_eq_nxBf gs]
end

mutual
/-- **`swapX` keeps the `EXPORTS` records.** -/
theorem nxB_swapX : ∀ v : Value, nxB (swapX v) = nxB v
  | .bool _ | .num _ | .text _ | .opt none => rfl
  | .tuple vs => by simp only [swapX, nxB]; exact nxBs_swapXs vs
  | .case _ w => by simp only [swapX, nxB]; exact nxB_swapX w
  | .struct gs => by simp only [swapX, nxB]; exact nxBf_swapXf gs
  | .list vs => by simp only [swapX, nxB]; exact nxBs_swapXs vs
  | .opt (some w) => by simp only [swapX, nxB]; exact nxB_swapX w

theorem nxBs_swapXs : ∀ vs : List Value, nxBs (swapXs vs) = nxBs vs
  | [] => rfl
  | v :: vs => by
    simp only [swapXs, nxBs]
    rw [nxB_swapX v, nxBs_swapXs vs]

theorem nxBf_swapXf : ∀ gs : List (IL.AtomS × Value), nxBf (swapXf gs) = nxBf gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [swapXf, nxBf]
    rw [nxBf_swapXf gs]
    by_cases ha : a = "EXPORTS"
    · subst ha; simp
    · rw [ite_eq_right ha, nxB_swapX v]
end

mutual
/-- **`swapX` fixes values without `EXPORTS` records.** -/
theorem swapX_of_nxB : ∀ v : Value, nxB v = true → swapX v = v
  | .bool _, _ | .num _, _ | .text _, _ | .opt none, _ => rfl
  | .tuple vs, h => by simp only [swapX]; rw [swapXs_of_nxBs vs h]
  | .case _ w, h => by simp only [swapX]; rw [swapX_of_nxB w h]
  | .struct gs, h => by simp only [swapX]; rw [swapXf_of_nxBf gs h]
  | .list vs, h => by simp only [swapX]; rw [swapXs_of_nxBs vs h]
  | .opt (some w), h => by simp only [swapX]; rw [swapX_of_nxB w h]

theorem swapXs_of_nxBs : ∀ vs : List Value, nxBs vs = true → swapXs vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    simp only [swapXs]
    rw [swapX_of_nxB v h.1, swapXs_of_nxBs vs h.2]

theorem swapXf_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → swapXf gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [swapXf, h.1.2, ite_false]
    rw [swapX_of_nxB v h.1.1, swapXf_of_nxBf gs h.2]
end

/-! ## Strictness gives commutation -/

theorem valsNx_map_eraseA (ws : List ArgV) : ValsNx (ws.map eraseA) ↔ ValsNx ws := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
    cases a with
    | val w => simp only [List.map_cons, eraseA, valsNx_cons_val, nxB_swapX, ih]
    | _ =>
      simp only [List.map_cons, eraseA]
      constructor
      · intro h u hu
        rcases List.mem_cons.1 hu with hu | hu
        · cases hu
        · exact ih.1 (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) u hu
      · intro h u hu
        rcases List.mem_cons.1 hu with hu | hu
        · cases hu
        · exact ih.2 (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) u hu

theorem map_eraseA_of_valsNx : ∀ ws : List ArgV, ValsNx ws → ws.map eraseA = ws
  | [], _ => rfl
  | a :: ws, h => by
    have h' : ValsNx ws := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rw [List.map_cons, map_eraseA_of_valsNx ws h']
    cases a with
    | val w => rw [eraseA, swapX_of_nxB w (h w (List.mem_cons_self ..))]
    | _ => rfl

mutual
/-- Every value is in the swap set of every value. -/
theorem allIn_true : ∀ v : Value, AllIn (fun _ => True) v
  | .bool _ => trivial
  | .num _ => trivial
  | .text _ => trivial
  | .tuple vs => allIns_true vs
  | .case _ w => allIn_true w
  | .struct gs => ⟨fun _ => trivial, allInf_true gs⟩
  | .list vs => allIns_true vs
  | .opt none => trivial
  | .opt (some w) => allIn_true w

theorem allIns_true : ∀ vs : List Value, AllIns (fun _ => True) vs
  | [] => trivial
  | v :: vs => ⟨allIn_true v, allIns_true vs⟩

theorem allInf_true : ∀ gs : List (IL.AtomS × Value), AllInf (fun _ => True) gs
  | [] => trivial
  | (_, v) :: gs => ⟨allIn_true v, allInf_true gs⟩
end

/-- **A strict primitive commutes with `swapX`.** -/
theorem swap_of_oks {f : List ArgV → Option Value} {ws : List ArgV} (h : ∀ ws, OKS ws (f ws)) :
    f (ws.map eraseA) = (f ws).map swapX := by
  by_cases hw : ValsNx ws
  · rw [map_eraseA_of_valsNx ws hw]
    cases hf : f ws with
    | none => rfl
    | some u => simp [swapX_of_nxB u ((h ws).ok u hf).1]
  · have h₁ : f ws = none := by
      cases hf : f ws with
      | none => rfl
      | some u => exact absurd ((h ws).ok u hf).2 hw
    have h₂ : f (ws.map eraseA) = none := by
      cases hf : f (ws.map eraseA) with
      | none => rfl
      | some u => exact absurd ((valsNx_map_eraseA ws).1 ((h _).ok u hf).2) hw
    rw [h₁, h₂]
    rfl

/-! ## The 2.0 layers are strict -/

open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap in
theorem oks_growCall20 (x : IL.Id) (ws : List ArgV) : OKS ws (Whole.growCall20 x ws) := by
  unfold Whole.growCall20
  by_cases h₁ : x = "growtable"
  · simp only [h₁, ite_true]
    refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
    have hs := h.choose_spec
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hv
    refine ⟨nxB_tableInstV u, ?_⟩
    rw [hs]
    simp [nxB_tableInstV, nxB_refV]
  · simp only [h₁, ite_false]
    by_cases h₂ : x = "growmemory"
    · simp only [h₂, ite_true]
      refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
      have hs := h.choose_spec
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hv
      refine ⟨nxB_memInstV u, ?_⟩
      rw [hs]
      simp [nxB_memInstV]
    · simp only [h₂, ite_false]
      exact oks_none

open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap in
theorem oks_vbytesCall20 (ws : List ArgV) : OKS ws (Whole.vbytesCall20 ws) := by
  unfold Whole.vbytesCall20
  refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
  cases hv
  refine ⟨nxB_bytesV _, ?_⟩
  rw [h.choose_spec]
  simp

open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap in
theorem oks_lanesCall20 (ws : List ArgV) : OKS ws (Whole.lanesCall20 ws) := by
  unfold Whole.lanesCall20
  refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
  cases hv
  refine ⟨by simp [Whole.lanesV20], ?_⟩
  rw [h.choose_spec]
  have hs : ∀ sz : PackSize, nxB (Whole.shapeV20 sz) = true := fun sz => by cases sz <;> rfl
  simp only [valsNx_cons_val, valsNx_nil, and_true]
  exact ⟨hs _, rfl⟩

open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap in
theorem oks_ibytesCall20 (ws : List ArgV) : OKS ws (Whole.ibytesCall20 ws) := by
  refine ⟨fun v hv => ?_⟩
  unfold Whole.ibytesCall20 at hv
  split at hv
  · cases hv
    exact ⟨nxB_bytesV _, by simp⟩
  · cases hv

open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap in
theorem oks_nbytesCall20 (ws : List ArgV) : OKS ws (Whole.nbytesCall20 ws) := by
  unfold Whole.nbytesCall20
  refine oks_dite (fun h => ⟨fun v hv => ?_⟩) (fun _ => oks_none)
  cases hv
  refine ⟨nxB_bytesV _, ?_⟩
  rw [h.choose_spec]
  simp [nxB_numTypeV, nxB_numV]

theorem oks_floatIntB (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKS ws ((Sim.Floats.floatIntB P).call x ws) := by
  show OKS ws (if x ∈ Sim.Floats.floatNames then Sim.Floats.floatCall' P x ws
    else Sim.IntNumeric.intCall x ws)
  split
  · exact Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.oks_floatCall' P x ws
  · exact Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.oks_intCall x ws

theorem oks_storeB (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKS ws ((Whole.storeB P).call x ws) := by
  show OKS ws (if x = "nbytes_" then Whole.nbytesCall20 ws else
    if x = "lanes_" then Whole.lanesCall20 ws else if x = "ibytes_" then Whole.ibytesCall20 ws
    else if x = "vbytes_" then Whole.vbytesCall20 ws else
    if x = "growtable" ∨ x = "growmemory" then Whole.growCall20 x ws
    else (Sim.Floats.floatIntB P).call x ws)
  split
  · exact oks_nbytesCall20 ws
  split
  · exact oks_lanesCall20 ws
  split
  · exact oks_ibytesCall20 ws
  split
  · exact oks_vbytesCall20 ws
  split
  · exact oks_growCall20 x ws
  · exact oks_floatIntB P x ws

theorem oks_withUtf8 (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKS ws ((Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.withUtf8 (Whole.storeB P)).call x ws) := by
  show OKS ws ((Utf8Mono.utf8Env20T (Whole.storeB P)).builtins.call x ws)
  by_cases hx : x = "utf8"
  · subst hx
    rw [Utf8Mono.call_utf8Env20T_utf8 (Whole.storeB P) ws]
    exact Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.oks_utf8Call ws
  · rw [Utf8Mono.call_utf8Env20T_of_ne (Whole.storeB P) hx ws]
    exact oks_storeB P x ws

/-- **The primitives of `utf8Env20T (storeB P)` commute with `swapX`.** -/
theorem biSwap_storeB (P : Silmaril.Wasm.Numerics.Profile) (gd : String → Bool) :
    BIErase (fun _ => True) gd (Utf8Mono.utf8Env20T (Whole.storeB P)) := by
  intro x ws _ _
  exact ⟨swap_of_oks (oks_withUtf8 P x), fun u _ => allIn_true u⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
