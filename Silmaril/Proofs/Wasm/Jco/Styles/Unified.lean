module

public import Silmaril.Wasm.Jco.Styles.Unified.Defs
public import Silmaril.Wasm.Jco.Styles.EncWrap.Thms
public import Silmaril.Wasm.Jco.Styles.Spill.Thms
public import Silmaril.Wasm.Jco.Styles.Wide.Thms

/-!
# One wrapper covering the FFI styles: proofs

Proofs of `Silmaril.Wasm.Jco.Styles.Unified.Thms`. The unified wrapper's `cabi_realloc` is the one
of `wrapE` (`wrapU_realloc0`). With old pointer `0` it is the allocator (`wrapU_realloc_zero`),
so on the spilling path it agrees with the `cabi_realloc` of `wrapS` (`lowerSpill_congr`). Each
path then reduces to the variant's own lemma: `canonCallS_spill`, the argument of
`canonCallW_mv` with encoded parameters (`canonCallWE_mv`), and `canonCallE_wrapE`.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Styles.Unified

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy)
open Silmaril.Proofs.Wasm.Jco (find_liftsFrom mvShim_run liftWide_after)

variable (M : CoreInst) (md : Meta)

/-! ## The adaptor -/

theorem wrapU_realloc0 (enc : StrEnc) :
    (wrapU md enc).callRef M (.adapt 0) = (wrapE md .utf8).callRef M (.adapt 0) := by
  funext xs
  simp [XComp.callRef, wrapU, adaptorUOf, wrapE, adaptorXOf]

theorem wrapU_shim (enc : StrEnc) (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrapU md enc).callRef M (.adapt (i + 1)) = (exportShimU md s).run M := by
  funext xs
  simp [XComp.callRef, wrapU, adaptorUOf, hi]

theorem wrapU_find (enc : StrEnc) (name : String) :
    (wrapU md enc).lifts.find? (·.sig.name == name) =
      ((liftsFrom 0 md.world).find? (·.sig.name == name)).map (Lift.withEnc enc) := by
  simp only [wrapU, List.find?_map]
  rfl

theorem wrapU_realloc_zero (hC : md.Conforms M) (enc : StrEnc) (a n : Nat) :
    (wrapU md enc).callRef M (.adapt 0) [i32n 0, i32n 0, i32n a, i32n n] =
      M.call md.alloc [i32n n, i32n a] := by
  rw [wrapU_realloc0, wrapE_realloc M md hC 0 0 a n]
  simp [reallocEmuF, reallocEmu]

theorem lowerSpill_congr {R R' : List Flat → RM M.St (List Flat)}
    (h : ∀ a n : Nat, R [i32n 0, i32n 0, i32n a, i32n n] = R' [i32n 0, i32n 0, i32n a, i32n n])
    (ts : List ValTy) (ns : List Nat) (vals : List Silmaril.Wasm.Component.Val) :
    lowerSpill M R ts ns vals = lowerSpill M R' ts ns vals := by
  simp only [lowerSpill, reallocCall, h]

/-! ## The three paths -/

/-- The spilling path. -/
theorem canonCallS_spillU (hL : MemLawful M) (hC : md.Conforms M) (enc : StrEnc) (s : Sig)
    {ts : List ValTy} {ns : List Nat} (hsp : spillOf s.params = some (ts, ns)) (vs : List PVal) :
    canonCallS M ((wrapU md enc).callRef M (.adapt 0)) ((spillShim s ts ns).run M) s vs =
      md.specCallSpill M s ts ns vs := by
  have hR : ∀ a n : Nat, (wrapU md enc).callRef M (.adapt 0) [i32n 0, i32n 0, i32n a, i32n n] =
      (wrapS md).callRef M (.adapt 0) [i32n 0, i32n 0, i32n a, i32n n] := fun a n =>
    (wrapU_realloc_zero M md hC enc a n).trans (wrapS_realloc M md _ _ _ _).symm
  have e : canonCallS M ((wrapU md enc).callRef M (.adapt 0)) ((spillShim s ts ns).run M) s vs =
      canonCallS M ((wrapS md).callRef M (.adapt 0)) ((spillShim s ts ns).run M) s vs := by
    unfold canonCallS
    simp only [hsp]
    exact RM.bind_congr fun vals => by rw [lowerSpill_congr M hR]
  rw [e]
  exact canonCallS_spill M md hL s hsp vs

/-- The multi-value path, with encoded parameters. -/
theorem canonCallWE_mv (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (enc : StrEnc) (s : Sig) (hs : s ∈ md.world) {ts : List ValTy} {ns : List Nat}
    (hw : wideOf s.result = some (ts, ns)) (vs : List PVal) :
    canonCallWE M enc ((wrapU md enc).callRef M (.adapt 0)) ((mvShim md s ts ns).run M) s vs =
      md.specCallMVE M enc s ts ns vs := by
  obtain ⟨-, hn⟩ := wideOf_some hw
  unfold canonCallWE Meta.specCallMVE
  rw [wrapU_realloc0, lowerParamsE_congr M (wrapE_realloc M md hC) enc]
  refine RM.bind_congr_returns (lowerParamsE_length M enc _ _ _) fun xs hx => ?_
  have hR := hMV s hs ts ns hw xs
  rw [mvShim_run M md s hn (hC.alloc _) xs hx hR, RM.bind_assoc]
  refine RM.bind_congr_returns hR fun rs hrs => ?_
  simp only [RM.bind_assoc]
  refine RM.bind_congr fun r => RM.bind_congr fun p => ?_
  have hl : liftResultW M s.result [Flat.i32 p] = liftWide M ts ns p := by
    simp only [liftResultW, hw]
    exact RM.pure_bind p _
  simp only [RM.pure_bind, hl]
  exact liftWide_after M hL hn hrs p

/-- The encoded path. -/
theorem canonCallE_plainU (hC : md.Conforms M) (enc : StrEnc) (i : Nat) (s : Sig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallE M enc ((wrapU md enc).callRef M (.adapt 0)) ((exportShim md s).run M) s vs =
      md.specCallE M enc s vs := by
  rw [wrapU_realloc0, ← wrapE_callRef0 M md enc, ← wrapE_shim M md enc i s hi]
  exact canonCallE_wrapE M md hC enc i s hi vs

/-- **The lift of world function `i` of the unified wrapper.** -/
theorem wrapU_at (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M) (enc : StrEnc)
    (i : Nat) (s : Sig) (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallU M enc ((wrapU md enc).callRef M (.adapt 0)) ((wrapU md enc).callRef M (.adapt (i + 1)))
      s vs = md.specCallU M enc s vs := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  rw [wrapU_shim M md enc i s hi]
  unfold canonCallU Meta.specCallU exportShimU
  cases hsp : spillOf s.params with
  | some p =>
    obtain ⟨ts, ns⟩ := p
    exact canonCallS_spillU M md hL hC enc s hsp vs
  | none =>
    cases hw : wideOf s.result with
    | some p =>
      obtain ⟨ts, ns⟩ := p
      simp only [exportShimW, hw]
      exact canonCallWE_mv M md hL hC hMV enc s hs hw vs
    | none =>
      simp only [exportShimW, hw, AFn.toX_run]
      exact canonCallE_plainU M md hC enc i s hi vs

/-- **The unified wrapper behaves as the unified convention.** -/
theorem wrapU_correct (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (enc : StrEnc) (name : String) (vs : List PVal) :
    (wrapU md enc).callExportWith M (canonCallU M) name vs = md.specU M enc name vs := by
  unfold XComp.callExportWith Meta.specU
  rw [wrapU_find]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]; rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    exact wrapU_at M md hL hC hMV enc i s hi vs

/-! ## Reductions to the variants -/

theorem specCallE_utf8_call (s : Sig) (vs : List PVal) :
    md.specCallE M .utf8 s vs = md.specCall M s vs := by
  unfold Meta.specCallE Meta.specCall
  rw [lowerParamsE_utf8, lowerParams_agree M md (reallocEmuF_zero M md)]
  simp only [liftResultE_utf8]

theorem specCallMVE_utf8 (s : Sig) (ts : List ValTy) (ns : List Nat) (vs : List PVal) :
    md.specCallMVE M .utf8 s ts ns vs = md.specCallMV M s ts ns vs := by
  unfold Meta.specCallMVE Meta.specCallMV
  rw [lowerParamsE_utf8, lowerParams_agree M md (reallocEmuF_zero M md)]

theorem specU_E (enc : StrEnc) (h1 : md.noSpill) (h2 : md.narrow) :
    md.specU M enc = md.specE M enc := by
  funext name vs
  unfold Meta.specU Meta.specE
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hs : s ∈ md.world := List.mem_of_find?_eq_some hf
    simp only [Meta.specCallU, h1 s hs, h2 s hs]

theorem specU_S (h2 : md.narrow) : md.specU M .utf8 = md.specS M := by
  funext name vs
  unfold Meta.specU Meta.specS
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hs : s ∈ md.world := List.mem_of_find?_eq_some hf
    simp only [Meta.specCallU, h2 s hs, specCallE_utf8_call]
    cases spillOf s.params <;> rfl

theorem specU_W (h1 : md.noSpill) : md.specU M .utf8 = md.specW M := by
  funext name vs
  unfold Meta.specU Meta.specW
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hs : s ∈ md.world := List.mem_of_find?_eq_some hf
    simp only [Meta.specCallU, h1 s hs]
    cases wideOf s.result with
    | none => exact specCallE_utf8_call M md s vs
    | some p => exact specCallMVE_utf8 M md s p.1 p.2 vs

end Silmaril.Proofs.Wasm.Jco.Styles.Unified
