module

public import Silmaril.Wasm.Jco.Async.Unified.Defs
public import Silmaril.Wasm.Jco.Async.Thms
public import Silmaril.Wasm.Jco.Styles.Unified.Thms
public import Silmaril.Proofs.Wasm.Jco.Async.Basic

/-!
# Async lifts in the unified wrapper: proofs

Proofs of `Silmaril.Wasm.Jco.Async.Unified.Thms`. The lifts of `awrapU md enc` are those of
`awrap md` with the encoding added (`lifts_awrapU`). The component underneath is
`wrapU md.sync enc` (`base_awrapU`). A synchronous lift is then `wrapU_at` over `M.withStore`,
and an async lift is the async shim over the plain export shim (`lift_awrapU`).
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Async.Unified

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Async
open Silmaril.Proofs.Wasm.Jco.Async (find_awrap find_awrap_none map_lift_zip conforms_withStore
  returns_liftFst)
open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst)

/-- Add the encoding to a lift with a style. -/
def withEncA (enc : StrEnc) (al : ALift) : AXLift := ⟨al.lift.withEnc enc, al.async⟩

theorem zip_withEnc (enc : StrEnc) : ∀ (k : Nat) (ws : List ASig),
    ((liftsFrom k (ws.map (·.sig))).map (Lift.withEnc enc)).zipWith
        (fun l s => (⟨l, s.async⟩ : AXLift)) ws =
      ((liftsFrom k (ws.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift)) ws).map
        (withEncA enc)
  | _, [] => rfl
  | k, _ :: ws => by simp [liftsFrom, zip_withEnc enc (k + 1) ws, withEncA]

theorem lifts_awrapU (md : AMeta) (enc : StrEnc) :
    (awrapU md enc).lifts =
      ((liftsFrom 0 (md.world.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift))
        md.world).map (withEncA enc) :=
  zip_withEnc enc 0 md.world

theorem map_lift_zipU (enc : StrEnc) : ∀ (k : Nat) (ws : List ASig),
    (((liftsFrom k (ws.map (·.sig))).map (Lift.withEnc enc)).zipWith
        (fun l s => (⟨l, s.async⟩ : AXLift)) ws).map (·.lift) =
      (liftsFrom k (ws.map (·.sig))).map (Lift.withEnc enc)
  | _, [] => rfl
  | k, _ :: ws => by simp [liftsFrom, map_lift_zipU enc (k + 1) ws]

theorem base_awrapU (md : AMeta) (enc : StrEnc) : (awrapU md enc).base = wrapU md.sync enc := by
  simp only [AXComp.base, wrapU, awrapU]
  rw [show md.sync.world = md.world.map (·.sig) from rfl, map_lift_zipU]

theorem find_awrapU (md : AMeta) (enc : StrEnc) (name : String) :
    (awrapU md enc).lifts.find? (·.lift.sig.name == name) =
      (((liftsFrom 0 (md.world.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift))
        md.world).find? (·.lift.sig.name == name)).map (withEncA enc) := by
  rw [lifts_awrapU, List.find?_map]
  rfl

theorem memLawful_withStore (hL : MemLawful M) : MemLawful M.withStore :=
  ⟨fun s m => hL.mem_set s.1 m, fun s m m' => by
    show (M.setMem (M.setMem s.1 m) m', s.2) = (M.setMem s.1 m', s.2)
    rw [hL.set_set]⟩

theorem conformsMV_withStore (md : Meta) (hMV : md.ConformsMV M) : md.ConformsMV M.withStore :=
  fun s hs ts ns hw xs => returns_liftFst (hMV s hs ts ns hw xs)

/-- One async lift of `awrapU`, on the plain path. -/
theorem async_lift (md : AMeta) (hC : md.sync.Conforms M) (enc : StrEnc) (i : Nat) (sig : Sig)
    (st : Style) (hi : md.sync.world[i]? = some sig) (hsp : spillOf sig.params = none)
    (hw : wideOf sig.result = none) (vs : List PVal) :
    asyncCall M ((wrapU md.sync enc).callRef M.withStore (.adapt 0))
        (shimRun M ((wrapU md.sync enc).callRef M.withStore (.adapt (i + 1))) sig.result st)
        (AComp.noCallback M) st sig vs = aspecCall M md ⟨sig, some st⟩ vs := by
  have hC' := conforms_withStore M md.sync hC
  have hsh : (wrapU md.sync enc).callRef M.withStore (.adapt (i + 1)) =
      (exportShim md.sync sig).run M.withStore := by
    rw [wrapU_shim _ _ enc i sig hi]
    simp only [exportShimU, hsp, exportShimW, hw, AFn.toX_run]
  rw [asyncCall_shim, hsh, wrapU_plain_utf8 M.withStore md.sync hC' enc i sig hi]
  rfl

/-- One lift of `awrapU`. -/
theorem lift_awrapU (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (hP : md.AsyncPlain) (enc : StrEnc) (i : Nat) (s : ASig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    (match withEncA enc (⟨⟨s.sig, .adapt (0 + i + 1), .adapt 0⟩, s.async⟩ : ALift) with
      | ⟨l, none⟩ =>
        canonCallU M.withStore l.enc ((awrapU md enc).base.callRef M.withStore l.realloc)
          ((awrapU md enc).base.callRef M.withStore l.callee) l.sig vs
      | ⟨l, some st⟩ =>
        asyncCall M ((awrapU md enc).base.callRef M.withStore l.realloc)
          (shimRun M ((awrapU md enc).base.callRef M.withStore l.callee) l.sig.result st)
          (AComp.noCallback M) st l.sig vs) =
      (match s with
        | ⟨sig, none⟩ => md.sync.specCallU M.withStore enc sig vs
        | ⟨sig, some st⟩ => aspecCall M md ⟨sig, some st⟩ vs) := by
  have hi' : md.sync.world[i]? = some s.sig := by simp [AMeta.sync, hi]
  rw [base_awrapU, Nat.zero_add]
  rcases s with ⟨sig, _ | st⟩
  · exact wrapU_at M.withStore md.sync (memLawful_withStore M hL)
      (conforms_withStore M md.sync hC) (conformsMV_withStore M md.sync hMV) enc i sig hi' vs
  · obtain ⟨hsp, hw⟩ := hP _ (List.mem_of_getElem? hi) rfl
    exact async_lift M md hC enc i sig st hi' hsp hw vs

/-- **The unified wrapper with async lifts behaves as `aspecU`.** -/
theorem awrapU_correct (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (hP : md.AsyncPlain) (enc : StrEnc) (name : String)
    (vs : List PVal) :
    (awrapU md enc).callExport M name vs = aspecU M md enc name vs := by
  unfold AXComp.callExport aspecU
  rw [find_awrapU]
  rcases h : ((liftsFrom 0 (md.world.map (·.sig))).zipWith (fun l s => (⟨l, s.async⟩ : ALift))
      md.world).find? (·.lift.sig.name == name) with _ | al
  · rw [h, find_awrap_none name 0 md.world h]
    rfl
  · obtain ⟨i, s, hi, hf, rfl⟩ := find_awrap name 0 md.world al h
    rw [h, hf, Option.map_some]
    have e := lift_awrapU M md hL hC hMV hP enc i s hi vs
    rcases s with ⟨sig, _ | st⟩ <;> exact e

/-- With `utf8` and no spilled or wide signatures, `aspecU` is `aspec`. -/
theorem aspecU_aspec (md : AMeta) (h1 : md.sync.noSpill) (h2 : md.sync.narrow) :
    aspecU M md .utf8 = aspec M md := by
  funext name vs
  unfold aspecU aspec
  cases hf : md.world.find? (·.sig.name == name) with
  | none => rfl
  | some s =>
    have hs : s.sig ∈ md.sync.world := List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
    rcases s with ⟨sig, _ | st⟩
    · show md.sync.specCallU M.withStore .utf8 sig vs = md.sync.specCall M.withStore sig vs
      simp only [Meta.specCallU, h1 _ hs, h2 _ hs]
      exact specCallE_utf8_sig M.withStore md.sync sig vs
    · rfl

end Silmaril.Proofs.Wasm.Jco.Async.Unified
