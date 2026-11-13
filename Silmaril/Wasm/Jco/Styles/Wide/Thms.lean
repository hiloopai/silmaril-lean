module

public import Silmaril.Wasm.Jco.Styles.Wide.Defs
public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Shim

/-!
# Wide results: the multi-value wrapper is correct

Proofs of the lemmas in `Silmaril.Proofs.Wasm.Jco.Styles.Wide.*`.

* `canonCallW_narrow`: on results that are not wide, `canonCallW` is `canonCall`.
* **`wrapW_correct`**: for a module with a lawful memory (`MemLawful`) that conforms to the C
  convention (`Meta.Conforms`) and whose functions with wide results return their flat values
  (`Meta.ConformsMV`), the multi-value wrapper `wrapW md` behaves as the multi-value style
  `md.specW M` on every export. The canonical lift loads each field through the return pointer,
  and this is the flat lift of the values the function returned: the roundtrip
  `loadScalar_store`, for separated writes (`liftWide_after`).
* `thinW_callExport`: the thin wrapper of a module that returns wide results through a pointer
  itself (the canonical retptr convention) follows `canonSpecW`.
* `specW_narrow`: on worlds without wide results the multi-value style is `Meta.spec`, and
  `wrapW_narrow`: `wrapW md` behaves as `wrap md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy)
open Silmaril.Proofs.Wasm.Jco (run_plain run_out find_liftsFrom specParams_length mvShim_run
  liftWide_after)

variable (M : CoreInst) (md : Meta)

theorem canonCallW_narrow (R callee : List Flat → RM M.St (List Flat)) (sig : Sig)
    (h : wideOf sig.result = none) (vs : List PVal) :
    canonCallW M R callee sig vs = canonCall M R callee sig vs := by
  unfold canonCallW canonCall liftResultW
  simp only [h]

theorem wideOf_some {r : Option PTy} {ts : List ValTy} {ns : List Nat}
    (h : wideOf r = some (ts, ns)) : r = some (.val (.record ts)) ∧ ts.mapM scalarSize = some ns := by
  unfold wideOf at h
  split at h
  · next ts' =>
    split at h
    · cases hm : ts'.mapM scalarSize with
      | none => rw [hm] at h; cases h
      | some ns' =>
        rw [hm] at h
        cases h
        exact ⟨rfl, hm⟩
    · cases h
  · cases h

theorem wrapW_realloc (n : Nat) :
    (wrapW md).callRef M (.adapt 0) [i32n 0, i32n 0, i32n 1, i32n n] =
      M.call md.alloc [i32n n, i32n 1] := by
  simp only [XComp.callRef, wrapW, List.getElem?_cons_zero, AFn.toX_run]
  exact reallocShim_run M md.alloc _ _ _ _

theorem wrapW_shim (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrapW md).callRef M (.adapt (i + 1)) = (exportShimW md s).run M := by
  funext xs
  simp [XComp.callRef, wrapW, hi]

/-- One export with a wide result. -/
theorem canonCallW_mv (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (s : Sig) (hs : s ∈ md.world) {ts : List ValTy} {ns : List Nat}
    (hw : wideOf s.result = some (ts, ns)) (vs : List PVal) :
    canonCallW M ((wrapW md).callRef M (.adapt 0)) ((mvShim md s ts ns).run M) s vs =
      md.specCallMV M s ts ns vs := by
  obtain ⟨hr, hn⟩ := wideOf_some hw
  unfold canonCallW Meta.specCallMV
  rw [lowerParams_agree M md (wrapW_realloc M md)]
  refine RM.bind_congr_returns (specParams_length M md _ _) fun xs hx => ?_
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

/-- One export with a result that is not wide. -/
theorem canonCallW_plain (hC : md.Conforms M) (s : Sig) (hs : s ∈ md.world)
    (hw : wideOf s.result = none) (vs : List PVal) :
    canonCallW M ((wrapW md).callRef M (.adapt 0)) ((exportShim md s).run M) s vs =
      md.specCall M s vs := by
  rw [canonCallW_narrow M _ _ s hw]
  unfold canonCall Meta.specCall
  rw [lowerParams_agree M md (wrapW_realloc M md)]
  refine RM.bind_congr_returns (specParams_length M md _ _) fun xs hx => ?_
  cases h : inMem s.result
  · rw [run_plain M md s h xs hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [run_out M md hC s hs h xs hx]
    simp only [↓reduceIte, RM.bind_assoc, RM.pure_bind]

theorem wrapW_find (name : String) :
    (wrapW md).lifts.find? (·.sig.name == name) =
      ((liftsFrom 0 md.world).find? (·.sig.name == name)).map
        fun l => ⟨l.sig, l.callee, l.realloc, .utf8⟩ := by
  simp only [wrapW, List.find?_map]
  rfl

/-- The lift of world function `i`. -/
theorem wrapW_at (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M) (i : Nat)
    (s : Sig) (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallW M ((wrapW md).callRef M (.adapt 0)) ((wrapW md).callRef M (.adapt (i + 1))) s vs =
      (match wideOf s.result with
        | some (ts, ns) => md.specCallMV M s ts ns vs
        | none => md.specCall M s vs) := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  rw [wrapW_shim M md i s hi]
  cases hw : wideOf s.result with
  | none =>
    simp only [exportShimW, hw, AFn.toX_run]
    exact canonCallW_plain M md hC s hs hw vs
  | some p =>
    obtain ⟨ts, ns⟩ := p
    simp only [exportShimW, hw]
    exact canonCallW_mv M md hL hC hMV s hs hw vs

/-- **The multi-value wrapper behaves as the multi-value style.** -/
theorem wrapW_correct (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (name : String) (vs : List PVal) :
    (wrapW md).callExportWith M (fun _ => canonCallW M) name vs = md.specW M name vs := by
  unfold XComp.callExportWith Meta.specW
  rw [wrapW_find]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]; rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    exact wrapW_at M md hL hC hMV i s hi vs

/-- No world function has a wide result. -/
def Meta.narrow (md : Meta) : Prop := ∀ s ∈ md.world, wideOf s.result = none

theorem specW_narrow (h : md.narrow) : md.specW M = md.spec M := by
  funext name vs
  unfold Meta.specW Meta.spec
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hw : wideOf s.result = none := h s (List.mem_of_find?_eq_some hf)
    simp only [hw]

/-- **On worlds without wide results the multi-value wrapper is `wrap`.** -/
theorem wrapW_narrow (hL : MemLawful M) (hC : md.Conforms M) (h : md.narrow) :
    (wrapW md).callExportWith M (fun _ => canonCallW M) = (wrap md).callExport M := by
  have hMV : md.ConformsMV M := fun s hs ts ns hw => by rw [h s hs] at hw; cases hw
  funext name vs
  rw [wrapW_correct M md hL hC hMV, specW_narrow M md h, wrap_correct M md hC]

/-! ## The retptr style for wide results -/

/-- The thin wrapper of a module that returns wide results through a pointer itself (the
canonical retptr convention), with its `realloc` `r`. -/
def thinW (md : Meta) (r : String) : XComp :=
  { lifts := md.world.map fun s => ⟨s, .core s.name, .core r, .utf8⟩ }

/-- The canonical convention with wide results. -/
def canonSpecW (world : List Sig) (r : String) (name : String) (vs : List PVal) :
    RM M.St (Option PVal) :=
  match world.find? (·.name == name) with
  | some s => canonCallW M (M.call r) (M.call s.name) s vs
  | none => RM.fail

/-- The thin wrapper follows the canonical convention with wide results, for every module. -/
theorem thinW_callExport (r name : String) (vs : List PVal) :
    (thinW md r).callExportWith M (fun _ => canonCallW M) name vs = canonSpecW M md.world r name vs := by
  unfold XComp.callExportWith canonSpecW
  simp only [thinW, List.find?_map]
  have hp : ((fun x : XLift => x.sig.name == name) ∘
      fun s : Sig => ({ sig := s, callee := .core s.name, realloc := .core r, enc := .utf8 } : XLift)) =
      fun s : Sig => s.name == name := rfl
  rw [hp]
  cases md.world.find? (·.name == name) <;> rfl

end Silmaril.Wasm.Jco
