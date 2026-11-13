module

public import Silmaril.Wasm.Jco.Styles.Spill.Defs
public import Silmaril.Proofs.Wasm.Jco.Styles.Spill.Shim
public import Silmaril.Wasm.Jco.Styles.Wide.Thms

/-!
# Spilled parameters: the wrapper is correct

* **`canonCallS_spill`**: for a lawful memory, the canonical spilling of the parameters through
  the adaptor's `cabi_realloc`, followed by the spill shim, is the C convention with all
  parameters flat (`Meta.specCallSpill`). The shim's loads read back the stored fields:
  `loadVal_store` for separated writes.
* **`wrapS_correct`**: so `wrapS md` behaves as `md.specS M` on every export, for a module with
  a lawful memory that conforms to the C convention.
* `specS_noSpill`, `wrapS_noSpill`: on worlds without spilled signatures this is `Meta.spec`
  and `wrap`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)
open Silmaril.Proofs.Wasm.Jco (run_plain run_out find_liftsFrom specParams_length spillShim_at
  storeAll_ok writeAll_read fieldWrites_sep scalarSize_pos bind_congr_ok bind_eq_at)

variable (M : CoreInst) (md : Meta)

theorem spillOf_some {ps : List PTy} {ts : List ValTy} {ns : List Nat}
    (h : spillOf ps = some (ts, ns)) : ts.mapM scalarSize = some ns := by
  unfold spillOf at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ts', -, ns', hns, rfl, rfl⟩ := h
    exact hns
  · cases h

theorem wrapS_realloc (a b c d : Flat) :
    (wrapS md).callRef M (.adapt 0) [a, b, c, d] = M.call md.alloc [d, c] := by
  simp only [XComp.callRef, wrapS, List.getElem?_cons_zero, AFn.toX_run]
  exact reallocShim_run M md.alloc _ _ _ _

theorem wrapS_shim (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrapS md).callRef M (.adapt (i + 1)) = (exportShimS md s).run M := by
  funext xs
  simp [XComp.callRef, wrapS, hi]

/-- One export with spilled parameters. -/
theorem canonCallS_spill (hL : MemLawful M) (s : Sig) {ts : List ValTy} {ns : List Nat}
    (hsp : spillOf s.params = some (ts, ns)) (vs : List PVal) :
    canonCallS M ((wrapS md).callRef M (.adapt 0)) ((spillShim s ts ns).run M) s vs =
      md.specCallSpill M s ts ns vs := by
  have hn := spillOf_some hsp
  unfold canonCallS Meta.specCallSpill
  simp only [hsp]
  refine RM.bind_congr fun vals => ?_
  unfold lowerSpill reallocCall
  cases hc : ValTy.checkList ts vals
  · simp only [RM.check_false, RM.fail_bind]
  · simp only [RM.check_true, RM.pure_bind, RM.bind_assoc, wrapS_realloc]
    refine RM.bind_congr fun r => RM.bind_congr fun p => RM.bind_congr fun _ => ?_
    refine bind_congr_ok fun st u st' h => ?_
    have hw := storeAll_ok M hL _ st st' u h
    have hread := writeAll_read hw (fieldWrites_sep p.toNat 0 ns (scalarSize_pos hn) ts _)
    exact bind_eq_at (spillShim_at M s hn hc hread) _

/-- One export without spilled parameters. -/
theorem canonCallS_plain (hC : md.Conforms M) (s : Sig) (hs : s ∈ md.world)
    (hsp : spillOf s.params = none) (vs : List PVal) :
    canonCallS M ((wrapS md).callRef M (.adapt 0)) ((exportShim md s).run M) s vs =
      md.specCall M s vs := by
  unfold canonCallS
  simp only [hsp]
  unfold canonCall Meta.specCall
  rw [lowerParams_agree M md (fun n => wrapS_realloc M md _ _ _ _)]
  refine RM.bind_congr_returns (specParams_length M md _ _) fun xs hx => ?_
  cases h : inMem s.result
  · rw [run_plain M md s h xs hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [run_out M md hC s hs h xs hx]
    simp only [↓reduceIte, RM.bind_assoc, RM.pure_bind]

/-- The lift of world function `i`. -/
theorem wrapS_at (hL : MemLawful M) (hC : md.Conforms M) (i : Nat) (s : Sig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallS M ((wrapS md).callRef M (.adapt 0)) ((wrapS md).callRef M (.adapt (i + 1))) s vs =
      (match spillOf s.params with
        | some (ts, ns) => md.specCallSpill M s ts ns vs
        | none => md.specCall M s vs) := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  rw [wrapS_shim M md i s hi]
  cases hsp : spillOf s.params with
  | none =>
    simp only [exportShimS, hsp, AFn.toX_run]
    exact canonCallS_plain M md hC s hs hsp vs
  | some p =>
    obtain ⟨ts, ns⟩ := p
    simp only [exportShimS, hsp]
    exact canonCallS_spill M md hL s hsp vs

theorem wrapS_find (name : String) :
    (wrapS md).lifts.find? (·.sig.name == name) =
      ((liftsFrom 0 md.world).find? (·.sig.name == name)).map
        fun l => ⟨l.sig, l.callee, l.realloc, .utf8⟩ := by
  simp only [wrapS, List.find?_map]
  rfl

/-- **The wrapper with spilled parameters behaves as the C convention with all parameters
flat.** -/
theorem wrapS_correct (hL : MemLawful M) (hC : md.Conforms M) (name : String) (vs : List PVal) :
    (wrapS md).callExportWith M (fun _ => canonCallS M) name vs = md.specS M name vs := by
  unfold XComp.callExportWith Meta.specS
  rw [wrapS_find]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]; rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    exact wrapS_at M md hL hC i s hi vs

/-- No world function spills its parameters. -/
def Meta.noSpill (md : Meta) : Prop := ∀ s ∈ md.world, spillOf s.params = none

theorem specS_noSpill (h : md.noSpill) : md.specS M = md.spec M := by
  funext name vs
  unfold Meta.specS Meta.spec
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hsp : spillOf s.params = none := h s (List.mem_of_find?_eq_some hf)
    simp only [hsp]

/-- **Without spilled signatures the wrapper is `wrap`.** -/
theorem wrapS_noSpill (hL : MemLawful M) (hC : md.Conforms M) (h : md.noSpill) :
    (wrapS md).callExportWith M (fun _ => canonCallS M) = (wrap md).callExport M := by
  funext name vs
  rw [wrapS_correct M md hL hC, specS_noSpill M md h, wrap_correct M md hC]

end Silmaril.Wasm.Jco
