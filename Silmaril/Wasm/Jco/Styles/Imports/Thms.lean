module

public import Silmaril.Wasm.Jco.Styles.Imports.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms

/-!
# World imports: the behaviour theorem

* `lowerBytes_agree`: storing bytes through a `realloc` that answers `realloc(0, 0, 1, n)` as
  `alloc(n, 1)` is the C convention's copy.
* `imps_wrapI`: the imports `wrapI md` gives the core instance (`canon lower` through the
  adaptor's `cabi_realloc`) **are** the C convention's imports (`IMeta.specImports`).
* **`wrapI_correct`**: for an instance that conforms with every choice of imports, calling export
  `name` of `wrapI md` is world function `name` under the C convention with imports. This extends
  `wrap_correct` to worlds with imports.
* `wrapI_ofCore`: for an instance without imports, `wrapI` behaves as `wrap` (so `wrap_correct`
  is the import-free case), and `spec_ofCore`: the C convention with imports is `Meta.spec`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)
open Silmaril.Proofs.Wasm.Jco (callRef_realloc lowerParams_wrap specParams_length run_plain run_out
  callRef_shim find_liftsFrom)

theorem lowerBytes_agree (M : CoreInst) (md : Meta) {R : List Flat → RM M.St (List Flat)}
    (hR : ∀ n : Nat, R [i32n 0, i32n 0, i32n 1, i32n n] = M.call md.alloc [i32n n, i32n 1])
    (limit : Nat) (bs : List UInt8) : lowerBytes M R limit bs = md.specBytes M limit bs := by
  simp only [lowerBytes, Meta.specBytes]
  congr 1
  funext _
  rw [hR]

variable (M : ICoreInst) (H : Host M.St) (md : IMeta)

theorem find?_lowers (n : String) :
    (md.imports.map fun s => (⟨s, .adapt 0⟩ : Lower)).find? (·.sig.name == n) =
      (md.imports.find? (·.name == n)).map fun s => ⟨s, .adapt 0⟩ := by
  rw [List.find?_map]
  rfl

/-- **The lowered imports of `wrapI` are the C convention's imports.** -/
theorem imps_wrapI : (wrapI md).imps M H = md.specImports M H := by
  funext n
  unfold IComp.imps IMeta.specImports
  simp only [wrapI, find?_lowers]
  cases md.imports.find? (·.name == n) with
  | none => rfl
  | some s =>
    show canonLowerWith (M.inst noImports) (lowerBytes (M.inst noImports)
      ((wrap md.toMeta).callRef (M.inst noImports) (.adapt 0))) (H n) s = _
    rw [funext₂ (lowerBytes_agree _ md.toMeta (fun n => callRef_realloc _ md.toMeta _ _ _ _))]

theorem lowerParam_inst (a b : Imports M.St) (R : List Flat → RM M.St (List Flat))
    (t : PTy) (v : PVal) : lowerParam (M.inst a) R t v = lowerParam (M.inst b) R t v := by
  cases t <;> cases v <;> rfl

/-- Lowering does not depend on the imports. -/
theorem lowerParams_inst (a b : Imports M.St) (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal),
      lowerParams (M.inst a) R ps vs = lowerParams (M.inst b) R ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    simp only [lowerParams, lowerParam_inst M a b R t v, lowerParams_inst a b R ts vs]

/-- One export of `wrapI`: lowering through the `realloc` shim without imports, the export shim
with the lowered imports. -/
theorem canonCall_wrapI (hC : md.Conforms M) (s : Sig) (hs : s ∈ md.world) (vs : List PVal) :
    canonCall (M.inst (md.specImports M H))
        ((wrap md.toMeta).callRef (M.inst noImports) (.adapt 0))
        ((exportShim md.toMeta s).run (M.inst (md.specImports M H))) s vs =
      md.specCall M H s vs := by
  unfold canonCall IMeta.specCall
  rw [lowerParams_inst M _ noImports, lowerParams_wrap]
  refine RM.bind_congr_returns (specParams_length _ md.toMeta _ _) ?_
  intro xs hx
  cases h : inMem s.result
  · rw [run_plain _ md.toMeta s h xs hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [run_out _ md.toMeta (hC _) s hs h xs hx]
    simp only [↓reduceIte, RM.bind_assoc, RM.pure_bind]

/-- **The behaviour theorem with world imports.** -/
theorem wrapI_correct (hC : md.Conforms M) (name : String) (vs : List PVal) :
    (wrapI md).callExport M H name vs = md.spec M H name vs := by
  have hl : (wrapI md).comp.lifts = liftsFrom 0 md.world := rfl
  unfold IComp.callExport IMeta.spec
  rw [hl, imps_wrapI]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx]
    show canonCall _ _ ((wrap md.toMeta).callRef _ (.adapt (i + 1))) s vs = _
    rw [callRef_shim _ md.toMeta i s hi]
    exact canonCall_wrapI M H md hC s (List.mem_of_getElem? hi) vs

/-- Without imports, the C convention with imports is `Meta.spec`. -/
theorem spec_ofCore (N : CoreInst) (H : Host N.St) :
    md.spec (ICoreInst.ofCore N) H = md.toMeta.spec N := by
  funext name vs
  unfold IMeta.spec Meta.spec
  cases md.world.find? (·.name == name) <;> rfl

/-- **`wrap_correct` is the import-free case**: over an instance without imports, `wrapI md`
behaves as `wrap md.toMeta`. -/
theorem wrapI_ofCore (N : CoreInst) (H : Host N.St) (hC : md.toMeta.Conforms N) :
    (wrapI md).callExport (ICoreInst.ofCore N) H = (wrap md.toMeta).callExport N := by
  funext name vs
  rw [wrapI_correct (ICoreInst.ofCore N) H md (fun _ => hC), spec_ofCore md N H, wrap_correct N md.toMeta hC]

end Silmaril.Wasm.Jco
