module

public import Silmaril.Wasm.Jco.Styles.Unified.Defs
public import Silmaril.Wasm.Jco.Styles.EncWrap.Thms
public import Silmaril.Wasm.Jco.Styles.Spill.Thms
public import Silmaril.Wasm.Jco.Styles.Wide.Thms
import Silmaril.Proofs.Wasm.Jco.Styles.Unified

/-!
# One wrapper covering the FFI styles: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Styles.Unified`.

* **`wrapU_correct`**: for a module with a lawful memory (`MemLawful`) that conforms to the C
  convention (`Conforms`) and to the multi-value style (`ConformsMV`), the unified wrapper
  `wrapU md enc` behaves as the unified convention `md.specU M enc` on every export. Spilled
  parameters, wide results with parameters at the encoding `enc`, and encoded strings are
  covered in one component.
* Reductions to each variant, as equations of behaviours:
  - **`wrapU_wrapE`**: without spilled or wide signatures, `wrapU md enc` is `wrapE md enc`;
  - **`wrapU_wrapS`**: with `utf8` and no wide result, `wrapU md .utf8` is `wrapS md`;
  - **`wrapU_wrapW`**: with `utf8` and no spilled signature, `wrapU md .utf8` is `wrapW md`;
  - **`wrapU_wrap`**: with `utf8` and neither, `wrapU md .utf8` is `wrap md`.

  The conventions reduce in the same way (`specU_E`, `specU_S`, `specU_W`, `specU_spec`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

variable (M : CoreInst) (md : Meta)

/-- **The unified wrapper behaves as the unified convention.** -/
theorem wrapU_correct (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (enc : StrEnc) (name : String) (vs : List PVal) :
    (wrapU md enc).callExportWith M (canonCallU M) name vs = md.specU M enc name vs :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.wrapU_correct M md hL hC hMV enc name vs

/-- Without spilled or wide signatures the unified convention is the encoded one. -/
theorem specU_E (enc : StrEnc) (h1 : md.noSpill) (h2 : md.narrow) :
    md.specU M enc = md.specE M enc :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.specU_E M md enc h1 h2

/-- With `utf8` and no wide result it is the spilling convention. -/
theorem specU_S (h2 : md.narrow) : md.specU M .utf8 = md.specS M :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.specU_S M md h2

/-- With `utf8` and no spilled signature it is the multi-value style. -/
theorem specU_W (h1 : md.noSpill) : md.specU M .utf8 = md.specW M :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.specU_W M md h1

/-- With `utf8` and neither, it is the C convention. -/
theorem specU_spec (h1 : md.noSpill) (h2 : md.narrow) : md.specU M .utf8 = md.spec M := by
  rw [specU_S M md h2, specS_noSpill M md h1]

/-- **The unified wrapper reduces to the encoded wrapper.** -/
theorem wrapU_wrapE (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (enc : StrEnc) (h1 : md.noSpill) (h2 : md.narrow) :
    (wrapU md enc).callExportWith M (canonCallU M) =
      (wrapE md enc).callExportWith M (canonCallE M) := by
  funext name vs
  rw [wrapU_correct M md hL hC hMV, specU_E M md enc h1 h2, wrapE_correct M md hC]

/-- **The unified wrapper reduces to the spilling wrapper.** -/
theorem wrapU_wrapS (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (h2 : md.narrow) :
    (wrapU md .utf8).callExportWith M (canonCallU M) =
      (wrapS md).callExportWith M (fun _ => canonCallS M) := by
  funext name vs
  rw [wrapU_correct M md hL hC hMV, specU_S M md h2, wrapS_correct M md hL hC]

/-- **The unified wrapper reduces to the multi-value wrapper.** -/
theorem wrapU_wrapW (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (h1 : md.noSpill) :
    (wrapU md .utf8).callExportWith M (canonCallU M) =
      (wrapW md).callExportWith M (fun _ => canonCallW M) := by
  funext name vs
  rw [wrapU_correct M md hL hC hMV, specU_W M md h1, wrapW_correct M md hL hC hMV]

/-- **The unified wrapper reduces to `wrap`.** -/
theorem wrapU_wrap (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M)
    (h1 : md.noSpill) (h2 : md.narrow) :
    (wrapU md .utf8).callExportWith M (canonCallU M) = (wrap md).callExport M := by
  funext name vs
  rw [wrapU_correct M md hL hC hMV, specU_spec M md h1 h2, wrap_correct M md hC]

end Silmaril.Wasm.Jco

namespace Silmaril.Wasm.Jco

variable (M : CoreInst) (md : Meta)

/-- The lift of world function `i` of the unified wrapper. -/
theorem wrapU_at (hL : MemLawful M) (hC : md.Conforms M) (hMV : md.ConformsMV M) (enc : StrEnc)
    (i : Nat) (s : Sig) (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallU M enc ((wrapU md enc).callRef M (.adapt 0)) ((wrapU md enc).callRef M (.adapt (i + 1)))
      s vs = md.specCallU M enc s vs :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.wrapU_at M md hL hC hMV enc i s hi vs

/-- The encoded path of the unified wrapper, at `utf8`, is the C convention. -/
theorem wrapU_plain_utf8 (hC : md.Conforms M) (enc : StrEnc) (i : Nat) (s : Sig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCall M ((wrapU md enc).callRef M (.adapt 0)) ((exportShim md s).run M) s vs =
      md.specCall M s vs := by
  rw [← canonCallE_utf8, ← Silmaril.Proofs.Wasm.Jco.Styles.Unified.specCallE_utf8_call]
  have e := Silmaril.Proofs.Wasm.Jco.Styles.Unified.canonCallE_plainU M md hC .utf8 i s hi vs
  rw [Silmaril.Proofs.Wasm.Jco.Styles.Unified.wrapU_realloc0] at e ⊢
  exact e

/-- The C convention with `utf8`, one world function. -/
theorem specCallE_utf8_sig (s : Sig) (vs : List PVal) :
    md.specCallE M .utf8 s vs = md.specCall M s vs :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.specCallE_utf8_call M md s vs

theorem wrapU_shim (enc : StrEnc) (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrapU md enc).callRef M (.adapt (i + 1)) = (exportShimU md s).run M :=
  Silmaril.Proofs.Wasm.Jco.Styles.Unified.wrapU_shim M md enc i s hi

end Silmaril.Wasm.Jco
