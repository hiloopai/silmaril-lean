module

public import Silmaril.Wasm.Jco.Styles.Unified.Imports.Defs
public import Silmaril.Wasm.Jco.Styles.Unified.Thms
public import Silmaril.Wasm.Jco.Styles.Imports.Thms
import Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports

/-!
# The unified wrapper with world imports: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports`. Assume that `M`'s allocator does not
depend on its imports (`IMeta.AllocIndep`), and that `M` conforms with every choice of imports.

* **`wrapUI_correct`**: `wrapUI md enc` behaves as the unified convention `specU` over the
  instance with the C convention's imports `md.specImports M H`. This covers spilled
  parameters, wide results, string encodings and world imports in one component.
* **`wrapUI_wrapI`**: with `utf8` and no spilled or wide signatures, `wrapUI md .utf8` is
  `wrapI md`.
* **`wrapUI_ofCore`**: over an instance without imports, `wrapUI md enc` is `wrapU md enc`.
* `spec_inst`: the C convention with imports is `Meta.spec` over the instance with the C
  convention's imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

variable (M : ICoreInst) (H : Host M.St) (md : IMeta)

/-- The C convention with imports, over the instance with its imports. -/
theorem spec_inst (hA : md.AllocIndep M) :
    md.spec M H = md.toMeta.spec (M.inst (md.specImports M H)) :=
  Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports.spec_inst M H md hA

/-- **The unified wrapper with world imports behaves as the unified convention.** -/
theorem wrapUI_correct (hA : md.AllocIndep M) (hL : MemLawful (M.inst noImports))
    (hC : md.Conforms M) (hMV : ∀ imps, md.toMeta.ConformsMV (M.inst imps)) (enc : StrEnc)
    (name : String) (vs : List PVal) :
    (wrapUI md enc).callExport M H name vs =
      md.toMeta.specU (M.inst (md.specImports M H)) enc name vs := by
  have hL' : MemLawful (M.inst (md.specImports M H)) := ⟨hL.mem_set, hL.set_set⟩
  rw [Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports.callExport_wrapUI M H md hA hC,
    Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports.imps_wrapUI M H md hC,
    wrapU_correct _ md.toMeta hL' (hC _) (hMV _)]

/-- **With `utf8` and no spilled or wide signatures, `wrapUI` is `wrapI`.** -/
theorem wrapUI_wrapI (hA : md.AllocIndep M) (hL : MemLawful (M.inst noImports))
    (hC : md.Conforms M) (hMV : ∀ imps, md.toMeta.ConformsMV (M.inst imps))
    (h1 : md.toMeta.noSpill) (h2 : md.toMeta.narrow) :
    (wrapUI md .utf8).callExport M H = (wrapI md).callExport M H := by
  funext name vs
  rw [wrapUI_correct M H md hA hL hC hMV, specU_spec _ md.toMeta h1 h2, wrapI_correct M H md hC,
    spec_inst M H md hA]

/-- **Without imports, `wrapUI` is `wrapU`.** -/
theorem wrapUI_ofCore (N : CoreInst) (H : Host N.St) (hC : md.toMeta.Conforms N) (enc : StrEnc) :
    (wrapUI md enc).callExport (ICoreInst.ofCore N) H =
      (wrapU md.toMeta enc).callExportWith N (canonCallU N) := by
  funext name vs
  exact Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports.callExport_wrapUI (ICoreInst.ofCore N) H md
    (fun _ _ => rfl) (fun _ => hC) enc name vs

end Silmaril.Wasm.Jco
