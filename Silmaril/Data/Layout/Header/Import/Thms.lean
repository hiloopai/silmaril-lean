module

public import Silmaril.Data.Layout.Header.Import.Defs
import Silmaril.Proofs.Data.Layout.Header.Import

/-!
# The clang import: general theorems

PROVED (standard axioms):

* `importNodes_length`: **no declaration is dropped**: the import has one entry per top-level
  node of the document, whether or not the strict decoder accepts it;
* `ofJson_provenance`: the import keeps the provenance it is given;
* `Imported.eq_of`: an import is determined by its provenance, entries and error, so a pinned
  import is pinned by one kernel computation of its entries (`Pinned.import_<name>`);
* `mem_names_of_proto`: a name with a prototype is one of the header's names.

The theorems about the pinned artifacts are in `Header.Import.Pinned.Thms`.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import

theorem importNodes_length (env : TyEnv) (ts : List Silmaril.Compiler.Clang.TotalJson.Tree) :
    (importNodes env ts).length = ts.length :=
  Silmaril.Proofs.Data.Layout.Header.Import.importNodes_length env ts

theorem ofJson_provenance (prov : Provenance) (json : String) :
    (Imported.ofJson prov json).provenance = prov :=
  Silmaril.Proofs.Data.Layout.Header.Import.ofJson_provenance prov json

theorem Imported.eq_of {i : Imported} {p : Provenance} {es : List Entry} (hp : i.provenance = p)
    (he : i.entries = es) (hn : i.error = none) : i = ⟨p, es, none⟩ := by
  cases i; simp_all

theorem mem_names_of_proto {H : Header} {f : String} {cp : CProto} (h : H.proto? f = some cp) :
    f ∈ H.names :=
  Silmaril.Proofs.Data.Layout.Header.Import.mem_names_of_proto h

end Silmaril.Data.Layout.Header.Import

end
