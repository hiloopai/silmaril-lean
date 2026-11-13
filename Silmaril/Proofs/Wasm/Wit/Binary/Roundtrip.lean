module

public import Silmaril.Proofs.Wasm.Wit.Binary.Bytes
public import Silmaril.Proofs.Wasm.Wit.Binary.Canon
public import Silmaril.Proofs.Wasm.Wit.Binary.Inject

/-!
# WIT packages: the round trips at the byte level

* `decodePackage_encodePackage_canon`: the bytes of a valid package with
  distinct names decode to the package with its functions in wit-component's
  order, docs kept (`inject_docsJson`).
* `encodePackage_decodePackage`: for such a package already in that order,
  encoding the decoded package gives the same bytes. Without the order
  assumption this is false (`Golden.reorderCounter`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

theorem decodePackage_encodePackage_canon {deps : Env} {p : Package}
    (hv : p.Valid deps) (hu : p.NamesUnique) {b : ByteArray} (h : encodePackage deps p = .ok b) :
    decodePackage b = .ok p.canon := by
  rw [decodePackage_encodePackage hv h, inject_docsJson hu]

/-- **encode ∘ decode = id on the image of canonical packages** (bytes). -/
theorem encodePackage_decodePackage {deps : Env} {p : Package}
    (hv : p.Valid deps) (hu : p.NamesUnique) (hc : p.canon = p) {b : ByteArray}
    (h : encodePackage deps p = .ok b) {q : Package} (hq : decodePackage b = .ok q) :
    encodePackage deps q = .ok b := by
  have hq' : q = p := by
    rw [decodePackage_encodePackage_canon hv hu h, hc] at hq; exact (Except.ok.inj hq).symm
  rw [hq', h]

end Silmaril.Wasm.Wit.Binary
