module

public import Silmaril.Wasm.Institution.Entry.Defs
public import Silmaril.Proofs.Wasm.Institution.Entry.Basic

@[expose] public section

/-!
# Single-invocation logics: results

Proofs are in `Silmaril.Proofs.Wasm.Institution.Entry.Basic`.

* `valid_entryRef_iff`: validity of `s ⊑ s'` at the full interface is
  `Equiv.ModuleRefines E R s s'`; `valid_entryEquiv_iff`: `Equiv.ModuleEquiv E R s s'`.
* `refines_close_iff`: `a ⊑_R b ↔ a ⊑_Eq close R b`; `Refines.restrict`: hiding.
* Translations (comorphisms, model-expansive): `comapT` (pullback of entry points, e.g.
  Binaryen IR lowering), `progT` (any denotation-preserving program map, e.g. lifting),
  `closeT`, `equivT`.
-/
