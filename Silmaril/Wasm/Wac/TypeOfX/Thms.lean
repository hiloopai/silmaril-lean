module

public import Silmaril.Wasm.Wac.TypeOfX.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Thms
public import Silmaril.Proofs.Wasm.Wac.TypeOfX.Names

/-!
# WAC: correctness of the type inference of component binaries

* `typeOf_names`: **the package type `typeOf` infers has the component's own interface
  names**: its imports are exactly the component's top-level imports, by name and in order,
  and its exports are among the component's top-level exports, in order (type exports become
  the package's definitions). Every step of the inference is accounted for
  (`Names.track_ofSecs` in `Silmaril.Proofs.Wasm.Wac.TypeOfX.Names`): import and export sections
  append their names, every other step (types, aliases, instances, `canon`, nested
  components, which are inferred in a scope of their own) leaves both lists alone.
* `typeOfX_ofAst`: on a component without async built-ins, `typeOfX` is `typeOf`;
  `typeOfX_names`: the same names for components with built-ins (their erasure keeps every
  import and export section);
* `decodeAnyX_encode`: a package that the verified encoder wrote, and that `decodePkg` does
  not read, has the type `typeOf` gives its component (through `parseX_encode`).

What is not proved: that the *kinds* (types) inferred are right. They come from
`Bridge.decExtern`/`decDefType`, the same decoder as `decodePkg`, and are compared with `wac`
in the tests (`targets` verdicts) rather than proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

/-- **The type `typeOf` infers has the component's import and export names.** -/
theorem typeOf_names {c : Ast} {p : PkgType} {nom : Bridge.NomTable}
    (h : typeOf c = .ok (p, nom)) :
    p.imports.map (·.1) = importNames c ∧ (p.exports.map (·.1)).Sublist (exportNames c) := by
  cases c with
  | mk ss =>
    cases hr : (ofAst (.mk ss)).run {} with
    | error e =>
      have h' : typeOf (.mk ss) = .error e := by unfold typeOf; rw [hr]; rfl
      rw [h'] at h; exact nomatch h
    | ok r =>
      have h1 : (typeOf (.mk ss)).map (·.1.imports) = .ok r.1.1 := by unfold typeOf; rw [hr]; rfl
      have h2 : ∃ l, l.Sublist r.1.2 ∧ (typeOf (.mk ss)).map (·.1.exports) = .ok l := by
        unfold typeOf; rw [hr]; exact ⟨_, List.filter_sublist, rfl⟩
      obtain ⟨l, hl, h2'⟩ := h2
      have hi : p.imports = r.1.1 := by rw [h] at h1; exact Except.ok.inj h1
      have he : p.exports = l := by rw [h] at h2'; exact Except.ok.inj h2'
      obtain ⟨hni, hne⟩ := ofAst_names ss hr
      refine ⟨by rw [hi, hni]; rfl, ?_⟩
      rw [he]
      exact (hne ▸ hl.map _ : (l.map (·.1)).Sublist (exportNamesOf ss))

/-- On a component without async built-ins, `typeOfX` is `typeOf`. -/
theorem typeOfX_ofAst (c : Ast) : typeOfX (AstX.ofAst c) = typeOf c := by
  rw [typeOfX, erase_ofAst]

/-- **The names `typeOfX` reports** are those of the component's erasure. -/
theorem typeOfX_names {c : AstX} {p : PkgType} {nom : Bridge.NomTable}
    (h : typeOfX c = .ok (p, nom)) :
    p.imports.map (·.1) = importNames c.erase ∧
      (p.exports.map (·.1)).Sublist (exportNames c.erase) :=
  typeOf_names h

/-- A package written by the verified encoder that `decodePkg` does not read is typed by
`typeOf` of its component. -/
theorem decodeAnyX_encode {c : Ast} {b : ByteArray} (hb : encode c = some b) {e : String}
    (hd : Bridge.decodePkg b = .error e) {r : PkgType × Bridge.NomTable}
    (h : typeOf c = .ok r) : decodeAnyX b = .ok r := by
  simp only [decodeAnyX, hd, parseX_encode hb, typeOfX_ofAst, h]

end Silmaril.Wasm.Wac.TypeOf
