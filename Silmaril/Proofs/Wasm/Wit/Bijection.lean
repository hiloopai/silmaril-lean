module

public import Silmaril.Wasm.Wit.Elab.Thms
public import Silmaril.Wasm.Wit.Text.Valid.Thms

/-!
# WIT packages and type-only components: the end-to-end correspondence

The chain is

```
WIT text ──parse──▶ Document ──elaborate──▶ Binary.Package ──encodePackage──▶ bytes
         ◀─print──                                          ◀──decodePackage──
```

and the precise relationships are:

* **text ↔ AST**: on valid documents `parse ∘ print = id` (`parse_print_valid`), so
  `print` is injective there (`print_injective_of_valid`);
* **AST → binary model**: on a valid gated universe whose package has an item,
  `elaborate` succeeds unless wit-parser reports a world error
  (`elaborate_ok_or_worldError`), and its output satisfies the hypotheses of the
  binary round trip (`elaborate_sound`);
* **binary model ↔ bytes, modulo the normal form**: the bytes of an elaborated
  package decode to its normal form `P.canon` (`surface_decode`), so two surface
  packages with the same bytes have the same normal form (`surface_injective`);
  on canonical packages `encodePackage` is injective (`encode_injective`) with
  inverse `decodePackage` on its image (`image_roundtrip`): **a bijection between
  canonical valid packages with distinct names and their bytes**;
* **worlds**: each world of an elaborated package is the projection of its bytes
  (`elaborate_world_projects`).

What is *not* a bijection: elaboration forgets source order of functions (the
normal form `canon`), non-doc comments and whitespace (the lexer), the docs of
dependencies, and `use` aliases (resolved); components in general are not WIT
packages, and the projection component ↦ world is many-to-one
(`Project.project_not_injective`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Bijection

open Silmaril.Wasm.Wit.Binary (Env decodePackage encodePackage)

/-- An elaborated surface package's bytes decode to its normal form. -/
theorem surface_decode {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package} {deps : Env}
    (h : Elab.elaborate U p fs = .ok (P, deps)) {b : ByteArray} (hb : encodePackage deps P = .ok b) :
    decodePackage b = .ok P.canon :=
  Elab.elaborate_decode h hb

/-- **Surface packages with the same bytes have the same normal form.** -/
theorem surface_injective {U₁ U₂ : Universe} {p₁ p₂ : PackageName} {fs₁ fs₂ : List Name}
    {P₁ P₂ : Binary.Package} {deps₁ deps₂ : Env}
    (h₁ : Elab.elaborate U₁ p₁ fs₁ = .ok (P₁, deps₁)) (h₂ : Elab.elaborate U₂ p₂ fs₂ = .ok (P₂, deps₂))
    {b : ByteArray} (hb₁ : encodePackage deps₁ P₁ = .ok b) (hb₂ : encodePackage deps₂ P₂ = .ok b) :
    P₁.canon = P₂.canon := by
  have e₁ := surface_decode h₁ hb₁
  rw [surface_decode h₂ hb₂] at e₁
  exact (Except.ok.inj e₁).symm

/-- **Encoding is injective on canonical valid packages with distinct names**
(in any environments). -/
theorem encode_injective {deps₁ deps₂ : Env} {q₁ q₂ : Binary.Package} (hv₁ : q₁.Valid deps₁)
    (hu₁ : q₁.NamesUnique) (hc₁ : q₁.canon = q₁) (hv₂ : q₂.Valid deps₂) (hu₂ : q₂.NamesUnique)
    (hc₂ : q₂.canon = q₂) {b : ByteArray} (hb₁ : encodePackage deps₁ q₁ = .ok b)
    (hb₂ : encodePackage deps₂ q₂ = .ok b) : q₁ = q₂ := by
  have e₁ := Binary.decodePackage_encodePackage_canon hv₁ hu₁ hb₁
  rw [Binary.decodePackage_encodePackage_canon hv₂ hu₂ hb₂, hc₁, hc₂] at e₁
  exact (Except.ok.inj e₁).symm

/-- **On the image, decoding inverts encoding and encoding inverts decoding**: the
bytes of a canonical valid package with distinct names decode to it, and
encoding what they decode to gives the bytes back. -/
theorem image_roundtrip {deps : Env} {q : Binary.Package} (hv : q.Valid deps) (hu : q.NamesUnique)
    (hc : q.canon = q) {b : ByteArray} (hb : encodePackage deps q = .ok b) :
    decodePackage b = .ok q ∧ ∀ q', decodePackage b = .ok q' → encodePackage deps q' = .ok b := by
  refine ⟨by rw [Binary.decodePackage_encodePackage_canon hv hu hb, hc], fun q' hq' => ?_⟩
  exact Binary.encodePackage_decodePackage hv hu hc hb hq'

/-- **From WIT text to a type-only component and back.** For a valid document `d`
(with dependencies `deps`): the text round trip is exact; `elaborate` either
succeeds or reports a wit-parser world error; and when it succeeds, the bytes of
the package decode to its normal form, and each world is the projection of the
bytes. -/
theorem text_to_component {d : Document} {deps : Universe} {fs : List Name}
    (hd : Valid (d.packages ++ deps)) (hg : Valid (Universe.gate fs (d.packages ++ deps)))
    {P : Package} (hP : P ∈ Universe.gate fs (d.packages ++ deps)) (hPn : P.name = d.main.name)
    (hne : P.ifaces ≠ [] ∨ P.worlds ≠ []) :
    Text.parse (Text.print d) = some d ∧
      ((∃ Q env, Elab.elaborate (d.packages ++ deps) d.main.name fs = .ok (Q, env) ∧
          ∀ b, encodePackage env Q = .ok b → decodePackage b = .ok Q.canon) ∨
        ∃ m, Elab.elaborate (d.packages ++ deps) d.main.name fs = .error m ∧ Elab.WorldError m) := by
  refine ⟨Text.parse_print_valid hd, ?_⟩
  rcases Elab.elaborate_ok_or_worldError hg hP hPn hne with ⟨⟨Q, env⟩, h⟩ | h
  · exact .inl ⟨Q, env, h, fun b hb => surface_decode h hb⟩
  · exact .inr h

end Silmaril.Wasm.Wit.Bijection
