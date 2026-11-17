module

public import Silmaril.Logic.Smt.SExpr.Writer.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Concrete presentations: named, versioned S-expression codecs

A logic's abstract syntax can have **many** concrete presentations. A presentation is not the
logic: the same abstract type `A` (formulas, judgments, terms) may be read and written by several
codecs, and the identity of the logic stays the abstract syntax.

`SExpCodec A` is one presentation over the S-expressions `Silmaril.Logic.Smt.SE`:
* `name` and `version` identify it (`"silmaril.pa.formula"`, `"1"`);
* `encode : A → SE` writes the canonical form of an abstract value;
* `decode : SE → Option A` reads, and `decode_eq_some_iff` says that it accepts exactly the
  canonical forms: `decode e = some a ↔ encode a = e`. So `encode` is injective and the relation
  "`e` presents `a`" is the graph of `encode`.

**Concrete sentences.** `Sen c` is the S-expressions that present some value, with the bijection
`Sen.toAbs` / `Sen.ofAbs` to the abstract values (`Thms`). A consequence system over the abstract
syntax is read over a presentation by `System.pullback` along `toAbs` (`viaCodec`, in
`Silmaril.Logic.Consequence.Soundness`).

**Bytes.** `print c a := render (c.encode a)`; `parse c` reads one S-expression and decodes it.
`parse c (print c a) = some a` whenever the printed atoms are legal for the reader (`Thms`).

**Many presentations.** `rename c σ` is another presentation of the same abstract syntax: every
atom renamed by a bijection `σ`. The renaming *induces* the identity on abstract syntax
(`Thms`: `rename_induces`).

**Translations between presentations.** `translate c₁ c₂` rewrites a presentation into another
over the same abstract syntax (decode, then encode). A map of S-expressions `m` *induces* a map of
abstract values `f` from `c₁` to `c₂` when `m (c₁.encode a) = c₂.encode (f a)` (`Induces`): the
abstract map is then computed by rewriting syntax (`Thms`). This is the shape of an institution
morphism whose sentence map is a simple S-expression morphism; no claim is made that every morphism
has this form.
-/

@[expose] public section

namespace Silmaril.Logic.Concrete

open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (render)

universe u v

/-- **A concrete presentation** of `A` over S-expressions: named, versioned, with a decoder that
accepts exactly the canonical forms. -/
structure SExpCodec (A : Type u) where
  /-- The presentation's name, e.g. `"silmaril.pa.formula"`. -/
  name : String
  /-- Its version. -/
  version : String
  /-- The canonical form of a value. -/
  encode : A → SE
  /-- Read a canonical form. -/
  decode : SE → Option A
  /-- The decoder accepts exactly the canonical forms. -/
  decode_eq_some_iff : ∀ e a, decode e = some a ↔ encode a = e

/-- Rename every atom of an S-expression. -/
def mapAtoms (f : String → String) : SE → SE
  | .atom s => .atom (f s)
  | .list es => .list (es.map (mapAtoms f))

namespace SExpCodec

variable {A : Type u} {B : Type v}

/-- The S-expressions that present some value: the concrete sentences of a presentation. -/
def Sen (c : SExpCodec A) : Type := {e : SE // ∃ a, c.encode a = e}

/-- The concrete form of a value. -/
def Sen.ofAbs {c : SExpCodec A} (a : A) : c.Sen := ⟨c.encode a, a, rfl⟩

/-- The value a concrete sentence presents. -/
noncomputable def Sen.toAbs {c : SExpCodec A} (e : c.Sen) : A := Classical.choose e.2

/-- Print a value as ASCII bytes. -/
def print (c : SExpCodec A) (a : A) : List UInt8 := render (c.encode a)

/-- Parse exactly one S-expression and decode it. -/
def parse (c : SExpCodec A) (bytes : List UInt8) : Option A :=
  match readForms bytes with
  | some [e] => c.decode e
  | _ => none

/-- Rewrite one presentation into another of the same abstract syntax. -/
def translate (c₁ c₂ : SExpCodec A) (e : SE) : Option SE := (c₁.decode e).map c₂.encode

/-- A map of S-expressions `m` induces the map of values `f` from `c₁` to `c₂`. -/
def Induces (c₁ : SExpCodec A) (c₂ : SExpCodec B) (m : SE → SE) (f : A → B) : Prop :=
  ∀ a, m (c₁.encode a) = c₂.encode (f a)

/-- **Another presentation of the same abstract syntax**: rename every atom by a bijection
`σ` (keywords, names and numerals alike), under a new name and version. -/
def rename (c : SExpCodec A) (σ : String ≃ String) (name version : String) : SExpCodec A where
  name := name
  version := version
  encode a := mapAtoms σ (c.encode a)
  decode e := c.decode (mapAtoms σ.symm e)
  decode_eq_some_iff e a := by
    rw [c.decode_eq_some_iff]
    constructor
    · intro h; rw [h]; exact mapAtoms_inv σ e
    · intro h; rw [← h]; simpa using (mapAtoms_inv σ.symm (c.encode a)).symm
where
  /-- Renaming by `σ` then by `σ⁻¹` is the identity. -/
  mapAtoms_inv (σ : String ≃ String) : ∀ e, mapAtoms σ (mapAtoms σ.symm e) = e
    | .atom s => by simp [mapAtoms]
    | .list es => by
      simp only [mapAtoms, List.map_map]
      congr 1
      conv => rhs; rw [← List.map_id es]
      exact List.map_congr_left fun e _ => mapAtoms_inv σ e

end SExpCodec

end Silmaril.Logic.Concrete
