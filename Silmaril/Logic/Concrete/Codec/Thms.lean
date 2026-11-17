module

public import Silmaril.Logic.Concrete.Codec.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Thms

/-!
# Concrete presentations: laws

* `encode_injective`, `decode_encode`: encoding is injective and decoding inverts it.
* `Sen.toAbs_ofAbs`, `Sen.ofAbs_toAbs`, `Sen.encode_toAbs`, `Sen.decode_toAbs`: concrete sentences
  are in bijection with abstract values, and the decoder computes the bijection.
* `parse_print`: printing then parsing gives the value back when the printed atoms are legal.
* `translate_encode`, `translate_eq_some_iff`: translating between presentations of the same
  abstract syntax is decode-then-encode, defined exactly on the first presentation's forms.
* `Induces.decode`: an S-expression map that induces `f` computes `f` on canonical forms.
-/

@[expose] public section

namespace Silmaril.Logic.Concrete.SExpCodec

open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (LegalExpr render read_render)

universe u v

variable {A : Type u} {B : Type v} (c : SExpCodec A)

theorem decode_encode (a : A) : c.decode (c.encode a) = some a :=
  (c.decode_eq_some_iff _ a).2 rfl

theorem encode_injective : Function.Injective c.encode := fun a b h => by
  have := c.decode_encode a; rw [h, c.decode_encode] at this; exact (Option.some.inj this).symm

theorem Sen.encode_toAbs {c : SExpCodec A} (e : c.Sen) : c.encode e.toAbs = e.1 :=
  Classical.choose_spec e.2

theorem Sen.toAbs_ofAbs {c : SExpCodec A} (a : A) : (Sen.ofAbs (c := c) a).toAbs = a :=
  c.encode_injective (Sen.encode_toAbs _)

theorem Sen.ofAbs_toAbs {c : SExpCodec A} (e : c.Sen) : Sen.ofAbs e.toAbs = e :=
  Subtype.ext (Sen.encode_toAbs e)

/-- The decoder computes the value a concrete sentence presents. -/
theorem Sen.decode_toAbs {c : SExpCodec A} (e : c.Sen) : c.decode e.1 = some e.toAbs :=
  (c.decode_eq_some_iff _ _).2 (Sen.encode_toAbs e)

theorem Sen.map_toAbs_ofAbs {c : SExpCodec A} (Γ : List A) :
    (Γ.map (Sen.ofAbs (c := c))).map Sen.toAbs = Γ := by
  simp [List.map_map, Function.comp_def, Sen.toAbs_ofAbs]

/-- **Bytes round trip**, when the printed atoms are legal for the reader. -/
theorem parse_print (a : A) (h : LegalExpr (c.encode a)) : c.parse (c.print a) = some a := by
  simp [parse, print, read_render _ h, decode_encode]

theorem translate_encode (c₂ : SExpCodec A) (a : A) :
    translate c c₂ (c.encode a) = some (c₂.encode a) := by
  simp [translate, decode_encode]

theorem translate_eq_some_iff (c₂ : SExpCodec A) (e e' : SE) :
    translate c c₂ e = some e' ↔ ∃ a, c.encode a = e ∧ c₂.encode a = e' := by
  simp only [translate, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, (c.decode_eq_some_iff _ _).1 ha, rfl⟩
  · rintro ⟨a, rfl, rfl⟩; exact ⟨a, c.decode_encode a, rfl⟩

/-- An S-expression map that induces `f` computes `f` on canonical forms. -/
theorem Induces.decode {c₂ : SExpCodec B} {m : SE → SE} {f : A → B}
    (h : Induces c c₂ m f) (a : A) : c₂.decode (m (c.encode a)) = some (f a) := by
  rw [h a, c₂.decode_encode]

/-- The atom renaming of `rename` induces the identity on abstract syntax: it is a simple
S-expression morphism between two presentations of one logic. -/
theorem rename_induces (σ : String ≃ String) (name version : String) :
    Induces c (c.rename σ name version) (mapAtoms σ) id := fun _ => rfl

/-- Translating into a renamed presentation is the renaming, on canonical forms. -/
theorem translate_rename (σ : String ≃ String) (name version : String) (a : A) :
    translate c (c.rename σ name version) (c.encode a) = some (mapAtoms σ (c.encode a)) :=
  translate_encode c _ a

end Silmaril.Logic.Concrete.SExpCodec
