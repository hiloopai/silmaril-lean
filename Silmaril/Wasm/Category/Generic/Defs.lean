module

public import Silmaril.Compile.Category.Pass
public import Mathlib.Order.Hom.Basic

@[expose] public section

/-!
# The category of compilers: pieces missing from the pinned silmaril-lean

The pinned silmaril-lean has the category of compilers (`Silmaril.Compile.Category`:
`Language`, `Convention`, `Valid`, `CompRel`/`RelCat`, `Compiler`/`CompCat`, `Pass`,
`EndoPass`, `RoundTrip`, `Realises`, `Syntax`). The old private development had a few more
generic pieces; this file ports the ones the Wasm instances use.

* `roundTripTrans`: round trips compose (`L ⇄ M` then `M ⇄ S` is `L ⇄ S`), so an IR reached
  through a chain of round trips conjugates its optimizations to every language of the chain.
  Ported from `Silmaril/Compile/Category/RoundTripComp.lean`.
* `relForget`, `compForget`, `fibreOrderIso`, `fibreReindex`: the projections of `RelCat` and
  `CompCat` to conventions, and the fibres of `RelCat` (the lattice of relations below
  `Valid c`). Ported from `Silmaril/Compile/Category/Grothendieck.lean`.
* `Dialect`: a preorder of local rewrites proved once to imply refinement, and `Dialect.stage`
  packaging a stage that only proves its local law as an `EndoPass`. Ported from
  `Silmaril/Compile/Category/Dialect.lean` without its 2-cell corollaries.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category

universe u

variable {L M S : Language.{u}}

/-! ## Round trips compose -/

/-- **Composition of round trips**: lift through `M` and on to `S`, lower back through `M`.
The composite convention is below the identity by monotonicity of composition. -/
def roundTripTrans (T : RoundTrip L M) (U : RoundTrip M S) : RoundTrip L S where
  lift := T.lift ≫ₚ U.lift
  lower := U.lower ≫ₚ T.lower
  le_id := by
    calc (T.up ≫ U.up) ≫ U.down ≫ T.down = T.up ≫ (U.up ≫ U.down) ≫ T.down := by
          simp only [Category.assoc]
      _ ≤ T.up ≫ 𝟙 M ≫ T.down :=
          Convention.comp_mono le_rfl (Convention.comp_mono U.le_id le_rfl)
      _ = T.up ≫ T.down := by rw [Category.id_comp]
      _ ≤ 𝟙 L := T.le_id

theorem roundTripTrans_lift_run (T : RoundTrip L M) (U : RoundTrip M S) (p : L.Prog) :
    (roundTripTrans T U).lift.run p = (T.lift.run p).bind U.lift.run := rfl

theorem roundTripTrans_lower_run (T : RoundTrip L M) (U : RoundTrip M S) (q : S.Prog) :
    (roundTripTrans T U).lower.run q = (U.lower.run q).bind T.lower.run := rfl

/-! ## Projections to conventions (the Grothendieck view) -/

/-- The projection from compilation relations to conventions. -/
def relForget : RelCat.{u} ⥤ Language.{u} where
  obj X := X.lang
  map f := CompRel.conv f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection from compilers to conventions. -/
def compForget : CompCat.{u} ⥤ Language.{u} where
  obj X := X.lang
  map C := Compiler.conv C
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Taking graphs commutes with the projections to conventions. -/
theorem graphFunctor_forget : graphFunctor.{u} ⋙ relForget = compForget := rfl

variable {L' : Language.{u}}

/-- The fibre of `RelCat` over a convention is the lattice of relations below `Valid c`. -/
def fibreOrderIso (c : L ⟶ L') :
    {f : CompRel L L' // f.conv = c} ≃o Set.Iic (Valid c) where
  toFun f := ⟨f.1.rel, by have h := f.1.valid; rw [f.2] at h; exact h⟩
  invFun r := ⟨⟨c, r.1, r.2⟩, rfl⟩
  left_inv f := Subtype.ext (CompRel.ext f.2.symm rfl)
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    show a.1.rel ≤ b.1.rel ↔ a.1.conv ≤ b.1.conv ∧ a.1.rel ≤ b.1.rel
    rw [a.2, b.2]
    exact ⟨fun h => ⟨le_rfl, h⟩, And.right⟩

/-- Reindexing along convention refinement: relations valid at `c` are valid at any `d ≥ c`. -/
def fibreReindex {c d : L ⟶ L'} (h : c ≤ d) : Set.Iic (Valid c) →o Set.Iic (Valid d) where
  toFun r := ⟨r.1, le_trans r.2 (valid_mono h)⟩
  monotone' _ _ h' := h'

/-! ## Dialects: local rewrite laws as optimization contracts -/

/-- A local rewrite theory whose laws imply refinement in its language. -/
structure Dialect (L : Language.{u}) where
  /-- The permitted rewrites: `Law p q` allows replacing `p` by `q`. -/
  Law : L.Prog → L.Prog → Prop
  refl : ∀ p, Law p p
  trans : ∀ {p q r}, Law p q → Law q r → Law p r
  /-- The laws are sound: they imply refinement. -/
  refines : ∀ {p q}, Law p q → L.Refines p q

namespace Dialect

/-- Exact behavioural equivalence as the local law. -/
def equivalent (L : Language.{u}) : Dialect L where
  Law := L.BehEquiv
  refl p := ⟨L.refines_refl p, L.refines_refl p⟩
  trans h k := ⟨L.refines_trans h.1 k.1, L.refines_trans k.2 h.2⟩
  refines h := h.1

/-- Directed refinement as the local law. -/
def refinement (L : Language.{u}) : Dialect L where
  Law := L.Refines
  refl := L.refines_refl
  trans := L.refines_trans
  refines := id

/-- The one local obligation of a total optimization stage. -/
def StageOk (D : Dialect L) (f : L.Prog → L.Prog) : Prop := ∀ p, D.Law p (f p)

/-- A stage with its local dialect law is an optimization in the pass monoid. -/
def stage (D : Dialect L) (f : L.Prog → L.Prog) (h : D.StageOk f) : EndoPass L :=
  ⟨f, fun p => D.refines (h p)⟩

@[simp] theorem stage_run (D : Dialect L) (f : L.Prog → L.Prog) (h : D.StageOk f) :
    (D.stage f h).run = f := rfl

theorem StageOk.id (D : Dialect L) : D.StageOk id := D.refl

/-- Local laws compose in execution order. -/
theorem StageOk.seq {D : Dialect L} {f g : L.Prog → L.Prog}
    (hf : D.StageOk f) (hg : D.StageOk g) : D.StageOk (g ∘ f) :=
  fun p => D.trans (hf p) (hg (f p))

theorem stage_seq {D : Dialect L} {f g : L.Prog → L.Prog}
    (hf : D.StageOk f) (hg : D.StageOk g) :
    D.stage (g ∘ f) (hf.seq hg) = D.stage f hf * D.stage g hg := rfl

/-- A dialect law transports through any round trip. -/
def through (D : Dialect S) (T : RoundTrip L S) (f : S.Prog → S.Prog)
    (h : D.StageOk f) : Pass (𝟙 L) := T.conj (D.stage f h)

end Dialect

end Silmaril.Wasm.Category
