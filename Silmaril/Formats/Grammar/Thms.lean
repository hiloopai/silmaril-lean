module
public import Silmaril.Formats.Grammar.Defs

@[expose] public section
namespace Silmaril.Formats.Grammar.Ebnf
open CategoryTheory
namespace Expr
variable {T N U M V L : Type}
@[simp] theorem map_id (e : Expr T N) : e.map id id = e := by
  induction e <;> simp_all [map]
theorem map_comp (e : Expr T N) (f : T → U) (g : N → M) (h : U → V) (k : M → L) :
    (e.map f g).map h k = e.map (h ∘ f) (k ∘ g) := by
  induction e <;> simp_all [map]
end Expr

instance : Category System where
  Hom := Hom
  id G := ⟨id,id,rfl,fun _ => Expr.map_id _⟩
  comp f g :=
    { onTerminal := g.onTerminal ∘ f.onTerminal
      onNonterminal := g.onNonterminal ∘ f.onNonterminal
      start_commute := (congrArg g.onNonterminal f.start_commute).trans g.start_commute
      body_commute n := by rw [← Expr.map_comp, f.body_commute, g.body_commute]; rfl }

/-- Structural grammar morphisms transport finite derivations. -/
theorem Hom.derives {G H : System} (f : G ⟶ H) {e : Expr G.Terminal G.Nonterminal}
    {xs : List G.Terminal} (derivation : Derives G.body e xs) :
    Derives H.body (e.map f.onTerminal f.onNonterminal) (xs.map f.onTerminal) := by
  induction derivation with
  | epsilon => exact .epsilon
  | terminal t => exact .terminal _
  | reference h ih =>
    simp only [Expr.map]
    rw [f.body_commute] at ih
    exact .reference ih
  | sequence a b ha hb => simpa only [List.map_append, Expr.map] using Derives.sequence ha hb
  | left a ha => exact .left ha
  | right b hb => exact .right hb
  | nil => exact .nil
  | cons a b ha hb => simpa only [List.map_append, Expr.map] using Derives.cons ha hb

theorem Hom.accepts {G H : System} (f : G ⟶ H) {xs : List G.Terminal}
    (accepted : G.Accepts xs) : H.Accepts (xs.map f.onTerminal) := by
  have h := f.derives accepted
  change Derives H.body (.reference H.start) (xs.map f.onTerminal)
  simpa only [Expr.map, f.start_commute] using h

/-- Grammar presentations map to language relations; terminal renaming changes
the carrier and derivation preservation proves the relation-preserving square. -/
def toRelation : System ⥤ RelationCat where
  obj G := ⟨List G.Terminal,Unit,fun input _ => G.Accepts input⟩
  map f := ⟨List.map f.onTerminal,id,fun _ _ accepted => f.accepts accepted⟩
  map_id G := by
    apply Silmaril.EncCat₂.Hom.ext
    · funext xs; exact List.map_id xs
    · rfl
  map_comp f g := by
    apply Silmaril.EncCat₂.Hom.ext
    · funext xs
      change List.map (g.onTerminal ∘ f.onTerminal) xs =
        List.map g.onTerminal (List.map f.onTerminal xs)
      exact List.map_map.symm
    · rfl

namespace Derives
variable {T N : Type} {body : N → Expr T N}
theorem empty_iff (xs : List T) : Derives body .empty xs ↔ False := by
  constructor
  · intro h; cases h
  · exact False.elim
theorem epsilon_iff (xs : List T) : Derives body .epsilon xs ↔ xs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .epsilon
theorem alternative_iff (a b : Expr T N) (xs : List T) :
    Derives body (.alternative a b) xs ↔ Derives body a xs ∨ Derives body b xs := by
  constructor
  · intro h; cases h with
    | left h => exact Or.inl h
    | right h => exact Or.inr h
  · intro h; exact h.elim Derives.left Derives.right
theorem sequence_iff (a b : Expr T N) (xs : List T) :
    Derives body (.sequence a b) xs ↔
      ∃ left right, left ++ right = xs ∧ Derives body a left ∧ Derives body b right := by
  constructor
  · intro h; cases h with
    | sequence a b => exact ⟨_,_,rfl,a,b⟩
  · rintro ⟨left,right,rfl,a,b⟩; exact .sequence a b
end Derives
end Silmaril.Formats.Grammar.Ebnf
