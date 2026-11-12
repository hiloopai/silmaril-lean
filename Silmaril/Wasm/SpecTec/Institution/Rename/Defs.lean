module

public import Silmaril.Wasm.SpecTec.Institution.Defs

/-!
# The SpecTec specification institution with renamings of relation names

The signature category of `Silmaril.Wasm.SpecTec.Institution` is the inclusion preorder. Here its
morphisms are generalised to **renamings of relation names**: a morphism `Σ ⟶ Σ'` is a function
`f` on identifiers such that every relation declaration `(x, ps, op, t)` of `Σ` is sent to a
declaration `(f x, ps, op, t)` of `Σ'`, together with inclusions of the declared types and
functions.

* `renameP`, `renameRule`, `renameS`: the action of `f` on premises (through iterations), rules
  and sentences. Only the relation name of a `rulePr` premise, of a rule's declaration and of a
  fact is renamed; expressions, types, mixfix operators and function names are not.
* `renameI f D`: the interpretation `D` read through `f`.
* `SigR`, `SigHom`: signatures with renamings as morphisms, a category.
* `Model.reductR σ M`: the reduct of a `Σ'`-model along `σ : Σ ⟶ Σ'`, reading relations
  through `σ.f` and restricting to the symbols of `Σ`.

The satisfaction condition and the institution are in `Thms`. Renaming function and type names
would need a renaming of the whole expression syntax (`Exp`, `Typ`, `Arg`, `Path`, …) and a
proof that the evaluator commutes with it; that is not done.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

/-- A premise with its relation names renamed by `f`. -/
def renameP (f : IL.Id → IL.Id) : Prem → Prem
  | .rulePr x args op e => .rulePr (f x) args op e
  | .ifPr e => .ifPr e
  | .letPr e₁ e₂ => .letPr e₁ e₂
  | .elsePr => .elsePr
  | .iterPr pr it => .iterPr (renameP f pr) it

/-- A rule with the relation names of its premises renamed by `f`. -/
def renameRule (f : IL.Id → IL.Id) : Rule → Rule
  | .ruleD nm qs op e prems => .ruleD nm qs op e (prems.map (renameP f))

/-- A relation declaration with its name renamed by `f`. -/
def RelDecl.rename (f : IL.Id → IL.Id) (d : RelDecl) : RelDecl := (f d.1, d.2)

/-- A relation symbol with its name renamed by `f`. -/
def renameSym (f : IL.Id → IL.Id) (s : RelSym) : RelSym := (f s.1, s.2)

/-- A sentence with its relation names renamed by `f`. -/
def renameS (f : IL.Id → IL.Id) : SSen → SSen
  | .rule d r => .rule (d.rename f) (renameRule f r)
  | .fact x op args v => .fact (f x) op args v

/-- An interpretation read through the renaming `f`. -/
def renameI (f : IL.Id → IL.Id) (D : Interp) : Interp := fun x => D (f x)

/-- **A renaming of relation names** between signatures. -/
@[ext] structure SigHom (S T : Sig) where
  /-- The renaming of relation names. -/
  f : IL.Id → IL.Id
  /-- Declared types are kept. -/
  typs : S.typs ⊆ T.typs
  /-- Declared functions are kept. -/
  funs : S.funs ⊆ T.funs
  /-- Declarations are renamed to declarations. -/
  rels : ∀ d ∈ S.rels, d.rename f ∈ T.rels

/-- IL signatures, with renamings as morphisms. -/
structure SigR where
  /-- The signature. -/
  sig : Sig

/-- The identity renaming. -/
def SigHom.id (S : Sig) : SigHom S S := ⟨fun x => x, subset_rfl, subset_rfl, fun _ hd => hd⟩

/-- Composition of renamings. -/
def SigHom.comp {S T U : Sig} (σ : SigHom S T) (τ : SigHom T U) : SigHom S U :=
  ⟨fun x => τ.f (σ.f x), σ.typs.trans τ.typs, σ.funs.trans τ.funs,
    fun d hd => τ.rels _ (σ.rels d hd)⟩

instance : Category SigR where
  Hom S T := SigHom S.sig T.sig
  id S := SigHom.id S.sig
  comp σ τ := σ.comp τ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- An inclusion of signatures is the identity renaming. -/
def SigHom.ofLe {S T : Sig} (h : S ≤ T) : SigHom S T := ⟨fun x => x, h.1, h.2.1, h.2.2⟩

/-- **The reduct along a renaming**: relations read through `σ.f`, restricted to `Σ`. -/
def Model.reductR {S T : Sig} (σ : SigHom S T) (M : Model T) : Model S where
  env := M.env
  D := restrictI S.relSyms (renameI σ.f M.D)
  typs_def x hx := M.typs_def x (σ.typs hx)
  funs_def f hf := M.funs_def f (σ.funs hf)
  vanish _ _ _ _ hd := hd.1

end Silmaril.Wasm.SpecTec.Institution
