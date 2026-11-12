module

public import Silmaril.Wasm.SpecTec.Defs
public import Silmaril.Logic.Institution.Theory
public import Silmaril.Logic.Institution.Morphism

/-!
# The institution of SpecTec grammars

SpecTec's grammars (`GramD`) denote byte-string/attribute relations through the attribute-grammar
framework `Silmaril.SpecTec.Grammar` (`Sym`, `Gram`, `denote`). This module packages that
framework as an institution, in the sense of silmaril-lean's `Silmaril.Logic.Institution.Inst`
(a functor from signatures to rooms), parameterised by the attribute algebra `A : Attr α` (the
"logic" fixes how attributes compose; SpecTec uses `Sem.actAlg` on `Sem.Act`).

* **Signatures** `Sig D`: a type `N` of nonterminals together with a declaration `decl : N → D`
  (for SpecTec: the declared parameters and value type of the `GramD`, `scriptDecl`).
  **Morphisms** are renamings `N → N'` that preserve declarations; inclusions are a special case.
* **Sentences** `Sen N α`:
  - `prod x g`, the production `x ::= g`, read as the Horn clause "whatever `g` derives, `x`
    derives" (the body `g` may mention any nonterminals; its attribute actions are fixed
    semantic functions, which is where the non-grammar part of a script lives);
  - `derives g bs P`, the derivability assertion "`g` derives the bytes `bs` with an attribute
    satisfying `P`".
  Translation along a renaming renames the nonterminals (`renameSym`).
* **Models** `Model N α`: an interpretation of every nonterminal as a relation between byte
  strings and attributes. Model morphisms are pointwise inclusions; the reduct along a renaming
  is precomposition.
* **Satisfaction**: a symbol is interpreted compositionally in a model (`interp`, one clause per
  `Sym` constructor, the same operations `Grammar.step` uses), `prod x g` holds when
  `interp g ≤ I x`, and `derives g bs P` when some attribute `a` with `P a` has
  `interp g bs a`.

The satisfaction condition is `Sen.holds_rename` (from `interp_rename`). The theory of a grammar
`⟨A, P⟩` is the set of its productions (`prodAxioms P`), and `Grammar.denote` is its least model
(`Silmaril.Wasm.SpecTec.GrammarInst.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory
open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

/-! ## Renaming of symbols -/

section Rename

variable {N N' α : Type}

mutual

/-- Rename the nonterminals of a symbol. -/
def renameSym (f : N → N') : Sym N α → Sym N' α
  | .eps => .eps
  | .byte b => .byte b
  | .range lo hi => .range lo hi
  | .bytes l => .bytes l
  | .nt x => .nt (f x)
  | .seq gs => .seq (renameSyms f gs)
  | .alt gs => .alt (renameSyms f gs)
  | .star g => .star (renameSym f g)
  | .plus g => .plus (renameSym f g)
  | .opt g => .opt (renameSym f g)
  | .count g k => .count (renameSym f g) k
  | .attr h g => .attr h (renameSym f g)

/-- `renameSym` on a list of symbols. -/
def renameSyms (f : N → N') : List (Sym N α) → List (Sym N' α)
  | [] => []
  | g :: gs => renameSym f g :: renameSyms f gs

end

end Rename

/-! ## Interpretation of symbols in a model -/

section Interp

variable {N α : Type}

mutual

/-- The relation a symbol denotes when each nonterminal `x` denotes `I x`. This is
`Grammar.step` with `I` for the nonterminals and itself for the sub-symbols: one structural
pass, no unfolding of productions. -/
def interp (A : Attr α) (I : N → EncRel Bytes α) : Sym N α → EncRel Bytes α
  | .eps => epsRel A.nil
  | .byte b => byteRel A b
  | .range lo hi => rangeRel A lo hi
  | .bytes l => bytesRel A l
  | .nt x => I x
  | .seq gs => appendAll A (interps A I gs)
  | .alt gs => supList (interps A I gs)
  | .star g => kleene A (interp A I g)
  | .plus g => appendRel A (interp A I g) (kleene A (interp A I g))
  | .opt g => epsRel A.nil ⊔ interp A I g
  | .count g k => powRel A (interp A I g) k
  | .attr h g => EncRel.mapPartial h (interp A I g)

/-- `interp` on a list of symbols. -/
def interps (A : Attr α) (I : N → EncRel Bytes α) : List (Sym N α) → List (EncRel Bytes α)
  | [] => []
  | g :: gs => interp A I g :: interps A I gs

end

/-- `interps` is `List.map interp`. -/
theorem interps_eq_map (A : Attr α) (I : N → EncRel Bytes α) (gs : List (Sym N α)) :
    interps A I gs = gs.map (interp A I) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [interps, ih, List.map_cons]

end Interp

section RenameInterp

variable {N N' α : Type}

mutual

/-- **Renaming and interpretation commute**: interpreting a renamed symbol is interpreting the
symbol in the reduct. -/
theorem interp_rename (A : Attr α) (I : N' → EncRel Bytes α) (f : N → N') :
    ∀ g : Sym N α, interp A I (renameSym f g) = interp A (I ∘ f) g
  | .eps => rfl
  | .byte _ => rfl
  | .range _ _ => rfl
  | .bytes _ => rfl
  | .nt _ => rfl
  | .seq gs => congrArg (appendAll A) (interps_rename A I f gs)
  | .alt gs => congrArg supList (interps_rename A I f gs)
  | .star g => congrArg (kleene A) (interp_rename A I f g)
  | .plus g => congrArg (fun E => appendRel A E (kleene A E)) (interp_rename A I f g)
  | .opt g => congrArg (epsRel A.nil ⊔ ·) (interp_rename A I f g)
  | .count g k => congrArg (powRel A · k) (interp_rename A I f g)
  | .attr h g => congrArg (EncRel.mapPartial h) (interp_rename A I f g)

/-- `interp_rename` on lists. -/
theorem interps_rename (A : Attr α) (I : N' → EncRel Bytes α) (f : N → N') :
    ∀ gs : List (Sym N α), interps A I (renameSyms f gs) = interps A (I ∘ f) gs
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (interp_rename A I f g) (interps_rename A I f gs)

end

mutual

/-- Renaming along the identity does nothing. -/
theorem renameSym_id : ∀ g : Sym N α, renameSym id g = g
  | .eps => rfl
  | .byte _ => rfl
  | .range _ _ => rfl
  | .bytes _ => rfl
  | .nt _ => rfl
  | .seq gs => congrArg Sym.seq (renameSyms_id gs)
  | .alt gs => congrArg Sym.alt (renameSyms_id gs)
  | .star g => congrArg Sym.star (renameSym_id g)
  | .plus g => congrArg Sym.plus (renameSym_id g)
  | .opt g => congrArg Sym.opt (renameSym_id g)
  | .count g k => congrArg (Sym.count · k) (renameSym_id g)
  | .attr h g => congrArg (Sym.attr h) (renameSym_id g)

/-- `renameSym_id` on lists. -/
theorem renameSyms_id : ∀ gs : List (Sym N α), renameSyms id gs = gs
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (renameSym_id g) (renameSyms_id gs)

end

variable {N'' : Type}

mutual

/-- Renaming is functorial. -/
theorem renameSym_comp (f : N → N') (f' : N' → N'') :
    ∀ g : Sym N α, renameSym (f' ∘ f) g = renameSym f' (renameSym f g)
  | .eps => rfl
  | .byte _ => rfl
  | .range _ _ => rfl
  | .bytes _ => rfl
  | .nt _ => rfl
  | .seq gs => congrArg Sym.seq (renameSyms_comp f f' gs)
  | .alt gs => congrArg Sym.alt (renameSyms_comp f f' gs)
  | .star g => congrArg Sym.star (renameSym_comp f f' g)
  | .plus g => congrArg Sym.plus (renameSym_comp f f' g)
  | .opt g => congrArg Sym.opt (renameSym_comp f f' g)
  | .count g k => congrArg (Sym.count · k) (renameSym_comp f f' g)
  | .attr h g => congrArg (Sym.attr h) (renameSym_comp f f' g)

/-- `renameSym_comp` on lists. -/
theorem renameSyms_comp (f : N → N') (f' : N' → N'') :
    ∀ gs : List (Sym N α), renameSyms (f' ∘ f) gs = renameSyms f' (renameSyms f gs)
  | [] => rfl
  | g :: gs => congrArg₂ List.cons (renameSym_comp f f' g) (renameSyms_comp f f' gs)

end

end RenameInterp

/-! ## Sentences -/

/-- The sentences over the nonterminals `N`: productions (Horn clauses over grammar membership)
and derivability assertions. -/
inductive Sen (N α : Type) : Type
  /-- The production `x ::= g`: everything `g` derives, `x` derives. -/
  | prod (x : N) (g : Sym N α)
  /-- `g` derives the bytes `bs` with some attribute satisfying `P`. -/
  | derives (g : Sym N α) (bs : Bytes) (P : α → Prop)

namespace Sen

variable {N N' N'' α : Type}

/-- Sentence translation along a renaming. -/
def rename (f : N → N') : Sen N α → Sen N' α
  | .prod x g => .prod (f x) (renameSym f g)
  | .derives g bs P => .derives (renameSym f g) bs P

/-- Satisfaction of a sentence by an interpretation of the nonterminals. -/
def Holds (A : Attr α) (I : N → EncRel Bytes α) : Sen N α → Prop
  | .prod x g => interp A I g ≤ I x
  | .derives g bs P => ∃ a, interp A I g bs a ∧ P a

/-- **The satisfaction condition**: a renamed sentence holds in a model iff the sentence holds
in the reduct. -/
theorem holds_rename (A : Attr α) (I : N' → EncRel Bytes α) (f : N → N') (φ : Sen N α) :
    (φ.rename f).Holds A I ↔ φ.Holds A (I ∘ f) := by
  cases φ with
  | prod x g =>
    show interp A I (renameSym f g) ≤ I (f x) ↔ interp A (I ∘ f) g ≤ I (f x)
    rw [interp_rename]
  | derives g bs P =>
    show (∃ a, interp A I (renameSym f g) bs a ∧ P a) ↔ ∃ a, interp A (I ∘ f) g bs a ∧ P a
    rw [interp_rename]

theorem rename_id : (rename id : Sen N α → Sen N α) = id := by
  funext φ
  cases φ with
  | prod x g => exact congrArg (Sen.prod x) (renameSym_id g)
  | derives g bs P => exact congrArg (Sen.derives · bs P) (renameSym_id g)

theorem rename_comp (f : N → N') (f' : N' → N'') :
    (rename (f' ∘ f) : Sen N α → Sen N'' α) = rename f' ∘ rename f := by
  funext φ
  cases φ with
  | prod x g => exact congrArg (Sen.prod (f' (f x))) (renameSym_comp f f' g)
  | derives g bs P => exact congrArg (Sen.derives · bs P) (renameSym_comp f f' g)

end Sen

/-! ## Signatures -/

/-- A grammar signature: nonterminals with their declarations (for SpecTec: parameters and value
type). -/
structure Sig (D : Type) : Type 1 where
  /-- The nonterminals. -/
  N : Type
  /-- The declaration of each nonterminal. -/
  decl : N → D

/-- A signature morphism: a declaration-preserving renaming of nonterminals. -/
@[ext]
structure Sig.Hom {D : Type} (S T : Sig D) : Type where
  /-- The renaming. -/
  map : S.N → T.N
  /-- Declarations are preserved. -/
  decl_map : ∀ x, T.decl (map x) = S.decl x

instance (D : Type) : Category.{0} (Sig D) where
  Hom := Sig.Hom
  id _ := ⟨id, fun _ => rfl⟩
  comp f g := ⟨g.map ∘ f.map, fun x => (g.decl_map (f.map x)).trans (f.decl_map x)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Models -/

/-- A model: an interpretation of every nonterminal as a byte-string/attribute relation. -/
@[ext]
structure Model (N α : Type) : Type where
  /-- What each nonterminal derives. -/
  rel : N → EncRel Bytes α

instance (N α : Type) : Category.{0} (Model N α) where
  Hom I J := PLift (∀ x, I.rel x ≤ J.rel x)
  id _ := ⟨fun _ => le_rfl⟩
  comp f g := ⟨fun x => le_trans (f.down x) (g.down x)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct along a renaming: precomposition. -/
def Model.reduct {N N' α : Type} (f : N → N') : Model N' α ⥤ Model N α where
  obj I := ⟨I.rel ∘ f⟩
  map h := ⟨fun x => h.down (f x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The institution -/

section Institution

variable {α : Type}

/-- The room of the nonterminals `N`: sentences, models, satisfaction. It depends only on the
nonterminals, not on their declarations. -/
def room (A : Attr α) (N : Type) : Room.{0, 0, 0} :=
  ⟨Sen N α, Cat.of (Model N α), fun M φ => φ.Holds A M.rel⟩

/-- The corridor of a renaming. -/
def corridor (A : Attr α) {N N' : Type} (f : N → N') : room A N ⟶ room A N' :=
  ⟨Sen.rename f, Model.reduct f, fun M φ => Sen.holds_rename A M.rel f φ⟩

/-- **The institution of grammars over the attribute algebra `A`**, as a functor from
signatures with declarations in `D` to rooms. -/
def functor (A : Attr α) (D : Type) : Sig D ⥤ Room.{0, 0, 0} where
  obj S := room A S.N
  map σ := corridor A σ.map
  map_id _ := Room.hom_ext Sen.rename_id rfl
  map_comp σ τ := Room.hom_ext (Sen.rename_comp σ.map τ.map) rfl

/-- The institution of grammars, bundled. -/
def inst (A : Attr α) (D : Type) : Inst.{1, 0, 0, 0, 0} := ⟨Sig D, functor A D⟩

/-- The rooms of the institution are the rooms of the nonterminals. -/
theorem functor_obj (A : Attr α) (D : Type) (S : Sig D) : (functor A D).obj S = room A S.N := rfl

end Institution

/-! ## Grammars as theories -/

section Theories

variable {N α : Type}

/-- The axioms of a production table: one Horn clause `x ::= g` per production. -/
def prodAxioms (P : N → List (Sym N α)) : Set (Sen N α) :=
  {φ | ∃ x g, g ∈ P x ∧ φ = .prod x g}

/-- The productions of `P` whose nonterminal satisfies `p`: a fragment of the theory. -/
def prodAxiomsWhere (p : N → Prop) (P : N → List (Sym N α)) : Set (Sen N α) :=
  {φ | ∃ x g, p x ∧ g ∈ P x ∧ φ = .prod x g}

/-- The intended model of a grammar: each nonterminal denotes what `Grammar.denote` gives it. -/
def leastModel (G : Gram N α) : Model N α := ⟨fun x => denote G (.nt x)⟩

/-- The presentation `(S, prodAxioms P)` of a grammar over the signature `S`. -/
def presentation {D : Type} (A : Attr α) (S : Sig D) (P : S.N → List (Sym S.N α)) :
    Presentation (functor A D) :=
  ⟨S, prodAxioms P⟩

end Theories

/-! ## SpecTec scripts as grammar theories

A script's grammars are translated by `Sem.transProd` into the framework, over the nonterminals
`Sem.NT` (a grammar identifier with its unevaluated arguments) and the attribute algebra
`Sem.actAlg` on `Sem.Act`. The script's functions and relations are not part of the grammar
theory: they live inside the attribute actions of its productions, as a fixed background
interpretation. The signature of a script declares each nonterminal with the parameters and value
type of its `GramD` (`none` for an undeclared identifier). -/

section Script

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem (NT Act actAlg Env VarEnv Value prodsOf transSym)

/-- The declarations of SpecTec nonterminals: a `GramD`'s parameters and value type. -/
abbrev Decl : Type := Option (List IL.Param × IL.Typ)

/-- The declaration a script gives a nonterminal. -/
def scriptDecl (env : Env) (n : NT) : Decl := (env.findGram? n.1).map fun d => (d.1, d.2.1)

/-- The signature of a script: all nonterminals, declared as in the script. -/
def scriptSig (env : Env) : Sig Decl := ⟨NT, scriptDecl env⟩

/-- **The grammar theory of a script**: one Horn clause per production of every `GramD`, binary
and text grammars alike. -/
def scriptAxioms (env : Env) : Set (Sen NT Act) := prodAxioms (prodsOf env env)

/-- The theory of a script as a presentation in the institution of grammars. -/
def scriptPresentation (env : Env) : Presentation (functor actAlg Decl) :=
  presentation actAlg (scriptSig env) (prodsOf env env)

/-- The binary-format fragment: the productions of the grammars named `B…`. The first character
is read with `String.front`, which the kernel can evaluate in a module (`String.startsWith`
does not reduce there). -/
def binaryAxioms (env : Env) : Set (Sen NT Act) :=
  prodAxiomsWhere (fun n => n.1.front = 'B') (prodsOf env env)

/-- The text-format fragment: the productions of the grammars named `T…`. -/
def textAxioms (env : Env) : Set (Sen NT Act) :=
  prodAxiomsWhere (fun n => n.1.front = 'T') (prodsOf env env)

/-- Semantic consequence in the room of SpecTec nonterminals, which every script shares. -/
abbrev Entails (Γ : Set (Sen NT Act)) (φ : Sen NT Act) : Prop := (room actAlg NT).Entails Γ φ

/-- The derivability assertion "the nonterminal `x(args)`, called in scope `ρ`, derives the bytes
`bs` with value `v`". It mentions no script: the same sentence can be asked of every script. -/
def derivesNT (x : IL.Id) (args : List IL.Arg) (ρ : VarEnv) (bs : Bytes) (v : Value) :
    Sen NT Act :=
  .derives (.nt (x, args)) bs fun a => ∃ ρ', a ρ [v] ρ'

/-- The derivability assertion for an arbitrary IL symbol, translated in the script `env`. -/
def derivesSym (env : Env) (g : IL.Sym) (ρ : VarEnv) (bs : Bytes) (v : Value) : Sen NT Act :=
  .derives (transSym env g) bs fun a => ∃ ρ', a ρ [v] ρ'

end Script

end Silmaril.Wasm.SpecTec.GrammarInst
