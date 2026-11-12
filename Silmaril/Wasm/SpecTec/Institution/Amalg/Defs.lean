module

public import Silmaril.Wasm.SpecTec.Institution.Defs
public import Silmaril.Wasm.SpecTec.GrammarInst.Defs

/-!
# Whole SpecTec scripts with a shared evaluator: the amalgamated institution

`Institution.Juxt` combines the relational institution and the grammar institution as a sum: a
model is a pair of models, and nothing makes the two halves use the same functions. Here the two
are **amalgamated** over the evaluator: a model carries one environment `env`, and `env` evaluates
both the expressions and premises of relation rules (`EvalExp env`, as in `Sim.DDerives`) and the
attribute actions of grammar productions (`Sem.transProd env`, as in `Sem.gramOf`).

* **Signatures** `ASig`: an IL signature (types, functions, relations) and a set of grammar
  names, ordered componentwise; the category is that preorder.
* **Sentences** `ASen`, kept syntactic so that the model's evaluator reads them:
  - `rel φ`: a sentence of the relational institution;
  - `prod x ps p`: the IL production `p` of the grammar `x` with parameters `ps`, read as the
    Horn clauses `x(args) ::= transProd env ps args p` for every argument list `args`;
  - `derives g ρ bs v`: the IL symbol `g`, started in scope `ρ`, derives `bs` with value `v`.
  `rel φ` is over `Σ` when `φ` is; `prod x ps p` when `x` is a declared grammar name.
* **Models** `AModel Σ`: a relational model (`env`, `D`) and an interpretation `I` of the
  nonterminals `Sem.NT`. The reduct restricts `D` and keeps `env` and `I`: grammar
  interpretations are, like the evaluator, not restricted (restricting them would need the
  locality of `transSym` in the nonterminals, which is not proved).
* **Satisfaction** `ASen.Sat`: the relational satisfaction for `rel`, and the grammar
  institution's satisfaction (`GrammarInst.Sen.Holds`) of the sentences **translated with the
  model's own evaluator** for `prod` and `derives`.

`wholeTheory env` is the theory of a script: its relation rules and its productions. The
canonical model `canonW env O` interprets relations by `DDerivesB env O` and nonterminals by the
least model of `Sem.gramOf env`; at `O = noElse` it is the least model with evaluator `env`
(`Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril (EncRel)
open Silmaril.SpecTec.Grammar (Bytes)
open Silmaril.Wasm.SpecTec.Sim

/-- **A whole-script signature**: an IL signature and a set of grammar names. -/
@[ext] structure ASig where
  /-- Types, functions and relations. -/
  rel : Sig
  /-- Grammar names. -/
  grams : Set IL.Id

instance : PartialOrder ASig where
  le S T := S.rel ≤ T.rel ∧ S.grams ⊆ T.grams
  le_refl _ := ⟨le_rfl, subset_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  le_antisymm S T h k := ASig.ext (le_antisymm h.1 k.1) (h.2.antisymm k.2)

/-- **Whole-script sentences.** -/
inductive ASen where
  /-- A sentence of the relational institution. -/
  | rel (φ : SSen)
  /-- The production `p` of the grammar `x` with parameters `ps`, at every argument list. -/
  | prod (x : IL.Id) (ps : List Param) (p : IL.Prod)
  /-- `g`, started in the scope `ρ`, derives `bs` with value `v`. -/
  | derives (g : IL.Sym) (ρ : VarEnv) (bs : Bytes) (v : Value)

/-- A whole-script sentence is over `Σ`. -/
def ASen.InSig (S : ASig) : ASen → Prop
  | .rel φ => φ.InSig S.rel
  | .prod x _ _ => x ∈ S.grams
  | .derives _ _ _ _ => True

/-- The sentences over `Σ`. -/
def ASenOf (S : ASig) : Type := {φ : ASen // φ.InSig S}

/-- **A whole-script model**: a relational model and an interpretation of the nonterminals. -/
@[ext] structure AModel (S : ASig) where
  /-- The evaluator and the interpretation of relations. -/
  base : Model S.rel
  /-- The interpretation of the nonterminals. -/
  I : NT → EncRel Bytes Act

/-- The reduct: restrict the relations, keep the evaluator and the nonterminals. -/
def AModel.reduct {S T : ASig} (h : S ≤ T) (M : AModel T) : AModel S := ⟨M.base.reduct h.1, M.I⟩

/-- The grammar-institution sentence of a production, at the evaluator `env` and arguments
`args`. -/
def prodSen (env : Env) (x : IL.Id) (ps : List Param) (args : List IL.Arg) (p : IL.Prod) :
    GrammarInst.Sen NT Act :=
  .prod (x, args) (transProd env ps args p)

/-- **Satisfaction**, with one evaluator `env` for relations and grammars. -/
def ASen.Sat (alts : Reading) (env : Env) (D : Interp) (I : NT → EncRel Bytes Act) : ASen → Prop
  | .rel φ => φ.Sat alts env D
  | .prod x ps p => ∀ args, (prodSen env x ps args p).Holds actAlg I
  | .derives g ρ bs v => (GrammarInst.derivesSym env g ρ bs v).Holds actAlg I

/-- **The signature of a script**: its IL signature and its grammar names. -/
def asigOf (env : Env) : ASig := ⟨sigOf env, {x | (env.findGram? x).isSome}⟩

/-- **The theory of a whole script**: its relation rules and its productions. -/
def wholeTheory (env : Env) : Set ASen :=
  {ψ | (∃ φ ∈ theoryOf env, ψ = .rel φ) ∨
    ∃ x ps t prods p, env.findGram? x = some (ps, t, prods) ∧ p ∈ prods ∧ ψ = .prod x ps p}

/-- A model satisfies a set of whole-script sentences. -/
def ASatTh (alts : Reading) (env : Env) (D : Interp) (I : NT → EncRel Bytes Act)
    (Th : Set ASen) : Prop :=
  ∀ ψ ∈ Th, ψ.Sat alts env D I

/-- **Consequence at an evaluator**: every model with evaluator `env` that satisfies `Th`
satisfies `ψ`. -/
def EntailsAt (alts : Reading) (env : Env) (Th : Set ASen) (ψ : ASen) : Prop :=
  ∀ (D : Interp) (I : NT → EncRel Bytes Act), ASatTh alts env D I Th → ψ.Sat alts env D I

end Silmaril.Wasm.SpecTec.Institution
