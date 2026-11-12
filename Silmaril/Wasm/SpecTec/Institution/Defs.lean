module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Free
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# An institution of SpecTec specifications

SpecTec specifications (IL scripts) as an institution in the sense of
`Silmaril.Logic.Institution` (a functor `Sign ⥤ Room`). See `docs/projects/spectec/README.md`.

* **Signatures** `Sig`: IL signatures. A set of declared syntax (type) names, a set of declared
  function names, and a set of relation declarations `RelDecl = (x, params, mixop, type)`.
  Signatures are ordered componentwise by inclusion, and the signature category is that
  preorder (`Preorder.smallCategory`): a signature morphism is an inclusion. Renamings of
  relation names are the morphisms of a second signature category (`Institution.Rename`).
* **Sentences** `SSen`: a *rule* `rule d r` (an IL rule `r`, premises `⇒` conclusion, for the
  declared relation `d`) or a *fact* `fact x op args v` (the relation `x` derives `v` at the
  arguments `args`). A sentence belongs to `Σ` (`SSen.InSig`) when its relation declaration is
  in `Σ`, every relation symbol it mentions (conclusion and premises, through iterations) is
  declared in `Σ`, and every function it calls (the `defid` part of `IL.freeRule`, SpecTec's
  `free.ml`) is declared in `Σ`. `Sen Σ` is the subtype; translation along an inclusion is the
  identity.
* **Models** `Model Σ`: an evaluator environment `env` that defines every type and function of
  `Σ` (functions and types are read by our evaluator, `EvalExp`/`HasTyp`, as in `Sim.DDerives`),
  and an interpretation `D : Sim.Interp` of relations that vanishes outside the relation
  symbols of `Σ`. Model morphisms are equalities (a discrete category). The reduct along
  `Σ ≤ Σ'` keeps `env` and restricts `D` to the symbols of `Σ`.
* **Satisfaction** at a *conclusion reading* `alts : Exp → List Exp`: `rule d r` holds when every
  instance of the rule body (some alternative of the conclusion evaluates to `v` under a
  well-typed assignment satisfying the premises, with relations read by `D`) has `D` derive its
  conclusion: the Horn-clause reading. `fact x op args v` holds when `D x op args v`. Two
  readings are used: `decl` (the conclusion itself; `Sim.DDerives`) and `backend` (`conclAlts`;
  `Round6.Reading.DDerivesB`).
* `otherwise` premises are read as **false** in sentences (as `Sim.noElse`): the `otherwise`
  reading (`Sim.otherwise`) is not monotone and is not a Horn sentence. A rule with an
  `otherwise` premise is therefore satisfied by every model; its content is carried only by the
  canonical models below.

The theory of an environment (`theoryOf env`) is the set of its rule sentences, and its
signature is `sigOf env`. The canonical models are `canon env O` (`DDerives env O`) and
`canonB env O` (`DDerivesB env O`): they satisfy the theory at every `otherwise` reading `O`, and
at `O = noElse` they are the *least* models with evaluator `env` (`Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open CategoryTheory
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

/-! ## Signatures -/

/-- A relation symbol: a name and a mixfix operator. -/
abbrev RelSym : Type := IL.Id × MixopS

/-- A relation declaration: name, parameters, mixfix operator and type, as in `relD`. -/
abbrev RelDecl : Type := IL.Id × List Param × MixopS × Typ

/-- The symbol of a relation declaration. -/
def RelDecl.sym (d : RelDecl) : RelSym := (d.1, d.2.2.1)

/-- The parameters of a relation declaration. -/
def RelDecl.params (d : RelDecl) : List Param := d.2.1

/-- The mixfix operator of a relation declaration. -/
def RelDecl.op (d : RelDecl) : MixopS := d.2.2.1

/-- **An IL signature**: declared syntax names, function names and relation declarations. -/
@[ext] structure Sig where
  /-- Declared syntax (type) names. -/
  typs : Set IL.Id
  /-- Declared function names. -/
  funs : Set IL.Id
  /-- Declared relations. -/
  rels : Set RelDecl

namespace Sig

/-- The relation symbols declared by a signature. -/
def relSyms (S : Sig) : Set RelSym := RelDecl.sym '' S.rels

instance : PartialOrder Sig where
  le S T := S.typs ⊆ T.typs ∧ S.funs ⊆ T.funs ∧ S.rels ⊆ T.rels
  le_refl _ := ⟨subset_rfl, subset_rfl, subset_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.trans k.2.2⟩
  le_antisymm S T h k := Sig.ext (h.1.antisymm k.1) (h.2.1.antisymm k.2.1) (h.2.2.antisymm k.2.2)

/-- Inclusion of signatures includes their relation symbols. -/
theorem relSyms_mono {S T : Sig} (h : S ≤ T) : S.relSyms ⊆ T.relSyms :=
  Set.image_mono h.2.2

/-- The common part of two signatures. -/
def common (S T : Sig) : Sig := ⟨S.typs ∩ T.typs, S.funs ∩ T.funs, S.rels ∩ T.rels⟩

theorem common_le_left (S T : Sig) : common S T ≤ S :=
  ⟨Set.inter_subset_left, Set.inter_subset_left, Set.inter_subset_left⟩

theorem common_le_right (S T : Sig) : common S T ≤ T :=
  ⟨Set.inter_subset_right, Set.inter_subset_right, Set.inter_subset_right⟩

end Sig

/-! ## Sentences -/

/-- The relation symbols a premise mentions (through iterations). -/
def premSyms : Prem → List RelSym
  | .rulePr x _ op _ => [(x, op)]
  | .iterPr pr _ => premSyms pr
  | _ => []

/-- The relation symbols the premises of a rule mention. -/
def ruleSyms : Rule → List RelSym
  | .ruleD _ _ _ _ prems => prems.flatMap premSyms

/-- **SpecTec sentences**: rules of a declared relation, and relation facts. -/
inductive SSen where
  /-- The rule `r` of the relation declared by `d`. -/
  | rule (d : RelDecl) (r : Rule)
  /-- The relation `x` (operator `op`) derives `v` at the arguments `args`. -/
  | fact (x : IL.Id) (op : MixopS) (args : List ArgV) (v : Value)

/-- The functions a rule calls: the free `defid`s of `IL.freeRule` (SpecTec's `free_rule`). A
function parameter of the rule is bound, so it is not reported. -/
def ruleFuns (r : Rule) : Finset IL.Id := (IL.freeRule r).defid

/-- A sentence is over `Σ`: its relation is declared, and so is every relation symbol it mentions
and every function it calls. -/
def SSen.InSig (S : Sig) : SSen → Prop
  | .rule d r => d ∈ S.rels ∧ (∀ s ∈ ruleSyms r, s ∈ S.relSyms) ∧ ∀ f ∈ ruleFuns r, f ∈ S.funs
  | .fact x op _ _ => (x, op) ∈ S.relSyms

theorem SSen.InSig.mono {S T : Sig} (h : S ≤ T) : ∀ {φ : SSen}, φ.InSig S → φ.InSig T
  | .rule _ _, hφ => ⟨h.2.2 hφ.1, fun s hs => Sig.relSyms_mono h (hφ.2.1 s hs),
      fun f hf => h.2.1 (hφ.2.2 f hf)⟩
  | .fact _ _ _ _, hφ => Sig.relSyms_mono h hφ

/-- The sentences over `Σ`. -/
def Sen (S : Sig) : Type := {φ : SSen // φ.InSig S}

/-! ## Models -/

/-- **A `Σ`-model**: an evaluator environment defining `Σ`'s types and functions, and an
interpretation of relations vanishing outside `Σ`'s relation symbols. -/
@[ext] structure Model (S : Sig) where
  /-- The evaluator environment: reads types (`HasTyp`) and function calls (`EvalExp`). -/
  env : Env
  /-- The interpretation of relations. -/
  D : Interp
  /-- Every declared type is defined. -/
  typs_def : ∀ x ∈ S.typs, (env.findTyp? x).isSome
  /-- Every declared function is defined. -/
  funs_def : ∀ f ∈ S.funs, (env.findDef? f).isSome
  /-- No undeclared relation derives anything. -/
  vanish : ∀ x op avs w, D x op avs w → (x, op) ∈ S.relSyms

/-- `D` restricted to the relation symbols `R`. -/
def restrictI (R : Set RelSym) (D : Interp) : Interp := fun x op avs w => (x, op) ∈ R ∧ D x op avs w

/-- **The reduct** of a `Σ'`-model along `Σ ≤ Σ'`. -/
def Model.reduct {S T : Sig} (h : S ≤ T) (M : Model T) : Model S where
  env := M.env
  D := restrictI S.relSyms M.D
  typs_def x hx := M.typs_def x (h.1 hx)
  funs_def f hf := M.funs_def f (h.2.1 hf)
  vanish _ _ _ _ hd := hd.1

/-! ## Satisfaction -/

/-- A conclusion reading: the alternatives an IL conclusion may be read as. -/
abbrev Reading : Type := Exp → List Exp

/-- The declarative reading of `Sim.DDerives`: the conclusion itself. -/
def decl : Reading := fun e => [e]

/-- The backend reading of `Round6.Reading.DDerivesB`: `conclAlts`. -/
def backend : Reading := Round6.Reading.conclAlts

/-- The body of a rule at the reading `alts`: `Sim.RuleBody` at some alternative of the
conclusion. At `backend` this is `Round6.Reading.RuleBodyB`. -/
def RuleBodyA (alts : Reading) (env : Env) (D : Interp) (els : Prop) (ps : List Param)
    (args : List ArgV) (op : MixopS) : Rule → Value → Prop
  | .ruleD nm qs op' e prems, v => ∃ e' ∈ alts e, RuleBody env D els ps args op (.ruleD nm qs op' e' prems) v

/-- **Satisfaction** of a sentence by an environment and an interpretation, at the reading
`alts`; `otherwise` premises read as false. -/
def SSen.Sat (alts : Reading) (env : Env) (D : Interp) : SSen → Prop
  | .rule d r => ∀ args v, RuleBodyA alts env D False d.params args d.op r v → D d.1 d.op args v
  | .fact x op args v => D x op args v

/-- An environment and interpretation satisfy every sentence of `T`. -/
def SatTh (alts : Reading) (env : Env) (D : Interp) (T : Set SSen) : Prop :=
  ∀ φ ∈ T, φ.Sat alts env D

/-! ## The signature and theory of a script -/

/-- **The signature of an environment**: its declared types, functions and relations. -/
def sigOf (env : Env) : Sig where
  typs := {x | (env.findTyp? x).isSome}
  funs := {f | (env.findDef? f).isSome}
  rels := {d | ∃ rules, env.findRel? d.1 = some (d.2.1, d.2.2.1, d.2.2.2, rules)}

/-- **The theory of an environment**: every rule of every relation it declares. -/
def theoryOf (env : Env) : Set SSen :=
  {φ | ∃ (d : RelDecl) (rules : List Rule) (r : Rule),
    env.findRel? d.1 = some (d.2.1, d.2.2.1, d.2.2.2, rules) ∧ r ∈ rules ∧ φ = .rule d r}

/-- The theory of an environment, as sentences of its signature: the rules whose premises
mention declared relations and call declared functions only (all of them, for a well-formed
script; not proved here). -/
def theoryIn (env : Env) : Set (Sen (sigOf env)) := {φ | φ.1 ∈ theoryOf env}

/-- The sentence `Step` (operator `%~>%`) derives `(c, c')`: SpecTec's whole-machine step. -/
def stepFact (c c' : Value) : SSen := .fact "Step" "%~>%" [] (.tuple [c, c'])

/-! ## Versions as partial theory morphisms -/

/-- The rules of `env₁` that `env₂` keeps verbatim (same declaration, same rule). -/
def retained (env₁ env₂ : Env) : Set SSen := theoryOf env₁ ∩ theoryOf env₂

/-- The rules of `env₁` that `env₂` does not keep verbatim: the failures of the inclusion
`theoryOf env₁ → theoryOf env₂` to be a theory morphism. -/
def dropped (env₁ env₂ : Env) : Set SSen := theoryOf env₁ \ theoryOf env₂

end Silmaril.Wasm.SpecTec.Institution
