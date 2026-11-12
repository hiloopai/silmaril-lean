module

public import Silmaril.Wasm.SpecTec.Institution.Defs

/-!
# Renaming identifiers in IL syntax, scopes and environments

The relational institution's signature morphisms are inclusions (`Institution.Defs`) or
renamings of relation names (`Institution.Rename`). Renaming **function and type names** needs a
renaming of the whole expression syntax and of the evaluator's environment, which is defined
here.

`rn f` renames every identifier of a piece of IL syntax by `f : IL.Id → IL.Id`: type names,
function names, relation names, grammar names and variables alike. The SpecTec name spaces are
kept apart by the environment's maps, not by the identifiers, so one renaming of all of them is
the uniform choice; a renaming of function names alone is the special case of an `f` that moves
only function names. Values contain no identifiers (`Value` has only atoms and mixfix operators),
so they are not renamed; evaluated arguments (`ArgV`) are.

* `rnTyp`, `rnExp`, …, `rnProd`: the syntax, one mutual recursion over the IL's mutual block.
* `rnArgV`, `rnMap`, `rnVarEnv`: evaluated arguments, maps (keys and entries) and scopes.
* `rnEnv π`: an environment renamed along a permutation `π`. Its built-in functions are read
  through `π.symm`, so that a renamed call reaches the built-in of the original name.
* `rnI π D`: an interpretation of relations renamed along `π`.

The laws (`rn` is functorial, so `rnEnv π.symm` undoes `rnEnv π`) and the equivariance of the
evaluator are in `Silmaril.Proofs.Wasm.SpecTec.Institution.Perm*`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

variable (f : IL.Id → IL.Id)

mutual

/-- Rename an iteration. -/
def rnIter : Iter → Iter
  | .opt => .opt
  | .list => .list
  | .list1 => .list1
  | .listN e x => .listN (rnExp e) (rnIdOpt x)

/-- Rename an optional identifier. -/
def rnIdOpt : Option IL.Id → Option IL.Id
  | none => none
  | some x => some (f x)

/-- Rename a type. -/
def rnTyp : Typ → Typ
  | .varT x args => .varT (f x) (rnArgs args)
  | .boolT => .boolT
  | .numT t => .numT t
  | .textT => .textT
  | .tupT bs => .tupT (rnTypBinds bs)
  | .iterT t it => .iterT (rnTyp t) (rnIter it)

/-- Rename a tuple binder. -/
def rnTypBind : TypBind → TypBind
  | .mk x t => .mk (f x) (rnTyp t)

/-- Rename tuple binders. -/
def rnTypBinds : List TypBind → List TypBind
  | [] => []
  | b :: bs => rnTypBind b :: rnTypBinds bs

/-- Rename a type definition. -/
def rnDefTyp : DefTyp → DefTyp
  | .aliasT t => .aliasT (rnTyp t)
  | .structT fs => .structT (rnTypFields fs)
  | .variantT cs => .variantT (rnTypCases cs)

/-- Rename a record field type. -/
def rnTypField : TypField → TypField
  | .mk a t qs prems => .mk a (rnTyp t) (rnParams qs) (rnPrems prems)

/-- Rename record field types. -/
def rnTypFields : List TypField → List TypField
  | [] => []
  | c :: cs => rnTypField c :: rnTypFields cs

/-- Rename a variant case. -/
def rnTypCase : TypCase → TypCase
  | .mk op t qs prems => .mk op (rnTyp t) (rnParams qs) (rnPrems prems)

/-- Rename variant cases. -/
def rnTypCases : List TypCase → List TypCase
  | [] => []
  | c :: cs => rnTypCase c :: rnTypCases cs

/-- Rename an expression. -/
def rnExp : Exp → Exp
  | .varE x => .varE (f x)
  | .boolE b => .boolE b
  | .numE n => .numE n
  | .textE t => .textE t
  | .unE op t e => .unE op t (rnExp e)
  | .binE op t e₁ e₂ => .binE op t (rnExp e₁) (rnExp e₂)
  | .cmpE op t e₁ e₂ => .cmpE op t (rnExp e₁) (rnExp e₂)
  | .tupE es => .tupE (rnExps es)
  | .projE e i => .projE (rnExp e) i
  | .caseE op e => .caseE op (rnExp e)
  | .uncaseE e op => .uncaseE (rnExp e) op
  | .optE eo => .optE (rnExpOpt eo)
  | .theE e => .theE (rnExp e)
  | .strE fs => .strE (rnExpFields fs)
  | .dotE e a => .dotE (rnExp e) a
  | .compE e₁ e₂ => .compE (rnExp e₁) (rnExp e₂)
  | .listE es => .listE (rnExps es)
  | .liftE e => .liftE (rnExp e)
  | .memE e₁ e₂ => .memE (rnExp e₁) (rnExp e₂)
  | .lenE e => .lenE (rnExp e)
  | .catE e₁ e₂ => .catE (rnExp e₁) (rnExp e₂)
  | .idxE e₁ e₂ => .idxE (rnExp e₁) (rnExp e₂)
  | .sliceE e₁ e₂ e₃ => .sliceE (rnExp e₁) (rnExp e₂) (rnExp e₃)
  | .updE e₁ p e₂ => .updE (rnExp e₁) (rnPath p) (rnExp e₂)
  | .extE e₁ p e₂ => .extE (rnExp e₁) (rnPath p) (rnExp e₂)
  | .callE x args => .callE (f x) (rnArgs args)
  | .iterE e it => .iterE (rnExp e) (rnIterExp it)
  | .cvtE e t₁ t₂ => .cvtE (rnExp e) t₁ t₂
  | .subE e t₁ t₂ => .subE (rnExp e) (rnTyp t₁) (rnTyp t₂)

/-- Rename an optional expression. -/
def rnExpOpt : Option Exp → Option Exp
  | none => none
  | some e => some (rnExp e)

/-- Rename expressions. -/
def rnExps : List Exp → List Exp
  | [] => []
  | e :: es => rnExp e :: rnExps es

/-- Rename a record field. -/
def rnExpField : ExpField → ExpField
  | .mk a e => .mk a (rnExp e)

/-- Rename record fields. -/
def rnExpFields : List ExpField → List ExpField
  | [] => []
  | c :: cs => rnExpField c :: rnExpFields cs

/-- Rename a path. -/
def rnPath : Path → Path
  | .rootP => .rootP
  | .idxP p e => .idxP (rnPath p) (rnExp e)
  | .sliceP p e₁ e₂ => .sliceP (rnPath p) (rnExp e₁) (rnExp e₂)
  | .dotP p a => .dotP (rnPath p) a

/-- Rename an iteration with its domains. -/
def rnIterExp : IterExp → IterExp
  | .mk it ds => .mk (rnIter it) (rnDoms ds)

/-- Rename a domain. -/
def rnDom : Dom → Dom
  | .mk x e => .mk (f x) (rnExp e)

/-- Rename domains. -/
def rnDoms : List Dom → List Dom
  | [] => []
  | d :: ds => rnDom d :: rnDoms ds

/-- Rename a grammar symbol. -/
def rnSym : Sym → Sym
  | .varG x args => .varG (f x) (rnArgs args)
  | .numG n => .numG n
  | .textG t => .textG t
  | .epsG => .epsG
  | .seqG gs => .seqG (rnSyms gs)
  | .altG gs => .altG (rnSyms gs)
  | .rangeG g₁ g₂ => .rangeG (rnSym g₁) (rnSym g₂)
  | .iterG g it => .iterG (rnSym g) (rnIterExp it)
  | .attrG e g => .attrG (rnExp e) (rnSym g)

/-- Rename grammar symbols. -/
def rnSyms : List Sym → List Sym
  | [] => []
  | g :: gs => rnSym g :: rnSyms gs

/-- Rename an argument. -/
def rnArg : Arg → Arg
  | .expA e => .expA (rnExp e)
  | .typA t => .typA (rnTyp t)
  | .defA x => .defA (f x)
  | .gramA g => .gramA (rnSym g)

/-- Rename arguments. -/
def rnArgs : List Arg → List Arg
  | [] => []
  | a :: l => rnArg a :: rnArgs l

/-- Rename a parameter. -/
def rnParam : Param → Param
  | .expP x t => .expP (f x) (rnTyp t)
  | .typP x => .typP (f x)
  | .defP x ps t => .defP (f x) (rnParams ps) (rnTyp t)
  | .gramP x ps t => .gramP (f x) (rnParams ps) (rnTyp t)

/-- Rename parameters. -/
def rnParams : List Param → List Param
  | [] => []
  | p :: ps => rnParam p :: rnParams ps

/-- Rename a premise. -/
def rnPrem : Prem → Prem
  | .rulePr x args op e => .rulePr (f x) (rnArgs args) op (rnExp e)
  | .ifPr e => .ifPr (rnExp e)
  | .letPr e₁ e₂ => .letPr (rnExp e₁) (rnExp e₂)
  | .elsePr => .elsePr
  | .iterPr pr it => .iterPr (rnPrem pr) (rnIterExp it)

/-- Rename premises. -/
def rnPrems : List Prem → List Prem
  | [] => []
  | p :: ps => rnPrem p :: rnPrems ps

/-- Rename a family instance. -/
def rnInst : Inst → Inst
  | .instD qs args dt => .instD (rnParams qs) (rnArgs args) (rnDefTyp dt)

/-- Rename family instances. -/
def rnInsts : List Inst → List Inst
  | [] => []
  | i :: l => rnInst i :: rnInsts l

/-- Rename a rule. -/
def rnRule : Rule → Rule
  | .ruleD x qs op e prems => .ruleD (f x) (rnParams qs) op (rnExp e) (rnPrems prems)

/-- Rename rules. -/
def rnRules : List Rule → List Rule
  | [] => []
  | r :: rs => rnRule r :: rnRules rs

/-- Rename a definition clause. -/
def rnClause : Clause → Clause
  | .defD qs args e prems => .defD (rnParams qs) (rnArgs args) (rnExp e) (rnPrems prems)

/-- Rename definition clauses. -/
def rnClauses : List Clause → List Clause
  | [] => []
  | c :: cs => rnClause c :: rnClauses cs

/-- Rename a production. -/
def rnProd : IL.Prod → IL.Prod
  | .prodD qs g e prems => .prodD (rnParams qs) (rnSym g) (rnExp e) (rnPrems prems)

/-- Rename productions. -/
def rnProds : List IL.Prod → List IL.Prod
  | [] => []
  | p :: ps => rnProd p :: rnProds ps

end

/-! ## Evaluated arguments, maps, scopes and environments -/

/-- Rename an evaluated argument (values carry no identifiers). -/
def rnArgV : ArgV → ArgV
  | .val v => .val v
  | .typ t => .typ (rnTyp f t)
  | .defName x => .defName (f x)
  | .gram g => .gram (rnSym f g)

/-- Rename a map: its keys by `f`, its entries by `g`. -/
def rnMap {α : Type} (g : α → α) (m : Map α) : Map α := m.map fun p => (f p.1, g p.2)

/-- Rename a scope. -/
def rnVarEnv (ρ : VarEnv) : VarEnv :=
  ⟨rnMap f id ρ.vals, rnMap f (rnTyp f) ρ.typs, rnMap f f ρ.defs, rnMap f (rnSym f) ρ.grams⟩

/-- Rename a type definition entry. -/
def rnTypDef (d : TypDef) : TypDef := (rnParams f d.1, rnInsts f d.2)

/-- Rename a relation definition entry. -/
def rnRelDef (d : RelDef) : RelDef := (rnParams f d.1, d.2.1, rnTyp f d.2.2.1, rnRules f d.2.2.2)

/-- Rename a function definition entry. -/
def rnDefDef (d : DefDef) : DefDef := (rnParams f d.1, rnTyp f d.2.1, rnClauses f d.2.2)

/-- Rename a grammar definition entry. -/
def rnGramDef (d : GramDef) : GramDef := (rnParams f d.1, rnTyp f d.2.1, rnProds f d.2.2)

/-- Rename an environment along a permutation `π`. The built-ins of a renamed name are those of
the original name, at the original arguments. -/
def rnEnv (π : Equiv.Perm IL.Id) (env : Env) : Env where
  vars := rnMap π (rnTyp π) env.vars
  typs := rnMap π (rnTypDef π) env.typs
  defs := rnMap π (rnDefDef π) env.defs
  rels := rnMap π (rnRelDef π) env.rels
  grams := rnMap π (rnGramDef π) env.grams
  builtins := ⟨fun x ws => env.builtins.call (π.symm x) (ws.map (rnArgV π.symm))⟩

/-- An interpretation of relations renamed along `π`: the renamed relation derives at renamed
arguments what the original derives. -/
def rnI (π : Equiv.Perm IL.Id) (D : Interp) : Interp :=
  fun x op avs v => D (π.symm x) op (avs.map (rnArgV π.symm)) v

/-! ## Sentences -/

/-- Rename a relation declaration. -/
def rnDecl (d : RelDecl) : RelDecl := (f d.1, rnParams f d.2.1, d.2.2.1, rnTyp f d.2.2.2)

/-- Rename a sentence: the relation, its declaration, its rule and its arguments. -/
def rnS : SSen → SSen
  | .rule d r => .rule (rnDecl f d) (rnRule f r)
  | .fact x op args v => .fact (f x) op (args.map (rnArgV f)) v

/-- A conclusion reading is **equivariant** when renaming a conclusion renames its alternatives.
`decl` is (`decl_equivariant`). -/
def Equivariant (alts : Reading) : Prop :=
  ∀ (g : IL.Id → IL.Id) (e e' : Exp), e' ∈ alts e → rnExp g e' ∈ alts (rnExp g e)

end Silmaril.Wasm.SpecTec.Institution.Perm
