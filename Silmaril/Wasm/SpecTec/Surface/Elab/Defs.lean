module

public import Silmaril.Wasm.SpecTec.Surface.Parser.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast

/-!
# SpecTec surface syntax: elaboration to the IL

Elaboration of the fragment's declarations to SpecTec's internal language
`Silmaril.SpecTec.IL`, transcribed from
`specs/spectec/src/spectec/src/frontend/elab.ml` for the cases the fragment
reaches:

* a syntax alias `syntax x hint* = t` is
  `TypD (x, [], [InstD ([], [], AliasT t')])` (`elab.ml:2611-2645`), its hints
  becoming a `HintD` that the `--ast` printer drops;
* a signature `def $f(ps) : t` and every clause `def $f(as) = e -- prems` of
  the same `f` form one `DecD (f, ps', t', clauses')`: pass 1 emits the
  `DecD` at the signature (`elab.ml:2678-2687`), pass 2 elaborates each clause
  (`elab.ml:2769-2785`), and `populate_def` attaches the clauses in order
  (`elab.ml:2817-2835`);
* a declaration that is not recursive stays unwrapped by `recursify_defs`
  (`elab.ml:2895`). The fragment rejects a function whose clauses call it.

`Elab` is the relation, `elab?` the function, and `elab?_sound` (in
`Silmaril.Wasm.SpecTec.Surface.Elab.Thms`) says the function is sound for the
relation.

## What is simplified

* Types are checked only as far as the fragment needs: a type name must have
  been declared earlier in the script (`elab.ml:866-876`), arguments of types
  are not supported.
* A clause's quantifiers are its argument variables, in order. Each has the
  type of the declared syntax type of the same name when there is one (types
  without parameters double as variables, `elab.ml:2560`, looked up with
  `strip_var_suffix` at `elab.ml:270`; here only trailing primes are
  stripped), and otherwise the type of its parameter (`elab.ml:265-269`).
  Arguments other than variables and numerals, and variables in the body or
  premises not bound by the arguments, are outside the fragment.
* The operator type of a comparison or arithmetic operation is the numeric
  type of its left operand, after expanding one alias.
* Parameters come from arguments as `El.Convert.param_of_arg` does: a type
  name `t` gives the parameter named `t`, an iterated type the parameter `_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Elab

open Silmaril.Wasm.SpecTec.Surface.Syntax
open Silmaril.SpecTec

/-- The elaboration context: the parameterless syntax types declared so far,
each with its definition after expanding one alias. -/
structure Ctx where
  /-- Declared syntax types and their (expanded) alias targets. -/
  typs : List (String × IL.Typ)
  /-- Declared grammars with one parameter: name, parameter name, result
  type. -/
  grams : List (String × String × IL.Typ) := []

/-- The empty context. -/
def Ctx.empty : Ctx := ⟨[], []⟩

/-- The signature of a grammar. -/
def Ctx.gram? (Γ : Ctx) (g : String) : Option (String × IL.Typ) := Γ.grams.lookup g

/-- The context an IL script declares: its type definitions (an alias by its
target) and its one-parameter grammars by their signatures. This is how a
declaration is elaborated "in the context of the rest of a specification". -/
def Ctx.ofScript (s : IL.Script) : Ctx where
  typs := s.filterMap fun
    | .typD x [] [.instD [] [] (.aliasT t)] => some (x, t)
    | .typD x _ _ => some (x, .varT x [])
    | _ => none
  grams := s.filterMap fun
    | .gramD x [.expP p _] t _ => some (x, p, t)
    | _ => none

/-- The definition of a declared type name. -/
def Ctx.find? (Γ : Ctx) (x : String) : Option IL.Typ := Γ.typs.lookup x

/-- Expand a type name by one alias. -/
def Ctx.expand (Γ : Ctx) : IL.Typ → IL.Typ
  | .varT x [] => (Γ.find? x).getD (.varT x [])
  | t => t

/-! ## Types -/

/-- `iter` to `Il.iter`. -/
def elabIter : Iter → IL.Iter
  | .opt => .opt
  | .list => .list
  | .list1 => .list1

/-- `numtyp` to `Num.typ`. -/
def elabNumTyp : NumTyp → IL.NumTyp
  | .nat => .natT
  | .int => .intT
  | .rat => .ratT
  | .real => .realT

/-- `elab_typ` (`elab.ml:864-880`) for the fragment. -/
inductive ElabTyp (Γ : Ctx) : Typ → IL.Typ → Prop where
  | var {x : List Char} : (Γ.find? (String.ofList x)).isSome → ElabTyp Γ (.var x []) (.varT (String.ofList x) [])
  | bool : ElabTyp Γ .bool .boolT
  | num {t : NumTyp} : ElabTyp Γ (.num t) (.numT (elabNumTyp t))
  | text : ElabTyp Γ .text .textT
  | iter {t : Typ} {t' : IL.Typ} {it : Iter} :
      ElabTyp Γ t t' → ElabTyp Γ (.iter t it) (.iterT t' (elabIter it))

/-- `elab_typ`, as a function. -/
def elabTyp? (Γ : Ctx) : Typ → Option IL.Typ
  | .var x [] => if (Γ.find? (String.ofList x)).isSome then some (.varT (String.ofList x) []) else none
  | .var _ (_ :: _) => none
  | .bool => some .boolT
  | .num t => some (.numT (elabNumTyp t))
  | .text => some .textT
  | .iter t it => (elabTyp? Γ t).map (.iterT · (elabIter it))

/-! ## Expressions -/

/-- The decimal value of a `NATLIT`'s digits, `_` separators skipped
(`lexer.mll:22`, `Z.of_string`). -/
def natValue (s : List Char) : Nat :=
  s.foldl (fun n c => if c = '_' then n else 10 * n + (c.toNat - '0'.toNat)) 0

/-- The local variables of a clause, with their types. -/
abbrev Vars := List (String × IL.Typ)

/-- `cmpop` to `Num.cmpop`. -/
def elabCmp : CmpOp → IL.CmpOp
  | .eq => .eqOp
  | .ne => .neOp
  | .lt => .ltOp
  | .gt => .gtOp
  | .le => .leOp
  | .ge => .geOp

/-- `binop` to `Num.binop`. -/
def elabBin : BinOp → IL.BinOp
  | .add => .addOp
  | .sub => .subOp
  | .mul => .mulOp
  | .div => .divOp
  | .mod => .modOp

/-- The numeric operator type of an operand: a variable's type after expanding
one alias, or `nat` for a numeral. -/
def opTyp? (Γ : Ctx) (vs : Vars) : Exp → Option IL.OpTyp
  | .var x [] =>
    match (vs.lookup (String.ofList x)).map Γ.expand with
    | some (.numT t) => some (.numT t)
    | _ => none
  | .nat _ => some (.numT .natT)
  | _ => none

/-- `elab_exp` (`elab.ml:1337`) for the fragment: variables, numerals, calls,
parentheses (which leave no node), comparisons and arithmetic. -/
inductive ElabExp (Γ : Ctx) (vs : Vars) : Exp → IL.Exp → Prop where
  | var {x : List Char} : (vs.lookup (String.ofList x)).isSome → ElabExp Γ vs (.var x []) (.varE (String.ofList x))
  | nat {s : List Char} : ElabExp Γ vs (.nat s) (.numE (.natN (natValue s)))
  | paren {e : Exp} {e' : IL.Exp} : ElabExp Γ vs e e' → ElabExp Γ vs (.paren e) e'
  | call {f : List Char} {as : List Exp} {as' : List IL.Exp} :
      List.Forall₂ (ElabExp Γ vs) as as' →
      ElabExp Γ vs (.call f as) (.callE (String.ofList f) (as'.map .expA))
  | cmp {op : CmpOp} {e₁ e₂ : Exp} {t : IL.OpTyp} {e₁' e₂' : IL.Exp} :
      opTyp? Γ vs e₁ = some t → ElabExp Γ vs e₁ e₁' → ElabExp Γ vs e₂ e₂' →
      ElabExp Γ vs (.cmp op e₁ e₂) (.cmpE (elabCmp op) t e₁' e₂')
  | bin {op : BinOp} {e₁ e₂ : Exp} {t : IL.OpTyp} {e₁' e₂' : IL.Exp} :
      opTyp? Γ vs e₁ = some t → ElabExp Γ vs e₁ e₁' → ElabExp Γ vs e₂ e₂' →
      ElabExp Γ vs (.bin op e₁ e₂) (.binE (elabBin op) t e₁' e₂')

/-- `elab_exp`, as a function. -/
def elabExp? (Γ : Ctx) (vs : Vars) : Exp → Option IL.Exp
  | .var x [] =>
    if (vs.lookup (String.ofList x)).isSome then some (.varE (String.ofList x)) else none
  | .nat s => some (.numE (.natN (natValue s)))
  | .paren e => elabExp? Γ vs e
  | .call f as => (elabExps? Γ vs as).map fun as' => .callE (String.ofList f) (as'.map .expA)
  | .cmp op e₁ e₂ =>
    match opTyp? Γ vs e₁, elabExp? Γ vs e₁, elabExp? Γ vs e₂ with
    | some t, some e₁', some e₂' => some (.cmpE (elabCmp op) t e₁' e₂')
    | _, _, _ => none
  | .bin op e₁ e₂ =>
    match opTyp? Γ vs e₁, elabExp? Γ vs e₁, elabExp? Γ vs e₂ with
    | some t, some e₁', some e₂' => some (.binE (elabBin op) t e₁' e₂')
    | _, _, _ => none
  | _ => none
where
  /-- A list of expressions. -/
  elabExps? (Γ : Ctx) (vs : Vars) : List Exp → Option (List IL.Exp)
    | [] => some []
    | e :: es =>
      match elabExp? Γ vs e, elabExps? Γ vs es with
      | some e', some es' => some (e' :: es')
      | _, _ => none

/-! ## Premises -/

/-- `elab_prem` (`elab.ml:2030-2050`) for `if` and `otherwise`. -/
inductive ElabPrem (Γ : Ctx) (vs : Vars) : Prem → IL.Prem → Prop where
  | ifP {e : Exp} {e' : IL.Exp} : ElabExp Γ vs e e' → ElabPrem Γ vs (.ifP e) (.ifPr e')
  | otherwise : ElabPrem Γ vs .otherwise .elsePr

/-- `elab_prem`, as a function. -/
def elabPrem? (Γ : Ctx) (vs : Vars) : Prem → Option IL.Prem
  | .ifP e => (elabExp? Γ vs e).map .ifPr
  | .otherwise => some .elsePr

/-! ## Parameters and clauses -/

/-- `El.Convert.param_of_arg` and `elab_param` (`elab.ml:2429-2445`): a type
written as an argument gives a parameter named after a type name, or `_`. -/
def paramName : Typ → String
  | .var x _ => String.ofList x
  | .bool => "bool"
  | .num .nat => "nat"
  | .num .int => "int"
  | .num .rat => "rat"
  | .num .real => "real"
  | .text => "text"
  | .iter _ _ => "_"

/-- A signature argument read back as a type (the argument side of
`El.Convert.param_of_arg`): type names and their iterations. -/
def typOfArg? : Exp → Option Typ
  | .var x [] =>
    if x = "bool".toList then some .bool
    else if x = "nat".toList then some (.num .nat)
    else if x = "int".toList then some (.num .int)
    else if x = "rat".toList then some (.num .rat)
    else if x = "real".toList then some (.num .real)
    else if x = "text".toList then some .text
    else some (.var x [])
  | .iter e it => (typOfArg? e).map (.iter · it)
  | _ => none

/-- A signature argument elaborated as a parameter. -/
inductive ElabParam (Γ : Ctx) : Exp → IL.Param → Prop where
  | mk {e : Exp} {t : Typ} {t' : IL.Typ} :
      typOfArg? e = some t → ElabTyp Γ t t' → ElabParam Γ e (.expP (paramName t) t')

/-- `ElabParam`, as a function. -/
def elabParam? (Γ : Ctx) (e : Exp) : Option IL.Param :=
  match typOfArg? e with
  | some t => (elabTyp? Γ t).map (.expP (paramName t))
  | none => none

/-- A variable name with trailing primes removed (part of `strip_var_suffix`). -/
def stripPrimes (x : List Char) : List Char := (x.reverse.dropWhile (· == '\'')).reverse

/-- The type of a clause variable bound at a parameter of type `t`: the
declared syntax type of the same name, if any, otherwise `t`. -/
def varTyp (Γ : Ctx) (x : List Char) (t : IL.Typ) : IL.Typ :=
  if (Γ.find? (String.ofList (stripPrimes x))).isSome then .varT (String.ofList (stripPrimes x)) []
  else t

/-- The quantifiers bound by a clause's arguments against the parameters. -/
inductive ArgQuants (Γ : Ctx) : List Exp → List IL.Param → Vars → Prop where
  | nil : ArgQuants Γ [] [] []
  | var {x : List Char} {as : List Exp} {p : String} {t : IL.Typ} {ps : List IL.Param} {vs : Vars} :
      ArgQuants Γ as ps vs →
      ArgQuants Γ (.var x [] :: as) (.expP p t :: ps) ((String.ofList x, varTyp Γ x t) :: vs)
  | nat {s : List Char} {as : List Exp} {p : IL.Param} {ps : List IL.Param} {vs : Vars} :
      ArgQuants Γ as ps vs → ArgQuants Γ (.nat s :: as) (p :: ps) vs

/-- `ArgQuants`, as a function. -/
def argQuants? (Γ : Ctx) : List Exp → List IL.Param → Option Vars
  | [], [] => some []
  | .var x [] :: as, .expP _ t :: ps =>
    (argQuants? Γ as ps).map ((String.ofList x, varTyp Γ x t) :: ·)
  | .nat _ :: as, _ :: ps => argQuants? Γ as ps
  | _, _ => none

/-- The IL quantifiers of a clause, from its variables. -/
def quantsOf (vs : Vars) : List IL.Param := vs.map fun (x, t) => .expP x t

/-- `elab_def_pass2` on `DefD` (`elab.ml:2769-2785`) for the fragment: a
clause against the function's parameters. -/
inductive ElabClause (Γ : Ctx) (ps : List IL.Param) : Exp → List Exp → Exp → List Prem → IL.Clause → Prop where
  | mk {f : Exp} {as : List Exp} {e : Exp} {prems : List Prem} {vs : Vars} {as' : List IL.Exp}
      {e' : IL.Exp} {prems' : List IL.Prem} :
      ArgQuants Γ as ps vs → List.Forall₂ (ElabExp Γ vs) as as' → ElabExp Γ vs e e' →
      List.Forall₂ (ElabPrem Γ vs) prems prems' →
      ElabClause Γ ps f as e prems (.defD (quantsOf vs) (as'.map .expA) e' prems')

/-! ## Grammars -/

/-- Substitute `e` for the variable `p` in the arguments of a type
application, one level deep (enough for result types such as `uN(N)`). -/
def substTyp (p : String) (e : IL.Exp) : IL.Typ → IL.Typ
  | .varT x as => .varT x (as.map fun
      | .expA (.varE y) => if y = p then .expA e else .expA (.varE y)
      | a => a)
  | t => t

/-- The name of the implicit production result (`parser.mly:137`). -/
def implicitResult : String := "<implicit-prod-result>"

/-- The single production of a grammar alias `x : t = g(a)`: the short
production `<implicit-prod-result>:g(a) => <implicit-prod-result>`
(`parser.mly:136-139`), whose variable has the result type of `g` at `a`
(`infer_sym` in `elab_prod`, `elab.ml:2210-2225`). -/
def gramProd (g : String) (a' : IL.Exp) (τ : IL.Typ) : IL.Prod :=
  .prodD [.expP implicitResult τ] (.attrG (.varE implicitResult) (.varG g [.expA a']))
    (.varE implicitResult) []

/-! ## Scripts -/

/-- The clauses of `f` in a script, in order (the order `populate_def`
attaches them in). -/
def clausesOf (f : List Char) : List Def → List (List Exp × Exp × List Prem)
  | [] => []
  | .decClause g as e ps :: ds => if g = f then (as, e, ps) :: clausesOf f ds else clausesOf f ds
  | _ :: ds => clausesOf f ds

/-- The functions an IL expression calls (for the recursion check). -/
def callsIn : IL.Exp → List String
  | .callE f as => f :: callsInArgs as
  | .cmpE _ _ e₁ e₂ => callsIn e₁ ++ callsIn e₂
  | .binE _ _ e₁ e₂ => callsIn e₁ ++ callsIn e₂
  | _ => []
where
  /-- The functions a list of arguments calls. -/
  callsInArgs : List IL.Arg → List String
    | [] => []
    | .expA e :: as => callsIn e ++ callsInArgs as
    | _ :: as => callsInArgs as

/-- The functions a clause calls, in its body and `if` premises. -/
def clauseCalls : IL.Clause → List String
  | .defD _ _ e prems => callsIn e ++ prems.flatMap fun
      | .ifPr e => callsIn e
      | _ => []

/-- Elaboration of a script `ds`, declaration by declaration, with `all` the
whole script (for collecting clauses) and `Γ` the types declared so far. -/
inductive ElabDecls (all : List Def) : Ctx → List Def → IL.Script → Prop where
  | nil {Γ : Ctx} : ElabDecls all Γ [] []
  /-- A syntax alias (`elab.ml:2611-2645`). -/
  | syntaxAlias {Γ : Ctx} {x : List Char} {hs : List Hint} {t : Typ} {t' : IL.Typ} {ds : List Def}
      {s : IL.Script} :
      ElabTyp Γ t t' → ElabDecls all { Γ with typs := (String.ofList x, Γ.expand t') :: Γ.typs } ds s →
      ElabDecls all Γ (.syntaxAlias x hs t :: ds)
        (.typD (String.ofList x) [] [.instD [] [] (.aliasT t')] :: s)
  /-- A signature with its clauses (`elab.ml:2678-2687,2769-2785,2817-2835`),
  not recursive (`elab.ml:2895`). -/
  | decSig {Γ : Ctx} {f : List Char} {pas : List Exp} {t : Typ} {hs : List Hint} {ds : List Def}
      {ps : List IL.Param} {t' : IL.Typ} {cs : List IL.Clause} {s : IL.Script} :
      List.Forall₂ (ElabParam Γ) pas ps → ElabTyp Γ t t' →
      List.Forall₂ (fun (c : List Exp × Exp × List Prem) c' =>
        ElabClause Γ ps (.call f []) c.1 c.2.1 c.2.2 c') (clausesOf f all) cs →
      (∀ c ∈ cs, String.ofList f ∉ clauseCalls c) →
      ElabDecls all Γ ds s →
      ElabDecls all Γ (.decSig f pas t hs :: ds) (.decD (String.ofList f) ps t' cs :: s)
  /-- A clause contributes to its signature's `DecD`, not here (`elab.ml:2689`). -/
  | decClause {Γ : Ctx} {f : List Char} {as : List Exp} {e : Exp} {prems : List Prem} {ds : List Def}
      {s : IL.Script} :
      ElabDecls all Γ ds s → ElabDecls all Γ (.decClause f as e prems :: ds) s
  /-- A grammar alias `grammar x : t = g(a)` (`elab.ml:2707-2740`), for a
  grammar `g` of one parameter `p` with result type `τ`. -/
  | gramAlias {Γ : Ctx} {x g : List Char} {t : Typ} {hs : List Hint} {a : Exp} {ds : List Def}
      {t' : IL.Typ} {a' : IL.Exp} {p : String} {τ : IL.Typ} {s : IL.Script} :
      ElabTyp Γ t t' → Γ.gram? (String.ofList g) = some (p, τ) → ElabExp Γ [] a a' →
      ElabDecls all Γ ds s →
      ElabDecls all Γ (.gramAlias x t hs g [a] :: ds)
        (.gramD (String.ofList x) [] t' [gramProd (String.ofList g) a' (substTyp p a' τ)] :: s)
  /-- `SepD` elaborates to nothing (`elab.ml:2691`). -/
  | sep {Γ : Ctx} {ds : List Def} {s : IL.Script} :
      ElabDecls all Γ ds s → ElabDecls all Γ (.sep :: ds) s

/-- Elaboration of a whole script of the fragment. -/
def ElabScript (Γ : Ctx) (ds : List Def) (s : IL.Script) : Prop := ElabDecls ds Γ ds s

/-- `mapM` for `Option`, structurally. -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a, optMap f as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- A clause, as a function. -/
def elabClause? (Γ : Ctx) (ps : List IL.Param) (c : List Exp × Exp × List Prem) : Option IL.Clause :=
  match argQuants? Γ c.1 ps with
  | none => none
  | some vs =>
    match optMap (elabExp? Γ vs) c.1, elabExp? Γ vs c.2.1, optMap (elabPrem? Γ vs) c.2.2 with
    | some as', some e', some prems' => some (.defD (quantsOf vs) (as'.map .expA) e' prems')
    | _, _, _ => none

/-- `ElabDecls`, as a function. -/
def elabDecls? (all : List Def) : Ctx → List Def → Option IL.Script
  | _, [] => some []
  | Γ, .syntaxAlias x _ t :: ds =>
    match elabTyp? Γ t with
    | some t' =>
      (elabDecls? all { Γ with typs := (String.ofList x, Γ.expand t') :: Γ.typs } ds).map
        (.typD (String.ofList x) [] [.instD [] [] (.aliasT t')] :: ·)
    | none => none
  | Γ, .decSig f pas t _ :: ds =>
    match optMap (elabParam? Γ) pas, elabTyp? Γ t with
    | some ps, some t' =>
      match optMap (elabClause? Γ ps) (clausesOf f all) with
      | some cs =>
        if cs.all fun c => !(clauseCalls c).contains (String.ofList f) then
          (elabDecls? all Γ ds).map (.decD (String.ofList f) ps t' cs :: ·)
        else none
      | none => none
    | _, _ => none
  | Γ, .gramAlias x t _ g [a] :: ds =>
    match elabTyp? Γ t, Γ.gram? (String.ofList g), elabExp? Γ [] a with
    | some t', some (p, τ), some a' =>
      (elabDecls? all Γ ds).map
        (.gramD (String.ofList x) [] t' [gramProd (String.ofList g) a' (substTyp p a' τ)] :: ·)
    | _, _, _ => none
  | _, .gramAlias _ _ _ _ _ :: _ => none
  | Γ, .decClause _ _ _ _ :: ds => elabDecls? all Γ ds
  | Γ, .sep :: ds => elabDecls? all Γ ds
  | _, .unsupported _ :: _ => none

/-- The elaborator. -/
def elab? (Γ : Ctx) (ds : List Def) : Option IL.Script := elabDecls? ds Γ ds

end Silmaril.Wasm.SpecTec.Surface.Elab

namespace Silmaril.Wasm.SpecTec.Surface

open Silmaril.SpecTec

/-- Surface text `src` elaborates, in context `Γ`, to the IL script `s`: it
lexes to some tokens (`lexer.mll`), they parse to declarations of the fragment
(`parser.mly`), and those elaborate to `s` (`elab.ml`). -/
def SurfaceRel (Γ : Elab.Ctx) (src : String) (s : IL.Script) : Prop :=
  ∃ ts ds, Lexer.Lexes src.toList ts ∧ Parser.Parses ts ds ∧ Elab.ElabScript Γ ds s

/-- The whole pipeline, as a function. -/
def surface? (Γ : Elab.Ctx) (src : String) : Option IL.Script :=
  Lexer.lex? src >>= Parser.parse? >>= Elab.elab? Γ

end Silmaril.Wasm.SpecTec.Surface
