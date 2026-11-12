module

public import Silmaril.Wasm.Wac.Elab.Defs

/-!
# WAC: elaboration as relations

Big-step relations for the elaboration of `Silmaril.Wasm.Wac.Elab`, in which every
naming choice is one of the rule relations of `Silmaril.Wasm.Wac.Infer` and every type
check is the subtyping relation `Sub` (not the checker `sub`):

* `ElabExpr cx st e (st', i)`: `e` elaborates to node `i`, from state `st` to `st'`;
  `ElabArgs` for the inferred and named arguments (with `InferArg`, `NamedArg`, and
  distinct argument names), `ElabSpreads` with `SpreadPlan` (built from `PickExport`)
  for spread arguments; a `new` requires every argument to be an import of the package
  at a subtype (`ArgsTyped`) and, without `...`, every import to be given
  (`AllGiven`);
* `ElabStmt`, `ElabStmts`: statements; `ExportName` names unnamed exports;
* `ElabDoc env d g`: the statements, then implicit-import resolution, then the
  target check (`TargetOk`).

`Silmaril.Wasm.Wac.Elab.Thms` proves the elaborator sound for them (`elabDoc_sound`) and
derives the typing of the result.

Data plumbing without choices (adding a node, the alias of an export, the walk of a
package path) is shared with the elaborator. The premises on WIT declarations
(`typeStmt`, `importKind`) and on implicit imports (`Implicit.resolve`) are functions
here; each is proved equivalent to a relation: `typeStmt_iff`, `importKind_iff`
(`Silmaril.Wasm.Wac.WitDeclSpec`) and `aggregate_iff` (`Silmaril.Wasm.Wac.Implicit.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Syntax

/-- Every argument is an import of the package, at a subtype. -/
def ArgsTyped (imps : Externs) (g : CGraph) (acc : List (String × Nat)) : Prop :=
  ∀ a ∈ acc, ∃ k, imps.find a.1 = some k ∧ Sub (g.kindOf a.2) k

/-- Every import of the package is given. -/
def AllGiven (imps : Externs) (acc : List (String × Nat)) : Prop :=
  ∀ q ∈ imps, q.1 ∈ acc.map (·.1)

/-- The (import, export) pairs of a spread: for every import not supplied yet, the
export `PickExport` chooses, if any. -/
inductive SpreadPlan (exps : List String) (sup : List String) : List String → List (String × String) → Prop
  | nil : SpreadPlan exps sup [] []
  | supplied {n : String} {ns : List String} {pl : List (String × String)} :
      n ∈ sup → SpreadPlan exps sup ns pl → SpreadPlan exps sup (n :: ns) pl
  | unmatched {n : String} {ns : List String} {pl : List (String × String)} :
      n ∉ sup → (∀ e, ¬ PickExport exps n e) → SpreadPlan exps sup ns pl →
      SpreadPlan exps sup (n :: ns) pl
  | pick {n e : String} {ns : List String} {pl : List (String × String)} :
      n ∉ sup → PickExport exps n e → SpreadPlan exps sup ns pl →
      SpreadPlan exps sup (n :: ns) ((n, e) :: pl)

/-- Elaboration of the spread arguments, in order. -/
inductive ElabSpreads (imps : List String) :
    ESt → List (String × Nat) → List String → ESt × List (String × Nat) → Prop
  | nil {st : ESt} {acc : List (String × Nat)} : ElabSpreads imps st acc [] (st, acc)
  | cons {st : ESt} {acc : List (String × Nat)} {x : String} {xs : List String} {i : Nat}
      {es : Externs} {plan : List (String × String)} {r : ESt × List (String × Nat)} :
      st.scope.lookup x = some i → (st.g.kindOf i).exports? = some es →
      SpreadPlan es.names (acc.map (·.1)) imps plan → plan ≠ [] →
      ElabSpreads imps (aliasPlan es i st acc plan).1 (aliasPlan es i st acc plan).2 xs r →
      ElabSpreads imps st acc (x :: xs) r
mutual
/-- Elaboration of expressions. -/
inductive ElabExpr (cx : ECtx) : ESt → Silmaril.Wasm.Wac.Syntax.Expr → ESt × Nat → Prop
  | ident {st : ESt} {x : String} {i : Nat} :
      st.scope.lookup x = some i → ElabExpr cx st (.ident x) (st, i)
  | paren {st : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {r : ESt × Nat} : ElabExpr cx st e r → ElabExpr cx st (.paren e) r
  | access {st st1 : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {x n : String} {i : Nat} {es : Externs} {k : Kind} :
      ElabExpr cx st e (st1, i) → (st1.g.kindOf i).exports? = some es →
      TailOrSelf x es.names n → es.find n = some k →
      ElabExpr cx st (.access e x) (st1.aliasAt i n k)
  | namedAccess {st st1 : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {n : String} {i : Nat} {es : Externs} {k : Kind} :
      ElabExpr cx st e (st1, i) → (st1.g.kindOf i).exports? = some es → es.find n = some k →
      ElabExpr cx st (.namedAccess e n) (st1.aliasAt i n k)
  | new {st st1 st2 : ESt} {p : PkgName} {args : List Arg} {pk : PkgType}
      {acc acc2 : List (String × Nat)} {fill : Bool} :
      p.name ≠ cx.pkg.name → cx.env.lookup p.key = some pk →
      ElabArgs cx pk.imports.names st [] args (st1, acc, fill) →
      ElabSpreads pk.imports.names st1 acc (spreads args) (st2, acc2) →
      ArgsTyped pk.imports st2.g acc2 → (fill = false → AllGiven pk.imports acc2) →
      ElabExpr cx st (.new p args) (st2.add ⟨.inst p.key pk.imports acc2, .inst none pk.exports⟩)

/-- Elaboration of the inferred and named arguments, left to right. -/
inductive ElabArgs (cx : ECtx) :
    List String → ESt → List (String × Nat) → List Arg → ESt × List (String × Nat) × Bool → Prop
  | nil {imps : List String} {st : ESt} {acc : List (String × Nat)} : ElabArgs cx imps st acc [] (st, acc, false)
  | inferred {imps : List String} {st : ESt} {acc : List (String × Nat)} {x n : String} {i : Nat} {rest : List Arg}
      {r : ESt × List (String × Nat) × Bool} :
      st.scope.lookup x = some i → InferArg st.g imps x i n → n ∉ acc.map (·.1) →
      ElabArgs cx imps st (acc ++ [(n, i)]) rest r → ElabArgs cx imps st acc (.inferred x :: rest) r
  | named {imps : List String} {st st1 : ESt} {acc : List (String × Nat)} {a : ArgName} {e : Silmaril.Wasm.Wac.Syntax.Expr} {n : String} {i : Nat}
      {rest : List Arg} {r : ESt × List (String × Nat) × Bool} :
      ElabExpr cx st e (st1, i) → NamedArg imps a n → n ∉ acc.map (·.1) →
      ElabArgs cx imps st1 (acc ++ [(n, i)]) rest r → ElabArgs cx imps st acc (.named a e :: rest) r
  | spread {imps : List String} {st : ESt} {acc : List (String × Nat)} {x : String} {rest : List Arg}
      {r : ESt × List (String × Nat) × Bool} :
      ElabArgs cx imps st acc rest r → ElabArgs cx imps st acc (.spread x :: rest) r
  | fill {imps : List String} {st : ESt} {acc : List (String × Nat)} : ElabArgs cx imps st acc [.fill] (st, acc, true)

end

/-- Export node `i` as `n`: not the name of a type definition, not exported yet. -/
inductive ExportAs : ESt → Nat → String → ESt → Prop
  | mk {st : ESt} {i : Nat} {n : String} :
      (∀ j, st.scope.lookup n = some j → st.isDefn j = false) → st.g.hasExport n = false →
      ExportAs st i n { st with g := { st.g with exports := st.g.exports ++ [(n, i)] } }

/-- Spread exports. -/
inductive SpreadExports (es : Externs) (i : Nat) : ESt → Externs → ESt × Bool → Prop
  | nil {st : ESt} : SpreadExports es i st [] (st, false)
  | skip {st : ESt} {n : String} {k : Kind} {rest : Externs} {r : ESt × Bool} :
      st.g.hasExport n = true → SpreadExports es i st rest r → SpreadExports es i st ((n, k) :: rest) r
  | emit {st st2 : ESt} {n : String} {k : Kind} {rest : Externs} {r : ESt × Bool} :
      st.g.hasExport n = false → ExportAs (st.aliasAt i n k).1 (st.aliasAt i n k).2 n st2 →
      SpreadExports es i st2 rest r → SpreadExports es i st ((n, k) :: rest) (r.1, true)

/-- Bind a local name once. -/
inductive Binds : ESt → String → Nat → ESt → Prop
  | mk {st : ESt} {x : String} {i : Nat} :
      st.scope.lookup x = none → Binds st x i { st with scope := st.scope ++ [(x, i)] }

/-- Elaboration of statements. -/
inductive ElabStmt (cx : ECtx) : ESt → Stmt → ESt → Prop
  | import {st st2 : ESt} {i : Silmaril.Wasm.Wac.Syntax.Import} {k : Kind} :
      importKind cx st i.ty = .ok k → importName i k ∉ st.g.importNames →
      Binds (st.add ⟨.imp (importName i k), k.promote⟩).1 i.id
        (st.add ⟨.imp (importName i k), k.promote⟩).2 st2 →
      ElabStmt cx st (.import i) st2
  | type {st st2 : ESt} {t : TypeStmt} {n : String} {k : Kind} :
      typeStmt cx st t = .ok (n, k) → st.g.hasExport n = false →
      Binds { (st.add ⟨.defn n, k⟩).1 with
        g := { (st.add ⟨.defn n, k⟩).1.g with
          exports := (st.add ⟨.defn n, k⟩).1.g.exports ++ [(n, (st.add ⟨.defn n, k⟩).2)] } }
        n (st.add ⟨.defn n, k⟩).2 st2 →
      ElabStmt cx st (.type t) st2
  | «let» {st st1 st2 : ESt} {x : String} {e : Silmaril.Wasm.Wac.Syntax.Expr} {i : Nat} :
      ElabExpr cx st e (st1, i) → Binds st1 x i st2 → ElabStmt cx st (.let x e) st2
  | exportNone {st st1 st2 : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {i : Nat} {n : String} :
      ElabExpr cx st e (st1, i) → ExportName st1.g i n → ExportAs st1 i n st2 →
      ElabStmt cx st (.export e .none) st2
  | exportRename {st st1 st2 : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {i : Nat} {n : String} :
      ElabExpr cx st e (st1, i) → ExportAs st1 i n st2 → ElabStmt cx st (.export e (.rename n)) st2
  | exportSpread {st st1 st2 : ESt} {e : Silmaril.Wasm.Wac.Syntax.Expr} {i : Nat} {es : Externs} :
      ElabExpr cx st e (st1, i) → (st1.g.kindOf i).exports? = some es →
      SpreadExports es i st1 es (st2, true) → ElabStmt cx st (.export e .spread) st2

/-- Elaboration of a list of statements. -/
inductive ElabStmts (cx : ECtx) : ESt → List Stmt → ESt → Prop
  | nil {st : ESt} : ElabStmts cx st [] st
  | cons {st st1 st2 : ESt} {s : Stmt} {ss : List Stmt} :
      ElabStmt cx st s st1 → ElabStmts cx st1 ss st2 → ElabStmts cx st (s :: ss) st2

/-- The composition fits the world `(wi, we)`: it imports only imports of the world, at
a supertype of the world's, and exports every export of the world, at a subtype. -/
def TargetOk (g : CGraph) (wi we : Externs) : Prop :=
  (∀ p ∈ g.imports, ∃ k, wi.find p.1 = some k ∧ Sub k.promote p.2) ∧
  (∀ p ∈ we, ∃ j, g.exports.lookup p.1 = some j ∧ Sub (g.kindOf j) p.2.promote)

/-- **Elaboration of a document.** -/
inductive ElabDoc (env : PkgEnv) : Document → CGraph → Prop
  | mk {d : Document} {st : ESt} {g : CGraph} :
      ElabStmts ⟨env, d.pkg⟩ {} d.stmts st → Implicit.resolve st.g = .ok g →
      (∀ p, d.targets = some p → ∃ i wi we, resolvePath ⟨env, d.pkg⟩ st p = .ok (.type (.comp i wi we)) ∧
        TargetOk g wi we) →
      ElabDoc env d g

end Silmaril.Wasm.Wac
