module

public import Silmaril.Wasm.Component.Algebra.Term.Defs
public import Silmaril.Wasm.Wac.Graph.Defs
public import Silmaril.Wasm.Wac.Elab.Defs
public import Silmaril.Wasm.Wac.Bridge.Graph.Defs

/-!
# WAC compositions as terms of the component algebra

A WAC composition graph `g : Wac.Graph` (`Silmaril.Wasm.Wac.Graph`) over package interfaces
`S` is a term of the component algebra (`Silmaril.Wasm.Component.Algebra.Term`) whose
variables are the **packages**: `Graph.term S g` has

* the imports `g.iface S` (declared imports, then promoted ones, merged by name),
* one node `.inst (.var n.pkg) args` per instance `n` of package `n.pkg`, with the
  wiring `g.argsOf S I k n` that `Graph.build` gives it,
* the exports `g.mkExports S I`.

A WAC **document** is elaborated (`Wac.elabDoc`) to the elaborator's graph and translated
to a composition graph (`Bridge.toGraph`); `docTerm env S d` is its term and
`docComp env S P d` its component for the packages `P`.

Theorems (`Silmaril.Wasm.Component.Algebra.Wac.Thms`): the term evaluates to the existing
WAC semantics (`eval_term`: `(g.term S).eval P = g.build S P`, hence `Graph.toComp`), its
compositional semantics is `Graph.sem` (`sem_term`), nesting is substitution of terms
(`build_nestPkgs`), and substituting equivalent packages in a graph or a document gives
equivalent compositions (`build_equiv`, `toComp_equiv`, `toComp_update_equiv`,
`docComp_equiv`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra

variable {M : Type}

/-- The nodes of the term of a graph, from instance `k` on. -/
def Graph.termNodes (S : Nat → PkgSig) (g : Graph) (I : Iface) :
    Nat → List Inst → List (TNode M)
  | _, [] => []
  | k, n :: ns => .inst (.var n.pkg) (g.argsOf S I k n) :: g.termNodes S I (k + 1) ns

/-- **A composition graph as a term of the component algebra**, its variables being the
packages. -/
def Graph.term (S : Nat → PkgSig) (g : Graph) : Tm M :=
  .mk (g.iface S) (g.termNodes S (g.iface S) 0 g.nodes) (g.mkExports S (g.iface S))

/-- The composition graph of a WAC document, over the package interfaces `S`. -/
def docGraph (env : PkgEnv) (S : Nat → PkgSig) (d : Syntax.Document) :
    Except ElabError Graph :=
  (elabDoc env d).map (Bridge.toGraph S)

/-- **The term of a WAC document.** -/
def docTerm (env : PkgEnv) (S : Nat → PkgSig) (d : Syntax.Document) :
    Except ElabError (Tm M) :=
  (docGraph env S d).map (Graph.term S)

/-- The component of a WAC document, for the packages `P`. -/
def docComp (env : PkgEnv) (S : Nat → PkgSig) (P : Nat → Comp M) (d : Syntax.Document) :
    Except ElabError (Comp M) :=
  (docGraph env S d).map (Graph.build S P)

end Silmaril.Wasm.Wac
