module

public import Silmaril.Wasm.Component.Algebra.Equiv.Defs

/-!
# The component algebra: terms

A *term* is a component of the component IR in which some instances are instances of
**variables** (component parameters) instead of known components:

* `Tm.var k`: the `k`-th parameter;
* `Tm.mk I ns xs`: a component with imports `I`, nodes `ns` and exports `xs`, where a node
  is a core instance (`TNode.core m args`) or an instance of a subterm
  (`TNode.inst t args`).

A term with variables is a *multi-hole context*. Its operations:

* `Tm.eval P t : Comp M`: substitute the component `P k` for every variable `k`
  (instantiation of the context);
* `Tm.subst σ t : Tm M`: substitute the term `σ k` for every variable (terms form a
  clone; nesting a composition inside another is substitution);
* `Tm.sem C W D t`: the **compositional semantics** of a term: a strategy over `sigU`
  computed from the meanings `D k` of the variables (with export widths `W k`), by the
  same equations as `Comp.denU`.

Every operator of the algebra (`Silmaril.Wasm.Component.Algebra.Ops`) is the evaluation of
a term, and so is every WAC composition graph (`Silmaril.Wasm.Wac.Algebra`).
Theorems in `Silmaril.Wasm.Component.Algebra.Term.Thms`: `denU_eval` (the meaning of an
instantiated context is the semantics of the context applied to the meanings of the
arguments), `eval_equiv` (**congruence**), `eval_subst`, `ctxEquiv_iff` (contextual
equivalence is denotational equivalence).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

mutual
/-- A node of a term: a core instance or an instance of a subterm. -/
inductive TNode (M : Type) where
  /-- An instance of a core module. -/
  | core (m : M) (args : List Impl)
  /-- An instance of a subterm. -/
  | inst (t : Tm M) (args : List Impl)

/-- A term of the component algebra. -/
inductive Tm (M : Type) where
  /-- A parameter. -/
  | var (k : Nat)
  /-- A component: imports, nodes in topological order, exports. -/
  | mk (imports : Iface) (nodes : List (TNode M)) (exports : List Export)
end

variable {M : Type}

namespace Tm

mutual
/-- **Instantiation**: substitute the component `P k` for the variable `k`. -/
def eval (P : Nat → Comp M) : Tm M → Comp M
  | .var k => P k
  | .mk I ns xs => .mk I (Tm.evalNodes P ns) xs

/-- `eval` on a list of nodes. -/
def evalNodes (P : Nat → Comp M) : List (TNode M) → List (Node M)
  | [] => []
  | n :: ns => Tm.evalNode P n :: Tm.evalNodes P ns

/-- `eval` on a node. -/
def evalNode (P : Nat → Comp M) : TNode M → Node M
  | .core m args => .core m args
  | .inst t args => .inst (Tm.eval P t) args
end

mutual
/-- **Substitution** of terms for variables. -/
def subst (σ : Nat → Tm M) : Tm M → Tm M
  | .var k => σ k
  | .mk I ns xs => .mk I (Tm.substNodes σ ns) xs

/-- `subst` on a list of nodes. -/
def substNodes (σ : Nat → Tm M) : List (TNode M) → List (TNode M)
  | [] => []
  | n :: ns => Tm.substNode σ n :: Tm.substNodes σ ns

/-- `subst` on a node. -/
def substNode (σ : Nat → Tm M) : TNode M → TNode M
  | .core m args => .core m args
  | .inst t args => .inst (Tm.subst σ t) args
end

mutual
/-- A component as a closed term. -/
def ofComp : Comp M → Tm M
  | .mk I ns xs => .mk I (Tm.ofNodes ns) xs

/-- `ofComp` on a list of nodes. -/
def ofNodes : List (Node M) → List (TNode M)
  | [] => []
  | n :: ns => Tm.ofNode n :: Tm.ofNodes ns

/-- `ofComp` on a node. -/
def ofNode : Node M → TNode M
  | .core m args => .core m args
  | .inst c args => .inst (Tm.ofComp c) args
end

variable [CoreModule M]

mutual
/-- The number of exports of a term, given those `W k` of the variables. -/
def width (W : Nat → Nat) : Tm M → Nat
  | .var k => W k
  | .mk _ _ xs => xs.length

/-- The number of functions a node of a term exports. -/
def nodeWidth (W : Nat → Nat) : TNode M → Nat
  | .core m _ => (CoreModule.exports m).length
  | .inst t _ => Tm.width W t
end

/-- The size of the environment after the nodes `ns`, starting from `e`. -/
def envAfter (W : Nat → Nat) (e : Nat) : List (TNode M) → Nat
  | [] => e
  | n :: ns => Tm.envAfter W (e + nodeWidth W n) ns

mutual
/-- **The compositional semantics of a term**, from the meanings `D k` (of widths `W k`)
of its variables. -/
def sem (C : CoreSem M) (W : Nat → Nat) (D : Nat → Strategy sigU sigU) :
    Tm M → Strategy sigU sigU
  | .var k => D k
  | .mk I ns xs =>
    (Tm.semNodes C W D I.length ns (Strategy.ofHandler (maskH I.length))).comp
      (Strategy.ofHandler (exportsH (Tm.envAfter W I.length ns) xs))

/-- Extend the environment `E` (of `e` functions) by the nodes `ns`. -/
def semNodes (C : CoreSem M) (W : Nat → Nat) (D : Nat → Strategy sigU sigU) {X : Sig.{0}} :
    Nat → List (TNode M) → Strategy X sigU → Strategy X sigU
  | _, [], E => E
  | e, n :: ns, E =>
    Tm.semNodes C W D (e + nodeWidth W n) ns (ext e E (Tm.semNode C W D e n))

/-- The strategy of a node of a term, over an environment of `e` functions. -/
def semNode (C : CoreSem M) (W : Nat → Nat) (D : Nat → Strategy sigU sigU) :
    Nat → TNode M → Strategy sigU sigU
  | e, .core m args => coreNode C e m args
  | e, .inst t args => (Strategy.ofHandler (implsH e args)).comp (Tm.sem C W D t)
end

end Tm

variable [CoreModule M]

/-- **Contextual equivalence**: no context (term), instantiated with `c` for all its
variables on one side and with `c'` on the other, distinguishes them at its interface. -/
def CtxEquiv (C : CoreSem M) (c c' : Comp M) : Prop :=
  ∀ t : Tm M, IfaceEquiv C (t.eval fun _ => c) (t.eval fun _ => c')

/-- **Contextual refinement**: in every context, `c` refines `c'` at the interface. -/
def CtxRefines (C : CoreSem M) (c c' : Comp M) : Prop :=
  ∀ t : Tm M, IfaceRefines C (t.eval fun _ => c) (t.eval fun _ => c')

end Silmaril.Wasm.Component.Algebra
