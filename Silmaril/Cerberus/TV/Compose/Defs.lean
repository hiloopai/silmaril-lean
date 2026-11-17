module

public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Cerberus.TV.Applicability.Defs

/-!
# Composing whole-program evidence: along the pipeline, and function by function

The first compositional step of C translation validation (docs/projects/c-tv.md, roadmap
milestone "compositional evidence"). Two kinds of composition, both reduced to `TV.Refines`:

* **Vertical** (along a pipeline of translations): refinement is transitive
  (`Refines.trans` in `Thms`), so `C → Core₁ → Core₂ → …` statements compose without re-running a
  validator on the end points; equivalence is symmetric and transitive.
* **Horizontal** (per function, in contexts): `FileBindings.setFunction b f d` replaces the
  definition of the function `f` in the file `b`. `ContextRefines impl ctxs f d d'` says that in
  every context of the list `ctxs`, the program with `f := d'` refines the one with `f := d`; it is
  a raw, weak relation (vacuous for no context, a no-op for a symbol the context does not define).
  `FunctionRefines` adds what the standard shape needs: a nonempty list, and a substitution
  witness per context (`Substitutes`: `f` in the context's functions, not shadowed by its runtime).
  A replacement of `f` followed by one of `g` composes (`ContextRefines.then` in `Thms`), and a
  finite list of contexts is validated by `validateContexts`, sound for `FunctionRefines`
  (`validateContexts_sound`).

**Scope.** Contexts are explicit, finite lists of closed programs: this is not contextual
refinement for *all* contexts (that needs a simulation proof over the Core LTS, or contracts at
the function's boundary), not yet expression- or statement-level, and external calls are not yet
specified by contracts. Those are the next obligations of the milestone.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

/-- Replace the definition of the function whose symbol Lem's equality identifies with `f`. -/
def _root_.Silmaril.Cerberus.Codec.FileBindings.setFunction (b : Codec.FileBindings) (f : Sym)
    (d : Core.FunDecl Codec.wireModel Unit Unit) : Codec.FileBindings :=
  { b with funs := b.funs.map fun e => if e.1.key == f.key then (e.1, d) else e }

/-- The closed program of the file `b` with `f := d`. -/
def Closed.withFunction (b : Codec.FileBindings) (f : Sym)
    (d : Core.FunDecl Codec.wireModel Unit Unit) : Closed :=
  Closed.ofBindings (b.setFunction f d)

/-- **Contextual refinement over listed contexts (raw, weak)**: in every context `b ∈ ctxs`, the
program with `f := d'` refines the one with `f := d`. It holds vacuously for `ctxs = []`, and a
replacement is a no-op when `f` is not defined in `b.funs` (or is shadowed by `b.stdlib`, which the
dynamics looks up first): use `FunctionRefines`, which requires a substitution witness. -/
def ContextRefines (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) : Prop :=
  ∀ b ∈ ctxs, Refines impl (Closed.withFunction b f d) (Closed.withFunction b f d')

/-- **A substitution witness**: `f` is defined in the context's own functions and not in its
runtime library (`functionBody`/`procedureBody` look `stdlib` up first), so `setFunction b f`
actually replaces what a call of `f` runs. It says that `f` is replaced, not that the context calls
it: in a context that never reaches `f`, every replacement refines. -/
def Substitutes (b : Codec.FileBindings) (f : Sym) : Prop :=
  b.funs.any (fun e => e.1.key == f.key) = true ∧ b.stdlib.any (fun e => e.1.key == f.key) = false

instance (b : Codec.FileBindings) (f : Sym) : Decidable (Substitutes b f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Function-level refinement over listed contexts**: the contexts are not empty, `f` is
substituted in each of them (`Substitutes`), and in each the program with `f := after` refines the
one with `f := before`. Still a claim about the listed contexts only, not contextual refinement. -/
structure FunctionRefines (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (before after : Core.FunDecl Codec.wireModel Unit Unit) : Prop where
  nonempty : ctxs ≠ []
  substitutes : ∀ b ∈ ctxs, Substitutes b f
  refines : ContextRefines impl ctxs f before after

/-- **The context validator**: the contexts are not empty, each substitutes `f`, and the verdict
is `validated` in each. -/
def validateContexts (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) (bounds : Bounds := {}) : Bool :=
  !ctxs.isEmpty && ctxs.all (fun b => decide (Substitutes b f)) &&
  ctxs.all fun b => (validate impl (Closed.withFunction b f d) (Closed.withFunction b f d') bounds).verdict == .validated

end Silmaril.Cerberus.TV
