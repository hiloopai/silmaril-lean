module

public import Silmaril.Wasm.Wac.CGraph.Defs
public import Silmaril.Wasm.Wac.Names.Defs

/-!
# WAC: implicit imports

An instantiation `new p { …, ... }` leaves some imports of `p` unsatisfied; they
become imports of the composition (wac `5a7480c`, `CompositionGraph::resolve_imports`
in `crates/wac-graph/src/graph.rs`):

* every unsatisfied import, in the order of the instantiation nodes and then of the
  package's imports, is an *implicit import* of the same name;
* an implicit import may not have the name of an explicit import
  (`ImplicitImportConflict`);
* implicit imports of the same name, or of *semver-compatible* names (the same track,
  `compat`: `a:b/c@0.2.0` and `a:b/c@0.2.1`), are *merged* (`TypeAggregator`,
  `merge`), and shared by every instantiation that wanted them; a failed merge is
  `ImportTypeMergeConflict`. The merged import takes the *highest* version: when a
  later name is `verGt` the recorded one, the recorded entry is removed and the merged
  entry appended under the later name (wac's `shift_remove` and `insert`); otherwise
  the recorded entry keeps its name and position (wac's `name_redirects`);
* each instantiation then receives its implicit imports as arguments, after its
  explicit ones: the argument named like its import refers to the merged import
  compatible with that name (wac's `canonical_import_name`).

Merged imports are pairwise incompatible (`Tracks`, `aggregate_tracks`), so the merged
import compatible with a name is unique and wac's redirect table is the lookup
`findCompat` (`Silmaril.Wasm.Wac.Implicit.Thms`).

**Restriction.** wac also aggregates the *explicit* imports after the implicit ones, so an
explicit `a:b/c@0.2.1` absorbs an implicit `a:b/c@0.2.0`. Here an implicit import
semver-compatible with an explicit one is rejected as `ImplicitImportConflict` (wac
rejects only the exact name): an under-approximation, every accepted document
elaborates as in wac.

`resolve g` adds one `implicit` node per merged import after the existing nodes and
extends the arguments. Afterwards every instantiation has every import as an explicit
named argument (`Silmaril.Wasm.Wac.Implicit.Thms`). `Aggregate` is the aggregation as a
relation (`aggregate_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-- Drop the items named `n`. -/
def Externs.remove (es : Externs) (n : String) : Externs := es.filter fun p => !(p.1 == n)

namespace Implicit

/-- The imports of an instantiation not satisfied by its arguments. -/
def unsatisfied (imports : Externs) (args : List (String × Nat)) : Externs :=
  imports.filter fun p => !(args.any (·.1 == p.1))

/-- The unsatisfied imports of the instantiation nodes, in node order. -/
def wanted (g : CGraph) : Externs :=
  g.nodes.flatMap fun nd => match nd.op with
    | .inst _ imps args => unsatisfied imps args
    | _ => []

/-- The merged import compatible with `n` (the same name or the same semver track). -/
def findCompat (ms : Externs) (n : String) : Option (String × Kind) := ms.find? fun p => compat p.1 n

/-- Aggregate the wanted imports: a name compatible with no merged import is appended;
otherwise it is merged into the compatible one, which takes the later name when that
name has the higher version. An implicit import compatible with an explicit one is a
conflict. -/
def aggregate (explicit : List String) : Externs → Externs → Except ElabError Externs
  | ms, [] => .ok ms
  | ms, (n, k) :: rest =>
    if explicit.any (fun e => compat e n) then .error (.implicitImportConflict n)
    else match findCompat ms n with
      | none => aggregate explicit (ms ++ [(n, k)]) rest
      | some (m, k0) => match merge k0 k with
        | some k' =>
          if verGt n m then aggregate explicit (ms.remove m ++ [(n, k')]) rest
          else aggregate explicit (ms.replace m k') rest
        | none => .error (.importTypeMergeConflict n)

/-- The node of the merged implicit import compatible with `n`, once the merged imports
`ms` are appended after `base` nodes. -/
def nodeOf (base : Nat) (ms : Externs) (n : String) : Nat := base + ms.findIdx fun p => compat p.1 n

/-- **Aggregation as a relation.** Each wanted import `(n, k)` is incompatible with every
explicit import and either new (`fresh`: compatible with no merged import), or merged
into the compatible merged import `(m, k0)`, keeping its name (`keep`) or taking the
higher-versioned name `n` (`upgrade`). -/
inductive Aggregate (ex : List String) : Externs → Externs → Externs → Prop
  | nil (ms : Externs) : Aggregate ex ms [] ms
  | fresh {ms rest ms' : Externs} {n : String} {k : Kind} :
      (∀ e ∈ ex, compat e n = false) → (∀ q ∈ ms, compat q.1 n = false) →
      Aggregate ex (ms ++ [(n, k)]) rest ms' → Aggregate ex ms ((n, k) :: rest) ms'
  | keep {ms rest ms' : Externs} {n m : String} {k k0 k' : Kind} :
      (∀ e ∈ ex, compat e n = false) → (m, k0) ∈ ms → compat m n = true →
      merge k0 k = some k' → verGt n m = false →
      Aggregate ex (ms.replace m k') rest ms' → Aggregate ex ms ((n, k) :: rest) ms'
  | upgrade {ms rest ms' : Externs} {n m : String} {k k0 k' : Kind} :
      (∀ e ∈ ex, compat e n = false) → (m, k0) ∈ ms → compat m n = true →
      merge k0 k = some k' → verGt n m = true →
      Aggregate ex (ms.remove m ++ [(n, k')]) rest ms' → Aggregate ex ms ((n, k) :: rest) ms'

/-- Give an instantiation its implicit arguments. -/
def extend (base : Nat) (ms : Externs) (nd : CNode) : CNode :=
  match nd.op with
  | .inst p imps args =>
    { nd with op := .inst p imps (args ++ (unsatisfied imps args).map fun q => (q.1, nodeOf base ms q.1)) }
  | _ => nd

/-- **Resolve the implicit imports of a graph.** -/
def resolve (g : CGraph) : Except ElabError CGraph := do
  let ms ← aggregate (g.importNames) [] (wanted g)
  let base := g.nodes.length
  pure { g with nodes := (g.nodes.map (extend base ms)) ++ ms.map fun q => ⟨.implicit q.1, q.2⟩ }

/-- **Resolution as a relation**: the wanted imports aggregate to `ms`, which are appended
as implicit import nodes, and every instantiation receives its implicit arguments. -/
inductive Resolve (g : CGraph) : CGraph → Prop
  | mk {ms : Externs} : Aggregate g.importNames [] (wanted g) ms →
      Resolve g { g with nodes := (g.nodes.map (extend g.nodes.length ms)) ++ ms.map fun q => ⟨.implicit q.1, q.2⟩ }

end Implicit

/-- Every instantiation passes every import of its package. -/
def CGraph.Complete (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ p imps args, nd.op = .inst p imps args → ∀ q ∈ imps, ∃ j, (q.1, j) ∈ args

/-- Every argument of every instantiation is an import of its package, at a subtype. -/
def CGraph.Typed (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ p imps args, nd.op = .inst p imps args →
    ∀ a ∈ args, ∃ k, imps.find a.1 = some k ∧ Sub (g.kindOf a.2) k

end Silmaril.Wasm.Wac
