module

public import Silmaril.Wasm.Binaryen.MergeChecked

@[expose] public section

/-! Namespace-qualified export preparation for the checked GC merger.

The existing merger requires globally distinct export names. This additive
preparation assigns every original `(namespace, export)` a distinct candidate
name and rewrites import names through that same table. Function/global bodies,
indices, types and initialization are unchanged. Final output validation is
still required. These are source-rewrite/provenance APIs, not an assertion that
an equivalence theorem for the prepared program already applies to the original
program. Such a theorem needs explicit observation-name transport.
-/

namespace Silmaril.Wasm.Binaryen.MergeExportNames

inductive Policy where
  | reject
  | rename
  | skip
  deriving DecidableEq, Repr

structure Alias where
  namespaceName : String
  original : String
  output : String
  deriving DecidableEq, Repr

/-- A generated alias cannot capture any original export name, including names
belonging to a later module. The bounded search may safely reject. -/
def fresh? (base : String) (reserved used : List String) : Nat → Nat → Option String
  | 0, _ => none
  | fuel + 1, n =>
      let candidate := base ++ "_" ++ toString n
      if reserved.contains candidate || used.contains candidate then
        fresh? base reserved used fuel (n + 1)
      else some candidate

def aliasesAux? (reserved : List String) : List String →
    List (String × String) → Option (List Alias)
  | _, [] => some []
  | used, (ns, name) :: rest => do
      let output ← if used.contains name then
        fresh? name reserved used (reserved.length + 1) 1
        else some name
      let tail ← aliasesAux? reserved (output :: used) rest
      pure (⟨ns, name, output⟩ :: tail)

def aliases? (program : List (String × Module)) : Option (List Alias) :=
  let exports := program.flatMap fun (ns, m) => m.exports.map fun e => (ns, e.name)
  aliasesAux? (exports.map Prod.snd) [] exports

/-- Lookup is qualified by the source namespace, so equal base names in
unrelated providers never redirect a consumer to the wrong function. -/
def lookup (aliases : List Alias) (ns name : String) : String :=
  match aliases.find? (fun a => a.namespaceName == ns && a.original == name) with
  | some a => a.output
  | none => name

def rewrite (aliases : List Alias) (ns : String) (m : Module) : Module :=
  { m with
    imports := m.imports.map fun i => { i with name := lookup aliases i.moduleName i.name }
    exports := m.exports.map fun e => { e with name := lookup aliases ns e.name } }

def rewriteProgram (aliases : List Alias) (program : List (String × Module)) :
    List (String × Module) :=
  program.map fun (ns, m) => (ns, rewrite aliases ns m)

/-- Finite injection condition on the names that actually occur in an
original module's public interface. No global string injection is assumed. -/
def AliasInjectiveOn (aliases : List Alias) (ns : String) (m : Module) : Prop :=
  ∀ a ∈ m.exports, ∀ b ∈ m.exports,
    lookup aliases ns a.name = lookup aliases ns b.name → a.name = b.name

def aliasInjectiveB (aliases : List Alias) (ns : String) (m : Module) : Bool :=
  m.exports.all fun a => m.exports.all fun b =>
    lookup aliases ns a.name != lookup aliases ns b.name || a.name == b.name

theorem aliasInjectiveB_sound {aliases : List Alias} {ns : String} {m : Module}
    (checked : aliasInjectiveB aliases ns m = true) : AliasInjectiveOn aliases ns m := by
  intro a ha b hb same
  have pair := List.all_eq_true.mp (List.all_eq_true.mp checked a ha) b hb
  simpa [same] using pair

/-- Every link-time alias remains available during merging. Skip policy hides
only conflicting public exports after all import wiring has been resolved. -/
def visible (policy : Policy) (aliases : List Alias) (outputName : String) : Bool :=
  policy != .skip || aliases.any (fun a => a.output == outputName && a.output == a.original)

def publicModule (policy : Policy) (aliases : List Alias) (m : Module) : Module :=
  { m with exports := m.exports.filter fun e => visible policy aliases e.name }

structure Prepared where
  aliases : List Alias
  modules : List (String × Module)

def prepare? (policy : Policy) (program : List (String × Module)) : Option Prepared := do
  let aliases ← aliases? program
  if policy == .reject then
    pure ⟨aliases, program⟩
  else pure ⟨aliases, rewriteProgram aliases program⟩

/-- The renamer changes no executable module field. -/
theorem rewrite_without_interfaces (aliases : List Alias) (ns : String) (m : Module) :
    { rewrite aliases ns m with imports := m.imports, exports := m.exports } = m := by
  cases m
  rfl

/-- Public conflict filtering changes only the final interface. -/
theorem publicModule_without_exports (policy : Policy) (aliases : List Alias) (m : Module) :
    { publicModule policy aliases m with exports := m.exports } = m := by
  cases m
  rfl

end Silmaril.Wasm.Binaryen.MergeExportNames
