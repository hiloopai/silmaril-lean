module

public import Silmaril.Project.Registry.Load.Defs
public import Silmaril.Automata.Spec.Thms
public meta import Silmaril.Automata.Spec.Defs

/-!
# Machines in silmaril projects: the `machine` and `machine_binding` record kinds

**Source of truth.** A machine document is written in TOML, in a records file read by
`silmaril load` (the same reader as every other record kind; elaboration only *reads* files):

```toml
[[machine]]
name = "silmaril.example.door"
doc = "A door."
states = ["closed", "open"]
labels = ["open", "close"]
edges = [["closed", "open", "open"], ["open", "close", "closed"]]
initial = ["closed"]
```

The `machine` handler checks the document (`Document.wf`: a valid identifier, distinct names,
edges and layers on declared names), defines the Lean constant `<name> : Document` in the
current namespace (so the JSON machine can be reasoned about on its own), and fills the fields
`decl` (that constant), `deterministic` and `canonical` (`Document.canonJson`, the content
identity).

**Attachments.** A `machine_binding` attaches a typed machine to a document:

```toml
[[machine_binding]]
name = "silmaril.example.door.typed"
machine = "silmaril.example.door"
decl = "Door.machine"          # : DMachine S L, with FinNamed S and FinNamed L
marks = "Door.marks"           # optional : Marks S
```

The handler elaborates the theorem `<name>.bound : (DMachine.toSpec decl).canon = doc.spec.canon`
(and `<name>.layers` for the marks), proved by `canon_eq_of_equivB` from a membership check
evaluated by the kernel (`decide +kernel`), so a binding exists only
if the typed machine *is* the document up to declaration order. Several typed machines (over
different inductive types) may bind one document; `step_iff_of_canon_eq` then transfers steps
between them. Nothing is written back to the TOML: `#silmaril_machine_toml` prints the TOML of
a typed machine for the author to save.
-/

public meta section

namespace Silmaril.Automata.Registry

open Lean Meta Elab Command Silmaril.Project

/-- A list of strings field (absent: empty). -/
def strList (kind key : String) (fs : Fields) : CoreM (List String) := do
  match fs.get? key with
  | none => return []
  | some j =>
    match fromJson? (α := List String) j with
    | .ok xs => return xs
    | .error e => throwError "silmaril {kind}: `{key}` must be a list of strings ({e})"

/-- The document of a `machine` record's fields. -/
def docOf (kind name : String) (fs : Fields) : CoreM Document := do
  let edges ← match fs.get? "edges" with
    | none => pure []
    | some j => match fromJson? (α := List Edge) j with
      | .ok es => pure es
      | .error e => throwError "silmaril {kind}: `edges` must be a list of [src, label, dst] ({e})"
  return {
    id := name
    spec := ⟨← strList kind "states" fs, ← strList kind "labels" fs, edges⟩
    layers := ⟨← strList kind "initial" fs, ← strList kind "accepting" fs,
      ← strList kind "rejecting" fs, ← strList kind "error" fs⟩ }

/-- The term of a document literal. -/
def docTerm (d : Document) : CommandElabM Term := do
  let edges ← d.spec.edges.toArray.mapM fun e =>
    `(Silmaril.Automata.Edge.mk $(quote e.src) $(quote e.label) $(quote e.dst))
  `(({ id := $(quote d.id)
       spec := ⟨$(quote d.spec.states), $(quote d.spec.labels), [$edges,*]⟩
       layers := ⟨$(quote d.layers.initial), $(quote d.layers.accepting),
         $(quote d.layers.rejecting), $(quote d.layers.error)⟩ } : Silmaril.Automata.Document))

/-- `machine`: check the document, define its constant, fill `decl`, `deterministic`,
`canonical`. -/
@[silmaril_kind machine] def machineHandler : Handler where
  mainKey := "doc"
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let d ← liftCoreM (docOf kind name fs)
    unless Ident.valid d.id do throwError "silmaril {kind}: `{name}` is not a valid identifier"
    unless decide d.spec.states.Nodup do throwError "silmaril {kind}: repeated state names"
    unless decide d.spec.labels.Nodup do throwError "silmaril {kind}: repeated label names"
    unless d.spec.wf do throwError "silmaril {kind}: an edge uses an undeclared state or label"
    unless d.layers.wf d.spec.states do
      throwError "silmaril {kind}: a layer marks an undeclared state"
    let decl ← fullName name
    elabDef false decl #[] (some (← `(Silmaril.Automata.Document))) (← docTerm d)
    let fs ← liftCoreM (fs.push kind "decl" (.str (leanToName decl)) decl)
    let fs ← liftCoreM (fs.push kind "deterministic" (.bool d.spec.deterministicB))
    let fs ← liftCoreM (fs.push kind "canonical" (.str d.canonJson))
    return #[(name, fs)]

/-- `machine_binding`: prove that a typed machine (and its marks) is the document. -/
@[silmaril_kind machine_binding] def bindingHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let m ← liftCoreM (fs.str kind "machine")
    let some r := findRecord? (← getEnv) "machine" m
      | throwError "silmaril {kind}: no machine `{m}` (load it first)"
    let some docDecl := r.str? "decl" | throwError "silmaril {kind}: machine `{m}` has no decl"
    let docId := mkIdent (nameToLean docDecl)
    let c ← liftCoreM (fs.const kind "decl")
    let base ← fullName name
    let thm := base ++ `bound
    let ty ← `(Silmaril.Automata.Spec.canon (Silmaril.Automata.DMachine.toSpec $(mkIdent c)) =
      Silmaril.Automata.Spec.canon ($docId).spec)
    let pf ← `(Silmaril.Automata.Spec.canon_eq_of_equivB (by decide +kernel))
    try elabDef true thm #[] (some ty) pf
    catch e => throwError "silmaril {kind}: `{c}` does not match machine `{m}`: {e.toMessageData}"
    let mut fs ← liftCoreM (fs.push kind "theorem" (.str (leanToName thm)))
    if let some (.str mk) := fs.get? "marks" then
      let mc ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent (nameToLean mk))
      let lthm := base ++ `layers
      let lty ← `(Silmaril.Automata.Layers.canon (Silmaril.Automata.Marks.toLayers $(mkIdent mc)) =
        Silmaril.Automata.Layers.canon ($docId).layers)
      let lpf ← `(Silmaril.Automata.Layers.canon_eq_of_equivB (by decide +kernel))
      try elabDef true lthm #[] (some lty) lpf
      catch e => throwError "silmaril {kind}: marks `{mc}` do not match machine `{m}`: {e.toMessageData}"
      fs := fs.set "marks" (.str (leanToName mc))
    return #[(name, fs)]

/-- `#silmaril_machine_toml "id" M (marks)?`: print the `[[machine]]` table of a typed machine. -/
syntax (name := machineTomlCmd) "#silmaril_machine_toml " str term:max (term:max)? : command

macro_rules
  | `(#silmaril_machine_toml $id:str $m) =>
    `(#eval IO.print (Silmaril.Automata.Document.toToml
        ⟨$id, Silmaril.Automata.DMachine.toSpec $m, {}⟩))
  | `(#silmaril_machine_toml $id:str $m $mk) =>
    `(#eval IO.print (Silmaril.Automata.Document.toToml
        ⟨$id, Silmaril.Automata.DMachine.toSpec $m, Silmaril.Automata.Marks.toLayers $mk⟩))

end Silmaril.Automata.Registry
