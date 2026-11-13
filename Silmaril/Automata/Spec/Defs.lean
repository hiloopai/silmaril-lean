module

public import Silmaril.Automata.Machine.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.String.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Lean.Data.Json

@[expose] public section

/-!
# Machine documents: JSON/TOML finite machines

A **machine document** is a finite machine written with names: the JSON (or equivalent
TOML) object that the project database stores and the explorer draws.

```json
{ "id": "silmaril.example.door",
  "states": ["closed", "open"],
  "labels": ["open", "close"],
  "edges": [["closed", "open", "open"], ["open", "close", "closed"]],
  "layers": { "initial": ["closed"], "accepting": [], "rejecting": [], "error": [] } }
```

* `Spec`: states, labels and edges `(src, label, dst)` as names; `Spec.Step` is its relational
  semantics and `Spec.toLTS` the CSLib LTS on names. A spec may be nondeterministic.
* `Spec.wf`: well-formed (distinct state and label names, edges between declared names).
* `Spec.stepFn`: the step function a deterministic spec denotes (first matching edge).
* `Layers`: the marking layer (initial, accepting, rejecting, error), kept apart from the spec
  so that one spec can carry several markings (`Document`).
* `DMachine.toSpec`: the spec of a typed machine over `FinNamed` states and labels (states and
  labels in `elems` order, edges by state then label). `Thms` proves it well formed and
  deterministic, and that its steps are exactly the typed steps (`toSpec_step_iff`).
* `Spec.Typed`: the typed machine of a spec, over the subtypes of its declared names (the
  inverse direction, used by the category equivalence).

**Identity.** A document is identified by its `id` (`Ident.valid`: dot-separated segments
of `[a-z0-9_-]`, globally unique in a project, like other silmaril record names). Its *content*
identity is `Spec.canon`: states, labels and edges sorted and deduplicated. Two specs have the
same canonical form iff they have the same states, labels and edges (`canon_eq_iff`), so the
canonical JSON text (`Document.canonJson`, keys sorted by `Lean.Json.compress`) is a content
key that ignores declaration order; this is where content addressing would hang (not done
here).
-/

namespace Silmaril.Automata

/-- A valid identifier: non-empty dot-separated segments of `[a-z0-9_-]`. -/
def Ident.valid (s : String) : Bool :=
  (s.splitOn ".").all fun seg =>
    !seg.isEmpty && seg.all fun c => c.isLower || c.isDigit || c == '_' || c == '-'

/-- An edge `(src, label, dst)`. -/
structure Edge where
  src : String
  label : String
  dst : String
  deriving DecidableEq, Repr, Inhabited

/-- The lexicographic key of an edge. -/
def Edge.key (e : Edge) : Lex (String × Lex (String × String)) :=
  toLex (e.src, toLex (e.label, e.dst))

theorem Edge.key_injective : Function.Injective Edge.key := by
  intro a b h
  cases a; cases b
  simp only [Edge.key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1 h2 h3; rfl

instance : LinearOrder Edge := LinearOrder.lift' Edge.key Edge.key_injective

/-- A finite machine written with names. -/
structure Spec where
  states : List String
  labels : List String
  edges : List Edge
  deriving DecidableEq, Repr, Inhabited

/-- The marking layer of a document. -/
structure Layers where
  initial : List String := []
  accepting : List String := []
  rejecting : List String := []
  error : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- Every marked name is a declared state. -/
def Layers.wf (ly : Layers) (states : List String) : Bool :=
  (ly.initial ++ ly.accepting ++ ly.rejecting ++ ly.error).all states.contains

/-- A machine document: identifier, spec, layers. -/
structure Document where
  id : String
  spec : Spec
  layers : Layers := {}
  deriving DecidableEq, Repr, Inhabited

namespace Spec

/-- One step of the spec. -/
def Step (sp : Spec) (s l s' : String) : Prop := ⟨s, l, s'⟩ ∈ sp.edges

instance (sp : Spec) (s l s' : String) : Decidable (sp.Step s l s') :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The CSLib LTS of a spec, on names. -/
def toLTS (sp : Spec) : Cslib.LTS String String := ⟨sp.Step⟩

/-- Well formed: distinct names, edges between declared names. -/
def wf (sp : Spec) : Bool :=
  decide sp.states.Nodup && decide sp.labels.Nodup &&
    sp.edges.all fun e => sp.states.contains e.src && sp.labels.contains e.label &&
      sp.states.contains e.dst

/-- Deterministic: at most one successor per state and label. -/
def Deterministic (sp : Spec) : Prop := ∀ s l a b, sp.Step s l a → sp.Step s l b → a = b

/-- The successor of the first edge from `s` labelled `l`. -/
def stepFn (sp : Spec) (s l : String) : Option String :=
  (sp.edges.find? fun e => e.src == s && e.label == l).map Edge.dst

/-- Determinism, checked edge by edge (`deterministicB_iff` in `Thms`). -/
def deterministicB (sp : Spec) : Bool :=
  sp.edges.all fun e => sp.edges.all fun f => !(e.src == f.src && e.label == f.label) || e.dst == f.dst

/-- The canonical form: names and edges sorted and deduplicated. -/
def canon (sp : Spec) : Spec where
  states := sp.states.toFinset.sort (· ≤ ·)
  labels := sp.labels.toFinset.sort (· ≤ ·)
  edges := sp.edges.toFinset.sort (· ≤ ·)

/-- Same states, labels and edges. -/
def Equiv (sp sp' : Spec) : Prop :=
  (∀ s, s ∈ sp.states ↔ s ∈ sp'.states) ∧ (∀ l, l ∈ sp.labels ↔ l ∈ sp'.labels) ∧
    (∀ e, e ∈ sp.edges ↔ e ∈ sp'.edges)

/-- Same states, labels and edges, checked by membership (structural recursion only, so the
kernel evaluates it; `equivB_iff` in `Thms`). Bindings are proved with it. -/
def equivB (sp sp' : Spec) : Bool :=
  sp.states.all sp'.states.contains && sp'.states.all sp.states.contains &&
    sp.labels.all sp'.labels.contains && sp'.labels.all sp.labels.contains &&
    sp.edges.all sp'.edges.contains && sp'.edges.all sp.edges.contains

/-- The declared states as a type. -/
abbrev State (sp : Spec) : Type := {s // s ∈ sp.states}

/-- The declared labels as a type. -/
abbrev Label (sp : Spec) : Type := {l // l ∈ sp.labels}

/-- The typed machine of a spec over its declared names; a successor outside the declared
states (which a well-formed spec does not have) rejects. -/
def Typed (sp : Spec) : DMachine sp.State sp.Label where
  step s l := match sp.stepFn s.1 l.1 with
    | some d => if hd : d ∈ sp.states then some ⟨d, hd⟩ else none
    | none => none

end Spec

/-- The spec of a typed machine over `FinNamed` states and labels. -/
def DMachine.toSpec {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L) : Spec where
  states := FinNamed.names S
  labels := FinNamed.names L
  edges := (FinNamed.elems (α := S)).flatMap fun s => (FinNamed.elems (α := L)).filterMap fun l =>
    (M.step s l).map fun s' => ⟨FinNamed.name s, FinNamed.name l, FinNamed.name s'⟩

/-- The spec of a nondeterministic machine over `FinNamed` states and labels (successors in
`elems` order). -/
def NMachine.toSpec {S L : Type} [FinNamed S] [FinNamed L] [DecidableEq S] (M : NMachine S L) :
    Spec where
  states := FinNamed.names S
  labels := FinNamed.names L
  edges := (FinNamed.elems (α := S)).flatMap fun s => (FinNamed.elems (α := L)).flatMap fun l =>
    ((FinNamed.elems (α := S)).filter fun s' => decide (s' ∈ M.step s l)).map fun s' =>
      ⟨FinNamed.name s, FinNamed.name l, FinNamed.name s'⟩

/-- The layers of marks. -/
def Marks.toLayers {S : Type} [FinNamed S] (m : Marks S) : Layers where
  initial := ((FinNamed.elems (α := S)).filter m.initial).map FinNamed.name
  accepting := ((FinNamed.elems (α := S)).filter m.accepting).map FinNamed.name
  rejecting := ((FinNamed.elems (α := S)).filter m.rejecting).map FinNamed.name
  error := ((FinNamed.elems (α := S)).filter m.error).map FinNamed.name

/-- The document of a marked typed machine. -/
def Marked.toDocument {S L : Type} [FinNamed S] [FinNamed L] (id : String) (M : Marked S L) :
    Document :=
  ⟨id, M.machine.toSpec, M.marks.toLayers⟩

/-! ## JSON

The codec is written with structural recursion only (lists of strings, `[src, label, dst]`
triples, objects with fixed keys), so its round trip is a theorem (`Document.ofJson?_toJson` in
`Thms`): decoding the JSON value of a document gives the document back. -/

open Lean in
/-- A list of strings as a JSON array. -/
def strsToJson (xs : List String) : Json := .arr (xs.map Json.str).toArray

open Lean in
/-- A JSON array of strings. -/
def strsOfJson? (j : Json) : Except String (List String) := do
  let a ← j.getArr?
  a.toList.mapM Json.getStr?

open Lean in
/-- An edge as `[src, label, dst]`. -/
def Edge.toJson (e : Edge) : Json := strsToJson [e.src, e.label, e.dst]

open Lean in
/-- An edge from `[src, label, dst]`. -/
def Edge.ofJson? (j : Json) : Except String Edge := do
  match ← strsOfJson? j with
  | [a, b, c] => return ⟨a, b, c⟩
  | _ => throw "an edge is [src, label, dst]"

open Lean in
/-- Edges as a JSON array. -/
def edgesToJson (es : List Edge) : Json := .arr (es.map Edge.toJson).toArray

open Lean in
/-- A JSON array of edges. -/
def edgesOfJson? (j : Json) : Except String (List Edge) := do
  let a ← j.getArr?
  a.toList.mapM Edge.ofJson?

open Lean in
/-- The JSON object of a spec. -/
def Spec.toJson (sp : Spec) : Json := Json.mkObj
  [("states", strsToJson sp.states), ("labels", strsToJson sp.labels),
   ("edges", edgesToJson sp.edges)]

open Lean in
/-- A spec from the keys `states`, `labels`, `edges` of an object. -/
def Spec.ofJson? (j : Json) : Except String Spec := do
  return ⟨← strsOfJson? (← j.getObjVal? "states"), ← strsOfJson? (← j.getObjVal? "labels"),
    ← edgesOfJson? (← j.getObjVal? "edges")⟩

open Lean in
/-- The JSON object of layers. -/
def Layers.toJson (ly : Layers) : Json := Json.mkObj
  [("initial", strsToJson ly.initial), ("accepting", strsToJson ly.accepting),
   ("rejecting", strsToJson ly.rejecting), ("error", strsToJson ly.error)]

open Lean in
/-- A layer list: absent is empty. -/
def layerOfJson? (j : Json) (k : String) : Except String (List String) :=
  match j.getObjVal? k with
  | .ok v => strsOfJson? v
  | .error _ => .ok []

open Lean in
/-- Layers from an object (absent layers are empty). -/
def Layers.ofJson? (j : Json) : Except String Layers := do
  return ⟨← layerOfJson? j "initial", ← layerOfJson? j "accepting",
    ← layerOfJson? j "rejecting", ← layerOfJson? j "error"⟩

open Lean in
/-- The JSON object of a document. -/
def Document.toJson (d : Document) : Json := Json.mkObj
  [("id", .str d.id), ("states", strsToJson d.spec.states), ("labels", strsToJson d.spec.labels),
   ("edges", edgesToJson d.spec.edges), ("layers", d.layers.toJson)]

open Lean in
/-- A document from its JSON object (absent `layers` is empty). -/
def Document.ofJson? (j : Json) : Except String Document := do
  let layers ← match j.getObjVal? "layers" with
    | .ok v => Layers.ofJson? v
    | .error _ => pure {}
  return ⟨← (← j.getObjVal? "id").getStr?, ← Spec.ofJson? j, layers⟩

open Lean in
instance : ToJson Edge := ⟨Edge.toJson⟩
open Lean in
instance : FromJson Edge := ⟨Edge.ofJson?⟩
open Lean in
instance : ToJson Spec := ⟨Spec.toJson⟩
open Lean in
instance : FromJson Spec := ⟨Spec.ofJson?⟩
open Lean in
instance : ToJson Layers := ⟨Layers.toJson⟩
open Lean in
instance : FromJson Layers := ⟨Layers.ofJson?⟩
open Lean in
instance : ToJson Document := ⟨Document.toJson⟩
open Lean in
instance : FromJson Document := ⟨Document.ofJson?⟩

/-- The canonical layers: sorted and deduplicated. -/
def Layers.canon (ly : Layers) : Layers where
  initial := ly.initial.toFinset.sort (· ≤ ·)
  accepting := ly.accepting.toFinset.sort (· ≤ ·)
  rejecting := ly.rejecting.toFinset.sort (· ≤ ·)
  error := ly.error.toFinset.sort (· ≤ ·)

/-- A valid document: a valid identifier, a well-formed spec and layers on declared states. -/
def Document.wf (d : Document) : Bool :=
  Ident.valid d.id && d.spec.wf && d.layers.wf d.spec.states

/-- A TOML basic string. -/
def tomlStr (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap fun c =>
    if c == '"' then ['\\', '"'] else if c == '\\' then ['\\', '\\']
    else if c == '\n' then ['\\', 'n'] else [c]) ++ "\""

/-- A TOML array of strings. -/
def tomlArr (xs : List String) : String := "[" ++ ", ".intercalate (xs.map tomlStr) ++ "]"

/-- The `[[machine]]` table of a document (the source format `silmaril load` reads). -/
def Document.toToml (d : Document) (doc : Option String := none) : String :=
  let edges := d.spec.edges.map fun e => "  [" ++ ", ".intercalate [tomlStr e.src, tomlStr e.label, tomlStr e.dst] ++ "],"
  "\n".intercalate ([
    "[[machine]]",
    "name = " ++ tomlStr d.id] ++
    (match doc with | some t => ["doc = " ++ tomlStr t] | none => []) ++ [
    "states = " ++ tomlArr d.spec.states,
    "labels = " ++ tomlArr d.spec.labels,
    "edges = ["] ++ edges ++ ["]",
    "initial = " ++ tomlArr d.layers.initial,
    "accepting = " ++ tomlArr d.layers.accepting,
    "rejecting = " ++ tomlArr d.layers.rejecting,
    "error = " ++ tomlArr d.layers.error]) ++ "\n"

/-- Same marked states in each layer, checked by membership (`Layers.canon_eq_of_equivB`). -/
def Layers.equivB (ly ly' : Layers) : Bool :=
  let same (a b : List String) := a.all b.contains && b.all a.contains
  same ly.initial ly'.initial && same ly.accepting ly'.accepting &&
    same ly.rejecting ly'.rejecting && same ly.error ly'.error

/-- The canonical JSON text of a document (content identity, see the module doc). -/
def Document.canonJson (d : Document) : String :=
  (Lean.toJson ({ d with spec := d.spec.canon, layers := d.layers.canon } : Document)).compress

end Silmaril.Automata
