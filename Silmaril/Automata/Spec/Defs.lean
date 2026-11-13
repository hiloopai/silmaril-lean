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

/-! ## JSON -/

open Lean in
instance : ToJson Edge := ⟨fun e => Json.arr #[e.src, e.label, e.dst]⟩

open Lean in
instance : FromJson Edge := ⟨fun j => do
  let #[a, b, c] ← j.getArr? | throw "an edge is [src, label, dst]"
  return ⟨← a.getStr?, ← b.getStr?, ← c.getStr?⟩⟩

open Lean in
instance : ToJson Spec := ⟨fun sp => Json.mkObj
  [("states", toJson sp.states), ("labels", toJson sp.labels), ("edges", toJson sp.edges)]⟩

open Lean in
instance : FromJson Spec := ⟨fun j => do
  return ⟨← j.getObjValAs? _ "states", ← j.getObjValAs? _ "labels", ← j.getObjValAs? _ "edges"⟩⟩

open Lean in
instance : ToJson Layers := ⟨fun ly => Json.mkObj
  [("initial", toJson ly.initial), ("accepting", toJson ly.accepting),
   ("rejecting", toJson ly.rejecting), ("error", toJson ly.error)]⟩

open Lean in
instance : FromJson Layers := ⟨fun j => do
  let get (k : String) : Except String (List String) :=
    match j.getObjVal? k with
    | .ok v => fromJson? v
    | .error _ => .ok []
  return ⟨← get "initial", ← get "accepting", ← get "rejecting", ← get "error"⟩⟩

open Lean in
instance : ToJson Document := ⟨fun d => Json.mkObj
  [("id", d.id), ("states", toJson d.spec.states), ("labels", toJson d.spec.labels),
   ("edges", toJson d.spec.edges), ("layers", toJson d.layers)]⟩

open Lean in
instance : FromJson Document := ⟨fun j => do
  let layers ← match j.getObjVal? "layers" with
    | .ok v => fromJson? v
    | .error _ => pure {}
  return ⟨← j.getObjValAs? _ "id", ← fromJson? j, layers⟩⟩

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
