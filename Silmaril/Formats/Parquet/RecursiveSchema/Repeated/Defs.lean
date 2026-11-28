module

public import Silmaril.Formats.Parquet.RecursiveSchema.Defs
public import Silmaril.Formats.Parquet.ListFile.Defs

/-! Checked canonical Parquet LIST and Struct declarations.
The legacy entry point admits at most one repeated site per leaf. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated

open RecursiveSchema (Location Site Kind Entry entries Unannotated RepetitionWire)

@[expose] public section

inductive Absence where
  | node
  | list
  | element
  | descendant
  deriving DecidableEq, Repr

/-- At this definition level the named optional site or repeated
wrapper is the first one not reached. -/
inductive Step where
  | optional (site : Location) (role : Absence)
  | emptyList (outer wrapper : Location)
  deriving DecidableEq, Repr

def Step.wrapper? : Step → Option (Location × Location)
  | .optional .. => none
  | .emptyList outer wrapper => some (outer, wrapper)

structure Boundary where
  outer : Location
  wrapper : Location
  /-- The level just before the first element slot, representing an empty List. -/
  emptyLevel : Nat
  deriving DecidableEq, Repr

structure Leaf where
  site : Site
  kind : Kind
  steps : List Step
  repeated : Option Boundary
  deriving DecidableEq, Repr

def Leaf.maxDefinition (leaf : Leaf) : Nat := leaf.steps.length

def Leaf.maxRepetition (leaf : Leaf) : Nat := if leaf.repeated.isSome then 1 else 0

def Leaf.ofNonRepeated (leaf : RecursiveSchema.Leaf) : Leaf :=
  ⟨leaf.site, leaf.kind, leaf.optional.map (fun site => .optional site .node), none⟩

inductive Presence where
  | absent (step : Step)
  | value
  deriving DecidableEq, Repr

inductive Position where
  | rowStart
  | continuation
  deriving DecidableEq, Repr

structure Slot where
  position : Position
  presence : Presence
  deriving DecidableEq, Repr

inductive LevelError where
  | repetition (leaf : Location) (slot actual maximum : Nat)
  | definition (leaf : Location) (slot actual maximum : Nat)
  | continuation (leaf : Location) (slot definition : Nat)
  deriving DecidableEq, Repr

def Leaf.classifyDefinition (leaf : Leaf) (slot level : Nat) : Except LevelError Presence :=
  if level = leaf.maxDefinition then .ok .value else
    match leaf.steps[level]? with
    | some step => .ok (.absent step)
    | none => .error (.definition leaf.site.location slot level leaf.maxDefinition)

/-- Classify one pair locally. A continuation must reach an element slot.
Whether a previous slot opened this List is checked by a later consumer. -/
def Leaf.classify (leaf : Leaf) (slot repetition definition : Nat) : Except LevelError Slot := do
  if repetition > leaf.maxRepetition then
    throw (.repetition leaf.site.location slot repetition leaf.maxRepetition)
  let present ← leaf.classifyDefinition slot definition
  if repetition = 0 then return ⟨.rowStart, present⟩
  if leaf.repeated.any (fun boundary => boundary.emptyLevel < definition) then
    return ⟨.continuation, present⟩
  .error (.continuation leaf.site.location slot definition)

inductive Field where
  | group (site : Site) (children : List Field)
  | list (site : Site) (wrapper : Location) (element : Field)
  | leaf (plan : Leaf)
  deriving Repr

def Field.leaves : Field → List Leaf
  | .group _ children => children.flatMap Field.leaves
  | .list _ _ element => element.leaves
  | .leaf plan => [plan]

def Field.arrow : Field → Arrow.RecursiveSchema.Field
  | .group site children => .node (some site.name) site.nullable .struct (children.map Field.arrow)
  | .list site _ element => .node (some site.name) site.nullable .list [element.arrow]
  | .leaf plan => .node (some plan.site.name) plan.site.nullable plan.kind.arrow []

structure Context where
  path : List String := []
  steps : List Step := []
  repeated : Option Boundary := none
  elementRoot : Bool := false
  allowNested : Bool := false

def Context.site (ctx : Context) (ordinal : Nat) (name : String) (nullable : Bool) : Site :=
  (RecursiveSchema.Context.mk ctx.path []).site ordinal name nullable

def Context.role (ctx : Context) : Absence :=
  if ctx.elementRoot then .element else if ctx.repeated.isSome then .descendant else .node

def Context.enter (ctx : Context) (site : Site) : Context :=
  ⟨site.location.path,
    if site.nullable then ctx.steps ++ [.optional site.location ctx.role] else ctx.steps,
    ctx.repeated, false, ctx.allowNested⟩

def wrapperAt (site : Site) (ordinal : Nat) (entry : Entry) : Location :=
  ⟨ordinal + 1, site.location.path ++ [entry.1.name]⟩

def Context.enterList (ctx : Context) (site : Site) (wrapper : Location) : Context :=
  let steps := if site.nullable then ctx.steps ++ [.optional site.location .list] else ctx.steps
  ⟨wrapper.path, steps ++ [.emptyList site.location wrapper],
    some ⟨site.location, wrapper, steps.length⟩, true, ctx.allowNested⟩

def Context.admitsList (ctx : Context) : Prop :=
  ctx.allowNested = true ∨ ctx.repeated = none

instance (ctx : Context) : Decidable ctx.admitsList := by
  unfold Context.admitsList
  infer_instance

def Wrapper (entry : Entry) : Prop :=
  entry.1.name = "list" ∧ entry.1.repetition = some .repeated ∧
    entry.1.physicalType = none ∧ entry.1.numChildren = some 1 ∧
    entry.1.typeLength = none ∧ Unannotated entry

instance (entry : Entry) : Decidable (Wrapper entry) := by
  unfold Wrapper
  infer_instance

def ListOuter (entry : Entry) : Prop :=
  entry.1.physicalType = none ∧ entry.1.numChildren = some 1 ∧ entry.1.typeLength = none

instance (entry : Entry) : Decidable (ListOuter entry) := by
  unfold ListOuter
  infer_instance

inductive Error where
  | original (cause : RecursiveSchema.Error)
  | pageLess (cause : Footer.PageLessRecursive.Error)
  | annotation (site : Location) (cause : ListFile.OpenError)
  | listShape (site : Location)
  | wrapper (site : Location)
  | nestedRepeated (outer priorWrapper : Location)
  deriving DecidableEq, Repr

mutual

/-- Every admitted branch consumes original SchemaElements in physical
preorder. A List consumes its unannotated repeated wrapper between the
outer item and element, although the wrapper is absent from Arrow. -/
inductive FieldWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry) :
    Nat → Context → Nat → Field → Nat → Prop where
  | leaf {depth ctx ordinal entry nullable kind} :
      original[ordinal]? = some entry → Unannotated entry → RepetitionWire entry nullable →
      entry.1.typeLength = none → entry.1.physicalType = some kind.physical →
      entry.1.numChildren.getD 0 = 0 →
      FieldWire reader original (depth + 1) ctx ordinal
        (.leaf ⟨ctx.site ordinal entry.1.name nullable, kind,
          (ctx.enter (ctx.site ordinal entry.1.name nullable)).steps, ctx.repeated⟩) (ordinal + 1)
  | group {depth ctx ordinal entry nullable count children next} :
      original[ordinal]? = some entry → Unannotated entry → RepetitionWire entry nullable →
      entry.1.typeLength = none → entry.1.physicalType = none →
      entry.1.numChildren = some count → 0 < count →
      FieldsWire reader original depth (ctx.enter (ctx.site ordinal entry.1.name nullable))
        count.toNat (ordinal + 1) children next →
      FieldWire reader original (depth + 1) ctx ordinal
        (.group (ctx.site ordinal entry.1.name nullable) children) next
  | list {depth ctx ordinal entry nullable wrapper element next} :
      original[ordinal]? = some entry → RepetitionWire entry nullable → ListOuter entry →
      ListFile.checkList reader entry.2 = .ok () → ctx.admitsList →
      original[ordinal + 1]? = some wrapper → Wrapper wrapper →
      FieldWire reader original depth
        (ctx.enterList (ctx.site ordinal entry.1.name nullable)
          (wrapperAt (ctx.site ordinal entry.1.name nullable) ordinal wrapper))
        (ordinal + 2) element next →
      FieldWire reader original (depth + 2) ctx ordinal
        (.list (ctx.site ordinal entry.1.name nullable)
          (wrapperAt (ctx.site ordinal entry.1.name nullable) ordinal wrapper) element) next

inductive FieldsWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry) :
    Nat → Context → Nat → Nat → List Field → Nat → Prop where
  | nil {depth ctx ordinal} : FieldsWire reader original depth ctx 0 ordinal [] ordinal
  | cons {depth ctx count ordinal field more middle next} :
      FieldWire reader original depth ctx ordinal field middle →
      FieldsWire reader original depth ctx count middle more next →
      FieldsWire reader original depth ctx (count + 1) ordinal (field :: more) next

end

structure RootWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (depth : Nat) (root : Entry) (fields : List Field) (allowNested : Bool := false) : Prop where
  originalRoot : original[0]? = some root
  unannotated : Unannotated root
  group : root.1.physicalType = none ∧ root.1.typeLength = none
  repetition : root.1.repetition = none ∨ root.1.repetition = some .required
  children : ∃ count, root.1.numChildren = some count ∧ 0 < count ∧
    FieldsWire reader original depth { allowNested := allowNested } count.toNat 1 fields original.size

def NamedAt (original : Array Entry) (location : Location) (entry : Entry) : Prop :=
  original[location.ordinal]? = some entry ∧
    ∃ parent, location.path = parent ++ [entry.1.name]

inductive StepWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (path : List String) : Step → Prop where
  | optional {site role entry} :
      NamedAt original site entry → entry.1.repetition = some .optional →
      (role = .list → ListFile.checkList reader entry.2 = .ok ()) →
      site.path <+: path → StepWire reader original path (.optional site role)
  | emptyList {outer wrapper outerEntry wrapperEntry} :
      NamedAt original outer outerEntry → NamedAt original wrapper wrapperEntry →
      ListOuter outerEntry → ListFile.checkList reader outerEntry.2 = .ok () →
      Wrapper wrapperEntry → wrapper.ordinal = outer.ordinal + 1 →
      wrapper.path = outer.path ++ [wrapperEntry.1.name] →
      wrapper.path <+: path → StepWire reader original path (.emptyList outer wrapper)

/-- The distinguished empty-list step describes the sole repeated
site on the physical path, at its original definition level. -/
structure StepsWire (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (path : List String) (steps : List Step) (repeated : Option Boundary) : Prop where
  original : ∀ step ∈ steps, StepWire reader original path step
  wrappers : steps.filterMap Step.wrapper? = repeated.toList.map (fun b => (b.outer, b.wrapper))
  boundary : ∀ b, repeated = some b → steps[b.emptyLevel]? = some (.emptyList b.outer b.wrapper)

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) (allowNested : Bool := false) where
  container : ThriftCompact.Traversal.Field
  items : List Footer.ColumnOrder.Item
  root : Entry
  fields : List Field
  leaves : Array Leaf
  originalItems : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items)
  aligned : snapshot.metadata.schema.length = items.length
  grammar : RootWire (Footer.ColumnOrder.footerReader limits.footer snapshot) (entries snapshot items)
    (limits.maxSchemaDepth - 1) root fields allowNested
  ordered : leaves = (fields.flatMap Field.leaves).toArray

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.checkRecursive limits bytes = .ok snapshot

def Compiled.arrow {limits : Snapshot.Limits} {snapshot : Snapshot.Checked} {allowNested : Bool}
    (schema : Compiled limits snapshot allowNested) : Arrow.RecursiveSchema.Schema :=
  ⟨schema.fields.map Field.arrow⟩

end

private def entryAt (original : Array Entry) (ordinal : Nat) (missing : Error) :
    Except Error {entry // original[ordinal]? = some entry} :=
  match original[ordinal]? with
  | none => .error missing
  | some entry => .ok ⟨entry, rfl⟩

private def checkRepetition (entry : Entry) (location : Location) :
    Except Error {nullable // RepetitionWire entry nullable} :=
  match found : entry.1.repetition with
  | some .required => .ok ⟨false, found⟩
  | some .optional => .ok ⟨true, found⟩
  | other => .error (.original (.repetition location other))

private structure FieldResult (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (depth : Nat) (ctx : Context) (ordinal : Nat) where
  field : Field
  next : Nat
  wire : FieldWire reader original depth ctx ordinal field next

private structure FieldsResult (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (depth : Nat) (ctx : Context) (count ordinal : Nat) where
  fields : List Field
  next : Nat
  wire : FieldsWire reader original depth ctx count ordinal fields next

private def readFields {reader : ThriftCompact.Traversal.Reader} {original : Array Entry}
    {depth : Nat} {ctx : Context}
    (readField : (ordinal : Nat) → Except Error (FieldResult reader original depth ctx ordinal)) :
    (count ordinal : Nat) → Except Error (FieldsResult reader original depth ctx count ordinal)
  | 0, ordinal => .ok ⟨[], ordinal, .nil⟩
  | count + 1, ordinal => do
    let first ← readField ordinal
    let rest ← readFields readField count first.next
    return ⟨first.field :: rest.fields, rest.next, .cons first.wire rest.wire⟩

private def readField (reader : ThriftCompact.Traversal.Reader) (original : Array Entry) :
    (depth : Nat) → (ctx : Context) → (ordinal : Nat) →
      Except Error (FieldResult reader original depth ctx ordinal)
  | 0, ctx, ordinal => do
    let entry ← entryAt original ordinal (.original (.missing ⟨ordinal, ctx.path⟩))
    throw (.original (.depth (ctx.site ordinal entry.val.1.name false).location))
  | depth + 1, ctx, ordinal => do
    let ⟨entry, found⟩ ← entryAt original ordinal (.original (.missing ⟨ordinal, ctx.path⟩))
    let location := (ctx.site ordinal entry.1.name false).location
    let ⟨nullable, repetition⟩ ← checkRepetition entry location
    let site := ctx.site ordinal entry.1.name nullable
    if unannotated : Unannotated entry then
      if natural : entry.1.typeLength = none then
        let childContext := ctx.enter site
        match physical : entry.1.physicalType with
        | none =>
          match count : entry.1.numChildren with
          | none => throw (.original (.arity location none))
          | some children =>
            if positive : 0 < children then
              let parsed ← readFields (readField reader original depth childContext)
                children.toNat (ordinal + 1)
              return ⟨.group site parsed.fields, parsed.next,
                .group found unannotated repetition natural physical count positive parsed.wire⟩
            else throw (.original (.arity location (some children)))
        | some type =>
          if terminal : entry.1.numChildren.getD 0 = 0 then
            match kind : type with
            | .int32 =>
              return ⟨.leaf ⟨site, .int32, childContext.steps, ctx.repeated⟩, ordinal + 1,
                .leaf found unannotated repetition natural (physical.trans (congrArg some kind)) terminal⟩
            | .int64 =>
              return ⟨.leaf ⟨site, .int64, childContext.steps, ctx.repeated⟩, ordinal + 1,
                .leaf found unannotated repetition natural (physical.trans (congrArg some kind)) terminal⟩
            | other => throw (.original (.physical location other))
          else throw (.original (.arity location entry.1.numChildren))
      else throw (.original (.typeLength location))
    else
      match annotation : ListFile.checkList reader entry.2 with
      | .error cause => throw (.annotation location cause)
      | .ok () =>
        if shape : ListOuter entry then
          if admitted : ctx.admitsList then
            let ⟨wrapper, wrapperFound⟩ ←
              entryAt original (ordinal + 1) (.original (.missing ⟨ordinal + 1, site.location.path⟩))
            let wrapperLocation := wrapperAt site ordinal wrapper
            match depthEq : depth with
            | 0 => throw (.original (.depth wrapperLocation))
            | remaining + 1 =>
              if wrapperShape : Wrapper wrapper then
                let child ← readField reader original remaining (ctx.enterList site wrapperLocation) (ordinal + 2)
                return ⟨.list site wrapperLocation child.field, child.next, by
                  rw [depthEq]
                  exact .list found repetition shape annotation admitted wrapperFound wrapperShape child.wire⟩
              else throw (.wrapper wrapperLocation)
          else
            match repeated : ctx.repeated with
            | some prior => throw (.nestedRepeated location prior.wrapper)
            | none => (admitted (.inr repeated)).elim
        else throw (.listShape location)

private def readRoot (reader : ThriftCompact.Traversal.Reader) (original : Array Entry)
    (depth : Nat) (allowNested : Bool) :
    Except Error {value : Entry × List Field // RootWire reader original depth value.1 value.2 allowNested} := do
  let ⟨root, found⟩ ← entryAt original 0 (.original .root)
  if unannotated : Unannotated root then
    if group : root.1.physicalType = none ∧ root.1.typeLength = none then
      if repetition : root.1.repetition = none ∨ root.1.repetition = some .required then
        match count : root.1.numChildren with
        | none => throw (.original .root)
        | some children =>
          if positive : 0 < children then
            let parsed ← readFields (readField reader original depth { allowNested := allowNested }) children.toNat 1
            if exactEnd : parsed.next = original.size then
              return ⟨(root, parsed.fields), ⟨found, unannotated, group, repetition,
                children, count, positive, exactEnd ▸ parsed.wire⟩⟩
            else throw (.original (.trailing parsed.next))
          else throw (.original .root)
      else throw (.original .root)
    else throw (.original .root)
  else throw (.original (.annotation ⟨0, []⟩))

/-- The same checked footer traversal serves the single-wrapper reader and the nested tree compiler. -/
public def compileWith (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) (allowNested : Bool) :
    Except Error (Compiled limits snapshot allowNested) := do
  match original : Footer.NestedLeaf.readItems limits.footer snapshot with
  | .error cause => throw (.original (.footerItems cause))
  | .ok (container, items) =>
    if aligned : snapshot.metadata.schema.length = items.length then
      let reader := Footer.ColumnOrder.footerReader limits.footer snapshot
      let ⟨(root, fields), grammar⟩ ← readRoot reader (entries snapshot items) (limits.maxSchemaDepth - 1) allowNested
      return ⟨container, items, root, fields, (fields.flatMap Field.leaves).toArray,
        original, aligned, grammar, rfl⟩
    else throw (.original (.schemaExtent snapshot.metadata.schema.length items.length))

public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Error (Compiled limits snapshot) :=
  compileWith limits snapshot false

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Error (Source limits bytes) := do
  match original : Snapshot.checkRecursive limits bytes with
  | .error (.original cause) => throw (.original (.snapshot cause))
  | .error (.pageLess cause) => throw (.pageLess cause)
  | .ok snapshot => return ⟨snapshot, ← compile limits snapshot, original⟩

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated
