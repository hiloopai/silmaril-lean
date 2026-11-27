module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping

/-! # The typed packet of a lowered and versioned edge

A certified jump of a φ graph is followed through the lowering and the
versioning, and the value that the versioned jump carries is typed.

On a jump to a block the lowering sends the φ operands of the target that
this predecessor supplies, packed in the order of the rows, and the
versioning pairs them with the record of the target, in the order of its
layout. The pair has the computed packet type of the target. The record
holds source registers only: the packet register is the parameter of
every lowered block and is left out of every layout.

On a jump to a label that is not a block there is no record, and the
payload has the declared type of the label.

Both hold for any typing of the versioned names in which the current
version of every source register has its declared type.

The versioning maintains that state along a body. A certified body,
lowered and versioned from any current versions at any depth, is typed
in the named typing: every binder has the type of its operand, and every
jump carries a value of the type of its label, by the two theorems on
edges. The typing of names is one function of the name. It has to give
the declared type to the current version of every source register, and
to every later version; nothing is asked of the versions in between. The
canonical typing, in which every version of a register has the declared
type of the register, is such a typing at every state, so no freshness of
versions is needed for the types to agree. Since a name has one type
wherever it is bound, binding a name again is harmless for typing; that
distinct binders get distinct positions is a separate matter and is not
used. The entry of the versioned lowering is the versioned entry at the
initial versions, so it is typed in the canonical typing.

The canonical typing is not a typing of a whole versioned block. A block
first takes its packet apart, unpacks the record and decodes the φ
operands, and the names it binds on the way hold the rest of a tuple: the
packet register at several versions, and one more version of every
register of the record. The statement for bodies is for any typing that
is canonical from some depth on.

A whole versioned block is typed in `blockTyping`, which is explicit. The
packet has the computed packet type. The temporaries have the types of
what remains: a version of the packet register has the type of the rest
of the φ operands, and an even version of a source register, from `4` to
twice the length of the record plus `2`, has the type of the rest of the
record. Every other version of a source register has its declared type.
The temporaries do not touch what the body needs. After the prefix, the
current version of a source register is its initial version, the odd
version at which the record gave it, or a version above the record at
which a φ row gave it; and the body binds above all of them. At each of
these the typing gives the declared type. So the theorem for bodies
applies after the prefix.

No freshness or distinctness is assumed. The registers of a record need
not be distinct and the φ destinations need not be distinct or apart from
the record: every binder of the prefix has its own version, and a name is
a register with a version. A typing by name can go wrong only if one
name is bound at two types, and the versioning never binds a name twice
in a block.

The elaboration replaces names by positions, and it keeps the typing. A
positional context agrees with a typing of names when every position
that a name is sent to has the type of the name. The captures give such
a context for the entry, when the capture context has the declared types
of the captures; the packet gives one for a block. A binder adds the
newest slot at the type of its name and moves the older names one slot,
so the agreement is kept under every binder; a name that is bound again
simply gets a newer slot of the type of the name. An elaborated value
then has the type of the value, an elaborated primitive is applied at
its source type, and an elaborated jump carries a value of the type of
its index. The index of a label is the first block with that label, and
otherwise the first position of the label among the exits; the type at
that index is the computed packet type of that block, or the declared
type of the label, which is the type that a jump to the label carries.

So the elaborated lowering of a certified φ graph passes the typing check
at the computed packet types, when the capture context has the declared
types of the captures. The typed elaboration returns the elaborated
graph; with the theorem on closed tables no elaboration is assumed, and
every hypothesis is a check on the φ graphs.

Nothing about names is assumed beyond the certificate. Overlapping names
do not invalidate the statement: typing is by name, a name has one type,
and the positional context follows the names through every binder.

The forwarding normalization keeps the certificate, for any table, with
the copies at the declared types of their registers. It changes three
things and reorders nothing. The reads of a body are renamed by the
reader of its block, and each φ operand by the reader of its
predecessor; a reader sends a register to itself or to a copy of it, so
it keeps types. The rows of a block get, after the original rows and in
the order of the table, one row for each register the block receives,
with one operand for each listed predecessor: the register as that
predecessor reads it, which has the type of the copy. The one fact about
the graph that is used is that a body is a listed predecessor of every
block it jumps to; otherwise the operand of a copy row would be the unit
default. That is so by the definition of the predecessors.

So the typed elaboration follows from checks on the original graph: its
certificate, its fragment, a closed table, and captures that cover the
inputs at their declared types. With the inferred table the closedness
comes from the scope check with claims, the condition on claims and a
rank.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row)

universe u v

variable {Base V K : Type u} {F : Type v}

/-- A value read at current versions has the type of the value, when the
current version of each register it reads has the type of the register. -/
theorem valueType_rn {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) (value : Val W)
    (current : ∀ z ∈ value.fvList, versioned (z, cur z) = types z) :
    valueType versioned (Version.rn cur value) = valueType types value :=
  valueType_rn_proof types versioned cur value current

/-- The record of a list of registers, read at current versions, has the
record type of the list. -/
theorem valueType_record {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) (registers : List W)
    (current : ∀ y ∈ registers, versioned (y, cur y) = types y) :
    valueType versioned (Version.pack cur registers) = recordType types registers :=
  valueType_record_proof types versioned cur registers current

/-- The packed φ operands of an edge have the type of the rows, when each
operand has the type of its destination. -/
theorem valueType_args [DecidableEq K] (types : V → Ty Base) (pred : Option K)
    (rows : List (Row V K))
    (operands : ∀ row ∈ rows, valueType types (row.operand pred) = types row.dst) :
    valueType (lifted types) (Phi.pack (Phi.arguments pred rows)) = argsType types rows :=
  valueType_args_proof types pred rows operands

variable [DecidableEq V] [DecidableEq K]

/-- The record that the versioning carries to a block of the lowering is
the layout of the lowered block. -/
theorem destinations_lower (graph : Graph V K F) (key : K) :
    Versioning.destinations (Phi.OrderedExits.lower graph) (some key) =
      (graph.blocks.lookup key).map fun block =>
        Versioning.slots (Phi.OrderedExits.lower graph)
          (Phi.OrderedExits.lowerBlock graph key block) :=
  destinations_some_proof graph key

/-- The record of a lowered block holds source registers only. -/
theorem slots_some (graph : Graph V K F) (key : K) (block : Block V K F) :
    ∀ y ∈ Versioning.slots (Phi.OrderedExits.lower graph)
      (Phi.OrderedExits.lowerBlock graph key block), ∃ r, y = some r :=
  slots_some_proof graph key block

variable [DecidableEq Base] [HasTy F (Ty Base)]

/-- A certified jump to a block, lowered and versioned, carries a packet
of the computed packet type of the block, when the current version of
every source register has its declared type. -/
theorem edge_packet (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred : Option K) (key : K) (block : Block V K F) (value : Val V)
    (found : graph.blocks.lookup key = some block)
    (typed : termTyped graph types exitType pred (.br (some key) value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br (some key) value : Term V (Option K) F)).toRegion = .br (some key) payload ∧
      valueType versioned payload = packetType graph types key block :=
  edge_packet_proof graph types exitType pred key block value found typed live cur depth versioned
    current

/-- A certified jump to a label that is not a block, lowered and
versioned, carries a payload of the declared type of the label, and no
record. -/
theorem exit_payload (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred target : Option K) (value : Val V)
    (absent : Phi.OrderedExits.lookup graph target = none)
    (typed : termTyped graph types exitType pred (.br target value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br target value : Term V (Option K) F)).toRegion = .br target payload ∧
      valueType versioned payload = exitType target :=
  exit_payload_proof graph types exitType pred target value absent typed live cur depth versioned
    current

/-- A certified body, lowered and versioned from the given current
versions and depth, is typed, for any typing of the versioned names that
gives the declared type to the current version of every source register
and to every later version. -/
theorem body_version_typed (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred : Option K) (live : List (Option V))
    (versioned : Option V × Nat → Ty Base) (source : CFG.Body V (Option K) F)
    (cur : Option V → Nat) (depth : Nat)
    (typed : bodyTyped graph types exitType pred source = true)
    (current : ∀ register, versioned (some register, cur (some register)) = types register)
    (fresh : ∀ register v, depth < v → versioned (some register, v) = types register) :
    regionTyped versioned (targetType graph types exitType)
      (Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur depth
        (Phi.liftBody (Phi.OrderedExits.branchValue graph pred) source).toRegion) = true :=
  version_body_typed_proof graph types exitType pred live versioned source cur depth typed current
    fresh

/-- In the canonical typing a certified body, lowered and versioned, is
typed from any current versions at any depth. -/
theorem body_version_canon (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred : Option K) (live : List (Option V))
    (source : CFG.Body V (Option K) F) (cur : Option V → Nat) (depth : Nat)
    (typed : bodyTyped graph types exitType pred source = true) :
    regionTyped (canon types) (targetType graph types exitType)
      (Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur depth
        (Phi.liftBody (Phi.OrderedExits.branchValue graph pred) source).toRegion) = true :=
  body_version_typed graph types exitType pred live (canon types) source cur depth typed
    (fun _ => rfl) (fun _ _ _ => rfl)

/-- The entry of the versioned lowering of a certified graph is typed in
the canonical typing. -/
theorem entry_typed (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (certificate : certified graph types exitType = true) :
    regionTyped (canon types) (targetType graph types exitType)
      (Versioning.compile (Phi.OrderedExits.lower graph)).entry.toRegion = true := by
  simp only [certified, Bool.and_eq_true] at certificate
  rw [compile_entry_toRegion]
  exact body_version_canon graph types exitType none _ graph.entry (fun _ => 0) 0 certificate.1

/-- The body of a block of a certified graph, lowered and versioned from
any current versions at any depth, is typed in the canonical typing. -/
theorem block_body_typed (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (certificate : certified graph types exitType = true)
    (item : K × Block V K F) (member : item ∈ graph.blocks) (live : List (Option V))
    (cur : Option V → Nat) (depth : Nat) :
    regionTyped (canon types) (targetType graph types exitType)
      (Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur depth
        (Phi.liftBody (Phi.OrderedExits.branchValue graph (some item.1)) item.2.body).toRegion) =
      true := by
  simp only [certified, Bool.and_eq_true, List.all_eq_true] at certificate
  exact body_version_canon graph types exitType (some item.1) live item.2.body cur depth
    (certificate.2 item member)

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The packet of a versioned block has the computed packet type, which
is the product of the types of its two parts. -/
theorem blockTyping_packet (graph : Graph V K F) (types : V → Ty Base) (key : K)
    (block : Block V K F) :
    blockTyping graph types key block (none, 0) = packetType graph types key block ∧
      packetType graph types key block =
        .product (blockTyping graph types key block (none, 1))
          (blockTyping graph types key block (none, 2)) :=
  ⟨rfl, rfl⟩

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The temporaries of the prefix do not touch the versions that the body
uses: a source register has its declared type at its initial version, at
every odd version, and at every version above the record. -/
theorem blockTyping_source (graph : Graph V K F) (types : V → Ty Base) (key : K)
    (block : Block V K F) (register : V) (version : Nat)
    (side : version % 2 = 1 ∨ version < 4 ∨
      2 + 2 * (Versioning.slots (Phi.OrderedExits.lower graph)
        (Phi.OrderedExits.lowerBlock graph key block)).length < version) :
    blockTyping graph types key block (some register, version) = types register := by
  simp only [blockTyping]
  split
  · omega
  · rfl

/-- A versioned block of the lowering of a certified graph is typed in
its block typing, from its packet at the computed packet type. This is
the block that the versioning produces: the prefix that takes the packet
apart, unpacks the record and decodes the φ operands, and the versioned
body. -/
theorem block_typed (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (certificate : certified graph types exitType = true) (item : K × Block V K F)
    (member : item ∈ graph.blocks) :
    regionTyped (blockTyping graph types item.1 item.2) (targetType graph types exitType)
      (Versioning.compileBlock (Phi.OrderedExits.lower graph)
        (Phi.OrderedExits.lowerBlock graph item.1 item.2)).body.toRegion = true :=
  block_typed_proof graph types exitType certificate item member

/-- An elaborated body that is typed by name passes the positional check,
when the positional context agrees with the typing of names and each
indexed label has the type of the label. -/
theorem body_checked {N L : Type u} [DecidableEq N] {labels : Nat}
    (index : L → Option (Fin labels)) (types : Fin labels → Ty Base) (ty : N → Ty Base)
    (labelType : L → Ty Base)
    (labelsOk : ∀ label i, index label = some i → types i = labelType label) {n : Nat}
    (names : Names N n) (ctx : BoundCtx (Ty Base) n) (source : CFG.Body N L F)
    (code : LambdaSSA.Flat F labels n) (agree : ∀ z i, names z = some i → ctx.get i = ty z)
    (typed : regionTyped ty labelType source.toRegion = true)
    (elaborated : body index names source = some code) : checkBody types ctx code = true :=
  body_checked_proof index types ty labelType labelsOk names ctx source code agree typed
    elaborated

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The index that the elaboration gives a label has the type that a jump
to the label carries: the computed packet type at the first block of
that label, or the declared type at the first position of the label
among the exits. -/
theorem labels_typed (graph : Graph V K F) (exits : List (Option K)) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (label : Option K)
    (i : Fin ((Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length + exits.length))
    (indexed : labelIndex (Versioning.compile (Phi.OrderedExits.lower graph)).blocks exits label =
      some i) :
    SSA.FiniteSum.append (internal graph types) (external exits exitType) i =
      targetType graph types exitType label :=
  labels_typed_proof graph exits types exitType label i indexed

/-- The elaborated lowering of a certified φ graph passes the typing check
at the computed packet types, when the capture context has the declared
types of the captures. -/
theorem certified_checks (graph : Graph V K F) (exits : List (Option K)) (types : V → Ty Base)
    (exitType : Option K → Ty Base) {n : Nat} (captures : Fin n → Option V)
    (captureTypes : BoundCtx (Ty Base) n)
    (target : LambdaSSA.FiniteCFG F (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length
      exits.length n)
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i))
    (elaborated : NamedFlat.compile (Phi.OrderedExits.lower graph) exits captures = some target) :
    check target captureTypes (internal graph types) (external exits exitType) = true :=
  certified_checks_proof graph exits types exitType captures captureTypes target certificate
    declared elaborated

/-- The typed elaboration of the lowering of a certified φ graph returns
the elaborated graph at the computed packet types. -/
theorem compileTyped_of_certified (graph : Graph V K F)
    (exits : List (Option K)) (types : V → Ty Base) (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option V) (captureTypes : BoundCtx (Ty Base) n)
    {target : LambdaSSA.FiniteCFG F (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length
      exits.length n}
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i))
    (elaborated : NamedFlat.compile (Phi.OrderedExits.lower graph) exits captures = some target) :
    ∃ result, compileTyped (Phi.OrderedExits.lower graph) exits captures captureTypes
        (internal graph types) (external exits exitType) = some result ∧ result.val = target :=
  compileTyped_of_check (Phi.OrderedExits.lower graph) exits captures captureTypes
    (internal graph types) (external exits exitType) elaborated
    (certified_checks graph exits types exitType captures captureTypes target certificate declared
      elaborated)

/-- A certified body stays certified under the forwarding normalization,
when the entry or block that runs it is a listed predecessor of every
block it jumps to. -/
theorem body_forward_typed (graph : Graph V K F) (table : Phi.Forward.Table V K)
    (types : V → Ty Base) (exitType : Option K → Ty Base) (pred : Option K)
    (source : CFG.Body V (Option K) F)
    (listed : ∀ key, some key ∈ source.targets → pred ∈ graph.predecessors key)
    (typed : bodyTyped graph types exitType pred source = true) :
    bodyTyped (Phi.Forward.forward graph table) (forwardTypes types) exitType pred
      (Phi.Forward.body (Phi.Forward.reader table pred) source) = true :=
  forward_body_typed_proof graph table types exitType pred source listed typed

/-- The forwarding normalization keeps the certificate, for any table,
with the copies at the declared types of their registers. -/
theorem certified_forward (graph : Graph V K F) (table : Phi.Forward.Table V K)
    (types : V → Ty Base) (exitType : Option K → Ty Base)
    (certificate : certified graph types exitType = true) :
    certified (Phi.Forward.forward graph table) (forwardTypes types) exitType = true :=
  certified_forward_proof graph table types exitType certificate

/-- The typed elaboration succeeds for the normalized graph of a closed
forwarding table, from checks on the φ graphs only: the table is closed,
the graph is in the fragment, the normalized graph is certified, and the
captures cover the declared inputs at their declared types. -/
theorem compileTyped_of_closed (graph : Graph V K F)
    (table : Phi.Forward.Table V K) (exits : List (Option K)) (inputs : List V)
    (types : Phi.Forward.Name V K → Ty Base) (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option (Phi.Forward.Name V K)) (captureTypes : BoundCtx (Ty Base) n)
    (isClosed : Phi.Forward.closed graph table exits inputs = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z))
    (certificate : certified (Phi.Forward.forward graph table) types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i)) :
    (compileTyped (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits captures
      captureTypes (internal (Phi.Forward.forward graph table) types)
      (external exits exitType)).isSome = true := by
  obtain ⟨target, elaborated⟩ := Option.isSome_iff_exists.mp
    (NamedFlat.Phi.compile_of_closed graph table exits inputs captures isClosed fragment covered)
  obtain ⟨result, typed, _⟩ := compileTyped_of_certified (Phi.Forward.forward graph table)
    exits types exitType captures captureTypes certificate declared elaborated
  rw [typed]
  rfl

/-- The typed elaboration of the normalized graph of a closed forwarding
table succeeds, from checks on the original graph and the table: the
table is closed, the graph is in the fragment and certified, and the
captures cover the declared inputs at their declared types. -/
theorem compileTyped_of_source (graph : Graph V K F) (table : Phi.Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (types : V → Ty Base)
    (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option (Phi.Forward.Name V K)) (captureTypes : BoundCtx (Ty Base) n)
    (isClosed : Phi.Forward.closed graph table exits inputs = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted (forwardTypes types) (captures i)) :
    (compileTyped (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits captures
      captureTypes (internal (Phi.Forward.forward graph table) (forwardTypes types))
      (external exits exitType)).isSome = true :=
  compileTyped_of_closed graph table exits inputs (forwardTypes types) exitType captures
    captureTypes isClosed fragment covered (certified_forward graph table types exitType certificate)
    declared

/-- The typed elaboration after the inferred normalization succeeds, from
checks on the original graph only: the existing scope check with arrival
claims, claims that list no register of their block, a rank, the
fragment, the typing certificate, and captures that cover the declared
inputs at their declared types. -/
theorem compileTyped_infer_of_ranked (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (arrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate V K) (rank : K → Nat)
    (types : V → Ty Base) (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option (Phi.Forward.Name V K)) (captureTypes : BoundCtx (Ty Base) n)
    (inScope : Phi.OrderedExits.check graph exits inputs arrivals = true)
    (claims : Phi.Forward.claimed graph arrivals = true)
    (acyclic : Phi.Forward.ranked graph rank = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted (forwardTypes types) (captures i)) :
    (compileTyped (Phi.OrderedExits.lower
        (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))) exits captures
      captureTypes
      (internal (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))
        (forwardTypes types))
      (external exits exitType)).isSome = true :=
  compileTyped_of_source graph _ exits inputs types exitType captures captureTypes
    (Phi.Forward.closed_infer_of_ranked graph exits inputs arrivals rank inScope claims acyclic)
    fragment covered certificate declared

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
