module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.SourceSemantics

/-! # From the φ source to the typed packed program

One square, from checks on the original φ graph to its compiled program.
On one side is the independent φ evaluator of the original graph, which
reads every φ operand in the store of the predecessor, observed at the
ordered exits. On the other is the typed packed program of the
elaborated lowering of the normalized graph, run on the supplied input
record. They are equal as trees, in every model of the primitives.

The square composes existing theorems; no denotation is proved again.

* The forwarding normalization keeps the φ run, when no block defines a
  register that it receives.
* The lowering and the versioning keep it: the φ run is the lexical run
  of the versioned lowering.
* The elaboration keeps the lexical run of a named graph at the numbered
  exits, for an accepted elaboration.
* The packed program of a typed elaborated graph, on the packed input
  record, runs as the graph does on the decoded captures.

The last three are the steps of the existing theorem for admissions of φ
graphs at the live-out exit interface. That theorem takes the elaboration
and its typing as fields of the admission, and its exits carry a payload
with a live-out record. Here the same steps are composed at any exit
types, and the elaboration and its typing are obtained from the source:
the elaboration succeeds for a closed table in the fragment, and its
result is typed at the computed packet types for a certified graph.

Typing and semantics stay apart. The typing certificate is used for one
thing: the typed packed program needs a typing of the elaborated graph.
The equality of runs does not depend on which typing is chosen, and the
steps on runs use no typing.

The captures are the ones supplied and the exits are the declared ones
in their order. The values of the copies in the input store do not
matter: the original graph is run on the original part of the store.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (Region FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

universe u v

variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {n : Nat} {β : BoundCtx (Ty κ) n}

local notation "Atoms" => AtomValues.carrier (κ := κ)

/-- The φ run of a graph, at the ordered exits, is the run of the typed
packed program of its elaborated lowering, at any exit types and for any
typing of the elaborated graph. -/
theorem packed_observe (source : Phi.Graph V K P.Instr) (C : Captures V β)
    (exits : List (Option K))
    {internal : Fin (Versioning.compile (Phi.OrderedExits.lower source)).blocks.length → Ty κ}
    {external : Fin exits.length → Ty κ}
    {code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower source)).blocks.length
      exits.length n}
    (elaborated : NamedFlat.compile (Phi.OrderedExits.lower source) exits C.names = some code)
    (typed : code.HasType β internal external) {Events : Type u → Type u}
    (M : Model (κ := κ) Events P.Instr) (record : Input β) (ambient : Env (Sigma Atoms)) :
    (Phi.OrderedExits.run (treeModel M.raw) source (C.store record) >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code :=
  packed_observe_proof source C exits elaborated typed M record ambient

variable [DecidableEq κ]

/-- The semantic square for a closed forwarding table, from checks on the
original graph and the table: no block defines a register it receives,
the table is closed, the graph is in the fragment and certified, and the
captures cover the declared inputs at their declared types. The lowering
of the normalized graph elaborates to a graph that is typed at the
computed packet types, and the φ run of the original graph at the
ordered exits is the run of its typed packed program. -/
theorem source_square (graph : Phi.Graph V K P.Instr) (table : Phi.Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (types : V → Ty κ)
    (exitType : Option K → Ty κ) (C : Captures (Phi.Forward.Name V K) β)
    (valid : Phi.Forward.check graph table = true)
    (isClosed : Phi.Forward.closed graph table exits inputs = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, C.names i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, β.get i = lifted (forwardTypes types) (C.names i)) :
    ∃ (code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph table))).blocks.length exits.length n)
      (typed : code.HasType β (internal (Phi.Forward.forward graph table) (forwardTypes types))
        (external exits exitType)),
      NamedFlat.compile (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits C.names =
        some code ∧
      ∀ {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr) (record : Input β)
        (ambient : Env (Sigma Atoms)),
        (Phi.OrderedExits.run (treeModel M.raw) graph (C.store record ∘ Sum.inl) >>= fun p =>
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          region M.raw (extend ambient (encodeValue Atoms _ record))
            (Program.ofCFGEntry typed).code :=
  source_square_proof graph table exits inputs types exitType C valid isClosed fragment covered
    certificate declared

/-- The semantic square from checks on the original graph only, with the
inferred forwarding table: the existing scope check with arrival claims,
claims that list no register of their block, a rank, the fragment, the
typing certificate, and captures that cover the declared inputs at their
declared types. -/
theorem source_square_infer (graph : Phi.Graph V K P.Instr) (exits : List (Option K))
    (inputs : List V) (arrivals : Phi.GlobalSSA.Certificate V K) (rank : K → Nat)
    (types : V → Ty κ) (exitType : Option K → Ty κ) (C : Captures (Phi.Forward.Name V K) β)
    (inScope : Phi.OrderedExits.check graph exits inputs arrivals = true)
    (claims : Phi.Forward.claimed graph arrivals = true)
    (acyclic : Phi.Forward.ranked graph rank = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, C.names i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, β.get i = lifted (forwardTypes types) (C.names i)) :
    ∃ (code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs)))).blocks.length
          exits.length n)
      (typed : code.HasType β
        (internal (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))
          (forwardTypes types)) (external exits exitType)),
      NamedFlat.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))) exits C.names =
        some code ∧
      ∀ {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr) (record : Input β)
        (ambient : Env (Sigma Atoms)),
        (Phi.OrderedExits.run (treeModel M.raw) graph (C.store record ∘ Sum.inl) >>= fun p =>
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          region M.raw (extend ambient (encodeValue Atoms _ record))
            (Program.ofCFGEntry typed).code :=
  source_square_infer_proof graph exits inputs arrivals rank types exitType C inScope claims
    acyclic fragment covered certificate declared

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics
