module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
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
packed program of its elaborated lowering, at any exit types. -/
theorem packed_observe_proof (source : Phi.Graph V K P.Instr) (C : Captures V β)
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
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code := by
  let input := C.store record
  let store := Phi.inputEnv (treeModel M.raw) input
  have agrees (i : Fin n) : NamedFlat.Entry.inputEnv β record i.val = store (C.names i, 0) := by
    simpa [input, store, captureEnv, i.isLt, Phi.inputEnv, Phi.liftStore, treeModel] using
      C.inputEnv_eq record i
  have openTree := NamedFlat.compile_run_tree M.raw (Phi.OrderedExits.lower source) exits C.names
    elaborated store (NamedFlat.Entry.inputEnv β record) agrees
  have lexical := Phi.OrderedExits.run_commutes (treeModel M.raw) ⟨fun _ _ => rfl⟩ source input
  calc
    _ = ((Phi.OrderedExits.run (treeModel M.raw) source input >>= fun p =>
          pure (treeExitNumber exits p)) >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
      simp only [input, bind_assoc, pure_bind]
    _ = (region M.raw (NamedFlat.Entry.inputEnv β record) code.erase >>= fun p =>
          pure (FiniteCFG.packedTreeOutput p)) :=
      congrArg (fun t => t >>= fun p => pure (FiniteCFG.packedTreeOutput p))
        ((congrArg (fun t => t >>= fun p => pure (treeExitNumber exits p)) lexical).trans openTree)
    _ = _ := by
      change _ = region M.raw (extend ambient (encodeValue Atoms _ record))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList)
      rw [← NamedFlat.Entry.inputEnv_packet β record,
        NamedFlat.Capture.packed_context_tree M.raw typed ambient]

open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping in
/-- The semantic square for a closed forwarding table. From checks on the
original graph and the table, the lowering of the normalized graph
elaborates to a graph that is typed at the computed packet types, and the
φ run of the original graph at the ordered exits is the run of its typed
packed program. -/
theorem source_square_proof [DecidableEq κ] (graph : Phi.Graph V K P.Instr)
    (table : Phi.Forward.Table V K) (exits : List (Option K)) (inputs : List V)
    (types : V → Ty κ) (exitType : Option K → Ty κ) (C : Captures (Phi.Forward.Name V K) β)
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
            (Program.ofCFGEntry typed).code := by
  obtain ⟨code, elaborated⟩ := Option.isSome_iff_exists.mp
    (NamedFlat.Phi.compile_of_closed graph table exits inputs C.names isClosed fragment covered)
  have typed := check_sound code β _ _
    (certified_checks (Phi.Forward.forward graph table) exits (forwardTypes types) exitType
      C.names β code (certified_forward graph table types exitType certificate) declared
      elaborated)
  refine ⟨code, typed, elaborated, fun M record ambient => ?_⟩
  rw [← Phi.Forward.run_forward (treeModel M.raw) graph table valid (C.store record)]
  exact packed_observe_proof (Phi.Forward.forward graph table) C exits elaborated typed M record
    ambient

open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping in
/-- The semantic square from checks on the original graph only, with the
inferred forwarding table. -/
theorem source_square_infer_proof [DecidableEq κ] (graph : Phi.Graph V K P.Instr)
    (exits : List (Option K)) (inputs : List V) (arrivals : Phi.GlobalSSA.Certificate V K)
    (rank : K → Nat) (types : V → Ty κ) (exitType : Option K → Ty κ)
    (C : Captures (Phi.Forward.Name V K) β)
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
            (Program.ofCFGEntry typed).code := by
  have labels : (graph.blocks.map Prod.fst).Nodup := by
    have checks := inScope
    simp only [Phi.OrderedExits.check, Phi.GlobalSSA.check, Phi.Graph.check, Bool.and_eq_true,
      decide_eq_true_eq] at checks
    have distinct := checks.2.1.1.1
    simpa [Phi.OrderedExits.forScope, List.map_map, Function.comp_def] using distinct
  exact source_square_proof graph _ exits inputs types exitType C
    (Phi.Forward.check_infer graph exits inputs labels)
    (Phi.Forward.closed_infer_of_ranked graph exits inputs arrivals rank inScope claims acyclic)
    fragment covered certificate declared

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics
