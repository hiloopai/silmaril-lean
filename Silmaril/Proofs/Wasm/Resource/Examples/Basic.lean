module

public import Silmaril.Wasm.Resource.Examples.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms
public import Silmaril.Wasm.Spec.Litmus.Thms

/-!
# Resource protocol examples: litmus programs

A litmus program (the prefixes of one trace) satisfies a protocol sentence iff the protocol
accepts the trace (`models_progOf_proto_iff`), which `decide` evaluates.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Litmus
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A set of prefixes satisfies a protocol iff the protocol accepts the whole trace. -/
theorem sat_prefixesOf_iff {Ty A R S : Type} {X : Iface Ty} (l : List (Event A R X))
    (φ : Protocol S (Event A R X)) :
    (protoLogic Ty A R S).Sat (prefixesOf l) φ ↔ φ.acceptsB l = true := by
  rw [Protocol.acceptsB_iff]
  exact ⟨fun h => h l (List.prefix_refl l), fun h _ ht => Protocol.Accepts.of_prefix h ht⟩

/-- **A litmus program satisfies a protocol sentence iff the protocol accepts its trace.** -/
theorem models_progOf_proto_iff {S : Type} {X : Iface Unit} (l : List (Ev X))
    (φ : Protocol S (Ev X)) :
    Models (protoLogic Unit (List Val) (Behaviour Val) S)
      (Semantics.ofSets Unit (List Val) (Behaviour Val)) (progOf l) φ ↔ φ.acceptsB l = true :=
  (models_progOf_iff (protoLogic Unit (List Val) (Behaviour Val) S) l φ).trans
    (sat_prefixesOf_iff l φ)

end Silmaril.Wasm.Resource
