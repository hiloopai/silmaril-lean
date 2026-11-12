module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Memory
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Agg
public import Silmaril.Wasm.SpecTec.Sim.Prims.Defs

/-!
# The dispatch

`read_done` sends each index of `readDone` to its lemma, for any `B` with `NoAcc B`;
`noAcc_builtins` discharges `NoAcc` for the concrete `Prims.builtins`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **`NoAcc` for the concrete `B`**: none of the accessors is a float, integer or host
primitive. -/
theorem noAcc_builtins (prof : Numerics.Profile) (hn : H → String) (host : HostSemantics H) :
    NoAcc (Prims.builtins prof hn host) where
  local_ _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]
  global _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]
  table _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]
  mem _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]
  elem _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]
  data _ := by simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **The dispatch**: every index of `readDone` has its backward lemma. -/
theorem read_done (B : Builtins) (NA : NoAcc B) (i : Nat) (hi : i ∈ readDone) (c : Config H)
    (w : Value) (hc : Typed (simEnv B) hn c)
    (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have CD := Typing.ctrlDecode_simEnv B
  simp only [readDone, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_localGet B NA c w hc hf, bwd_globalGet B NA c w hc hf,
    bwd_tableGetOob B NA c w hc hf, bwd_tableGetVal B NA c w hc hf,
    bwd_tableFillOob B NA c w hc hf, bwd_memoryFillOob B NA c w hc hf,
    Aggregates.bwd_structGetNull B CD aggDecode c w hc hf,
    Aggregates.bwd_arrayGetNull B CD aggDecode c w hc hf,
    Aggregates.bwd_arrayLenNull B CD aggDecode c w hc hf, bwd_arrayFillNull B c w hc hf,
    bwd_arrayInitElemNull B c w hc hf, bwd_arrayInitDataNull B c w hc hf]

end Silmaril.Wasm.SpecTec.Sim.BwdRead
