module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.Thms
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.Next

/-!
# Round 9, rm: every structured `Step_read` rule at memory SIMD code

* `read_exits`: the rules 8, 9, 10, 13, 14, 15, 16, 19, 20 hold backward at `configVD` in every
  `simEnv B`, at every configuration, with no typing hypothesis
  (`Raw/…/Round9/RMRead/{Exits,Return}`).
* `read_struct`: with `block` (0), `loop` (1), `return_call_ref-frame-addr` (11),
  `throw_ref-handler-catch` (17), `-catch_ref` (18) and `try_table` (22), at the concrete
  primitives (`Raw/…/Round9/RMRead/{FrameAddr,Block,Catch,TryTable}`).
* `adminsMS_of_handlerNext`: rule 21 fires only at memory-SIMD-free code.

So `RMPure.RestMSHCI` follows from `RestMSHCJ` (`restMSHCI_of_J`), and
`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPJ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (configVD)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- The structured `Step_read` rules proved here. -/
def readExits : List Nat := [8, 9, 10, 13, 14, 15, 16, 19, 20]

/-- **The nine exit rules of `Step_read` hold backward at `configVD`.** -/
theorem read_exits (B : Builtins) : ∀ i ∈ readExits, LeafRD B hn P host i := by
  intro i hi
  simp only [readExits, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwdRD_returnCallRefLabel B, bwdRD_returnCallRefHandler B,
    bwdRD_returnCallRefFrameNull B, bwdRD_throwRefInstrs B, bwdRD_throwRefLabel B,
    bwdRD_throwRefFrame B, bwdRD_throwRefHandlerEmpty B, bwdRD_throwRefHandlerCatchAll B,
    bwdRD_throwRefHandlerCatchAllRef B]

/-- The structured rules `read_struct` proves (15 of 16). -/
def readStruct : List Nat := readExits ++ [0, 1, 11, 17, 18, 22]

/-- **Fifteen structured `Step_read` rules hold backward at `configVD`**, at the concrete
primitives, up to `CodeEq`. -/
theorem read_struct (i : Nat) (hi : i ∈ readStruct) (c : Config H) (w : Value)
    (hf : Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (Round7.MemSimd.adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  have up : ∀ {j}, LeafRD (Prims.builtins P hn host) hn P host j →
      Fires (simEnv (Prims.builtins P hn host)) "Step_read" j (.tuple [configVD hn c, w]) →
      ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (Round7.MemSimd.adminsToVD js) ∧
        Step P host c ⟨c.store, c.frame, is'⟩ := fun hL hj => by
    obtain ⟨is', hw, hs⟩ := hL c w hj
    exact ⟨is', is', Bwd.CodeEq.refl is', hw, hs⟩
  simp only [readStruct, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with he | rfl | rfl | rfl | rfl | rfl | rfl
  · exact up (read_exits _ i he) hf
  · exact up bwdRD_block hf
  · exact up bwdRD_loop hf
  · exact bwdRD_returnCallRefFrameAddr _ Integrate.callInv_concrete c w hf
  · exact up (bwdRD_throwRefHandlerCatch _) hf
  · exact up (bwdRD_throwRefHandlerCatchRef _) hf
  · exact up bwdRD_tryTable hf

/-- `RMAtom.structRead` is the fifteen rules of `read_struct` and rule 21. -/
theorem structRead_split : ∀ i ∈ RMAtom.structRead, i ∈ readStruct ∨ i = 21 := by decide

/-- **`RestMSHCJ` gives `RMPure.RestMSHCI`.** -/
theorem restMSHCI_of_J (h : RestMSHCJ hn P host) : RMPure.RestMSHCI hn P host where
  read := by
    intro i hi c w hms _ _ hf
    rcases structRead_split i hi with he | rfl
    · exact read_struct i he c w hf
    · exact absurd (adminsMS_of_handlerNext _ hf) hms
  firesRead := h.firesRead

/-- **`OpenRMRestDPJ` gives `RMPure.OpenRMRestDPI`.** -/
theorem openRMRestDPI_of_J (O : OpenRMRestDPJ hn P host) : RMPure.OpenRMRestDPI hn P host :=
  ⟨O.forward, restMSHCI_of_J O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPJ`.** -/
theorem wholeStepValidRM_of_restDPJ
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPJ hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMPure.wholeStepValidRM_of_restDPI fun H hn hinj host hf hh nd r =>
    openRMRestDPI_of_J (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
