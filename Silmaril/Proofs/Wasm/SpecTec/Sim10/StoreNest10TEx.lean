module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreNest10T

/-!
# A nested store over a store holding a storing function

`labelStoreCfg10`: the store holds one memory (empty) and one function whose body is
`i32.store`; the code is `label 0 {} (i32.const 0; i32.const 0; i32.store)`. V1 traps inside the
label (`step_labelStoreCfg10`, a `Nest10 StoreLeaf10` step).

* In `simEnv10` its image is not typed (`not_typed10_labelStoreCfg`): the label's body holds a
  `STORE`. So no theorem stated in `simEnv10` says anything about it.
* In `simEnv10T` both images are typed (kernel evaluation), and **`fwd10T_storeNest` gives the
  step between them** (`sstep10T_labelStoreCfg`): a store under a label, in a state whose store
  holds a storing function.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim (typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (bytesB10 Nest10)

/-- One empty memory, and one function whose body is `i32.store`. -/
def storeFnMemStore10 : Store Empty :=
  { funcs := [.wasm ⟨[], []⟩ {} ⟨⟨0⟩, [], [.intStore .i32 none ⟨0, 0⟩]⟩],
    memories := [⟨ByteArray.empty, none⟩] }

/-- The redex inside the label. -/
def storeRedex10 : List Admin :=
  [value (.int .i32 0), value (.int .i32 0), .source (.intStore .i32 none ⟨0, 0⟩)]

/-- **The configuration**: a store under a label, over `storeFnMemStore10`. -/
def labelStoreCfg10 : Config Empty :=
  ⟨storeFnMemStore10, StoreFix.memStoreFrame10, [.label 0 [] storeRedex10]⟩

/-- Its successor: the trap, inside the label. -/
def labelStoreCfg10' : Config Empty :=
  ⟨storeFnMemStore10, StoreFix.memStoreFrame10, [.label 0 [] [.trap]]⟩

/-- **The V1 step**, a trapping store nested under a label. -/
theorem nest_labelStoreCfg10 : Nest10 StoreLeaf10 labelStoreCfg10 labelStoreCfg10' :=
  .label (.leaf (.intStoreTrap _ _ _ _ _ _ _ ⟨0⟩ ⟨ByteArray.empty, none⟩ rfl (by decide))) 0 []

theorem step_labelStoreCfg10 (host : HostSemantics Empty) :
    Step host labelStoreCfg10 labelStoreCfg10' :=
  Nest10.step (fun _ _ h => h.step) nest_labelStoreCfg10

/-- **In `simEnv10` its image is not typed**, at every builtins. -/
theorem not_typed10_labelStoreCfg (B : Builtins) :
    ¬ Typed10 (simEnv10 B) Empty.elim labelStoreCfg10 := by
  intro h
  have ha := typedV_list_iff.1 (Whole.typedV_code_of_typed10 h) _ (.head _)
  exact Whole.not_typed_store3 ⟨_, rfl⟩ (Whole.label_inv10 ha).2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem typed10T_labelStoreCfg (B : Builtins) :
    Typed10 (simEnv10T B) Empty.elim labelStoreCfg10 :=
  ⟨300, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem typed10T_labelStoreCfg' (B : Builtins) :
    Typed10 (simEnv10T B) Empty.elim labelStoreCfg10' :=
  ⟨300, by with_unfolding_all rfl⟩

/-- **The corrected 1.0 script steps between the images**, by the general theorem. -/
theorem sstep10T_labelStoreCfg (P : Profile) :
    SStepB (simEnv10T (bytesB10 P)) (configV Empty.elim labelStoreCfg10)
      (configV Empty.elim labelStoreCfg10') :=
  fwd10T_storeNest nest_labelStoreCfg10 (typed10T_labelStoreCfg _) (typed10T_labelStoreCfg' _)

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
