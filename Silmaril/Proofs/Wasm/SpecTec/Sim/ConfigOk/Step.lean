module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Thms
public import Silmaril.Wasm.Execution.Core.Typing.Config

/-!
# A typed step: the simulation's hypotheses hold of a configuration that steps

Round 2 showed `Typed` only for value code (`Typing.typed_vals`), which does not step, so no
step between two `Typed` configurations was exhibited. Here `typedStep_exists`: for every `B`,
encoding `hn`, profile and host, the configuration `nop` on the empty store and frame is

* typed by Core (`ConfigOk c []`),
* in the integrated forward fragment (`Integrate.Covered c`, hence `StoreOk c.store`),
* `Typed (simEnv B) hn c`, and its successor `c'` (the empty code) is `Typed` too,
* and `c` steps to `c'` (`Step.parametric .nop`).

So the non-bundle hypotheses of `Integrate.forward_concrete` and of the forward conjunct of
`Integrate.Task.wholeStepBounded` are jointly satisfiable *on a step*.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ConfigOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation

variable {H : Type} {B : Builtins}

/-- The configuration `nop` on the empty store, with no locals and the empty module instance. -/
def nopConfig : Silmaril.Wasm.Execution.Core.Config H :=
  ⟨{}, ⟨[], {}⟩, [.plain .nop]⟩

/-- Its successor: the same state with empty code. -/
def doneConfig : Silmaril.Wasm.Execution.Core.Config H :=
  ⟨{}, ⟨[], {}⟩, []⟩

set_option maxRecDepth 100000 in
/-- `NOP` is a typed `instr`. -/
theorem typedV_nop : TypedV (simEnv B) (.varT "instr" []) (instrToV .nop) :=
  Typing.typedV_closedCase (IntNumeric.findTyp_instr' B) rfl hasTyp_tupT_nil

/-- `nop` on the empty state is `Typed`. -/
theorem typed_nopConfig (hn : H → String) : Typed (simEnv B) hn (nopConfig (H := H)) := by
  have T := Typing.typingFacts_simEnv B hn
  have h0 := (T.config (doneConfig (H := H))).1 (Typing.typed_vals hn [] [])
  refine (T.config _).2 ⟨h0.1, ?_⟩
  exact typedV_list_iff.2 fun u hu => by
    simp only [nopConfig, adminsToV, adminToV, List.mem_singleton] at hu
    subst hu
    exact typedV_nop

/-- The empty code on the empty state is `Typed`. -/
theorem typed_doneConfig (hn : H → String) : Typed (simEnv B) hn (doneConfig (H := H)) :=
  Typing.typed_vals hn [] []

/-- The empty module instance is typed by Core, in the empty context. -/
theorem moduleInstOk_empty (s : Silmaril.Wasm.Execution.Core.Store H) :
    Silmaril.Wasm.Execution.Core.ModuleInstOk s {}
      { types := [], recs := [], tags := [], globals := [], mems := [], tables := [],
        funcs := [], datas := [], elems := [], refs := List.range 0 } :=
  .mk (k := 0) (by simp) .nil .nil .nil .nil .nil (by simp) .nil (by simp) List.nodup_nil
    (by simp) (Nat.zero_le _)

/-- The empty store is typed by Core. -/
theorem coreStoreOk_empty :
    Silmaril.Wasm.Execution.Core.StoreOk ({} : Silmaril.Wasm.Execution.Core.Store H) where
  tags := by simp
  globals := by simp
  mems := by simp
  tables := by simp
  funcs := by simp
  elems := by simp
  structs := by simp
  arrays := by simp
  exns := by simp
  acyclicStructs := by simp
  acyclicArrays := by simp
  acyclicExns := by simp
  structsClosed := by simp
  arraysClosed := by simp

/-- `nop` on the empty state is typed by Core, with result type `[]`. -/
theorem configOk_nopConfig : Silmaril.Wasm.Execution.Core.ConfigOk (nopConfig (H := H)) [] :=
  ⟨_, ⟨coreStoreOk_empty, _, [], moduleInstOk_empty _, .nil, rfl⟩,
    .single (.plain (.parametric .nop))⟩

/-- `nop` on the empty state is in the integrated forward fragment. -/
theorem covered_nopConfig : Integrate.Covered (nopConfig (H := H)) :=
  ⟨.cons rfl (fun _ _ _ h => by cases h) .nil .nil, Integrate.unpacked_empty [],
    Integrate.storeOk_empty⟩

/-- **A typed step.** For every `B`, encoding, numeric profile and host there are configurations
`c → c'`, both `Typed`, with `c` typed by Core (`ConfigOk`) and in the integrated forward fragment
(`Covered`, which includes `StoreOk c.store`). -/
theorem typedStep_exists (B : Builtins) (hn : H → String) (P : Numerics.Profile)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    ∃ c c' : Silmaril.Wasm.Execution.Core.Config H,
      Silmaril.Wasm.Execution.Core.ConfigOk c [] ∧ Integrate.Covered c ∧
      Integrate.StoreOk c.store ∧ Typed (simEnv B) hn c ∧ Typed (simEnv B) hn c' ∧
      Silmaril.Wasm.Execution.Core.Step P host c c' :=
  ⟨nopConfig, doneConfig, configOk_nopConfig, covered_nopConfig, Integrate.storeOk_empty,
    typed_nopConfig hn, typed_doneConfig hn, .parametric .nop⟩

end Silmaril.Wasm.SpecTec.Sim.ConfigOk
