module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Defs

/-!
# Round 4: `Bounded` is not preserved by Core's step

`Round4.Bounded` includes round 2's `Integrate.StoreOk`, whose memory bound is `< 2 ^ 32` bytes.
The bound has to be strict: on a memory of exactly `2 ^ 32` bytes `memory.fill` at the last byte
is a Core step whose SpecTec counterpart produces the ill-typed `CONST I32 (% 2 ^ 32)`
(`Memory.fillSucc_full_ne`). But Core lets an `i32` memory grow to exactly `2 ^ 32` bytes
(`Memory.grow_full`), so validity does not keep `Bounded`:

* `growCfg`: one `i32` memory of no pages and no maximum, and `i32.const 65536; memory.grow 0`;
* `configOk_growCfg : ConfigOk growCfg [.i32]`, `bounded_growCfg : Bounded growCfg`;
* `step_growCfg`: Core steps (`memory.grow-succeed`, under `Profile.spec nd r`) to a memory of
  `2 ^ 32` bytes, which is not `Bounded` (`not_bounded_preserved`).

So the multi-step corollaries (`Round4.steps_sim`, `ssteps_sim`) assume `BoundedReach`. Core's
validity itself is preserved (`Step.preservation`, silmaril-lean).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- Memory index `0`. -/
def memIdx0 : MemIdx := ⟨0⟩

/-- The store with one empty `i32` memory without maximum. -/
def growStore : Store H := { mems := [Memory.emptyMem32] }

/-- The module instance listing that memory. -/
def growModule : ModuleInst := { mems := [0] }

/-- `i32.const 65536; memory.grow 0`, on `growStore`. -/
def growCfg : Config H :=
  ⟨growStore, ⟨[], growModule⟩, [aconst .i32 65536, .plain (.memoryGrow memIdx0)]⟩

theorem storeOk_growStore : StoreOk (growStore (H := H)) where
  tags := by simp [growStore]
  globals := by simp [growStore]
  mems := by
    simp only [growStore, List.mem_singleton]
    rintro _ rfl
    exact ⟨show Memory.emptyMem32.type.Valid by decide, rfl⟩
  tables := by simp [growStore]
  funcs := by simp [growStore]
  elems := by simp [growStore]
  structs := by simp [growStore]
  arrays := by simp [growStore]
  exns := by simp [growStore]
  acyclicStructs := by simp [growStore]
  acyclicArrays := by simp [growStore]
  acyclicExns := by simp [growStore]
  structsClosed := by simp [growStore]
  arraysClosed := by simp [growStore]

theorem moduleInstOk_growModule :
    ∃ C, ModuleInstOk (growStore (H := H)) growModule C ∧ C.mems = [Memory.emptyMem32.type] :=
  ⟨_, .mk (k := 0) (by simp [growModule]) .nil .nil .nil (.cons (.mem rfl) .nil) .nil
    (by simp [growModule]) .nil (by simp [growModule]) (by simp [growModule])
    (by simp [growModule]) (Nat.zero_le _), rfl⟩

/-- **The configuration is valid**: `⊢ growCfg : i32`. -/
theorem configOk_growCfg : ConfigOk (growCfg (H := H)) [.num (.int .i32)] := by
  obtain ⟨C, hC, hm⟩ := moduleInstOk_growModule (H := H)
  refine ⟨{ C with locals := C.locals ++ [] }, ⟨storeOk_growStore, C, [], hC, .nil, rfl⟩, ?_⟩
  have hx : ({ C with locals := C.locals ++ [] } : Context).mems[memIdx0.toNat]? =
      some ⟨.i32, ⟨0, none⟩⟩ := by
    simp [hm, memIdx0, Idx.toNat, Memory.emptyMem32]
  exact .cons (.plain (.numeric (.intConst .i32 65536))) (by simp)
    (.single (.plain (.memory (.memoryGrow hx))))

/-- **The configuration is bounded.** -/
theorem bounded_growCfg : Bounded (growCfg (H := H)) where
  store := ⟨⟨by simp [growCfg, growStore], by simp [growCfg, growStore]⟩,
    ⟨by simp [growCfg, growStore], by simp [growCfg, growStore], by simp [growCfg, growStore]⟩,
    by
      simp only [growCfg, growStore, List.mem_singleton]
      rintro _ rfl
      exact ⟨rfl, by decide⟩⟩
  storeBnd := ⟨by simp [growCfg, growStore], by simp [growCfg, growStore],
    by simp [growCfg, growStore], by simp [growCfg, growStore], by simp [growCfg, growStore],
    by simp [growCfg, growStore], by simp [growCfg, growStore]⟩
  frame := ⟨by simp [growCfg, growModule], by simp [growCfg, growModule]⟩
  code := by simp [growCfg, AdminsBnd, AdminBnd, instrBnd]

/-- **Core steps from it** (`memory.grow-succeed`) to a memory of `2 ^ 32` bytes. -/
theorem step_growCfg (nd : Bool) (r : RelaxedChoice) {host : HostSemantics H} :
    ∃ c', Step (Profile.spec nd r) host (growCfg (H := H)) c' ∧
      ∃ mi ∈ c'.store.mems, mi.bytes.size = 2 ^ 32 := by
  obtain ⟨mi', hg, hsz⟩ := Memory.grow_full
  have hm : (growStore (H := H)).mem? ⟨[], growModule⟩ memIdx0 = some (0, Memory.emptyMem32) := by
    simp [Store.mem?, growStore, growModule, memIdx0, Idx.toNat]
  refine ⟨_, .memory (.growSucceed (n := 65536) hm (by rw [show (65536 : BitVec AddrType.i32.intType.width).toNat = 2 ^ 16 from rfl]; exact hg) trivial), mi', ?_, hsz⟩
  simp [Store.setMem, growStore]

/-- **`Bounded` is not preserved by Core's step, even from valid configurations.** -/
theorem not_bounded_preserved (nd : Bool) (r : RelaxedChoice) {host : HostSemantics H} :
    ¬ ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Bounded c →
      Step (Profile.spec nd r) host c c' → Bounded c' := by
  intro h
  obtain ⟨c', hs, mi, hmi, hsz⟩ := step_growCfg (H := H) nd r (host := host)
  have hb := h _ c' _ configOk_growCfg bounded_growCfg hs
  have := (hb.store.mems mi hmi).2
  omega

end Silmaril.Wasm.SpecTec.Sim.Round4
