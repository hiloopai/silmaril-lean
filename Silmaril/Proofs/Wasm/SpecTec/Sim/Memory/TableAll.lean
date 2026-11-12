module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Grow

/-!
# Track memory: `Forward.table`, all constructors, on bounded stores

`fwd_table_bounded` discharges every constructor of `TableStep` at `simEnv B` for a source store
whose tables and element segments have fewer than `2 ^ 32` entries (`TablesBounded`). That bound
implies every per-rule no-wrap hypothesis (gap G1) for both address types. It holds on every
store Core reaches from an instantiated module whose tables are `i32`-indexed
(`TableInst.grow?` keeps `|refs| ≤ 2 ^ |at| - 1`, and element segments come from a binary of
fewer than `2 ^ 32` entries); it is *not* implied by `Typed`, which does not bound list lengths.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Tables and element segments with fewer than `2 ^ 32` entries. -/
def TablesBounded (s : Store H) : Prop :=
  (∀ ti ∈ s.tables, ti.refs.length < 2 ^ 32) ∧ (∀ ei ∈ s.elems, ei.refs.length < 2 ^ 32)

/-- Both address types are at least 32 bits wide. -/
theorem pow32_le (a : AddrType) : 2 ^ 32 ≤ 2 ^ a.intType.width := by
  cases a <;> decide

/-- The table a lookup finds is shorter than `2 ^ |at|`, for every `at`. -/
theorem table_lt {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (hb : TablesBounded s) (ht : s.table? f x = some (ta, ti)) (a : AddrType) :
    ti.refs.length < 2 ^ a.intType.width :=
  Nat.lt_of_lt_of_le (hb.1 ti (List.mem_of_getElem? (State.Store.table?_eq_some ht).2))
    (pow32_le a)

/-- The element segment a lookup finds is shorter than `2 ^ 32`. -/
theorem elem_lt {s : Store H} {f : Frame} {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (hb : TablesBounded s) (he : s.elem? f y = some (ea, ei)) : ei.refs.length < 2 ^ 32 :=
  hb.2 ei (List.mem_of_getElem? (State.Store.elem?_eq_some he).2)

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (M : MemTyping (simEnv B)) (GF : GrowFuns (simEnv B))
  (IT : InstTyping (simEnv B))
include T St M GF IT

/-- **`Forward.table` on bounded stores**: every `TableStep`, in any profile, from a store whose
tables and element segments have fewer than `2 ^ 32` entries, is a SpecTec step of the images. -/
theorem fwd_table_bounded {P : Numerics.Profile} {c c' : Config H} (h : TableStep P c c')
    (hb : TablesBounded c.store) : FwdP (simEnv B) hn c c' := by
  cases h with
  | getOob h₁ h₂ => exact State.fwd_tableGetOob B T St h₁ h₂
  | getVal h₁ h₂ => exact State.fwd_tableGetVal B T St h₁ h₂
  | setOob h₁ h₂ => exact State.fwd_tableSetOob B T St h₁ h₂
  | setVal h₁ h₂ => exact State.fwd_tableSetVal B T St h₁ h₂
  | size h₁ => exact fwd_tableSize B T St M h₁ (table_lt hb h₁ _)
  | growSucceed h₁ h₂ _ => exact fwd_tableGrowSucceed B T St GF IT h₁ h₂ (table_lt hb h₁ _)
  | growFail h₁ h₂ => exact State.fwd_tableGrowFail B T St h₁ h₂
  | fillOob h₁ h₂ => exact State.fwd_tableFillOob B T St h₁ h₂
  | fillZero h₁ h₂ => exact fwd_tableFillZero B T St h₁ h₂
  | @fillSucc s f x a i n v ta ti h₁ h₂ h₃ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₃ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact fwd_tableFillSucc B T St h₁ h₂ h₃ (by have := table_lt hb h₁ a; omega)
  | copyOob h₁ h₂ h₃ => exact fwd_tableCopyOob B T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact fwd_tableCopyZero B T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ h₃ h₄ h₅ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₄ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact fwd_tableCopyLe B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a₁; omega, by have := table_lt hb h₂ a₂; omega⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ h₃ h₄ h₅ =>
    exact fwd_tableCopyGt B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a₁; omega, by have := table_lt hb h₂ a₂; omega⟩
  | initOob h₁ h₂ h₃ => exact fwd_tableInitOob B T St h₁ h₂ h₃
  | initZero h₁ h₂ h₃ => exact fwd_tableInitZero B T St h₁ h₂ h₃
  | @initSucc s f x y a i j n ta ea ti ei r h₁ h₂ h₃ h₄ h₅ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₄ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact fwd_tableInitSucc B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a; omega, by have := elem_lt hb h₂; omega⟩
  | elemDrop h₁ => exact State.fwd_elemDrop B T St h₁

end Silmaril.Wasm.SpecTec.Sim.Memory
