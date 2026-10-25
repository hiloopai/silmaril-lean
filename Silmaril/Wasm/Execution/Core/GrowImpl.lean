module

public import Silmaril.Wasm.Execution.Core.Store

@[expose] public section

/-! # Executable growth

`TableInst.grow?` and `MemInst.grow?` state the maximum check as
`∀ j, max = some j → i' ≤ j.val`, whose `Decidable` instance enumerates
`Fin (2 ^ 64)`: the compiled code never finishes. The `@[csimp]` lemmas below
replace them, in compiled code only, by equal functions that inspect the
optional maximum directly. Modules that run `grow?` (the interpreter families
in `SingleThreaded/Exec`) import this file so that their code is compiled
against the fast versions; the definitions used in proofs are unchanged.
-/

namespace Silmaril.Wasm.Execution.Core

/-- `TableInst.grow?` with a direct check of the optional maximum. -/
def TableInst.growImpl? (ti : TableInst) (n : Nat) (r : Ref) : Option TableInst :=
  let i' := ti.refs.length + n
  if i' ≤ 2 ^ ti.type.address.width - 1 ∧ ti.type.limits.max.all (fun j => i' ≤ j.val) then
    some ⟨{ ti.type with limits := { ti.type.limits with min := Fin.ofNat _ i' } },
      ti.refs ++ List.replicate n r⟩
  else none

/-- `MemInst.grow?` with a direct check of the optional maximum. -/
def MemInst.growImpl? (mi : MemInst) (n : Nat) : Option MemInst :=
  let i' := mi.bytes.size / Memory.pageSize + n
  if i' ≤ 2 ^ (mi.type.address.width - 16) ∧ mi.type.limits.max.all (fun j => i' ≤ j.val) then
    some ⟨{ mi.type with limits := { mi.type.limits with min := Fin.ofNat _ i' } },
      mi.bytes ++ ByteArray.mk (Array.replicate (n * Memory.pageSize) 0)⟩
  else none

theorem forall_max_iff_all (m : Option (Fin (2 ^ 64))) (i : Nat) :
    (∀ j, m = some j → i ≤ j.val) ↔ m.all (fun j => i ≤ j.val) = true := by
  cases m <;> simp

@[csimp] theorem TableInst.grow?_eq_growImpl? : @TableInst.grow? = @TableInst.growImpl? := by
  funext ti n r
  simp only [TableInst.grow?, TableInst.growImpl?, forall_max_iff_all]

@[csimp] theorem MemInst.grow?_eq_growImpl? : @MemInst.grow? = @MemInst.growImpl? := by
  funext mi n
  simp only [MemInst.grow?, MemInst.growImpl?, forall_max_iff_all]

end Silmaril.Wasm.Execution.Core
