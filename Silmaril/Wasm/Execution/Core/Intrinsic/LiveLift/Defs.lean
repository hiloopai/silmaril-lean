module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs

@[expose] public section

/-! # Exact lifting of live integer sequences

No `unreachable` is admitted: its polymorphic output is not inferable from
the instruction alone. Each supported instruction has a principal next stack
at a given input stack and initialized local declaration list.
-/

namespace Silmaril.Wasm.Execution.Core.Intrinsic

def Slot.lookup : (locals : List IntType) → (index : Nat) →
    Option (Σ kind, {ref : Slot locals kind // ref.toNat = index})
  | [], _ => none
  | kind :: _, 0 => some ⟨kind, .here, rfl⟩
  | _ :: tail, index + 1 => (lookup tail index).map fun ⟨kind, ref, h⟩ =>
    ⟨kind, .there ref, congrArg (· + 1) h⟩

abbrev Op.Lifted (locals input : List IntType) (raw : Instr) :=
  Σ output, {op : Op locals input output // op.erase = raw ∧ raw ≠ .unreachable}

def Op.reify? (locals : List IntType) : (input : List IntType) → (raw : Instr) →
    Option (Op.Lifted locals input raw)
  | stack, .nop => some ⟨stack, .nop, rfl, fun h => Instr.noConfusion h⟩
  | _ :: rest, .drop => some ⟨rest, .drop, rfl, fun h => Instr.noConfusion h⟩
  | stack, .localGet index => do
    let ⟨kind, ref, h⟩ ← Slot.lookup locals index.toNat
    have bound : ref.toNat < 2 ^ 32 := h ▸ index.value.isLt
    have same : ref.index bound = index := Idx.toNat_injective h
    some ⟨kind :: stack, .localGet ref bound, congrArg Instr.localGet same, fun h => Instr.noConfusion h⟩
  | .i32 :: .i32 :: rest, .intBinOp .i32 op =>
    some ⟨.i32 :: rest, .intBin op, rfl, fun h => Instr.noConfusion h⟩
  | .i64 :: .i64 :: rest, .intBinOp .i64 op =>
    some ⟨.i64 :: rest, .intBin op, rfl, fun h => Instr.noConfusion h⟩
  | _, _ => none

abbrev Code.Lifted (locals input : List IntType) (raw : List Instr) :=
  Σ output, {code : Code locals input output // code.erase = raw ∧ .unreachable ∉ raw}

def Code.reify? (locals : List IntType) : (input : List IntType) → (raw : List Instr) →
    Option (Code.Lifted locals input raw)
  | stack, [] => some ⟨stack, .done, rfl, by simp⟩
  | stack, rawOp :: rawTail => do
    let ⟨middle, op, hOp, hSafe⟩ ← Op.reify? locals stack rawOp
    let ⟨output, tail, hTail, hLive⟩ ← Code.reify? locals middle rawTail
    some ⟨output, .seq op tail, congrArg₂ List.cons hOp hTail, by
      intro member
      exact (List.mem_cons.mp member).elim (fun eq => hSafe eq.symm) hLive⟩

abbrev Code.Live (locals input : List IntType) :=
  Σ output, {code : Code locals input output // .unreachable ∉ code.erase}

/-- A computable exact-stack profile, not another definition of `InstrsOk`. -/
abbrev Code.CheckedRaw (locals input : List IntType) :=
  {raw : List Instr // (Code.reify? locals input raw).isSome}

end Silmaril.Wasm.Execution.Core.Intrinsic
