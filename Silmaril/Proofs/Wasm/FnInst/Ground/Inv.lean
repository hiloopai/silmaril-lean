module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Steps

@[expose] public section

/-! # Inverting the machine's steps at a grounded instruction

`step_inv`: under the closed host, a step of `vals W ++ i :: rest` at a stack-only
non-constant instruction or at `local.get` is the step `step1` computes, and it keeps the
store and the frame. The per-instruction head inversions are silmaril-lean's
(`GuardSim.head_localGet`, `GuardSim.head_eqz`, `RedundantSetLine.head_drop`,
`ConstBranch.head_nop`) plus `head_bin` for the binary operators.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- The operator of a binary-operator step at type `i32` is never a trap. -/
theorem bin_ok_of {b : Bin} {x y z : BitVec 32}
    (hz : Numerics.intBinOp .i32 b.op x y = .ok z) : z = b.eval x y := by
  have h₂ : (Except.ok (b.eval x y) : Except IntTrap (BitVec 32)) = Except.ok z :=
    (Bin.intBinOp_eq b x y).symm.trans hz
  exact (Except.ok.inj h₂).symm

theorem bin_not_trap {b : Bin} {x y : BitVec 32} {e : IntTrap}
    (hz : Numerics.intBinOp .i32 b.op x y = .error e) : False := by
  have h₂ : (Except.ok (b.eval x y) : Except IntTrap (BitVec 32)) = Except.error e :=
    (Bin.intBinOp_eq b x y).symm.trans hz
  cases h₂

/-- The shape of a binary-operator step of the fragment. -/
theorem bin_shape {args : List Val} {b : Bin} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width}
    (hc : vals args ++ [Admin.plain (.intBinOp .i32 b.op)] =
      [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]) :
    vals args = [.plain (.intConst t x), .plain (.intConst t y)] ∧ IntType.i32 = t ∧
      b.op = op := by
  obtain ⟨h1, h2⟩ := (SingleThreaded.Det.append_singleton_inj
    (l₂ := [Admin.plain (.intConst t x), .plain (.intConst t y)])).mp hc
  have h3 : IntType.i32 = t ∧ b.op = op := by simpa using h2
  exact ⟨h1, h3⟩

/-- A binary operator of the fragment pops two `i32` operands and pushes the result. -/
theorem head_bin {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H} (b : Bin)
    (h : SingleThreaded.Det.Head P s f args (.plain (.intBinOp .i32 b.op)) c₀) :
    ∃ x y : BitVec 32, args = [Val.i32 x, Val.i32 y] ∧
      c₀ = ⟨s, f, vals [Val.i32 (b.eval x y)]⟩ := by
  have hv := h.fam_inv (by simp [SingleThreaded.Det.famOf])
  simp only [SingleThreaded.Det.famOf, SingleThreaded.Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize hc : vals args ++ [Admin.plain (.intBinOp .i32 b.op)] = l at hv
  cases hv with
  | @intBinOp t op x y z hz =>
    obtain ⟨h1, rfl, rfl⟩ := bin_shape hc
    obtain rfl := bin_ok_of hz
    exact ⟨x, y, SingleThreaded.vals_injective h1, rfl⟩
  | @intBinOpTrap t op x y e hz =>
    obtain ⟨-, rfl, rfl⟩ := bin_shape hc
    exact (bin_not_trap hz).elim
  | _ =>
    have := congrArg List.getLast? hc
    simp at this

/-- The instructions whose steps the bridge inverts. -/
def Inv (i : GInstr) : Prop := (i.stk = true ∨ ∃ x, i = .localGet x) ∧ i.isConst = false

/-- `local.get` reads its local. -/
theorem head_get {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain (GInstr.localGet x).lower) c₀) :
    ∃ out, c₀ = ⟨s, f, vals out⟩ ∧
      ∀ S, step1 (.localGet x) f (args.reverse ++ S) = some (f, out.reverse ++ S) := by
  obtain ⟨rfl, v, hv, rfl⟩ := GuardSim.head_localGet h
  refine ⟨[v], rfl, fun S => ?_⟩
  show (f.local? x).bind (fun o => o.map fun v => (f, v :: S)) = some (f, [v] ++ S)
  rw [hv]
  rfl

/-- **Head inversion**: the head step of an inverted instruction is `step1`'s. -/
theorem head_g {i : GInstr} (hi : Inv i) {s : Store H} {f : Frame} {args : List Val}
    {c₀ : Config H} (h : SingleThreaded.Det.Head P s f args (.plain i.lower) c₀) :
    ∃ out, c₀ = ⟨s, f, vals out⟩ ∧ ∀ S, step1 i f (args.reverse ++ S) = some (f, out.reverse ++ S) := by
  cases i with
  | const _ => exact absurd hi.2 (by simp [GInstr.isConst])
  | localSet _ | localTee _ => exact absurd hi.1 (by simp [GInstr.stk])
  | bin b =>
    obtain ⟨x, y, rfl, rfl⟩ := head_bin b h
    exact ⟨_, rfl, fun S => rfl⟩
  | eqz =>
    obtain ⟨x, rfl, rfl⟩ := GuardSim.head_eqz h
    exact ⟨[Val.i32 (intTestOp .i32 .eqz x)], rfl, fun S => rfl⟩
  | drop =>
    obtain ⟨v, rfl, rfl⟩ := RedundantSetLine.head_drop h
    exact ⟨[], rfl, fun S => rfl⟩
  | nop =>
    obtain ⟨rfl, rfl⟩ := ConstBranch.head_nop h
    exact ⟨[], rfl, fun S => rfl⟩
  | localGet x => exact head_get h

theorem lower_val {i : GInstr} (hc : i.isConst = false) : (Admin.plain i.lower).val? = none := by
  cases i <;> first | rfl | exact absurd hc (by simp [GInstr.isConst])

/-- **Step inversion** at a grounded instruction. -/
theorem step_inv {i : GInstr} (hi : Inv i) {s : Store H} {f : Frame} {W : List Val}
    {rest : List Admin} {c' : Config H}
    (h : Step P closedHost ⟨s, f, vals W ++ .plain i.lower :: rest⟩ c') :
    ∃ Y, step1 i f W.reverse = some (f, Y) ∧ c' = ⟨s, f, vals Y.reverse ++ rest⟩ := by
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := GuardSim.head_inv (lower_val hi.2) (by simp)
    (by cases i <;> simp [GInstr.lower]) h
  obtain ⟨out, rfl, hs⟩ := head_g hi hh
  refine ⟨out.reverse ++ vs.reverse, by simpa using hs vs.reverse, by simp⟩

end Silmaril.Wasm.FnInst.Ground
