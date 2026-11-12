module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Lime1Core.Tables
-- Silmaril addition for build time (not in the silmaril source): the non-nesting cases of
-- `core_instr_aux` of `Lime1Core.lean`, moved out of its structural recursion unchanged.
-- Hand copy (track ws4-p1-lime-wasmi): source namespaces kept, only import lines rewritten.

/-! # Lime1 and Core 3.0 agree on instruction encodings: Core to Lime1 without nesting

Part of `Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Lime1Core`: the cases of `core_instr_aux` whose
Core instruction has no nested body, proved without recursion. Not in the silmaril source.
-/

@[expose] public section

open Silmaril.Wasm.Binary

namespace Silmaril.Wasm.Binary.Lime1Core

open Lime1.Binary (TableIdxZero TableZero ZeroPayload)

/-! ## Instructions without nested bodies: Core to Lime1 -/

/-- The Core instructions with nested bodies: the recursive cases of `core_instr_aux`. -/
def coreNested : Wasm.Instr → Bool
  | .block _ _ | .loop _ _ | .if_ _ _ _ => true
  | _ => false

/-! The opcode tables of `Core.Instr` produce no instruction with a nested body. -/

theorem plainOp_coreNested {op : UInt8} {i : Wasm.Instr} (h : Core.PlainOp op i) :
    coreNested i = false := by
  cases h <;> rfl

theorem prefixFBOp_coreNested {n : Nat} {i : Wasm.Instr} (h : Core.PrefixFBOp n i) :
    coreNested i = false := by
  cases h <;> rfl

theorem prefixFCOp_coreNested {n : Nat} {i : Wasm.Instr} (h : Core.PrefixFCOp n i) :
    coreNested i = false := by
  cases h <;> rfl

theorem prefixFDOp_coreNested {n : Nat} {i : Wasm.Instr} (h : Core.PrefixFDOp n i) :
    coreNested i = false := by
  cases h <;> rfl

theorem memOp_coreNested {op : UInt8} {mk : MemIdx → Wasm.MemArg → Wasm.Instr}
    (h : Core.MemOp op mk) (x : MemIdx) (a : Wasm.MemArg) : coreNested (mk x a) = false := by
  cases h <;> rfl

theorem vecMemOp_coreNested {n : Nat} {mk : MemIdx → Wasm.MemArg → Wasm.Instr}
    (h : Core.VecMemOp n mk) (x : MemIdx) (a : Wasm.MemArg) : coreNested (mk x a) = false := by
  cases h <;> rfl

theorem vecMemLaneOp_coreNested {n : Nat} {mk : MemIdx → Wasm.MemArg → LaneIdx → Wasm.Instr}
    (h : Core.VecMemLaneOp n mk) (x : MemIdx) (a : Wasm.MemArg) (l : LaneIdx) :
    coreNested (mk x a l) = false := by
  cases h <;> rfl

theorem vecLaneOp_coreNested {n : Nat} {mk : LaneIdx → Wasm.Instr} (h : Core.VecLaneOp n mk)
    (l : LaneIdx) : coreNested (mk l) = false := by
  cases h <;> rfl

theorem core_instr_leaf {ov : Bool} : ∀ {b : Bytes} {ci : Wasm.Instr},
    Core.Instr (Core.Forms.ofOverlong ov) b ci → coreNested ci = false →
    ∀ {i : Lime1.Instr}, ci = i.toCore → Lime1.Binary.Instr ov b i := by
  intro b ci h hnest i hc
  cases h with
  | block | loop | if_ | ifElse => simp [coreNested] at hnest
  | plain h => subst hc; exact .plain (plainOp_lime1 h)
  | prefixFC h hn => subst hc; exact .prefixFC (prefixFCOp_lime1 h) hn
  | callIndirect hy hx =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact .callIndirect hy (tableIdxZero_lime1 hx)
  | mem h hm => exact mem_lime1 h hm hc
  | memorySize h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    obtain ⟨rfl, -⟩ := memIdx_reserved h
    exact .memorySize
  | memoryGrow h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    obtain ⟨rfl, -⟩ := memIdx_reserved h
    exact .memoryGrow
  | memoryCopy hn h₁ h₂ =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := memIdx_reserved h₁
    obtain ⟨rfl, -⟩ := memIdx_reserved h₂
    have := Lime1.Binary.Instr.memoryCopy (overlong := ov) hn
    simpa using this
  | memoryFill hn h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    obtain ⟨rfl, -⟩ := memIdx_reserved h
    exact .memoryFill hn
  | prefixFB h _ => subst hc; cases i <;> cases h
  | prefixFD h _ => subst hc; cases i <;> cases h
  | vecMem h _ _ => cases h <;> cases i <;> simp [Lime1.Instr.toCore] at hc
  | vecMemLane h _ _ => cases h <;> cases i <;> simp [Lime1.Instr.toCore] at hc
  | vecLane h _ => cases h <;> cases i <;> simp [Lime1.Instr.toCore] at hc
  | br h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .br h
  | brIf h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .brIf h
  | call h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .call h
  | localGet h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .localGet h
  | localSet h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .localSet h
  | localTee h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .localTee h
  | globalGet h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .globalGet h
  | globalSet h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    subst hc
    exact .globalSet h
  | brTable h h' =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact .brTable h h'
  | i32Const h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    cases hc
    exact .i32Const h
  | i64Const h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    cases hc
    exact .i64Const h
  | f32Const h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    cases hc
    exact .f32Const h
  | f64Const h =>
    cases i <;> simp [Lime1.Instr.toCore] at hc
    cases hc
    exact .f64Const h
  | _ =>
    have h' := congrArg Lime1.Instr.ofCore? hc
    simp [Lime1.Instr.ofCore?] at h'

end Silmaril.Wasm.Binary.Lime1Core
