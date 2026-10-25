module

public import Silmaril.Wasm.V1.ToCore.Types

/-! # Instruction injection and canonical-image retraction -/

@[expose] public section

namespace Silmaril.Wasm.V1

def loadPackToCore (p : Option (PackSize × Signedness)) :
    Option (Wasm.PackSize × Signedness) := p.map fun (n, s) => (n.toCore, s)

def loadPackOfCore? : Option (Wasm.PackSize × Signedness) →
    Option (Option (PackSize × Signedness))
  | none => some none
  | some (n, s) => (PackSize.ofCore? n).map fun n => some (n, s)

@[simp] theorem loadPackOfCore?_toCore (p : Option (PackSize × Signedness)) :
    loadPackOfCore? (loadPackToCore p) = some p := by
  rcases p with _ | ⟨n, s⟩ <;> simp [loadPackToCore, loadPackOfCore?]

def storePackOfCore? : Option Wasm.PackSize → Option (Option PackSize)
  | none => some none
  | some n => (PackSize.ofCore? n).map some

@[simp] theorem storePackOfCore?_toCore (p : Option PackSize) :
    storePackOfCore? (p.map PackSize.toCore) = some p := by
  cases p <;> simp [storePackOfCore?]

mutual
def Instr.toCore : Instr → Wasm.Instr
  | .nop => .nop
  | .unreachable => .unreachable
  | .drop => .drop
  | .select => .select none
  | .block t body => .block (BlockType.toCore t) (Expr.toCore body)
  | .loop t body => .loop (BlockType.toCore t) (Expr.toCore body)
  | .if_ t left right => .if_ (BlockType.toCore t) (Expr.toCore left) (Expr.toCore right)
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls l => .brTable ls l
  | .call f => .call f
  | .callIndirect t => .callIndirect ⟨0⟩ t
  | .return_ => .return_
  | .localGet x => .localGet x
  | .localSet x => .localSet x
  | .localTee x => .localTee x
  | .globalGet x => .globalGet x
  | .globalSet x => .globalSet x
  | .intLoad t p a => .intLoad t (loadPackToCore p) ⟨0⟩ a.toCore
  | .floatLoad t a => .floatLoad t ⟨0⟩ a.toCore
  | .intStore t p a => .intStore t (p.map PackSize.toCore) ⟨0⟩ a.toCore
  | .floatStore t a => .floatStore t ⟨0⟩ a.toCore
  | .memorySize => .memorySize ⟨0⟩
  | .memoryGrow => .memoryGrow ⟨0⟩
  | .intConst t x => .intConst t x
  | .floatConst t x => .floatConst t x
  | .intUnOp t op => .intUnOp t op.toCore
  | .intBinOp t op => .intBinOp t op
  | .intTestOp t op => .intTestOp t op
  | .intRelOp t op => .intRelOp t op
  | .floatUnOp t op => .floatUnOp t op
  | .floatBinOp t op => .floatBinOp t op
  | .floatRelOp t op => .floatRelOp t op
  | .convert op => .convert op.toCore

def Expr.toCore : Expr → Wasm.Expr
  | [] => []
  | i :: is => i.toCore :: Expr.toCore is
end

theorem Expr.toCore_eq_map (es : Expr) : toCore es = es.map Instr.toCore := by
  induction es with
  | nil => rfl
  | cons i es ih => simp only [toCore, ih, List.map_cons]

mutual
/-- Decode exactly the canonical original instruction image, rejecting newer syntax. -/
def Instr.ofCore? : Wasm.Instr → Option Instr
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select none => some .select
  | .block t body => do return .block (← BlockType.ofCore? t) (← Expr.ofCore? body)
  | .loop t body => do return .loop (← BlockType.ofCore? t) (← Expr.ofCore? body)
  | .if_ t left right => do
      return .if_ (← BlockType.ofCore? t) (← Expr.ofCore? left) (← Expr.ofCore? right)
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  | .call f => some (.call f)
  | .callIndirect table t => if table = ⟨0⟩ then some (.callIndirect t) else none
  | .return_ => some .return_
  | .localGet x => some (.localGet x)
  | .localSet x => some (.localSet x)
  | .localTee x => some (.localTee x)
  | .globalGet x => some (.globalGet x)
  | .globalSet x => some (.globalSet x)
  | .intLoad t p memory a => if memory = ⟨0⟩ then do
      return .intLoad t (← loadPackOfCore? p) (← MemArg.ofCore? a)
    else none
  | .floatLoad t memory a => if memory = ⟨0⟩ then do
      return .floatLoad t (← MemArg.ofCore? a)
    else none
  | .intStore t p memory a => if memory = ⟨0⟩ then do
      return .intStore t (← storePackOfCore? p) (← MemArg.ofCore? a)
    else none
  | .floatStore t memory a => if memory = ⟨0⟩ then do
      return .floatStore t (← MemArg.ofCore? a)
    else none
  | .memorySize memory => if memory = ⟨0⟩ then some .memorySize else none
  | .memoryGrow memory => if memory = ⟨0⟩ then some .memoryGrow else none
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => (IntUnOp.ofCore? op).map (.intUnOp t)
  | .intBinOp t op => some (.intBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .convert op => (ConvertOp.ofCore? op).map .convert
  | _ => none

def Expr.ofCore? : Wasm.Expr → Option Expr
  | [] => some []
  | i :: is => do return (← Instr.ofCore? i) :: (← Expr.ofCore? is)
end

mutual
@[simp] theorem Instr.ofCore?_toCore (i : Instr) : Instr.ofCore? i.toCore = some i := by
  cases i with
  | block t body => simp [Instr.toCore, Instr.ofCore?, Expr.ofCore?_toCore body]
  | loop t body => simp [Instr.toCore, Instr.ofCore?, Expr.ofCore?_toCore body]
  | if_ t left right =>
      simp [Instr.toCore, Instr.ofCore?, Expr.ofCore?_toCore left, Expr.ofCore?_toCore right]
  | _ => simp [Instr.toCore, Instr.ofCore?]
termination_by sizeOf i

@[simp] theorem Expr.ofCore?_toCore (es : Expr) : Expr.ofCore? (Expr.toCore es) = some es := by
  cases es with
  | nil => rfl
  | cons i es =>
      simp only [Expr.toCore, Expr.ofCore?, Instr.ofCore?_toCore i, Expr.ofCore?_toCore es]
      rfl
termination_by sizeOf es
end

theorem Instr.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

theorem Expr.toCore_injective : Function.Injective toCore := by
  intro a b h
  simpa using congrArg ofCore? h

end Silmaril.Wasm.V1
