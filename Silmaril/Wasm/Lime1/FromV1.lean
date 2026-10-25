module

public import Silmaril.Wasm.Lime1.ToCore
public import Silmaril.Wasm.V1.ToCore

/-! # The WebAssembly 1.0 injection into Lime1

All instruction, expression and module payloads are preserved. Commuting with
the direct Core 3 injection proves these maps injective without identifying any
source terms. These are syntax statements, separate from validation/execution.
-/

@[expose] public section
namespace Silmaril.Wasm.V1

def IntUnOp.toLime : IntUnOp → Lime1.IntUnOp
  | .clz => .clz
  | .ctz => .ctz
  | .popcnt => .popcnt

@[simp] theorem IntUnOp.toLime_toCore (op : IntUnOp) : op.toLime.toCore = op.toCore := by
  cases op <;> rfl

@[simp] theorem BlockType.toLime_toCore (t : BlockType) :
    (BlockType.toLime t).toCore = BlockType.toCore t := by cases t <;> rfl

mutual
def Instr.toLime : Instr → Lime1.Instr
  | .nop => .nop
  | .unreachable => .unreachable
  | .drop => .drop
  | .select => .select
  | .block t body => .block (BlockType.toLime t) (Expr.toLime body)
  | .loop t body => .loop (BlockType.toLime t) (Expr.toLime body)
  | .if_ t left right => .if_ (BlockType.toLime t) (Expr.toLime left) (Expr.toLime right)
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls l => .brTable ls l
  | .call f => .call f
  | .callIndirect t => .callIndirect t
  | .return_ => .return_
  | .localGet x => .localGet x
  | .localSet x => .localSet x
  | .localTee x => .localTee x
  | .globalGet x => .globalGet x
  | .globalSet x => .globalSet x
  | .intLoad t p a => .intLoad t p a
  | .floatLoad t a => .floatLoad t a
  | .intStore t p a => .intStore t p a
  | .floatStore t a => .floatStore t a
  | .memorySize => .memorySize
  | .memoryGrow => .memoryGrow
  | .intConst t x => .intConst t x
  | .floatConst t x => .floatConst t x
  | .intUnOp t op => .intUnOp t op.toLime
  | .intBinOp t op => .intBinOp t op
  | .intTestOp t op => .intTestOp t op
  | .intRelOp t op => .intRelOp t op
  | .floatUnOp t op => .floatUnOp t op
  | .floatBinOp t op => .floatBinOp t op
  | .floatRelOp t op => .floatRelOp t op
  | .convert op => .convert op.toCore

def Expr.toLime : Expr → Lime1.Expr
  | [] => []
  | i :: is => Instr.toLime i :: Expr.toLime is
end

mutual
@[simp] theorem Instr.toLime_toCore (i : Instr) :
    (Instr.toLime i).toCore = Instr.toCore i := by
  cases i with
  | block t body =>
    simp [Instr.toLime, Lime1.Instr.toCore, Instr.toCore, Expr.toLime_toCore body]
  | loop t body =>
    simp [Instr.toLime, Lime1.Instr.toCore, Instr.toCore, Expr.toLime_toCore body]
  | if_ t left right =>
    simp [Instr.toLime, Lime1.Instr.toCore, Instr.toCore,
      Expr.toLime_toCore left, Expr.toLime_toCore right]
  | intLoad _ _ _ => rfl
  | _ => simp [Instr.toLime, Lime1.Instr.toCore, Instr.toCore]
termination_by sizeOf i

@[simp] theorem Expr.toLime_toCore (es : Expr) :
    Lime1.Expr.toCore (Expr.toLime es) = Expr.toCore es := by
  cases es with
  | nil => rfl
  | cons i es =>
    simp only [Expr.toLime, Lime1.Expr.toCore, Expr.toCore,
      Instr.toLime_toCore i, Expr.toLime_toCore es]
termination_by sizeOf es
end

theorem Expr.toLime_eq_map (es : Expr) : toLime es = es.map Instr.toLime := by
  induction es with
  | nil => rfl
  | cons i es ih => simp only [toLime, ih, List.map_cons]

theorem Instr.toLime_injective : Function.Injective toLime := by
  intro a b h
  apply Instr.toCore_injective
  simpa using congrArg Lime1.Instr.toCore h

theorem Expr.toLime_injective : Function.Injective toLime := by
  intro a b h
  apply Expr.toCore_injective
  simpa using congrArg Lime1.Expr.toCore h

def Func.toLime (f : Func) : Lime1.Func := ⟨f.type, f.locals, Expr.toLime f.body⟩

def Global.toLime (g : Global) : Lime1.Global := ⟨g.type, Expr.toLime g.init⟩

def Elem.toLime (e : Elem) : Lime1.Elem := ⟨e.table, Expr.toLime e.offset, e.init⟩

def Data.toLime (d : Data) : Lime1.Data := ⟨d.memory, Expr.toLime d.offset, d.bytes⟩

def Module.toLime (m : Module) : Lime1.Module where
  types := m.types
  imports := m.imports
  funcs := m.funcs.map Func.toLime
  globals := m.globals.map Global.toLime
  tables := m.tables
  memories := m.memories
  elems := m.elems.map Elem.toLime
  data := m.data.map Data.toLime
  start := m.start
  exports := m.exports

@[simp] theorem Func.toLime_toCore (f : Func) : f.toLime.toCore = f.toCore := by
  simp [toLime, Lime1.Func.toCore, toCore]

@[simp] theorem Global.toLime_toCore (g : Global) : g.toLime.toCore = g.toCore := by
  simp [toLime, Lime1.Global.toCore, toCore]

@[simp] theorem Elem.toLime_toCore (e : Elem) : e.toLime.toCore = e.toCore := by
  simp [toLime, Lime1.Elem.toCore, toCore, Lime1.funcRef]

@[simp] theorem Data.toLime_toCore (d : Data) : d.toLime.toCore = d.toCore := by
  simp [toLime, Lime1.Data.toCore, toCore]

@[simp] theorem Module.toLime_toCore (m : Module) : m.toLime.toCore = m.toCore := by
  simp [toLime, Lime1.Module.toCore, toCore, List.map_map, Function.comp_def,
    Lime1.tableToCore, TableType.toCoreTable]

theorem Module.toLime_injective : Function.Injective toLime := by
  intro a b h
  apply Module.toCore_injective
  simpa using congrArg Lime1.Module.toCore h

theorem Func.toLime_injective : Function.Injective toLime := by
  rintro ⟨t, ls, body⟩ ⟨t', ls', body'⟩ h
  simp only [toLime, Declaration.Func.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  exact congrArg (Func.mk t ls) (Expr.toLime_injective h)

theorem Global.toLime_injective : Function.Injective toLime := by
  rintro ⟨t, body⟩ ⟨t', body'⟩ h
  simp only [toLime, Declaration.Global.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact congrArg (Global.mk t) (Expr.toLime_injective h)

theorem Elem.toLime_injective : Function.Injective toLime := by
  rintro ⟨t, body, init⟩ ⟨t', body', init'⟩ h
  simp only [toLime, Declaration.ActiveElem.mk.injEq] at h
  obtain ⟨rfl, h, rfl⟩ := h
  exact congrArg (fun es => Elem.mk t es init) (Expr.toLime_injective h)

theorem Data.toLime_injective : Function.Injective toLime := by
  rintro ⟨t, body, bytes⟩ ⟨t', body', bytes'⟩ h
  simp only [toLime, Declaration.ActiveData.mk.injEq] at h
  obtain ⟨rfl, h, rfl⟩ := h
  exact congrArg (fun es => Data.mk t es bytes) (Expr.toLime_injective h)

end Silmaril.Wasm.V1
