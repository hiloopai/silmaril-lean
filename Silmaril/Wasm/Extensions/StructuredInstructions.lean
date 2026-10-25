module

public import Silmaril.Wasm.Extensions.SharedMemory

/-! # Structured instruction syntax with an explicit leaf language

Profiles can add non-structured instructions without changing Core's AST. The
block, loop, conditional and `try_table` structure is shared. A `contextShape`
is only a syntax utility for existing anonymous type/local-context builders;
replacing an extension leaf is not an operational semantics theorem.
-/

@[expose] public section

namespace Silmaril.Wasm.Extensions.Structured

inductive Instr (Leaf : Type) where
  | leaf (i : Leaf)
  | block (type : BlockType) (body : List (Instr Leaf))
  | loop (type : BlockType) (body : List (Instr Leaf))
  | if_ (type : BlockType) (then_ else_ : List (Instr Leaf))
  | tryTable (type : BlockType) (catches : List Catch) (body : List (Instr Leaf))
  deriving Repr

abbrev Expr (Leaf : Type) := List (Instr Leaf)

mutual
  def Instr.contextShape {Leaf : Type} (leaf : Leaf → Wasm.Instr) : Instr Leaf → Wasm.Instr
    | .leaf i => leaf i
    | .block t is => .block t (Expr.contextShape leaf is)
    | .loop t is => .loop t (Expr.contextShape leaf is)
    | .if_ t a b => .if_ t (Expr.contextShape leaf a) (Expr.contextShape leaf b)
    | .tryTable t cs is => .tryTable t cs (Expr.contextShape leaf is)

  def Expr.contextShape {Leaf : Type} (leaf : Leaf → Wasm.Instr) : Expr Leaf → Wasm.Expr
    | [] => []
    | i :: is => i.contextShape leaf :: Expr.contextShape leaf is
end

/-- A module whose function-body language is explicit. Other constant-expression
positions retain Core syntax, which excludes extension operations there. -/
structure FunctionModule (Body : Type) where
  types : List RecType := []
  imports : List SharedMemory.Import := []
  funcs : List (Declaration.Func ValType Body) := []
  tables : List Table := []
  memories : List SharedMemory.MemoryType := []
  globals : List Global := []
  tags : List TagType := []
  elems : List Elem := []
  data : List Data := []
  start : Option FuncIdx := none
  exports : List Export := []
  deriving Repr

def FunctionModule.contextShape {Body : Type} (body : Body → Wasm.Expr)
    (m : FunctionModule Body) : SharedMemory.Module :=
  { types := m.types, imports := m.imports, funcs := m.funcs.map (Declaration.Func.mapBody body),
    tables := m.tables, memories := m.memories, globals := m.globals, tags := m.tags,
    elems := m.elems, data := m.data, start := m.start, exports := m.exports }

end Silmaril.Wasm.Extensions.Structured
