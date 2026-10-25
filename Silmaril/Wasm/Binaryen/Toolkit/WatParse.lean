module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

@[expose] public section

/-! # Parsing the canonical numeric and structured WAT fragment

Candidate parsing is untrusted computation. Acceptance reifies the candidate
with `moduleSyntax?` and requires exact equality with the original syntax
tree. Thus numeric spellings, field order and all omitted/extra clauses are
checked by the same canonical builder used by the disassembler.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (toList?)

def parseNat? : SExp → Option Nat
  | .atom (.sym text) => text.toNat?
  | _ => none

def parseIndex? {k : IndexKind} (x : SExp) : Option (Wasm.Idx k) := do
  Wasm.Idx.ofNat? (← parseNat? x)

def parseValue? : SExp → Option ValType
  | .atom (.sym "i32") => some (.num (.int .i32))
  | .atom (.sym "i64") => some (.num (.int .i64))
  | .atom (.sym "f32") => some (.num (.float .f32))
  | .atom (.sym "f64") => some (.num (.float .f64))
  | _ => none

def parseFloat? (t : FloatType) : SExp → Option (BitVec t.width)
  | .atom (.sym text) => (ValuesExamples.fnCands t text.toList).head?
  | _ => none

def parseParameters? (x : SExp) : Option (List ValType) := do
  let .atom (.sym "param") :: xs ← toList? x | none
  xs.mapM parseValue?

def parseResults? (x : SExp) : Option (List ValType) := do
  let .atom (.sym "result") :: xs ← toList? x | none
  xs.mapM parseValue?

def parseLocals? (x : SExp) : Option (List ValType) := do
  let .atom (.sym "local") :: xs ← toList? x | none
  xs.mapM parseValue?

def parseType? (x : SExp) : Option RecType := do
  let [.atom (.sym "type"), ft] ← toList? x | none
  let [.atom (.sym "func"), ps, rs] ← toList? ft | none
  let params ← parseParameters? ps
  let results ← parseResults? rs
  pure ⟨[⟨true, [], .func ⟨params, results⟩⟩]⟩

def parseTypeUse? (x : SExp) : Option TypeIdx := do
  let [.atom (.sym "type"), i] ← toList? x | none
  parseIndex? i

/-- Reuse the existing keyword decoder, retaining exactly the nullary
families emitted by `instructionSyntax?`. -/
def parseNullary? (name : String) : Option Instr := do
  let i ← Text.Core.NullaryDecode.decode name
  match i with
  | .nop | .unreachable | .drop | .return_ | .intUnOp .. | .intBinOp .. |
      .intTestOp .. | .intRelOp .. | .floatUnOp .. | .floatBinOp .. |
      .floatRelOp .. | .convert .. => some i
  | _ => none

/-- Canonical structured signatures: one explicit result clause, with zero
or one scalar result. Type-index signatures are outside this fragment. -/
def parseBlockHeader? (x : SExp) : Option BlockType := do
  match ← toList? x with
  | [.atom (.sym "result")] => some .empty
  | [.atom (.sym "result"), value] => some (.value (← parseValue? value))
  | _ => none

def parseAttribute? (stem : String) : SExp → Option Nat
  | .atom (.sym text) =>
      if stem.toList.isPrefixOf text.toList then
        (String.ofList (text.toList.drop stem.toList.length)).toNat?
      else none
  | _ => none

/-- The canonical serializer always supplies index, offset and byte alignment.
Reification subsequently checks their exact original spellings. -/
def parseMemoryOp? (name : String) (memory offset alignment : SExp) : Option Instr := do
  let entry ← Text.Core.memOps.find? (fun entry => entry.1 == name)
  let memory ← parseIndex? memory
  let offset ← parseAttribute? "offset=" offset
  let alignment ← parseAttribute? "align=" alignment
  if h : offset < 2 ^ 32 ∧ alignment ∈ [1, 2, 4, 8] then
    let i := entry.2.2 memory ⟨⟨Nat.log2 alignment, by
      have := Nat.log2_le_self alignment
      have : alignment = 1 ∨ alignment = 2 ∨ alignment = 4 ∨ alignment = 8 := by
        simpa using h.2
      omega⟩, ⟨offset, by omega⟩⟩
    match i with
    | .intLoad .. | .intStore .. => some i
    | _ => none
  else none

mutual
/-- The fuel is derived from the complete finite input tree. It bounds both
sequence traversal and descent into folded structured instructions. -/
def parseInstructionsFuel? : Nat → List SExp → Option (List Instr)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, .atom (.sym "i32.const") :: arg :: rest => do
      let n ← parseNat? arg
      if n < 2 ^ 32 then
        pure (.intConst .i32 (BitVec.ofNat 32 n) :: (← parseInstructionsFuel? fuel rest))
      else none
  | fuel + 1, .atom (.sym "i64.const") :: arg :: rest => do
      let n ← parseNat? arg
      if n < 2 ^ 64 then
        pure (.intConst .i64 (BitVec.ofNat 64 n) :: (← parseInstructionsFuel? fuel rest))
      else none
  | fuel + 1, .atom (.sym "f32.const") :: arg :: rest => do
      pure (.floatConst .f32 (← parseFloat? .f32 arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "f64.const") :: arg :: rest => do
      pure (.floatConst .f64 (← parseFloat? .f64 arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "local.get") :: arg :: rest => do
      pure (.localGet (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "local.set") :: arg :: rest => do
      pure (.localSet (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "local.tee") :: arg :: rest => do
      pure (.localTee (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "global.get") :: arg :: rest => do
      pure (.globalGet (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "global.set") :: arg :: rest => do
      pure (.globalSet (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "call") :: arg :: rest => do
      pure (.call (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "br") :: arg :: rest => do
      pure (.br (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "br_if") :: arg :: rest => do
      pure (.brIf (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "memory.init") :: memory :: data :: rest => do
      pure (.memoryInit (← parseIndex? memory) (← parseIndex? data) ::
        (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "data.drop") :: arg :: rest => do
      pure (.dataDrop (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "memory.size") :: arg :: rest => do
      pure (.memorySize (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym "memory.grow") :: arg :: rest => do
      pure (.memoryGrow (← parseIndex? arg) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, .atom (.sym name) :: memory :: offset :: alignment :: rest =>
      match parseMemoryOp? name memory offset alignment with
      | some i => do pure (i :: (← parseInstructionsFuel? fuel rest))
      | none => do pure ((← parseNullary? name) ::
          (← parseInstructionsFuel? fuel (memory :: offset :: alignment :: rest)))
  | fuel + 1, .atom (.sym name) :: rest => do
      pure ((← parseNullary? name) :: (← parseInstructionsFuel? fuel rest))
  | fuel + 1, x :: rest => do
      pure ((← parseStructuredFuel? fuel x) :: (← parseInstructionsFuel? fuel rest))

def parseStructuredFuel? : Nat → SExp → Option Instr
  | 0, _ => none
  | fuel + 1, x => do
      match ← toList? x with
      | .atom (.sym "block") :: header :: body =>
          pure (.block (← parseBlockHeader? header) (← parseInstructionsFuel? fuel body))
      | .atom (.sym "loop") :: header :: body =>
          pure (.loop (← parseBlockHeader? header) (← parseInstructionsFuel? fuel body))
      | [.atom (.sym "if"), header, yes, no] =>
          let .atom (.sym "then") :: left ← toList? yes | none
          let .atom (.sym "else") :: right ← toList? no | none
          pure (.if_ (← parseBlockHeader? header)
            (← parseInstructionsFuel? fuel left) (← parseInstructionsFuel? fuel right))
      | _ => none
end

def syntaxNodes : SExp → Nat
  | .nil | .atom _ => 1
  | .cons head tail => 1 + syntaxNodes head + syntaxNodes tail

/-- Scalar instructions and folded block/loop/if trees, including numeric
branches. The entire input determines the traversal bound; there is no
caller-supplied parsing fuel. Integer bitpatterns and indices stay bounded. -/
def parseInstructions? (xs : List SExp) : Option (List Instr) :=
  parseInstructionsFuel? (xs.foldl (fun budget x => budget + syntaxNodes x + 1) 1) xs

def parseFunction? (x : SExp) : Option Func := do
  let .atom (.sym "func") :: ty :: ls :: body ← toList? x | none
  pure ⟨← parseTypeUse? ty, ← parseLocals? ls, ← parseInstructions? body⟩

def parseExport? (x : SExp) : Option Export := do
  let [.atom (.sym "export"), .atom (.str bytes), index] ← toList? x | none
  match ← toList? index with
  | [.atom (.sym "func"), i] => pure ⟨← Unicode.utf8? bytes, .func (← parseIndex? i)⟩
  | [.atom (.sym "memory"), i] => pure ⟨← Unicode.utf8? bytes, .memory (← parseIndex? i)⟩
  | [.atom (.sym "global"), i] => pure ⟨← Unicode.utf8? bytes, .global (← parseIndex? i)⟩
  | _ => none

def parseMemory? (x : SExp) : Option MemoryType := do
  let .atom (.sym "memory") :: limits ← toList? x | none
  match limits with
  | [min] =>
      let min ← parseNat? min
      if h : min < 2 ^ 64 then pure ⟨.i32, ⟨⟨min, h⟩, none⟩⟩ else none
  | [min, max] =>
      let min ← parseNat? min
      let max ← parseNat? max
      if h : min < 2 ^ 64 ∧ max < 2 ^ 64 then
        pure ⟨.i32, ⟨⟨min, h.1⟩, some ⟨max, h.2⟩⟩⟩
      else none
  | _ => none

def parseGlobalType? (x : SExp) : Option GlobalType := do
  match toList? x with
  | some [.atom (.sym "mut"), value] => pure ⟨.var, ← parseValue? value⟩
  | _ => pure ⟨.const, ← parseValue? x⟩

def parseGlobal? (x : SExp) : Option Global := do
  let .atom (.sym "global") :: type :: init ← toList? x | none
  pure ⟨← parseGlobalType? type, ← parseInstructions? init⟩

def parseData? (x : SExp) : Option Data := do
  match ← toList? x with
  | [.atom (.sym "data"), .atom (.str bytes)] => pure ⟨⟨bytes.toArray⟩, .passive⟩
  | [.atom (.sym "data"), memory, offset, .atom (.str bytes)] =>
      let [.atom (.sym "memory"), index] ← toList? memory | none
      let .atom (.sym "offset") :: body ← toList? offset | none
      pure ⟨⟨bytes.toArray⟩, .active (← parseIndex? index) (← parseInstructions? body)⟩
  | _ => none

/-- Explicit function and numeric-global imports, with numeric type
references and UTF-8 names. -/
def parseImport? (x : SExp) : Option Import := do
  let [.atom (.sym "import"), .atom (.str source), .atom (.str field), fn] ← toList? x | none
  let type ← match ← toList? fn with
    | [.atom (.sym "func"), type] => pure (ExternType.func (← parseTypeUse? type))
    | [.atom (.sym "global"), type] => pure (ExternType.global (← parseGlobalType? type))
    | _ => none
  pure ⟨← Unicode.utf8? source, ← Unicode.utf8? field, type⟩

/-- Parse fields into their distinct index spaces. The final reification
check rejects any field order that differs from the canonical builder. -/
def parseFields? : List SExp → Option Wasm.Module
  | [] => some {}
  | x :: xs => do
      let m ← parseFields? xs
      match ← toList? x with
      | .atom (.sym "type") :: _ =>
          pure { m with types := (← parseType? x) :: m.types }
      | .atom (.sym "import") :: _ =>
          pure { m with imports := (← parseImport? x) :: m.imports }
      | .atom (.sym "func") :: _ =>
          pure { m with funcs := (← parseFunction? x) :: m.funcs }
      | .atom (.sym "data") :: _ =>
          pure { m with data := (← parseData? x) :: m.data }
      | .atom (.sym "global") :: _ =>
          pure { m with globals := (← parseGlobal? x) :: m.globals }
      | .atom (.sym "memory") :: _ =>
          pure { m with memories := (← parseMemory? x) :: m.memories }
      | .atom (.sym "export") :: _ =>
          pure { m with exports := (← parseExport? x) :: m.exports }
      | _ => none

/-- Candidate parser for exactly one anonymous scalar module document. -/
def parseModule? (x : SExp) : Option Wasm.Module := do
  let [top] ← toList? x | none
  let .atom (.sym "module") :: fields ← toList? top | none
  parseFields? fields

/-- Accept a candidate only when the canonical builder reproduces the
complete input tree. No parser-correctness assumption enters the proof. -/
def parseCanonical? (x : SExp) : Option Wasm.Module := do
  let m ← parseModule? x
  if moduleSyntax? m = some x then some m else none

theorem parseCanonical?_reifies {x : SExp} {m : Wasm.Module}
    (h : parseCanonical? x = some m) : moduleSyntax? m = some x := by
  unfold parseCanonical? at h
  obtain ⟨candidate, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h; assumption
  · cases h

end Silmaril.Wasm.Binaryen.Toolkit.Wat
