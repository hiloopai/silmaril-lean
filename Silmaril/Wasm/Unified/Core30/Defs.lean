module

public import Silmaril.Wasm.Unified.Inst.Defs
public import Silmaril.Wasm.Unified.Codes.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3
public import Silmaril.Wasm.Validation.Instructions

/-!
# Core 3.0 as a model of the unified institution

silmaril-lean's Core 3.0 (`Silmaril.Wasm.Instr`, reduction `Step P host`) as a signature and a
model of the unified Wasm institution (`Silmaril.Wasm.Unified.Inst`).

## Opcodes of Core 3.0

`head i` is the opcode of a Core 3.0 instruction: the open name of its silmaril constructor
(`"intBinOp"`, `"block"`, ...) with parameters: the **family number** (the position of the
constructor in silmaril's `Instr`, so that decoding never compares names), then the
**operator parameters**, the codes (`Code`) of the fields that select a binary opcode (number
types, operators, shapes, signedness, pack sizes).
The remaining fields are immediates (`immsOf`: indices, memory arguments, lanes, constant bits,
block and reference types, each one `Imm.nat` of its code; constant bits are their `toNat`),
the structured bodies are blocks, and `try_table` catch clauses are the handler table
(`hdlOf`). The numbering is not the binary one: binary opcodes are another signature, related
by a renaming morphism (a later slice).

* `sig30`: the **3.0 signature**: the opcodes `head i` of all instructions, typed by
  `arity30` (a table by family number; `arity30_head` checks it against the encoding).
* `enc : Instr → UInstr sig30.Op`, `encCode`: the encoding of Core 3.0 syntax into the
  signature's syntax; `encCode_univ` reads it as universal code.

## The model

`alg30` interprets the 3.0 opcodes as **sets of silmaril instructions**: an opcode with
immediates, handler table and block meanings `Ds` denotes the instructions with that head,
those immediates and handlers, and bodies in `Ds`; sequences are sets of instruction lists.
Evaluation of encoded code contains the code (`mem_evalCode_encCode` in `Thms`).

`model30 P host s f okc` runs a meaning on argument values `vs` from the store `s` and frame
`f`: the behaviours (`behavioursOf P host`, i.e. reduction `Step P host` read as returns,
traps, throws and divergence) of `vals vs ++ expression is` for the decodings `is` that pass
the validation `okc`. Validation is a parameter: `okTrue` accepts everything (Core reduction
needs no typing), `okTyped C ft` is silmaril's `InstrsOk C is ft`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Core30

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Unified

/-- The code of a field, as an operator parameter. -/
abbrev p {α : Type} [Code α] (x : α) : Nat := code x

/-- The code of a field, as an immediate. -/
abbrev e {α : Type} [Code α] (x : α) : Imm := .nat (code x)

/-- The opcode of a Core 3.0 instruction: its constructor name and operator parameters. -/
def head : Instr → Opcode
  | .nop => .named "nop" [0]
  | .unreachable => .named "unreachable" [1]
  | .drop => .named "drop" [2]
  | .select _ => .named "select" [3]
  | .block _ _ => .named "block" [4]
  | .loop _ _ => .named "loop" [5]
  | .if_ _ _ _ => .named "if" [6]
  | .br _ => .named "br" [7]
  | .brIf _ => .named "brIf" [8]
  | .brTable _ _ => .named "brTable" [9]
  | .brOnNull _ => .named "brOnNull" [10]
  | .brOnNonNull _ => .named "brOnNonNull" [11]
  | .brOnCast _ _ _ => .named "brOnCast" [12]
  | .brOnCastFail _ _ _ => .named "brOnCastFail" [13]
  | .call _ => .named "call" [14]
  | .callRef _ => .named "callRef" [15]
  | .callIndirect _ _ => .named "callIndirect" [16]
  | .return_ => .named "return" [17]
  | .returnCall _ => .named "returnCall" [18]
  | .returnCallRef _ => .named "returnCallRef" [19]
  | .returnCallIndirect _ _ => .named "returnCallIndirect" [20]
  | .throw _ => .named "throw" [21]
  | .throwRef => .named "throwRef" [22]
  | .tryTable _ _ _ => .named "tryTable" [23]
  | .localGet _ => .named "localGet" [24]
  | .localSet _ => .named "localSet" [25]
  | .localTee _ => .named "localTee" [26]
  | .globalGet _ => .named "globalGet" [27]
  | .globalSet _ => .named "globalSet" [28]
  | .tableGet _ => .named "tableGet" [29]
  | .tableSet _ => .named "tableSet" [30]
  | .tableSize _ => .named "tableSize" [31]
  | .tableGrow _ => .named "tableGrow" [32]
  | .tableFill _ => .named "tableFill" [33]
  | .tableCopy _ _ => .named "tableCopy" [34]
  | .tableInit _ _ => .named "tableInit" [35]
  | .elemDrop _ => .named "elemDrop" [36]
  | .intLoad t k _ _ => .named "intLoad" [37, p t, p k]
  | .floatLoad t _ _ => .named "floatLoad" [38, p t]
  | .intStore t k _ _ => .named "intStore" [39, p t, p k]
  | .floatStore t _ _ => .named "floatStore" [40, p t]
  | .vecLoad op _ _ => .named "vecLoad" [41, p op]
  | .vecLoadLane k _ _ _ => .named "vecLoadLane" [42, p k]
  | .vecStore _ _ => .named "vecStore" [43]
  | .vecStoreLane k _ _ _ => .named "vecStoreLane" [44, p k]
  | .memorySize _ => .named "memorySize" [45]
  | .memoryGrow _ => .named "memoryGrow" [46]
  | .memoryFill _ => .named "memoryFill" [47]
  | .memoryCopy _ _ => .named "memoryCopy" [48]
  | .memoryInit _ _ => .named "memoryInit" [49]
  | .dataDrop _ => .named "dataDrop" [50]
  | .refNull _ => .named "refNull" [51]
  | .refIsNull => .named "refIsNull" [52]
  | .refAsNonNull => .named "refAsNonNull" [53]
  | .refEq => .named "refEq" [54]
  | .refTest _ => .named "refTest" [55]
  | .refCast _ => .named "refCast" [56]
  | .refFunc _ => .named "refFunc" [57]
  | .refI31 => .named "refI31" [58]
  | .i31Get k => .named "i31Get" [59, p k]
  | .structNew _ => .named "structNew" [60]
  | .structNewDefault _ => .named "structNewDefault" [61]
  | .structGet k _ _ => .named "structGet" [62, p k]
  | .structSet _ _ => .named "structSet" [63]
  | .arrayNew _ => .named "arrayNew" [64]
  | .arrayNewDefault _ => .named "arrayNewDefault" [65]
  | .arrayNewFixed _ _ => .named "arrayNewFixed" [66]
  | .arrayNewData _ _ => .named "arrayNewData" [67]
  | .arrayNewElem _ _ => .named "arrayNewElem" [68]
  | .arrayGet k _ => .named "arrayGet" [69, p k]
  | .arraySet _ => .named "arraySet" [70]
  | .arrayLen => .named "arrayLen" [71]
  | .arrayFill _ => .named "arrayFill" [72]
  | .arrayCopy _ _ => .named "arrayCopy" [73]
  | .arrayInitData _ _ => .named "arrayInitData" [74]
  | .arrayInitElem _ _ => .named "arrayInitElem" [75]
  | .externConvertAny => .named "externConvertAny" [76]
  | .anyConvertExtern => .named "anyConvertExtern" [77]
  | .intConst t _ => .named "intConst" [78, p t]
  | .floatConst t _ => .named "floatConst" [79, p t]
  | .intUnOp t op => .named "intUnOp" [80, p t, p op]
  | .intBinOp t op => .named "intBinOp" [81, p t, p op]
  | .intTestOp t op => .named "intTestOp" [82, p t, p op]
  | .intRelOp t op => .named "intRelOp" [83, p t, p op]
  | .floatUnOp t op => .named "floatUnOp" [84, p t, p op]
  | .floatBinOp t op => .named "floatBinOp" [85, p t, p op]
  | .floatRelOp t op => .named "floatRelOp" [86, p t, p op]
  | .convert op => .named "convert" [87, p op]
  | .vecConst _ => .named "vecConst" [88]
  | .vecUnOp op => .named "vecUnOp" [89, p op]
  | .vecBinOp op => .named "vecBinOp" [90, p op]
  | .vecTernOp op => .named "vecTernOp" [91, p op]
  | .vecTestOp op => .named "vecTestOp" [92, p op]
  | .vecIntUnOp sh op => .named "vecIntUnOp" [93, p sh, p op]
  | .vecFloatUnOp sh op => .named "vecFloatUnOp" [94, p sh, p op]
  | .vecIntBinOp sh op => .named "vecIntBinOp" [95, p sh, p op]
  | .vecFloatBinOp sh op => .named "vecFloatBinOp" [96, p sh, p op]
  | .vecIntTernOp sh op => .named "vecIntTernOp" [97, p sh, p op]
  | .vecFloatTernOp sh op => .named "vecFloatTernOp" [98, p sh, p op]
  | .vecAllTrue sh => .named "vecAllTrue" [99, p sh]
  | .vecIntRelOp sh op => .named "vecIntRelOp" [100, p sh, p op]
  | .vecFloatRelOp sh op => .named "vecFloatRelOp" [101, p sh, p op]
  | .vecShiftOp sh op => .named "vecShiftOp" [102, p sh, p op]
  | .vecBitmask sh => .named "vecBitmask" [103, p sh]
  | .vecSwizzle op => .named "vecSwizzle" [104, p op]
  | .vecShuffle _ => .named "vecShuffle" [105]
  | .vecExtUnOp s t op => .named "vecExtUnOp" [106, p s, p t, p op]
  | .vecExtBinOp s t op => .named "vecExtBinOp" [107, p s, p t, p op]
  | .vecExtTernOp s t op => .named "vecExtTernOp" [108, p s, p t, p op]
  | .vecNarrow s t k => .named "vecNarrow" [109, p s, p t, p k]
  | .vecConvert s t op => .named "vecConvert" [110, p s, p t, p op]
  | .vecSplat sh => .named "vecSplat" [111, p sh]
  | .vecExtractLane sh k _ => .named "vecExtractLane" [112, p sh, p k]
  | .vecReplaceLane sh _ => .named "vecReplaceLane" [113, p sh]

/-- The immediates of a Core 3.0 instruction. -/
def immsOf : Instr → List Imm
  | .select ts => [e ts]
  | .block bt _ | .loop bt _ | .if_ bt _ _ | .tryTable bt _ _ => [e bt]
  | .br l | .brIf l | .brOnNull l | .brOnNonNull l => [e l]
  | .brTable ls d => [e ls, e d]
  | .brOnCast l s t | .brOnCastFail l s t => [e l, e s, e t]
  | .call x | .returnCall x | .refFunc x => [e x]
  | .callRef x | .returnCallRef x | .structNew x | .structNewDefault x | .arrayNew x
  | .arrayNewDefault x | .arraySet x | .arrayFill x | .arrayGet _ x => [e x]
  | .callIndirect x y | .returnCallIndirect x y => [e x, e y]
  | .throw x => [e x]
  | .localGet x | .localSet x | .localTee x => [e x]
  | .globalGet x | .globalSet x => [e x]
  | .tableGet x | .tableSet x | .tableSize x | .tableGrow x | .tableFill x => [e x]
  | .tableCopy x y => [e x, e y]
  | .tableInit x y => [e x, e y]
  | .elemDrop x => [e x]
  | .intLoad _ _ m a | .floatLoad _ m a | .intStore _ _ m a | .floatStore _ m a
  | .vecLoad _ m a | .vecStore m a => [e m, e a]
  | .vecLoadLane _ m a l | .vecStoreLane _ m a l => [e m, e a, e l]
  | .memorySize x | .memoryGrow x | .memoryFill x => [e x]
  | .memoryCopy x y => [e x, e y]
  | .memoryInit x y => [e x, e y]
  | .dataDrop x => [e x]
  | .refNull h => [e h]
  | .refTest t | .refCast t => [e t]
  | .structGet _ x y => [e x, e y]
  | .structSet x y => [e x, e y]
  | .arrayNewFixed x n => [e x, e n]
  | .arrayNewData x y | .arrayInitData x y => [e x, e y]
  | .arrayNewElem x y | .arrayInitElem x y => [e x, e y]
  | .arrayCopy x y => [e x, e y]
  | .intConst _ b => [.nat b.toNat]
  | .floatConst _ b => [.nat b.toNat]
  | .vecConst b => [.nat b.toNat]
  | .vecShuffle ls => [e ls]
  | .vecExtractLane _ _ l | .vecReplaceLane _ l => [e l]
  | _ => []

/-- A catch clause as a handler-table entry. -/
def catchH : Catch → Handler
  | .catch_ x l => ⟨"catch", [e x, e l]⟩
  | .catchRef x l => ⟨"catch_ref", [e x, e l]⟩
  | .catchAll l => ⟨"catch_all", [e l]⟩
  | .catchAllRef l => ⟨"catch_all_ref", [e l]⟩

/-- The handler table of a Core 3.0 instruction (`try_table` catch clauses). -/
def hdlOf : Instr → List Handler
  | .tryTable _ cs _ => cs.map catchH
  | _ => []

/-- The syntactic types of the 3.0 opcode families, by family number. -/
def arityTab : Nat → OpTy
  | 0 => ⟨0, 0, false⟩
  | 1 => ⟨0, 0, false⟩
  | 2 => ⟨0, 0, false⟩
  | 3 => ⟨1, 0, false⟩
  | 4 => ⟨1, 1, false⟩
  | 5 => ⟨1, 1, false⟩
  | 6 => ⟨1, 2, false⟩
  | 7 => ⟨1, 0, false⟩
  | 8 => ⟨1, 0, false⟩
  | 9 => ⟨2, 0, false⟩
  | 10 => ⟨1, 0, false⟩
  | 11 => ⟨1, 0, false⟩
  | 12 => ⟨3, 0, false⟩
  | 13 => ⟨3, 0, false⟩
  | 14 => ⟨1, 0, false⟩
  | 15 => ⟨1, 0, false⟩
  | 16 => ⟨2, 0, false⟩
  | 17 => ⟨0, 0, false⟩
  | 18 => ⟨1, 0, false⟩
  | 19 => ⟨1, 0, false⟩
  | 20 => ⟨2, 0, false⟩
  | 21 => ⟨1, 0, false⟩
  | 22 => ⟨0, 0, false⟩
  | 23 => ⟨1, 1, true⟩
  | 24 => ⟨1, 0, false⟩
  | 25 => ⟨1, 0, false⟩
  | 26 => ⟨1, 0, false⟩
  | 27 => ⟨1, 0, false⟩
  | 28 => ⟨1, 0, false⟩
  | 29 => ⟨1, 0, false⟩
  | 30 => ⟨1, 0, false⟩
  | 31 => ⟨1, 0, false⟩
  | 32 => ⟨1, 0, false⟩
  | 33 => ⟨1, 0, false⟩
  | 34 => ⟨2, 0, false⟩
  | 35 => ⟨2, 0, false⟩
  | 36 => ⟨1, 0, false⟩
  | 37 => ⟨2, 0, false⟩
  | 38 => ⟨2, 0, false⟩
  | 39 => ⟨2, 0, false⟩
  | 40 => ⟨2, 0, false⟩
  | 41 => ⟨2, 0, false⟩
  | 42 => ⟨3, 0, false⟩
  | 43 => ⟨2, 0, false⟩
  | 44 => ⟨3, 0, false⟩
  | 45 => ⟨1, 0, false⟩
  | 46 => ⟨1, 0, false⟩
  | 47 => ⟨1, 0, false⟩
  | 48 => ⟨2, 0, false⟩
  | 49 => ⟨2, 0, false⟩
  | 50 => ⟨1, 0, false⟩
  | 51 => ⟨1, 0, false⟩
  | 52 => ⟨0, 0, false⟩
  | 53 => ⟨0, 0, false⟩
  | 54 => ⟨0, 0, false⟩
  | 55 => ⟨1, 0, false⟩
  | 56 => ⟨1, 0, false⟩
  | 57 => ⟨1, 0, false⟩
  | 58 => ⟨0, 0, false⟩
  | 59 => ⟨0, 0, false⟩
  | 60 => ⟨1, 0, false⟩
  | 61 => ⟨1, 0, false⟩
  | 62 => ⟨2, 0, false⟩
  | 63 => ⟨2, 0, false⟩
  | 64 => ⟨1, 0, false⟩
  | 65 => ⟨1, 0, false⟩
  | 66 => ⟨2, 0, false⟩
  | 67 => ⟨2, 0, false⟩
  | 68 => ⟨2, 0, false⟩
  | 69 => ⟨1, 0, false⟩
  | 70 => ⟨1, 0, false⟩
  | 71 => ⟨0, 0, false⟩
  | 72 => ⟨1, 0, false⟩
  | 73 => ⟨2, 0, false⟩
  | 74 => ⟨2, 0, false⟩
  | 75 => ⟨2, 0, false⟩
  | 76 => ⟨0, 0, false⟩
  | 77 => ⟨0, 0, false⟩
  | 78 => ⟨1, 0, false⟩
  | 79 => ⟨1, 0, false⟩
  | 80 => ⟨0, 0, false⟩
  | 81 => ⟨0, 0, false⟩
  | 82 => ⟨0, 0, false⟩
  | 83 => ⟨0, 0, false⟩
  | 84 => ⟨0, 0, false⟩
  | 85 => ⟨0, 0, false⟩
  | 86 => ⟨0, 0, false⟩
  | 87 => ⟨0, 0, false⟩
  | 88 => ⟨1, 0, false⟩
  | 89 => ⟨0, 0, false⟩
  | 90 => ⟨0, 0, false⟩
  | 91 => ⟨0, 0, false⟩
  | 92 => ⟨0, 0, false⟩
  | 93 => ⟨0, 0, false⟩
  | 94 => ⟨0, 0, false⟩
  | 95 => ⟨0, 0, false⟩
  | 96 => ⟨0, 0, false⟩
  | 97 => ⟨0, 0, false⟩
  | 98 => ⟨0, 0, false⟩
  | 99 => ⟨0, 0, false⟩
  | 100 => ⟨0, 0, false⟩
  | 101 => ⟨0, 0, false⟩
  | 102 => ⟨0, 0, false⟩
  | 103 => ⟨0, 0, false⟩
  | 104 => ⟨0, 0, false⟩
  | 105 => ⟨1, 0, false⟩
  | 106 => ⟨0, 0, false⟩
  | 107 => ⟨0, 0, false⟩
  | 108 => ⟨0, 0, false⟩
  | 109 => ⟨0, 0, false⟩
  | 110 => ⟨0, 0, false⟩
  | 111 => ⟨0, 0, false⟩
  | 112 => ⟨1, 0, false⟩
  | 113 => ⟨1, 0, false⟩
  | _ => ⟨0, 0, false⟩

/-- The syntactic types of the 3.0 opcodes: by the family number, the first parameter. -/
def arity30 : Opcode → OpTy
  | .named _ (k :: _) => arityTab k
  | _ => ⟨0, 0, false⟩

/-- **The Wasm 3.0 feature signature**: the opcodes of Core 3.0 instructions. -/
def sig30 : FSig := ⟨Set.range head, arity30⟩

/-- The opcode of an instruction, in the 3.0 signature. -/
def op30 (i : Instr) : sig30.Op := ⟨head i, i, rfl⟩

mutual
/-- **The encoding** of a Core 3.0 instruction in the 3.0 signature's syntax. -/
def enc : Instr → UInstr sig30.Op
  | .block bt b => .op (op30 (.block bt b)) [e bt] [encCode b] []
  | .loop bt b => .op (op30 (.loop bt b)) [e bt] [encCode b] []
  | .if_ bt b₁ b₂ => .op (op30 (.if_ bt b₁ b₂)) [e bt] [encCode b₁, encCode b₂] []
  | .tryTable bt cs b => .op (op30 (.tryTable bt cs b)) [e bt] [encCode b] (cs.map catchH)
  | i => .op (op30 i) (immsOf i) [] (hdlOf i)
/-- The encoding of a Core 3.0 instruction sequence. -/
def encCode : List Instr → sig30.Code
  | [] => []
  | i :: is => enc i :: encCode is
end

/-! ## The model -/

/-- Instruction lists with heads in `A` and tails in `D`. -/
def consSet (A : Set Instr) (D : Set (List Instr)) : Set (List Instr) :=
  {l | ∃ i t, l = i :: t ∧ i ∈ A ∧ t ∈ D}

/-- **The 3.0 opcode algebra**: an opcode denotes the instructions with that head, immediates
and handler table whose bodies lie in the block meanings. -/
def alg30 : Alg sig30.Op where
  I := Set Instr
  D := Set (List Instr)
  nil := {[]}
  cons := consSet
  op o imms Ds hs :=
    {i | head i = o.1 ∧ immsOf i = imms ∧ hdlOf i = hs ∧ List.Forall₂ (· ∈ ·) i.bodies Ds}

/-- The meaning of an instruction in the 3.0 algebra, as a set. -/
def evalI30 (i : UInstr sig30.Op) : Set Instr := alg30.evalInstr i

/-- The meaning of code in the 3.0 algebra, as a set. -/
def evalC30 (c : sig30.Code) : Set (List Instr) := alg30.evalCode c

/-- The behaviours of running code `is` on arguments `vs` from store `s` and frame `f`. -/
def behCode (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (is : List Instr) (vs : List Val) : Set (Behaviour Val) :=
  behavioursOf P host ⟨s, f, vals vs ++ expression is⟩

/-- **The Core 3.0 model** of the 3.0 signature, at profile `P`, host `host`, store `s`, frame
`f`, with validation `okc`. -/
def model30 (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model (List Val) (Behaviour Val) sig30 where
  alg := alg30
  ok := fun (D : Set (List Instr)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List Instr)) vs => {b | ∃ is ∈ D, okc is ∧ b ∈ behCode P host s f is vs}

/-- Validation accepting all code. -/
def okTrue : List Instr → Prop := fun _ => True

/-- silmaril's Core 3.0 validation of an instruction sequence in context `C` at type `ft`. -/
def okTyped (C : Validation.Context) (ft : Validation.InstrType) : List Instr → Prop :=
  fun is => Validation.InstrsOk C is ft

end Silmaril.Wasm.Unified.Core30
