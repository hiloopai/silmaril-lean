module

public import Silmaril.Machine.Vex.Execution.Defs

/-! # Independent, byte-decoded AMD64Scalar source model

This deliberately small decoder is for the listed AMD64 encodings only. It is
not a replacement for the repository's general x86 models. The source uses an
eager zero flag and does not interpret VEX statements or VEX flag recipes.
-/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar.X86

inductive Op where
  | movRdiToRax | addRsiToRax | cmpRdiRsi
  deriving DecidableEq, Repr

inductive Exit where
  | jmp (target : Word)
  | jcc (onZero : Bool) (taken next : Word)
  deriving DecidableEq, Repr

structure Block where
  body : List Op
  exit : Exit
  marks : List Mark
  deriving Repr

inductive DecodeError where
  | instruction (address : Word)
  | missingExit
  | trailingBytes (address : Word)
  deriving DecidableEq, Repr

def relative8 (next : Word) (displacement : UInt8) : Word :=
  next + (BitVec.ofNat 8 displacement.toNat).signExtend 64

def prepend (op : Op) (pc : Word) (rest : Block) : Block :=
  { rest with body := op :: rest.body, marks := ⟨pc, 3⟩ :: rest.marks }

def finish (pc : Word) (bytes : List UInt8) (exit : Exit) : Except DecodeError Block :=
  if bytes.isEmpty then .ok ⟨[], exit, [⟨pc, 2⟩]⟩ else .error (.trailingBytes (pc + 2))

def decode (pc : Word) : List UInt8 → Except DecodeError Block
  | [] => .error .missingExit
  | 0x48 :: 0x89 :: 0xf8 :: rest => (decode (pc + 3) rest).map (prepend .movRdiToRax pc)
  | 0x48 :: 0x01 :: 0xf0 :: rest => (decode (pc + 3) rest).map (prepend .addRsiToRax pc)
  | 0x48 :: 0x39 :: 0xf7 :: rest => (decode (pc + 3) rest).map (prepend .cmpRdiRsi pc)
  | 0xeb :: displacement :: rest => finish pc rest (.jmp (relative8 (pc + 2) displacement))
  | 0x74 :: displacement :: rest => finish pc rest (.jcc true (relative8 (pc + 2) displacement) (pc + 2))
  | 0x75 :: displacement :: rest => finish pc rest (.jcc false (relative8 (pc + 2) displacement) (pc + 2))
  | _ => .error (.instruction pc)

structure ScalarOps (value flag : Type) where
  zero : value
  add : value → value → value
  eq : value → value → flag

def Op.step {value flag : Type} (ops : ScalarOps value flag) (state : State value flag) :
    Op → State value flag
  | .movRdiToRax => { state with rax := state.rdi }
  | .addRsiToRax =>
    let sum := ops.add state.rax state.rsi
    { state with rax := sum, zf := ops.eq sum ops.zero }
  | .cmpRdiRsi => { state with zf := ops.eq state.rdi state.rsi }

def Exit.next {flag : Type} (zf : flag) : Exit → Next flag
  | .jmp target => .jump target
  | .jcc true taken next => .branch zf taken next
  | .jcc false taken next => .branch zf next taken

def concrete : ScalarOps Word Bool := ⟨0, (· + ·), (· == ·)⟩

def Block.run (block : Block) (input : Input) : Input :=
  let state := block.body.foldl (Op.step concrete) input
  { state with rip := (block.exit.next state.zf).target }

def symbolic : ScalarOps Term Term := ⟨.const 0, .add, .eq⟩

def entry (pc : Word) : State Term Term := ⟨.reg .rax, .reg .rdi, .reg .rsi, .initialZF, pc⟩

def Block.lower (block : Block) (pc : Word) : Plan :=
  let state := block.body.foldl (Op.step symbolic) (entry pc)
  ⟨state.rax, state.rdi, state.rsi, state.zf, block.exit.next state.zf⟩

end Silmaril.Machine.Vex.AMD64Scalar.X86
