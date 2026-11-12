module

public import Silmaril.Machine.RegisterFile
public import Silmaril.Semantics.CPort.Instruction.BitVector.Defs
/-!
# A reusable three-address bitvector language

The register type, word width, and literal width are independent of any target.
Literals denote bit patterns interpreted by signed resizing to the word width;
their width is a source-language restriction, not a claim that every backend has
a matching native immediate encoding. Operands are read before the destination
is written, so destinations may alias either input.
-/

@[expose] public section

namespace Silmaril.Machine.RegisterIR

universe u

abbrev Env (Register : Type u) (wordWidth : Nat) := RegisterFile Register (BitVec wordWidth)

/-- A small shared arithmetic vocabulary, interpreted by the existing bitvector model. -/
inductive Binary where
  | add | sub | and | or | xor
  deriving DecidableEq, Repr

def Binary.toBitVector : Binary → Instruction.BitVector.Binary
  | .add => .add
  | .sub => .sub
  | .and => .and
  | .or => .or
  | .xor => .xor

inductive Instr (Register : Type u) (wordWidth literalWidth : Nat) where
  | move (dest source : Register)
  | const (dest : Register) (value : BitVec literalWidth)
  | binary (op : Binary) (dest first second : Register)
  | unary (op : Instruction.BitVector.Unary) (dest source : Register)
  deriving DecidableEq, Repr

variable {Register : Type u} {wordWidth literalWidth : Nat}

def Instr.dest : Instr Register wordWidth literalWidth → Register
  | .move dest _ | .const dest _ | .binary _ dest _ _ | .unary _ dest _ => dest

def Instr.value (instr : Instr Register wordWidth literalWidth)
    (env : Env Register wordWidth) : BitVec wordWidth :=
  match instr with
  | .move _ source => env source
  | .const _ value => value.signExtend wordWidth
  | .binary op _ first second => op.toBitVector.eval (env first, env second)
  | .unary op _ source => op.eval (env source)

def step [DecidableEq Register] (instr : Instr Register wordWidth literalWidth)
    (env : Env Register wordWidth) : Env Register wordWidth :=
  RegisterFile.write env instr.dest (instr.value env)

@[simp] theorem step_dest [DecidableEq Register] (instr : Instr Register wordWidth literalWidth)
    (env : Env Register wordWidth) : step instr env instr.dest = instr.value env := by
  simp [step]

theorem step_other [DecidableEq Register] (instr : Instr Register wordWidth literalWidth)
    (env : Env Register wordWidth) (reg : Register) (h : reg ≠ instr.dest) :
    step instr env reg = env reg := by
  simp [step, h]

end Silmaril.Machine.RegisterIR
