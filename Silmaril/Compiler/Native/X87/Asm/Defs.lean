module
public import Silmaril.Compiler.Native.Asm.Defs
public import Silmaril.Compiler.Native.X87.Defs
/-! GNU x87 selection for typed native intrinsics. Each completed operation
balances its x87 stack and releases its private 32-byte scratch area. Integer
truncation temporarily selects RC=11 and restores the exact incoming control
word, without requiring the SSE3 FISTTP instruction. This is executable research
code; no numerical, exception, ABI or emitted-machine refinement is proved. -/
@[expose] public section
namespace Silmaril.Compiler.Native.X87.Asm
open Silmaril.Compiler.Native

/-- Only low ten bytes are the value; initialize the six padding bytes of a
fresh result too. Load every input before touching a possibly aliased result. -/
def storeExtended (destination : Nat) : String :=
  Native.Asm.read destination "r10" ++
    "  mov QWORD PTR [r10 + 8], 0\n  fstp TBYTE PTR [r10]\n"

/-- Extended constants 2^63 or 2^64, exactly encoded in scratch bytes 8..17. -/
def power (exponent : Nat) : String :=
  "  movabs r11, 9223372036854775808\n  mov QWORD PTR [rsp + 8], r11\n" ++
    s!"  mov WORD PTR [rsp + 16], {16383 + exponent}\n"

/-- An ordinary scalar is already sign/zero extended in its Mir register. The
unsigned-64 correction is exact with the usual 64-bit x87 precision control. -/
def loadScalar (format : Format) (source : Nat) : Except String String := do
  let value := Native.Asm.read source ++ "  mov QWORD PTR [rsp], rax\n"
  match format with
  | .extended => return Native.Asm.read source "r10" ++ "  fld TBYTE PTR [r10]\n"
  | .float32 => return value ++ "  fld DWORD PTR [rsp]\n"
  | .float64 => return value ++ "  fld QWORD PTR [rsp]\n"
  | .integer 8 false => return value ++ "  fild QWORD PTR [rsp]\n  test rax, rax\n  jns 1f\n" ++
      (power 64) ++ "  fld TBYTE PTR [rsp + 8]\n  faddp st(1), st\n1:\n"
  | .integer _ _ | .boolean => return value ++ "  fild QWORD PTR [rsp]\n"

/-- FUCOMIP leaves one temporary value, removed before reading the integer
flags. Parity distinguishes unordered from equality and the below predicates. -/
def predicate : Comparison → String
  | .eq => "  sete al\n  setnp dl\n  and al, dl\n"
  | .ne => "  setne al\n  setp dl\n  or al, dl\n"
  | .lt => "  setb al\n  setnp dl\n  and al, dl\n"
  | .le => "  setbe al\n  setnp dl\n  and al, dl\n"
  | .gt => "  seta al\n"
  | .ge => "  setae al\n"

def compare (condition : Comparison) (first second destination : Nat) : String :=
  Native.Asm.read second "r10" ++ "  fld TBYTE PTR [r10]\n" ++
    Native.Asm.read first "r10" ++ "  fld TBYTE PTR [r10]\n" ++
    "  fucomip st, st(1)\n  fstp st(0)\n" ++ predicate condition ++
    "  movzx eax, al\n" ++ Native.Asm.write destination

def truth (source destination : Nat) : String :=
  "  fldz\n" ++ Native.Asm.read source "r10" ++ "  fld TBYTE PTR [r10]\n" ++
    "  fucomip st, st(1)\n  fstp st(0)\n" ++ predicate .ne ++
    "  movzx eax, al\n" ++ Native.Asm.write destination

/-- RC changes only for FISTP. The original control word at scratch offset 24
survives the unsigned range split and is restored before normal completion.
NaN, infinities and out-of-range C integer conversions have no defined-C claim. -/
def truncate (unsigned64 : Bool) : String :=
  "  fnstcw WORD PTR [rsp + 24]\n  movzx eax, WORD PTR [rsp + 24]\n" ++
    "  or ax, 3072\n  mov WORD PTR [rsp + 26], ax\n  fldcw WORD PTR [rsp + 26]\n" ++
    (if unsigned64 then
      (power 63) ++ "  fld TBYTE PTR [rsp + 8]\n  fxch st(1)\n" ++
        "  fucomi st, st(1)\n  jb 1f\n  fsub st, st(1)\n" ++
        "  fistp QWORD PTR [rsp]\n  fstp st(0)\n  mov rax, QWORD PTR [rsp]\n" ++
        "  bts rax, 63\n  jmp 2f\n1:\n  fistp QWORD PTR [rsp]\n  fstp st(0)\n" ++
        "  mov rax, QWORD PTR [rsp]\n2:\n"
    else "  fistp QWORD PTR [rsp]\n  mov rax, QWORD PTR [rsp]\n") ++
    "  fldcw WORD PTR [rsp + 24]\n"

def convert (source target : Format) (input output : Nat) : Except String String := do
  if target == .boolean then return truth input output
  let loaded ← loadScalar source input
  if target == .extended then return loaded ++ storeExtended output
  match target with
  | .float32 => return loaded ++ "  fstp DWORD PTR [rsp]\n  mov eax, DWORD PTR [rsp]\n" ++
      Native.Asm.write output
  | .float64 => return loaded ++ "  fstp QWORD PTR [rsp]\n  mov rax, QWORD PTR [rsp]\n" ++
      Native.Asm.write output
  | .integer bytes signed => return loaded ++ truncate (bytes == 8 && !signed) ++
      (match bytes, signed with
        | 1, true => Native.Asm.unary .sext8 | 1, false => Native.Asm.unary .zext8
        | 2, true => Native.Asm.unary .sext16 | 2, false => Native.Asm.unary .zext16
        | 4, true => Native.Asm.unary .sext32 | 4, false => Native.Asm.unary .zext32
        | _, _ => "") ++ Native.Asm.write output
  | _ => throw "invalid native x87 scalar conversion"

/-- Operands/results are validated before any selector accesses their shape. -/
def emit (operation : Operation) (operands results : List Nat) : Except String String := do
  unless operation.supported do throw "unsupported native x87 operation/width"
  unless operands.length == operation.operands && results.length == operation.results do
    throw "native x87 intrinsic operand/result mismatch"
  let body ← match operation, operands, results with
    | .convert source .extended, [destination, input], [] => convert source .extended input destination
    | .convert source target, [input], [destination] => convert source target input destination
    | .compare condition, [first, second], [destination] => pure (compare condition first second destination)
    | .truth, [input], [destination] => pure (truth input destination)
    | .negate, [destination, input], [] => do
        return (← loadScalar .extended input) ++ "  fchs\n" ++ storeExtended destination
    | .arithmetic operator, [destination, first, second], [] => do
        let mnemonic := match operator with
          | .add => "faddp" | .sub => "fsubp" | .mul => "fmulp" | .div => "fdivp"
        return (← loadScalar .extended first) ++ (← loadScalar .extended second) ++
          s!"  {mnemonic} st(1), st\n" ++ storeExtended destination
    | _, _, _ => throw "invalid native x87 intrinsic shape"
  return "  sub rsp, 32\n" ++ body ++ "  add rsp, 32\n"

end Silmaril.Compiler.Native.X87.Asm
