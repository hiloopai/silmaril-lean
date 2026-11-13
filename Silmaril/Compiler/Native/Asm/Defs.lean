module
public import Silmaril.Compiler.Native.IR.Defs
/-! GNU assembler selection for native Mir operations. Virtual registers occupy
private stack slots; C pointers are machine addresses. This executable selector
is separate from the imported linear-memory backend and has no correctness
theorem yet. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Asm
open Silmaril.Machine
open Silmaril.Compile

/-- One original symbol character contributes either itself or a GNU quoted
symbol escape. Traversing the original characters once avoids re-escaping the
backslash introduced before a quote and preserves every other Unicode scalar. -/
def symbolChar : Char → List Char
  | '\\' => ['\\', '\\']
  | '"' => ['\\', '"']
  | character => [character]

/-- Quote a symbol for GNU assembly, escaping only backslash and double quote. -/
def symbol (s : String) : String :=
  String.ofList ('"' :: s.toList.flatMap symbolChar ++ ['"'])

def slot (r : Nat) : String := s!"QWORD PTR [rbp - {8 * (r + 1)}]"
def read (r : Nat) (into : String := "rax") : String := s!"  mov {into}, {slot r}\n"
def write (r : Nat) (source : String := "rax") : String := s!"  mov {slot r}, {source}\n"

def condition : Lir.Cond → String
  | .eq => "e" | .ne => "ne" | .lts => "l" | .ltu => "b"
  | .les => "le" | .leu => "be" | .gts => "g" | .gtu => "a"
  | .ges => "ge" | .geu => "ae"

def unary (op : Lir.Unop) : String :=
  let count (leading narrow : Bool) :=
    let r := if narrow then "eax" else "rax"
    let bits := if narrow then 32 else 64
    s!"  {if leading then "bsr" else "bsf"} {r}, {r}\n  jnz 1f\n  mov eax, {bits}\n" ++
      (if leading then s!"  jmp 2f\n1:\n  xor {r}, {bits - 1}\n2:\n" else "1:\n")
  let population :=
    "  mov r10, rax\n  shr r10, 1\n  movabs r11, 6148914691236517205\n" ++
    "  and r10, r11\n  sub rax, r10\n  mov r10, rax\n  movabs r11, 3689348814741910323\n" ++
    "  and rax, r11\n  shr r10, 2\n  and r10, r11\n  add rax, r10\n" ++
    "  mov r10, rax\n  shr r10, 4\n  add rax, r10\n  movabs r11, 1085102592571150095\n" ++
    "  and rax, r11\n  movabs r11, 72340172838076673\n  imul rax, r11\n  shr rax, 56\n"
  match op with
  | .sext8 => "  movsx rax, al\n"
  | .sext16 => "  movsx rax, ax\n"
  | .sext32 => "  movsxd rax, eax\n"
  | .zext8 => "  movzx eax, al\n"
  | .zext16 => "  movzx eax, ax\n"
  | .zext32 => "  mov eax, eax\n"
  | .eqz => "  test rax, rax\n  sete al\n  movzx eax, al\n"
  | .clz => count true false
  | .ctz => count false false
  | .popcnt => population
  | .clz32 => count true true
  | .ctz32 => count false true
  | .popcnt32 => "  mov eax, eax\n" ++ population

def binary (op : Lir.Binop) : String :=
  let shift (mn width : String) := s!"  mov rcx, r10\n  {mn} {width}, cl\n"
  let division (signed rem narrow : Bool) :=
    let a := if narrow then "eax" else "rax"
    let d := if narrow then "edx" else "rdx"
    let b := if narrow then "r10d" else "r10"
    (if signed then (if narrow then "  cdq\n" else "  cqo\n") else "  xor edx, edx\n") ++
      s!"  {if signed then "idiv" else "div"} {b}\n" ++
      (if rem then s!"  mov {a}, {d}\n" else "")
  match op with
  | .add => "  add rax, r10\n" | .sub => "  sub rax, r10\n"
  | .mul => "  imul rax, r10\n" | .and => "  and rax, r10\n"
  | .or => "  or rax, r10\n" | .xor => "  xor rax, r10\n"
  | .mulhu => "  mul r10\n  mov rax, rdx\n"
  | .mulhs => "  imul r10\n  mov rax, rdx\n"
  | .shl => shift "shl" "rax" | .shrs => shift "sar" "rax"
  | .shru => shift "shr" "rax" | .rotl => shift "rol" "rax" | .rotr => shift "ror" "rax"
  | .shl32 => shift "shl" "eax" | .shrs32 => shift "sar" "eax"
  | .shru32 => shift "shr" "eax" | .rotl32 => shift "rol" "eax" | .rotr32 => shift "ror" "eax"
  | .divs => division true false false | .divu => division false false false
  | .rems => division true true false | .remu => division false true false
  | .divs32 => division true false true | .divu32 => division false false true
  | .rems32 => division true true true | .remu32 => division false true true
  | .cmp c => s!"  cmp rax, r10\n  set{condition c} al\n  movzx eax, al\n"
  | .cmp32 c => s!"  cmp eax, r10d\n  set{condition c} al\n  movzx eax, al\n"

def load (w : Lir.Width) (ext : Lir.Ext) (off : Nat) : String :=
  let ptr := s!"[r10 + {off}]"
  match w, ext with
  | .b1, .zero => s!"  movzx eax, BYTE PTR {ptr}\n"
  | .b1, .sign => s!"  movsx rax, BYTE PTR {ptr}\n"
  | .b2, .zero => s!"  movzx eax, WORD PTR {ptr}\n"
  | .b2, .sign => s!"  movsx rax, WORD PTR {ptr}\n"
  | .b4, .zero => s!"  mov eax, DWORD PTR {ptr}\n"
  | .b4, .sign => s!"  movsxd rax, DWORD PTR {ptr}\n"
  | .b8, _ => s!"  mov rax, QWORD PTR {ptr}\n"

def store (w : Lir.Width) (off : Nat) : String :=
  let (size, reg) := match w with
    | .b1 => ("BYTE", "al") | .b2 => ("WORD", "ax")
    | .b4 => ("DWORD", "eax") | .b8 => ("QWORD", "rax")
  s!"  mov {size} PTR [r10 + {off}], {reg}\n"

def operation : Lir.Op Nat → Except String String
  | .const d v => return s!"  movabs rax, {v.toNat}\n" ++ write d
  | .move d s => return read s ++ write d
  | .unary op d s => return read s ++ unary op ++ write d
  | .binary op d a b => return read a ++ read b "r10" ++ binary op ++ write d
  | .load w ext d b off => return read b "r10" ++ load w ext off ++ write d
  | .store w b off s => return read b "r10" ++ read s ++ store w off
  | .slotGet .. | .slotSet .. => .error "native input must precede Lir slot allocation"

def floating (op : Lir.FOp) (d a b : Nat) : String :=
  let suffix : Lir.FFmt → String | .f32 => "ss" | .f64 => "sd"
  let toX (f : Lir.FFmt) (x : String) (r : Nat) :=
    read r ++ s!"  {if f == .f32 then "movd" else "movq"} {x}, {if f == .f32 then "eax" else "rax"}\n"
  let fromX (f : Lir.FFmt) :=
    s!"  {if f == .f32 then "movd eax" else "movq rax"}, xmm0\n" ++ write d
  let arith (mn : String) (f : Lir.FFmt) :=
    toX f "xmm0" a ++ toX f "xmm1" b ++ s!"  {mn}{suffix f} xmm0, xmm1\n" ++ fromX f
  match op with
  | .add f => arith "add" f | .sub f => arith "sub" f
  | .mul f => arith "mul" f | .div f => arith "div" f
  | .cmp f c =>
    let pred : Nat := match c with | .eq => 0 | .ne => 4 | .lt => 1 | .le => 2
    toX f "xmm0" a ++ toX f "xmm1" b ++
      s!"  cmp{suffix f} xmm0, xmm1, {pred}\n  movq rax, xmm0\n  and eax, 1\n" ++ write d
  | .ofInt f => read a ++ s!"  cvtsi2{suffix f} xmm0, rax\n" ++ fromX f
  | .toInt f wide => toX f "xmm0" a ++
      s!"  cvtt{suffix f}2si {if wide then "rax" else "eax"}, xmm0\n" ++ write d
  | .widen => toX .f32 "xmm0" a ++ "  cvtss2sd xmm0, xmm0\n" ++ fromX .f64
  | .narrow => toX .f64 "xmm0" a ++ "  cvtsd2ss xmm0, xmm0\n" ++ fromX .f32

end Silmaril.Compiler.Native.Asm
