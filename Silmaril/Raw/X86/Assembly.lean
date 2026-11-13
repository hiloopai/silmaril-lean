module

public import Silmaril.X86.Ext.Syntax
public import Batteries.Data.Except

/-!
# Readable input for a small x86 instruction subset

`parse` reads an Intel-style, destination-first listing into the existing
`Ext.Instr` type. It is a parser, not an assembler or a new instruction semantics.
It accepts the instruction forms used by the retained verification examples.
Every memory operand has an explicit size; immediate encodings use `imm8` or
`imm32`; jumps use `short` or `near`. Branch operands are signed byte displacements
from the next instruction, not absolute addresses. Calls use `rel32`.

`format` produces input in the same language when it supports an instruction.
Unsupported forms return `none`; they are never guessed or silently rewritten.
No general parser/printer correctness theorem is claimed here. Users should prove
equality with their listing and its source certificate, as the examples do.
-/

@[expose] public section

namespace Silmaril.X86.Assembly

open Ext

def registers : List (String × Reg × Nat) := [
  ("rax", .rax, 64), ("rcx", .rcx, 64), ("rdx", .rdx, 64), ("rbx", .rbx, 64),
  ("rsp", .rsp, 64), ("rbp", .rbp, 64), ("rsi", .rsi, 64), ("rdi", .rdi, 64),
  ("r8", .r8, 64), ("r9", .r9, 64), ("r10", .r10, 64), ("r11", .r11, 64),
  ("r12", .r12, 64), ("r13", .r13, 64), ("r14", .r14, 64), ("r15", .r15, 64),
  ("eax", .rax, 32), ("ecx", .rcx, 32), ("edx", .rdx, 32), ("ebx", .rbx, 32),
  ("esp", .rsp, 32), ("ebp", .rbp, 32), ("esi", .rsi, 32), ("edi", .rdi, 32),
  ("r8d", .r8, 32), ("r9d", .r9, 32), ("r10d", .r10, 32), ("r11d", .r11, 32),
  ("r12d", .r12, 32), ("r13d", .r13, 32), ("r14d", .r14, 32), ("r15d", .r15, 32),
  ("ax", .rax, 16), ("cx", .rcx, 16), ("dx", .rdx, 16), ("bx", .rbx, 16),
  ("sp", .rsp, 16), ("bp", .rbp, 16), ("si", .rsi, 16), ("di", .rdi, 16),
  ("r8w", .r8, 16), ("r9w", .r9, 16), ("r10w", .r10, 16), ("r11w", .r11, 16),
  ("r12w", .r12, 16), ("r13w", .r13, 16), ("r14w", .r14, 16), ("r15w", .r15, 16),
  ("al", .rax, 8), ("cl", .rcx, 8), ("dl", .rdx, 8), ("bl", .rbx, 8),
  ("spl", .rsp, 8), ("bpl", .rbp, 8), ("sil", .rsi, 8), ("dil", .rdi, 8),
  ("r8b", .r8, 8), ("r9b", .r9, 8), ("r10b", .r10, 8), ("r11b", .r11, 8),
  ("r12b", .r12, 8), ("r13b", .r13, 8), ("r14b", .r14, 8), ("r15b", .r15, 8)]

def reg? (s : String) : Option (Reg × Nat) :=
  (registers.find? (fun x => x.1 == s)).map (·.2)

def regName (r : Reg) (bits : Nat) : String :=
  ((registers.find? (fun x => x.2.1 == r && x.2.2 == bits)).map (·.1)).getD "?"

def flushToken (chars : List Char) (tokens : List String) : List String :=
  if chars.isEmpty then tokens else String.ofList chars.reverse :: tokens

def tokenizeChars : List Char → List Char → List String → List String
  | [], chars, tokens => (flushToken chars tokens).reverse
  | c :: cs, chars, tokens =>
    if c = ' ' || c = '\t' || c = '\r' then
      tokenizeChars cs [] (flushToken chars tokens)
    else if [',', '[', ']', '+', '-', '*'].contains c then
      tokenizeChars cs [] (String.ofList [c] :: flushToken chars tokens)
    else tokenizeChars cs (c :: chars) tokens

def tokenize (s : String) : List String := tokenizeChars s.toList [] []

/-- Structural splitting keeps closed parsing obligations reducible in the kernel.
The standard list/string splitters in the pinned toolchain do not expose all bodies. -/
def splitAux {α : Type} [BEq α] (separator : α) :
    List α → List α → List (List α) → List (List α)
  | [], chunk, chunks => (chunk.reverse :: chunks).reverse
  | x :: xs, chunk, chunks =>
    if x == separator then splitAux separator xs [] (chunk.reverse :: chunks)
    else splitAux separator xs (x :: chunk) chunks

def split {α : Type} [BEq α] (separator : α) (xs : List α) : List (List α) :=
  splitAux separator xs [] []

def natural (s : String) : Except String Nat := do
  let (radix, chars) := match s.toList with
    | '0' :: 'x' :: cs => (16, cs)
    | cs => (10, cs)
  if chars.isEmpty then throw "empty integer"
  chars.foldlM (fun n c => do
    let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else radix
    if d ≥ radix then throw s!"invalid integer: {s}"
    return radix * n + d) 0

def integer : List String → Except String Int
  | ["-", n] => return -(Int.ofNat (← natural n))
  | ["+", n] | [n] => return Int.ofNat (← natural n)
  | _ => throw "expected one integer"

def bits (width : Nat) (n : Int) (signedOnly : Bool := false) :
    Except String (BitVec width) := do
  let low := -(Int.ofNat (2 ^ (width - 1)))
  let high := if signedOnly then Int.ofNat (2 ^ (width - 1)) else Int.ofNat (2 ^ width)
  if n < low || high ≤ n then throw s!"integer {n} is outside the {width}-bit range"
  return BitVec.ofInt width n

def wideSize : Nat → Except String Sz
  | 32 => .ok .d | 64 => .ok .q
  | _ => .error "expected a 32-bit or 64-bit operand"

def size? : String → Option Nat
  | "byte" => some 8 | "word" => some 16 | "dword" => some 32 | "qword" => some 64
  | _ => none

def sizeName : Nat → String
  | 8 => "byte" | 16 => "word" | 32 => "dword" | _ => "qword"

def addressReg (s : String) : Except String Reg :=
  match reg? s with
  | some (r, 64) => .ok r
  | _ => .error s!"expected a 64-bit address register, got {s}"

def indexReg (s : String) (scale : String) : Except String Index := do
  let r ← addressReg s
  if h : r = .rsp then throw "rsp cannot be an index register"
  else
    let scale ← match scale with
      | "1" => pure (0#2) | "2" => pure (1#2)
      | "4" => pure (2#2) | "8" => pure (3#2)
      | _ => throw "index scale must be 1, 2, 4 or 8"
    return ⟨r, scale, h⟩

def displacement (ts : List String) : Except String (BitVec 32) := do
  if ts.isEmpty then return 0
  if !(ts.head! == "+" || ts.head! == "-") then
    throw "memory displacement requires + or -"
  let n ← integer ts
  bits 32 n true

def memory (ts : List String) : Except String Mem := do
  match ts with
  | base :: "+" :: idx :: "*" :: scale :: rest =>
    let b ← addressReg base
    let i ← indexReg idx scale
    return Mem.ofReg b (some i) (← displacement rest)
  | base :: "+" :: idx :: rest =>
    if (reg? idx).isSome then
      let b ← addressReg base
      let i ← indexReg idx "1"
      return Mem.ofReg b (some i) (← displacement rest)
    else
      return Mem.ofReg (← addressReg base) none (← displacement ("+" :: idx :: rest))
  | base :: rest =>
    return Mem.ofReg (← addressReg base) none (← displacement rest)
  | _ => throw "expected a base register inside brackets"

inductive Operand where
  | reg (r : Reg) (width : Nat)
  | mem (m : Mem) (width : Nat)
  | imm (n : Int) (width : Nat)

def operand (ts : List String) : Except String Operand := do
  match ts with
  | [r] =>
    match reg? r with
    | some (r, w) => return .reg r w
    | none => throw s!"unsupported register or missing immediate width: {r}"
  | "imm8" :: rest => return .imm (← integer rest) 8
  | "imm32" :: rest => return .imm (← integer rest) 32
  | size :: "ptr" :: "[" :: rest =>
    let some width := size? size | throw "expected byte/word/dword/qword ptr"
    let rev := rest.reverse
    let "]" :: rev := rev | throw "missing closing bracket"
    return .mem (← memory rev.reverse) width
  | _ => throw "unsupported operand; memory requires an explicit size"

def asRM : Operand → Except String (RM × Nat)
  | .reg r w => .ok (.reg r, w) | .mem m w => .ok (.mem m, w)
  | _ => .error "expected register or memory"

def sameWidth (a b : Nat) : Except String Unit :=
  if a = b then .ok () else .error "operand widths differ"

def alu? : String → Option AluOp
  | "add" => some .add | "or" => some .or | "and" => some .and
  | "sub" => some .sub | "xor" => some .xor | "cmp" => some .cmp | _ => none

def aluName : AluOp → String
  | .add => "add" | .or => "or" | .and => "and" | .sub => "sub" | .xor => "xor"
  | .cmp => "cmp"

def condition? : String → Option Cond
  | "jo" => some .o | "jno" => some .no | "jb" => some .b | "jae" => some .ae
  | "je" => some .e | "jne" => some .ne | "jbe" => some .be | "ja" => some .a
  | "js" => some .s | "jns" => some .ns | "jp" => some .p | "jnp" => some .np
  | "jl" => some .l | "jge" => some .ge | "jle" => some .le | "jg" => some .g
  | _ => none

def conditionName : Cond → String
  | .o => "jo" | .no => "jno" | .b => "jb" | .ae => "jae"
  | .e => "je" | .ne => "jne" | .be => "jbe" | .a => "ja"
  | .s => "js" | .ns => "jns" | .p => "jp" | .np => "jnp"
  | .l => "jl" | .ge => "jge" | .le => "jle" | .g => "jg"

def shift? : String → Option ShiftOp
  | "rol" => some .rol | "ror" => some .ror | "shl" => some .shl
  | "shr" => some .shr | "sar" => some .sar | _ => none

def shiftName : ShiftOp → String
  | .rol => "rol" | .ror => "ror" | .shl => "shl" | .shr => "shr" | .sar => "sar"

def binary (mnemonic : String) (lhs rhs : List String) : Except String Ext.Instr := do
  let a ← operand lhs
  let b ← operand rhs
  if mnemonic = "mov" then
    match a, b with
    | .reg d 8, .reg s 8 => return .mov8 d (.reg s)
    | .reg d 8, .mem s 8 => return .mov8 d (.mem s)
    | .mem d 8, .reg s 8 => return .store .b (.mem d) s
    | .mem d 16, .reg s 16 => return .store .w (.mem d) s
    | .reg d w, .mem s v =>
      sameWidth w v
      return .load (← wideSize w) d s
    | .reg d 32, .imm n 32 => return .movI32 d (← bits 32 n)
    | dst, .reg s v =>
      let (d, w) ← asRM dst
      sameWidth w v
      return .mov (← wideSize w) d s
    | dst, .imm n 32 =>
      let (d, w) ← asRM dst
      return .movI (← wideSize w) d (← bits 32 n)
    | _, _ => throw "unsupported mov operands"
  else if mnemonic = "imul" then
    let .reg dst width := a | throw "imul destination must be a register"
    let (src, sourceWidth) ← asRM b
    sameWidth width sourceWidth
    return .imul (← wideSize width) dst src
  else if let some op := alu? mnemonic then
    match a, b with
    | .reg d w, .mem s v =>
      sameWidth w v
      return .aluR (← wideSize w) op d (.mem s)
    | dst, .reg s v =>
      let (d, w) ← asRM dst
      sameWidth w v
      return .alu (← wideSize w) op d s
    | dst, .imm n 8 =>
      let (d, w) ← asRM dst
      return .aluI8 (← wideSize w) op d (← bits 8 n)
    | dst, .imm n 32 =>
      let (d, w) ← asRM dst
      return .aluI (← wideSize w) op d (← bits 32 n)
    | _, _ => throw "unsupported arithmetic operands"
  else throw s!"unsupported binary instruction: {mnemonic}"

def parseLine (ts : List String) : Except String Ext.Instr := do
  match ts with
  | ["ret"] => return .ret
  | ["leave"] => return .leave
  | ["endbr64"] => return .endbr64
  | ["ud2"] => return .ud2
  | ["push", r] => return .push (← addressReg r)
  | ["pop", r] => return .pop (← addressReg r)
  | "call" :: "rel32" :: rel => return .call (← bits 32 (← integer rel) true)
  | "jmp" :: "near" :: rel => return .jmp (← bits 32 (← integer rel) true)
  | "jmp" :: "short" :: rel => return .jmp8 (← bits 8 (← integer rel) true)
  | mnemonic :: rest =>
    if let some c := condition? mnemonic then
      match rest with
      | "near" :: rel => return .jcc c (← bits 32 (← integer rel) true)
      | "short" :: rel => return .jcc8 c (← bits 8 (← integer rel) true)
      | _ => throw "conditional jump requires short or near and a displacement"
    let parts := split "," rest
    let [lhs, rhs] := parts | throw "expected two operands separated by a comma"
    if let some op := shift? mnemonic then
      let (d, w) ← asRM (← operand lhs)
      let sz ← wideSize w
      match rhs with
      | ["cl"] => return .shift sz op d .cl
      | ["one"] => return .shift sz op d .one
      | "imm8" :: n => return .shift sz op d (.imm (← bits 8 (← integer n)))
      | _ => throw "shift count must be cl, one, or imm8 INTEGER"
    binary mnemonic lhs rhs
  | _ => throw "expected an instruction"

/-- Parse a newline-separated, destination-first listing. Semicolons start comments.
Identifiers are lowercase. There are no labels, directives, relocations or implicit
instruction-size choices. Invalid ranges are rejected before bit-vector conversion. -/
def parse (source : String) : Except String (List Ext.Instr) := do
  let mut result := []
  let mut line := 0
  for chars in split '\n' source.toList do
    line := line + 1
    let tokens := tokenizeChars (chars.takeWhile (· != ';')) [] []
    if !tokens.isEmpty then
      match parseLine tokens with
      | .ok i => result := i :: result
      | .error message => throw s!"line {line}: {message}"
  return result.reverse

def formatMem (m : Mem) (width : Nat) : Option String := do
  let .reg base := m.base | none
  let mut addr := regName base 64
  if let some idx := m.index then
    addr := addr ++ " + " ++ regName idx.reg 64
    if idx.scale.toNat != 0 then addr := addr ++ s!" * {2 ^ idx.scale.toNat}"
  let disp := m.disp.toInt
  if disp < 0 then addr := addr ++ s!" - {-disp}"
  else if disp > 0 then addr := addr ++ s!" + {disp}"
  return s!"{sizeName width} ptr [{addr}]"

def formatRM (r : RM) (width : Nat) : Option String :=
  match r with
  | .reg r => some (regName r width)
  | .mem m => formatMem m width

/-- Print supported instructions as input to `parse` and `x86%`.
`none` means this prototype has no lossless spelling for the instruction. -/
def format (i : Ext.Instr) : Option String := do
  match i with
  | .mov sz dst src => return s!"mov {← formatRM dst sz.bits}, {regName src sz.bits}"
  | .load sz dst src => return s!"mov {regName dst sz.bits}, {← formatMem src sz.bits}"
  | .mov8 dst src => return s!"mov {regName dst 8}, {← formatRM src 8}"
  | .store n (.mem dst) src => return s!"mov {← formatMem dst n.bits}, {regName src n.bits}"
  | .movI sz dst imm =>
    -- Register imm32 MOV has a different opcode, represented by `movI32`.
    if sz = .d then
      if let .reg _ := dst then none
      else return s!"mov {← formatRM dst sz.bits}, imm32 {imm.toInt}"
    else return s!"mov {← formatRM dst sz.bits}, imm32 {imm.toInt}"
  | .movI32 dst imm => return s!"mov {regName dst 32}, imm32 {imm.toNat}"
  | .alu sz op dst src =>
    return s!"{aluName op} {← formatRM dst sz.bits}, {regName src sz.bits}"
  | .aluR sz op dst (.mem src) =>
    return s!"{aluName op} {regName dst sz.bits}, {← formatMem src sz.bits}"
  | .aluI sz op dst imm =>
    return s!"{aluName op} {← formatRM dst sz.bits}, imm32 {imm.toInt}"
  | .aluI8 sz op dst imm =>
    return s!"{aluName op} {← formatRM dst sz.bits}, imm8 {imm.toInt}"
  | .imul sz dst src =>
    return s!"imul {regName dst sz.bits}, {← formatRM src sz.bits}"
  | .shift sz op dst count =>
    let count := match count with
      | .cl => "cl" | .one => "one" | .imm n => s!"imm8 {n.toNat}"
    return s!"{shiftName op} {← formatRM dst sz.bits}, {count}"
  | .call rel => return s!"call rel32 {rel.toInt}"
  | .jmp rel => return s!"jmp near {rel.toInt}"
  | .jmp8 rel => return s!"jmp short {rel.toInt}"
  | .jcc c rel => return s!"{conditionName c} near {rel.toInt}"
  | .jcc8 c rel => return s!"{conditionName c} short {rel.toInt}"
  | .push r => return s!"push {regName r 64}"
  | .pop r => return s!"pop {regName r 64}"
  | .ret => return "ret"
  | .leave => return "leave"
  | .endbr64 => return "endbr64"
  | .ud2 => return "ud2"
  | _ => none

end Silmaril.X86.Assembly
