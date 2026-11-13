module
public import Silmaril.Compiler.Native.Asm.Defs
public import Silmaril.Compiler.Native.Emit.Prologue.Defs
public import Silmaril.Compiler.Native.X87.Asm.Defs
public import Silmaril.Compiler.Native.Abi.Defs
public import Silmaril.Compiler.Native.Optimize.Defs
public import Silmaril.Compiler.Native.Types.Registered.Defs
public import Silmaril.Compiler.Native.Varargs.Defs
/-! Native SysV emission before symbol resolution. GNU as and the system linker
resolve real code/data addresses. ABI classification is shared with the formal
type/FFI layer. This emitter remains a trusted executable stage. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit
open Silmaril.Compile
open Silmaril.Machine
open Silmaril.Machine.SystemV.Abi

def aggregate : C.CType → Bool | .agg _ => true | _ => false

def normalize : C.CType → String
  | .int 1 true => Asm.unary .sext8 | .int 2 true => Asm.unary .sext16
  | .int 4 true => Asm.unary .sext32 | .int 1 false | .bool => Asm.unary .zext8
  | .int 2 false => Asm.unary .zext16
  | .int 4 false | .float 4 => Asm.unary .zext32
  | _ => ""

abbrev resultObject := Abi.Planning.resultObject
abbrev functionPlan := Abi.Planning.functionPlan
abbrev callPlan := Abi.Planning.callPlan

def gp : Silmaril.X86.Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- Read exactly the represented bytes, without touching aggregate tail padding. -/
def chunkLoad (offset bytes : Nat) : String := Id.run do
  let mut text := "  xor r11d, r11d\n"
  for i in (List.range bytes).reverse do
    text := text ++ s!"  shl r11, 8\n  mov r11b, BYTE PTR [r10 + {offset + i}]\n"
  return text

def chunkStore (offset bytes : Nat) : String := Id.run do
  let mut text := ""
  for i in [0:bytes] do
    text := text ++ s!"  mov BYTE PTR [r10 + {offset + i}], r11b\n"
    if i + 1 < bytes then text := text ++ "  shr r11, 8\n"
  return text

def fromLocation : Location → Except String String
  | .gp r => return s!"  mov r11, {gp r}\n"
  | .vector i 0 => return s!"  movq r11, xmm{i}\n"
  | .vector i 8 => return s!"  movdqa xmm15, xmm{i}\n  psrldq xmm15, 8\n  movq r11, xmm15\n"
  | .vector _ _ => .error "native wide-vector instruction selection remains pending"
  | .x87 _ => .error "x87 values require the extended native value representation"

def toLocation : Location → Except String String
  | .gp r => return s!"  mov {gp r}, r11\n"
  | .vector i 0 => return s!"  movq xmm{i}, r11\n"
  | .vector i 8 => return s!"  movq xmm15, r11\n  pslldq xmm15, 8\n  por xmm{i}, xmm15\n"
  | .vector _ _ => .error "native wide-vector instruction selection remains pending"
  | .x87 _ => .error "x87 values require the extended native value representation"

def memoryToChunks (chunks : List Chunk) : Except String String := do
  let mut text := ""
  for chunk in chunks do
    if let .x87 _ := chunk.location then
      pure ()
    else text := text ++ chunkLoad chunk.offset chunk.bytes ++ (← toLocation chunk.location)
  -- Push imaginary before real so a complex result has real in ST(0).
  for chunk in chunks.reverse do
    if let .x87 _ := chunk.location then
      text := text ++ s!"  fld TBYTE PTR [r10 + {chunk.offset}]\n"
  return text

def chunksToMemory (chunks : List Chunk) : Except String String := do
  let mut text := ""
  for chunk in chunks do
    if let .x87 _ := chunk.location then
      text := text ++ s!"  fstp TBYTE PTR [r10 + {chunk.offset}]\n"
    else text := text ++ (← fromLocation chunk.location) ++ chunkStore chunk.offset chunk.bytes
  return text

/-- The lowerer's three explicit C runtime helpers have fixed signatures.
Every source-level call must carry its own metadata; guessing an INTEGER-only
signature could silently corrupt a floating-point or aggregate call. -/
def runtimeCall (name : String) (args results : List Nat) : Except String CallInfo := do
  let pointer := C.CType.ptr (.mk [] .void)
  let (arguments, result, resultCount) ← match name with
    | "memcpy" => pure ([pointer, pointer, .int 8 false], pointer, 1)
    | "memset" => pure ([pointer, .int 4 true, .int 8 false], pointer, 1)
    | "abort" => pure ([], C.CType.void, 0)
    | _ => throw s!"missing native call signature for {name}"
  unless args.length == arguments.length && results.length == resultCount do
    throw s!"native runtime operand/signature mismatch for {name}"
  return {
    key := name
    callee := name
    indirectTarget := none
    arguments := arguments
    result := result
    namedCount := args.length
    variadic := false
    tags := ∅ }

def emitCall (info : CallInfo) (operands results : List Nat) : Except String String := do
  let plan ← callPlan info
  let indirect := info.indirectTarget.isSome
  let indirectRegister := if indirect then operands.head? else none
  let operands := if indirect then operands.drop 1 else operands
  let resultArea := if aggregate info.result then operands.head? else none
  let args := if aggregate info.result then operands.drop 1 else operands
  unless args.length == plan.arguments.length do throw "native call operand/signature mismatch"
  let mut text := if plan.stackSize == 0 then "" else s!"  sub rsp, {plan.stackSize}\n"
  -- Copy stack aggregates before assigning argument registers: REP uses RSI/RDI/RCX.
  for ((arg, type), r) in (plan.arguments.zip info.arguments).zip args do
    if let some offset := arg.stackOffset then
      if aggregate type then
        text := text ++ Asm.read r "rsi" ++
          s!"  lea rdi, [rsp + {offset}]\n  mov rcx, {arg.object.size}\n  rep movsb\n"
      else
        text := text ++ Asm.read r "r11" ++ s!"  mov QWORD PTR [rsp + {offset}], r11\n"
  if let .indirect .. := plan.result then
    let some area := resultArea | throw "missing native sret destination"
    text := text ++ Asm.read area "rdi"
  for ((arg, type), r) in (plan.arguments.zip info.arguments).zip args do
    if arg.stackOffset.isNone then
      if aggregate type then
        text := text ++ Asm.read r "r10" ++ (← memoryToChunks arg.chunks)
      else
        let [chunk] := arg.chunks | throw "scalar ABI argument requires one chunk"
        text := text ++ Asm.read r "r11" ++ (← toLocation chunk.location)
  if let some count := plan.variadicAL then text := text ++ s!"  mov eax, {count}\n"
  if indirect then
    let some target := indirectRegister
      | throw "missing native indirect-call target"
    -- The caller's original operand list carries the target before ABI arguments.
    text := text ++ Asm.read target "r11" ++ "  call r11\n"
  else text := text ++ s!"  call {Asm.symbol info.callee}\n"
  if plan.stackSize != 0 then text := text ++ s!"  add rsp, {plan.stackSize}\n"
  if let some area := resultArea then
    if let .direct chunks := plan.result then
      text := text ++ Asm.read area "r10" ++ (← chunksToMemory chunks)
  else if let some r := results.head? then
    let .direct [chunk] := plan.result | throw "native scalar return requires one chunk"
    text := text ++ (← fromLocation chunk.location) ++ "  mov rax, r11\n" ++
      normalize info.result ++ Asm.write r
  return text

structure Frame where
  bytes : Nat
  alignment : Nat
  parameterTemps : List Nat
  resultTemp : Nat

def frame (fn : Mir.Func) (info : FunctionInfo) (plan : CallPlan) : Frame := Id.run do
  let mut size := info.frameBytes
  let mut temps := []
  for (arg, type) in plan.arguments.zip info.signature.params do
    if aggregate (Types.Registered.ofCtype info.tags type) && arg.stackOffset.isNone then
      size := alignUp size arg.object.align
      temps := temps ++ [size]
      size := size + arg.object.size
    else temps := temps ++ [0]
  let resultTemp := alignUp size 16
  if aggregate info.signature.ret then
    if let .direct _ := plan.result then
      match resultObject info.tags info.signature.ret with
      | .ok (some object) => size := resultTemp + object.size
      | _ => pure ()
  let bytes := alignUp (size + 8 * Optimize.freshBase fn) 16
  return ⟨bytes, max 64 info.frameAlign, temps, resultTemp⟩

def entry (fn : Mir.Func) (info : FunctionInfo) (plan : CallPlan) (fr : Frame) : Except String String := do
  let hidden := aggregate info.signature.ret
  let params := if hidden then fn.params.drop 1 else fn.params
  unless params.length == plan.arguments.length do throw "native function parameter/signature mismatch"
  let mut text := ""
  if let some save := info.vaSaveOffset then
    unless info.signature.variadic && save + Varargs.saveBytes ≤ info.frameBytes do
      throw "invalid native variadic register-save area"
    -- Save before entry adaptation can overwrite a caller argument register.
    -- Saving all eight XMM registers is allowed independently of the AL bound.
    for (register, index) in gpArguments.zipIdx do
      text := text ++ s!"  mov QWORD PTR [rsp + {save + 8 * index}], {gp register}\n"
    for index in [0:8] do
      text := text ++ s!"  movdqu XMMWORD PTR [rsp + {save + 48 + 16 * index}], xmm{index}\n"
  if hidden then
    let some r := fn.params.head? | throw "missing internal aggregate result parameter"
    match plan.result with
    | .indirect .. => text := text ++ Asm.write r "rdi"
    | .direct _ => text := text ++ s!"  lea rax, [rsp + {fr.resultTemp}]\n" ++ Asm.write r
    | .void => throw "aggregate with void ABI result"
  for (((arg, type), r), temp) in ((plan.arguments.zip info.signature.params).zip params).zip fr.parameterTemps do
    let type := Types.Registered.ofCtype info.tags type
    if aggregate type then
      if let some off := arg.stackOffset then
        text := text ++ s!"  lea rax, [rbp + {16 + off}]\n" ++ Asm.write r
      else
        text := text ++ s!"  lea r10, [rsp + {temp}]\n" ++ (← chunksToMemory arg.chunks) ++
          "  mov rax, r10\n" ++ Asm.write r
    else
      if let some off := arg.stackOffset then
        let width := match arg.object.size with
          | 1 => Lir.Width.b1 | 2 => .b2 | 4 => .b4 | _ => .b8
        text := text ++ "  mov r10, rbp\n" ++ Asm.load width .zero (16 + off)
      else
        let [chunk] := arg.chunks | throw "native scalar parameter requires one chunk"
        text := text ++ (← fromLocation chunk.location) ++ "  mov rax, r11\n"
      text := text ++ normalize type ++ Asm.write r
  return text

def label (unit function block : Nat) : String := s!".Lccomp.{unit}.{function}.{block}"

def terminator (unit function : Nat) (fn : Mir.Func) (info : FunctionInfo)
    (plan : CallPlan) : Lir.Term Nat → Except String String
  | .jump target => return s!"  jmp {label unit function target}\n"
  | .branch r yes no => return Asm.read r ++
      s!"  test rax, rax\n  jne {label unit function yes}\n  jmp {label unit function no}\n"
  | .trap => return "  ud2\n"
  | .ret values => do
    let mut text := ""
    if aggregate info.signature.ret then
      let some r := fn.params.head? | throw "missing aggregate result parameter"
      text := text ++ Asm.read r "r10"
      match plan.result with
      | .direct chunks => text := text ++ (← memoryToChunks chunks)
      | .indirect .. => text := text ++ "  mov rax, r10\n"
      | .void => throw "aggregate with void ABI result"
    else if let some (.reg r) := values.head? then
      text := text ++ Asm.read r
      if let .float _ := info.signature.ret then text := text ++ "  movq xmm0, rax\n"
    return text ++ "  leave\n  ret\n"

def function (unit index : Nat) (artifact : Artifact) (fn : Mir.Func) : Except String String := do
  let some info := artifact.functions.find? (·.name == fn.name)
    | throw s!"missing native signature for {fn.name}"
  let plan ← functionPlan info
  let fr := frame fn info plan
  let alignment ← artifact.calls.foldlM (fun alignment call => do
    return max alignment (← callPlan call).stackAlign) fr.alignment
  let mut text := ".text\n" ++ (if fn.exported then s!".globl {Asm.symbol fn.name}\n" else "") ++
    (if fn.weak then s!".weak {Asm.symbol fn.name}\n" else "") ++
    s!".type {Asm.symbol fn.name}, @function\n{Asm.symbol fn.name}:\n" ++
    (Prologue.Plan.mk fr.bytes alignment).render ++ (← entry fn info plan fr)
  for (block, b) in fn.blocks.toList.zipIdx do
    text := text ++ s!"{label unit index b}:\n"
    for instr in block.instrs do
      text := text ++ (← match instr with
        | .op op => Asm.operation op
        | .fop op d a b => pure (Asm.floating op d a b)
        | .addr d "__ccomp_frame" _ => pure (Prologue.renderFrame d)
        | .addr d "__ccomp_va_overflow" offset => do
          unless info.signature.variadic && offset == 0 do
            throw "native va_start overflow address outside a variadic function"
          pure (s!"  lea rax, [rbp + {16 + Varargs.namedStackEnd plan}]\n" ++ Asm.write d)
        | .addr d sym off => pure (s!"  lea rax, [rip + {Asm.symbol sym} + {off}]\n" ++ Asm.write d)
        | .call sym args results =>
          match artifact.intrinsics.find? (·.key == sym) with
          | some intrinsic => X87.Asm.emit intrinsic.operation args results
          | none =>
            match artifact.calls.find? (·.key == sym) with
            | some call => emitCall call args results
            | none => do emitCall (← runtimeCall sym args results) args results
        | .callIndirect .. => throw "untyped native indirect call")
    text := text ++ (← terminator unit index fn info plan block.term)
  return text ++ s!".size {Asm.symbol fn.name}, . - {Asm.symbol fn.name}\n"

def data (object : Mir.Data) : Except String String := do
  let mut text := (if object.readonly then ".section .rodata\n" else ".data\n") ++
    (if object.exported then s!".globl {Asm.symbol object.name}\n" else "") ++
    (if object.weak then s!".weak {Asm.symbol object.name}\n" else "") ++
    s!".balign {max 1 object.align}\n.type {Asm.symbol object.name}, @object\n{Asm.symbol object.name}:\n"
  let mut pos := 0
  for reloc in object.relocs.mergeSort (fun a b => a.offset ≤ b.offset) do
    if reloc.offset < pos || reloc.offset + 8 > object.size then throw "invalid native data relocation"
    if reloc.offset > pos then
      let bytes := (List.range (reloc.offset - pos)).map fun i => (object.init[pos + i]?.getD 0).toNat
      text := text ++ "  .byte " ++ ",".intercalate (bytes.map toString) ++ "\n"
    text := text ++ s!"  .quad {Asm.symbol reloc.sym} + {reloc.addend}\n"
    pos := reloc.offset + 8
  let initialized := min object.init.size object.size
  if pos < initialized then
    text := text ++ "  .byte " ++ ",".intercalate ((List.range (initialized - pos)).map
      fun i => toString object.init[pos + i]!.toNat) ++ "\n"
    pos := initialized
  if pos < object.size then text := text ++ s!"  .zero {object.size - pos}\n"
  return text ++ s!".size {Asm.symbol object.name}, {object.size}\n"

def emit (artifacts : Array Artifact) : Except String String := do
  let mut text := ".intel_syntax noprefix\n"
  for (artifact, unit) in artifacts.toList.zipIdx do
    for (fn, index) in artifact.mir.funcs.toList.zipIdx do
      text := text ++ (← function unit index artifact fn)
    for object in artifact.mir.data do text := text ++ (← data object)
  return text ++ ".section .note.GNU-stack,\"\",@progbits\n"

end Silmaril.Compiler.Native.Emit
