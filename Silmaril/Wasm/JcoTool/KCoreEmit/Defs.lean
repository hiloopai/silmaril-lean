module

public import Silmaril.Wasm.JcoTool.KCore.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax
public import Silmaril.Wasm.Binaryen.Toolkit.WatRender
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer

/-!
# The generated stream modules as Core 3.0 modules: bytes and text with theorems

`Silmaril.Wasm.JcoTool.KCore` generates, from a byte kernel, a program `Prog` of a small fragment
of WebAssembly (`E`, `S`) and prints it as WebAssembly text (`Prog.wat`). Until now the bytes
given to `wasm-jco new` were `wasm-tools parse` of that text, and nothing linked them to the
generator. This module closes the emission side of that gap:

* **`toModule P name`**: the program as a module of silmaril's Core 3.0 AST
  (`Silmaril.Wasm.Module`), one instruction sequence per construct, with the same imports,
  memory, globals, functions and exports as `Prog.wat` (types listed in order of first use,
  as a text parser assigns them).
* **`wasmOf P name`**: its bytes, by silmaril's verified encoder `Binaryen.Exe.encodeModule?`
  (theorem `wasmOf_encodes`: the bytes encode `toModule P name` in the Core binary grammar,
  which is functional, so they encode nothing else).
* **`watOf P name`**: its text, by silmaril's checked printer (`Wat.moduleSyntax?`, then
  `renderWatDocument?`; theorem `watOf_encodes`: the text denotes `toModule P name` in the
  Core text grammar `Text.Core.Encodes`).
* **`watChecked P name`**: the original printer's text `Prog.wat`, accepted only when
  silmaril's sound WAT parser reads it as a module whose canonical encoding is the bytes
  `wasmOf P name` (theorem `watChecked_encodes`: the accepted text denotes `toModule P name`,
  so the printer `Prog.wat` is correct on every output the tool writes; translation
  validation, not a proof for all programs).

`wasm-jco kcore NAME KERNEL N` prints `watChecked` (refusing an output that fails the
check), and `wasm-jco kcore NAME KERNEL N -o OUT.wasm` writes `wasmOf`: the bytes the tests
give to `wasm-jco new` are now the verified encoding of `toModule (gen k N) name`.

What remains: that `toModule P name` *behaves*, under the Core 3.0 semantics, as `exec` says
(the realise part of `docs/projects/wasm-components.md`); this module only fixes which module
the bytes and the text are.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreEmit

open Silmaril.Wasm
open Silmaril.Wasm.JcoTool.KCore

/-! ## Indices and constants -/

/-- An index of any kind (taken modulo `2 ^ 32`). -/
def ix {k : IndexKind} (n : Nat) : Idx k := ⟨Fin.ofNat _ n⟩

def i32 : ValType := .num (.int .i32)
def i64 : ValType := .num (.int .i64)

/-- `i32.const n` (modulo `2 ^ 32`). -/
def c32 (n : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 n)

/-- The memory argument of `i32.load8_u` / `i32.store8` without immediates in the text:
alignment `2 ^ 0`, offset `0`. -/
def ma0 : MemArg := ⟨0, 0⟩

/-! ## Instructions -/

def binInstr : Bin → Instr
  | .add => .intBinOp .i32 .add
  | .sub => .intBinOp .i32 .sub
  | .eq => .intRelOp .i32 .eq
  | .ne => .intRelOp .i32 .ne
  | .ltu => .intRelOp .i32 (.lt .unsigned)
  | .geu => .intRelOp .i32 (.ge .unsigned)
  | .divu => .intBinOp .i32 (.div .unsigned)
  | .remu => .intBinOp .i32 (.rem .unsigned)
  | .shl => .intBinOp .i32 .shl

/-- An expression, unfolded: its operands, then its operator. -/
def eCode : E → List Instr
  | .c n => [c32 n]
  | .l i => [.localGet (ix i)]
  | .g i => [.globalGet (ix i)]
  | .bin o a b => eCode a ++ eCode b ++ [binInstr o]
  | .eqz a => eCode a ++ [.intTestOp .i32 .eqz]
  | .ld8 a => eCode a ++ [.intLoad .i32 (some (.i8, .unsigned)) (ix 0) ma0]

/-- The function indices of the imported built-ins, in the order `Prog.wat` imports them. -/
def biFn : BI → Nat
  | .taskReturn => 0
  | .streamNew => 1
  | .streamRead => 2
  | .streamWrite => 3
  | .dropR => 4
  | .dropW => 5
  | .wsNew => 6
  | .join => 7

/-- A built-in call, as `KCore.callWat` prints it. -/
def callCode (b : BI) (as : List (List Instr)) (d : List Nat) : List Instr :=
  match b, d with
  | .streamNew, [d₁, d₂] =>
    [.call (ix (biFn b)), .localSet (ix L64),
      .localGet (ix L64), .convert .wrap, .localSet (ix d₁),
      .localGet (ix L64), .intConst .i64 (BitVec.ofNat 64 32), .intBinOp .i64 (.shr .unsigned),
      .convert .wrap, .localSet (ix d₂)]
  | .streamRead, [d] => as.flatten ++ [.call (ix (biFn b)), .localSet (ix d)]
  | .streamWrite, [d] => as.flatten ++ [.call (ix (biFn b)), .localSet (ix d)]
  | .dropR, _ => as.flatten ++ [.call (ix (biFn b))]
  | .dropW, _ => as.flatten ++ [.call (ix (biFn b))]
  | .wsNew, [d] => [.call (ix (biFn b)), .localSet (ix d)]
  | .join, _ => as.flatten ++ [.call (ix (biFn b))]
  | .taskReturn, _ => as.flatten ++ [.call (ix (biFn b))]
  | _, _ => [.unreachable]

/-- A statement, unfolded. `if` and the blocks have the empty block type. -/
def sCode : S → List Instr
  | .nop => [.nop]
  | .unreachable => [.unreachable]
  | .lset i e => eCode e ++ [.localSet (ix i)]
  | .gset i e => eCode e ++ [.globalSet (ix i)]
  | .st8 a v => eCode a ++ eCode v ++ [.intStore .i32 (some .i8) (ix 0) ma0]
  | .mcopy d s n => eCode d ++ eCode s ++ eCode n ++ [.memoryCopy (ix 0) (ix 0)]
  | .seq a b => sCode a ++ sCode b
  | .ite c t f => eCode c ++ [.if_ .empty (sCode t) (sCode f)]
  | .block b => [.block .empty (sCode b)]
  | .loop b => [.loop .empty (sCode b)]
  | .br k => [.br (ix k)]
  | .brIf k c => eCode c ++ [.brIf (ix k)]
  | .ret e => eCode e ++ [.return_]
  | .call b as d => callCode b (as.map eCode) d

/-! ## The module -/

/-- A function type as a type-section entry. -/
def fty (ps rs : List ValType) : RecType := ⟨[⟨true, [], .func ⟨ps, rs⟩⟩]⟩

/-- The function types, in order of first use in `Prog.wat`. -/
def types : List RecType :=
  [fty [i32] [],                        -- 0: task.return, the drops
   fty [] [i64],                        -- 1: stream.new
   fty [i32, i32, i32] [i32],           -- 2: stream.read, stream.write, the callback
   fty [] [i32],                        -- 3: waitable-set.new
   fty [i32, i32] [],                   -- 4: waitable.join
   fty [i32, i32, i32, i32] [i32],      -- 5: cabi_realloc
   fty [i32] [i32]]                     -- 6: the lift

def imp (mn nm : String) (t : Nat) : Import := ⟨mn, nm, .func (ix t)⟩

/-- The imports of `Prog.wat`. -/
def imports (name : String) : List Import :=
  [imp "[export]$root" s!"[task-return]{name}" 0,
   imp "[export]$root" s!"[stream-new-0]{name}" 1,
   imp "[export]$root" s!"[async-lower][stream-read-0]{name}" 2,
   imp "[export]$root" s!"[async-lower][stream-write-0]{name}" 2,
   imp "[export]$root" s!"[stream-drop-readable-0]{name}" 0,
   imp "[export]$root" s!"[stream-drop-writable-0]{name}" 0,
   imp "$root" "[waitable-set-new]" 3,
   imp "$root" "[waitable-join]" 4]

/-- **The program as a Core 3.0 module**: the imports, a memory of two pages exported as
`memory`, `cabi_realloc`, the nine mutable `i32` globals, the lift (function `9`) and the
callback (function `10`), each body followed by `unreachable`. -/
def toModule (P : Prog) (name : String) : Module where
  types := types
  imports := imports name
  memories := [⟨.i32, ⟨2, none⟩⟩]
  globals := (List.range 9).map fun i => ⟨⟨.var, i32⟩, [c32 (P.g0 i)]⟩
  funcs :=
    [⟨ix 5, [], [c32 0x8000]⟩,
     ⟨ix 6, [i32, i32, i32, i32, i32, i32, i64], sCode P.entry ++ [.unreachable]⟩,
     ⟨ix 2, [i32, i32, i32, i32, i64], sCode P.cb ++ [.unreachable]⟩]
  exports :=
    [⟨"memory", .memory (ix 0)⟩,
     ⟨"cabi_realloc", .func (ix 8)⟩,
     ⟨s!"[async-lift]{name}", .func (ix 9)⟩,
     ⟨s!"[callback][async-lift]{name}", .func (ix 10)⟩]

/-! ## Bytes and text -/

/-- **The bytes**, by silmaril's verified encoder. -/
def wasmOf (P : Prog) (name : String) : Except String ByteArray :=
  (fun bs => ⟨bs.toArray⟩) <$> Silmaril.Wasm.Binaryen.Exe.encodeModule? (toModule P name)

/-- **The text**, by silmaril's checked printer. -/
def watOf (P : Prog) (name : String) : Except String String :=
  match Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax? (toModule P name) with
  | none => .error "kcore: the module is outside the printer's fragment"
  | some x =>
    match Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument? x with
    | none => .error "kcore: the module's text does not render"
    | some t => .ok t

/-- Silmaril's sound WAT parser on a whole document: the lexer, then the module reader. -/
def parseWat (t : String) : Option Module := do
  let x ← Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 t
  Silmaril.Wasm.Binaryen.Toolkit.Wat.parseSupported? x

/-- **The original printer's text, checked**: `Prog.wat P name` when silmaril's parser reads
it as a module that encodes to the same bytes as `toModule P name`. -/
def watChecked (P : Prog) (name : String) : Except String String := do
  let b ← wasmOf P name
  let t := P.wat name
  match parseWat t with
  | none => throw "kcore: the printed text is outside the WAT parser's fragment"
  | some m =>
    match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
    | .ok bs =>
      if bs == b.data.toList then pure t
      else throw "kcore: the printed text does not denote the generated module"
    | .error e => throw ("kcore: " ++ e)

end Silmaril.Wasm.JcoTool.KCoreEmit
