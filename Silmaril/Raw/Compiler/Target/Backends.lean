module

public import Silmaril.Compiler.Target.Runtime.Defs
public import Silmaril.Compiler.Target.RenameCheck.Defs
public import Silmaril.Semantics.CPort.Formats.ELF.Write.Defs
public import Silmaril.Compiler.Target.X86LayoutCorrect.Defs
public import Silmaril.Compiler.Target.X86Native.Defs
public import Silmaril.Machine.X86.Lir.Defs
public import Silmaril.Machine.RiscV.Lir.Defs
/-! # Backends: linked Lir to relocatable objects

`compile target linked` renumbers the virtual registers of the linked Lir program,
checked (`RegAlloc.renumberChecked k`: the most used ones, with live ranges shared, below
`k`; the program unchanged when the liveness certificate does not check), spills it
(`Lir.Alloc.firstK`, as the WebAssembly compiler does: `k = 7` onto the nine x86-64
allocatable registers, `k = 12` onto the fourteen RV64 ones), runs the verified backend (`X86.Backend.compile`
or `RiscV.Backend.compile`; on x86-64 it runs as `compileX86Fast`, the tabulated layout of
`Silmaril.Compile.Target.X86Layout`, by the `@[csimp]` lemma
`X86LayoutCorrect.compile_eq_compileX86Fast`) and wraps the code and the initial
linear-memory image in an ELF relocatable object (`Formats.ELF.Write`). On x86-64 a
program with floating-point instructions (`Lir.Instr.fop`, which the verified backend
rejects) goes through the unverified native emitter `X86Native.compile` instead, which
is the verified backend's code with scalar SSE2 sequences for `fop` (`docs/projects/cerberus.md`,
trusted base); RV64 rejects them.

* `.text`: the code, position independent, with one `FUNC` symbol per function
  (`__ccomp_start` is the entry);
* `.rodata.ccomp`: the image of `[dataBase, dataEnd)`, symbol `__ccomp_image`;
* absolute symbols `__ccomp_image_base`, `__ccomp_image_size`, `__ccomp_lmem_size`,
  `__ccomp_ctl` for the startup code.

The object needs no relocations: code reaches memory through the base register and
other functions through PC-relative calls.

## Intended theorem

`X86.Backend.compile_refines` and `RiscV.Backend.compile_refines` (with
`Alloc.spill_refines` and `RegAlloc.renumberChecked_refines`) give the refinement of
the original linked program by the machine code from the loaded state when no `fop` is
present (including `--float=soft`). The analogous native-float refinement is unproved
and tracked as open. What remains is
the loader statement: the process created by the startup code from this object
(mapped image, base and stack-limit registers, the call of `__ccomp_start`) is that
loaded state.
-/

@[expose] public section

namespace Silmaril.Compile.Target

open Silmaril.Machine
open Silmaril.Formats.ELF

inductive Arch where
  | x86_64
  | rv64
  deriving DecidableEq, Repr

def Arch.ofString? : String → Option Arch
  | "x86_64" | "x86-64" | "x86" => some .x86_64
  | "rv64" | "riscv64" => some .rv64
  | _ => none

def Arch.name : Arch → String
  | .x86_64 => "x86_64"
  | .rv64 => "rv64"

/-- Machine code and the offset of each function. -/
structure Code where
  bytes : ByteArray
  entries : Array Nat

def toBytes (l : List (BitVec 8)) : ByteArray := ⟨(l.map fun b => b.toNat.toUInt8).toArray⟩

/-- Select native scalar emission only when the spilled program contains float ops.
`none` selects the verified integer backend. Shared with the registry so both entry
points make exactly the same choice. The emitter remains unvalidated. -/
def nativeCodeX86 (q : Lir.Prog (Fin 9)) :
    Option (Except (List X86.Backend.Error) (ByteArray × Array Nat)) :=
  if X86Native.hasFop q then
    some (X86Native.compile (X86.Backend.Assign.fin 9 (by decide)) q 0)
  else none

def codeX86 (p : Lir.Prog Nat) : Except String Code :=
  let q := Lir.Alloc.spill (Lir.Alloc.firstK 7) (RegAlloc.renumberChecked 7 p)
  match nativeCodeX86 q with
  | some (.error es) => .error s!"x86-64 native-float backend: {repr (es.take 5)}"
  | some (.ok (bytes, entries)) => .ok ⟨bytes, entries⟩
  | none =>
    match X86.Backend.compile (X86.Backend.Assign.fin 9 (by decide)) q 0 with
    | .error es => .error s!"x86-64 backend: {repr (es.take 5)}"
    | .ok img => .ok ⟨toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩

def codeRV64 (p : Lir.Prog Nat) : Except String Code :=
  let q := Lir.Alloc.spill (Lir.Alloc.firstK 12) (RegAlloc.renumberChecked 12 p)
  match RiscV.Backend.compile (RiscV.Backend.Assign.fin 14 (by decide)) q with
  | .error e => .error s!"rv64 backend: {repr e}"
  | .ok img => .ok ⟨toBytes (RiscV.Ext.byteDecoder.encodeBlock img.code),
      ((List.range q.funcs.length).map fun i => 4 * RiscV.Backend.funcStart q i).toArray⟩

def Arch.machine : Arch → Nat
  | .x86_64 => 62
  | .rv64 => 243

/-- The symbol name of each function: its name in the link, or `__ccomp_dispatch.i` for a
function no name maps to (a dispatcher). -/
def objectNames (l : Mir.Linked) (code : Code) : Array String := Id.run do
  let mut a : Array (Option String) := Array.replicate code.entries.size none
  for (n, i) in l.funcs.toList do
    if i < a.size then a := a.set! i (some n)
  return a.mapIdx fun i o => o.getD s!"__ccomp_dispatch.{i}"

/-- The sections of the object file: `.text` and `.rodata.ccomp`. -/
def objectSections (l : Mir.Linked) (code : Code) : List Write.Section :=
  [ { name := ".text", flags := 6, align := 16, data := code.bytes },
    { name := ".rodata.ccomp", flags := 2, align := 16, data := l.image } ]

/-- The symbols of the object file: one `FUNC` per function, then the image and the
absolute symbols of the startup code. -/
def objectSymbols (l : Mir.Linked) (code : Code) : List Write.Sym :=
  let ends := code.entries.toList.drop 1 ++ [code.bytes.size]
  let fsyms := ((objectNames l code).toList.zip (code.entries.toList.zip ends)).map
    fun (n, (s, e)) => ({ name := n, sec := some 0, value := s, size := e - s, kind := 2 } : Write.Sym)
  fsyms ++ [
    { name := "__ccomp_image", sec := some 1, value := 0, size := l.image.size, kind := 1 },
    { name := "__ccomp_image_base", sec := none, value := l.dataBase, size := 0, kind := 0 },
    { name := "__ccomp_image_size", sec := none, value := l.image.size, size := 0, kind := 0 },
    { name := "__ccomp_lmem_size", sec := none, value := memSize, size := 0, kind := 0 },
    { name := "__ccomp_ctl", sec := none, value := l.data[ctlSymbol]?.getD dataBase, size := 0,
      kind := 0 } ]

/-- The object file of a linked program. Its round trip through the ELF reader is
`ObjectCorrect.readObject_object`. -/
def object (arch : Arch) (l : Mir.Linked) (code : Code) : ByteArray :=
  Write.writeRelocatable arch.machine 0 (objectSections l code) (objectSymbols l code)

/-- Compile a linked program to an object file. -/
def compile (arch : Arch) (l : Mir.Linked) : Except String ByteArray := do
  let code ← match arch with
    | .x86_64 => codeX86 l.prog
    | .rv64 => codeRV64 l.prog
  return object arch l code

end Silmaril.Compile.Target
