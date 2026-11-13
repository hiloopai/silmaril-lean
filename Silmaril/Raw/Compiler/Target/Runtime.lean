module

public import Silmaril.Compiler.Mir.Link.Defs
/-! # The process runtime of compiled programs

Compiled code addresses one **linear memory** of `memSize` bytes through a base
register (`r15` on x86-64, `s11` on RV64), exactly as Lir's memory model requires
(`Silmaril.Machine.Lir`: one byte memory addressed by natural numbers). The startup
code (`tools/ccomp/runtime/crt0-*.S`, hand-written assembly) maps it, copies the
initial image, installs the trap handler and calls `__ccomp_start`. The map:

| address | content |
| --- | --- |
| `0 … 0xfff` | null guard (mapped inaccessible by the startup code) |
| `0x1000` | `__ccomp_ctl`, the control block (below), then every data object |
| `dataEnd` | the output buffer, `outCap` bytes |
| `dataEnd + outCap` | the heap (bump allocation by the C library), up to `heapLimit` |
| `memSize - stackSize … memSize` | the software stack (address-taken locals), growing down |

The control block, eight 8-byte words: 0 the software stack pointer, 1 the heap
break, 2 the heap limit, 3 the number of bytes written to the output buffer, 4 the
exit status, 5 the exit kind (0 none, 1 `exit`, 2 `abort`), 6 the output buffer's
address, 7 its capacity.

Programs make no system calls: output is appended to the buffer, and `exit`/`abort`
record their status in the control block and execute Lir's `trap`. When `__ccomp_start`
returns, or the program traps, the startup code writes the buffer to standard output
and exits with `main`'s result, the recorded status, or the signal of the trap
(`SIGABRT` after `abort`). The observable behaviour of a process is thereby a function
of the Lir behaviour (returned value and final memory, or trap and memory), which is
what the backend theorems preserve.

All addresses are below 2³¹, so a linear address fits in a C `int` (Cerberus's
`va_list`). Function pointers are `funcPtrBase + 16 i` (`Silmaril.Compile.Mir.Link`).
-/

@[expose] public section

namespace Silmaril.Compile.Target

open Silmaril.Machine
open Silmaril.Compile.Mir

def memSize : Nat := 2 ^ 30
def dataBase : Nat := 0x1000
def funcPtrBase : Nat := 2 ^ 32
def outCap : Nat := 2 ^ 24
def stackSize : Nat := 2 ^ 26

def layout : Mir.Layout := ⟨dataBase, funcPtrBase⟩

def ctlSymbol : Symbol := "__ccomp_ctl"
def startSymbol : Symbol := "__ccomp_start"

/-- 8-byte little-endian words. -/
def words (ws : List Nat) : ByteArray := ws.foldl (fun b w => b ++ Mir.writeLE (ByteArray.mk (Array.replicate 8 0)) 0 8 w) .empty

/-- The control block. It must be the first data object of the link. -/
def ctl : Mir.Data :=
  { name := ctlSymbol, size := 64, align := 16,
    init := words [memSize, 0, memSize - stackSize, 0, 0, 0, 0, outCap],
    relocs := [⟨8, dataEndSymbol, outCap⟩, ⟨48, dataEndSymbol, 0⟩] }

/-- `argv` of `main`: one program name. -/
def argv : List Mir.Data :=
  [ { name := "__ccomp_progname", size := 6, align := 1, init := "a.out".toUTF8.push 0 },
    { name := "__ccomp_argv", size := 16, align := 8, relocs := [⟨0, "__ccomp_progname", 0⟩] } ]

/-- `__ccomp_start`: call `main` with no arguments, or with `argc = 1` and `argv`, and
return its result (0 for a `void main`). -/
def start (mainParams mainResults : Nat) : Mir.Func :=
  let call : Array Instr :=
    if mainParams ≥ 2 then
      #[.op (.const 1 1), .addr 2 "__ccomp_argv" 0, .call "main" [1, 2] (if mainResults = 1 then [0] else [])]
    else #[.call "main" [] (if mainResults = 1 then [0] else [])]
  let zero : Array Instr := if mainResults = 1 then #[] else #[.op (.const 0 0)]
  { name := startSymbol, params := [], results := 1,
    blocks := #[⟨call ++ zero, .ret [.reg 0]⟩] }

/-- The runtime unit, which goes first in a link. -/
def unit (mainParams mainResults : Nat) : Mir.Unit :=
  { funcs := #[start mainParams mainResults], data := #[ctl] ++ argv.toArray }

end Silmaril.Compile.Target
