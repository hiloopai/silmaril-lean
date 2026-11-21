module

public import Silmaril.Machine.SqliteRead.Defs
public import Silmaril.X86.Decompile.Region
public import Silmaril.X86.Ext.Wire.Machine

/-! The non-WAL `xRead` call site inside the pinned x86-64 `readDbPage`.
The cut begins after pager state has been projected into registers and ends
at handler entry, without executing the callback or the continuation. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteRead

open Silmaril.Machine.SqliteRead (Request Obs dispatch)
open Silmaril.X86 (MState State Word)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.Ext.Wire (Platform Outcome step)

def region : Silmaril.X86.Decompile.Region :=
  ⟨0x4b10d, [0x48, 0x8b, 0x07, 0x48, 0x0f, 0xaf, 0xca, 0xff, 0x50, 0x10]⟩

def continuation : Word := 0x4b117

/-- Page-index arithmetic from the C call site. `index` is `pgno - 1`. -/
structure PageRead where
  file : Word
  buffer : Word
  count : BitVec 32
  index : Nat

def PageRead.request (page : PageRead) : Request :=
  ⟨page.file, page.buffer, page.count, BitVec.ofNat 64 (page.index * page.count.toNat)⟩

def argument (state : State) : Request :=
  ⟨state.read .rdi, state.read .rsi, (state.read .rdx).setWidth 32, state.read .rcx⟩

def stackSlot (initial : MState) : Nat := (initial.core.read .rsp - 8#64).toNat

/-- Loaded code, pager projection, table layout and incoming SysV stack.
The nonzero target is supplied by the environment; admitting this numeric
address is not evidence that the handler runs or implements `xRead`. -/
structure Entry (initial : MState) (page : PageRead) (methods target : Word) : Prop where
  rip : initial.core.rip = 0x4b10d
  code : initial.memory.fetchBytes region.base region.bytes.length = some region.bytes
  file : initial.core.read .rdi = page.file
  buffer : initial.core.read .rsi = page.buffer
  count : initial.core.read .rdx = BitVec.ofNat 64 page.count.toNat
  index : initial.core.read .rcx = BitVec.ofNat 64 page.index
  validIndex : page.index + 1 < 2 ^ 32
  signedRange : page.index * page.count.toNat + page.count.toNat < 2 ^ 63
  fileTable : loadN initial.memory page.file 8 = some methods
  liveMethods : methods ≠ 0#64 ∧ methods.toNat + 24 ≤ 2 ^ 64
  readSlot : loadN initial.memory (methods + 16) 8 = some target
  nonnullTarget : target ≠ 0#64
  stackRange : 8 ≤ (initial.core.read .rsp).toNat
  stackAligned : (initial.core.read .rsp).toNat % 16 = 0
  stackReadable : initial.memory.Permitted .read (stackSlot initial) 8
  stackWritable : initial.memory.Permitted .write (stackSlot initial) 8
  stackApart : stackSlot initial + 8 ≤ page.buffer.toNat ∨
    page.buffer.toNat + page.count.toNat ≤ stackSlot initial

inductive Cut where
  | handlerEntry (entry : MState)
  | stopped (reason : Outcome)
  | rejected

/-- Only three steps are needed on the admitted cut. The successful label is
justified by the byte/entry check; budget failure is not divergence. -/
def run (platform : Platform) : Nat → MState → Cut
  | 0, _ => .rejected
  | fuel + 1, initial =>
    match step platform continuation initial with
    | .retired next =>
      if initial.core.rip = 0x4b114 then .handlerEntry next else run platform fuel next
    | other => .stopped other

def observe : Cut → Obs
  | .handlerEntry entry => dispatch (argument entry.core)
  | .stopped .trapped => ⟨[], .aborted ()⟩
  | .stopped (.undefinedCondition _) => ⟨[], .faulted .undefinedFlag⟩
  | .stopped .divideFault => ⟨[], .faulted .divide⟩
  | .stopped (.dataFault _) => ⟨[], .faulted .data⟩
  | .stopped .fetchFault => ⟨[], .faulted .fetch⟩
  | .stopped .undecodable => ⟨[], .faulted .unsupported⟩
  | _ => ⟨[], .faulted .validation⟩

/-- The boundary observation plus the continuation word, stack pointer, and
write footprint needed to formulate a separate handler-linking obligation. -/
structure Dispatches (platform : Platform) (initial : MState) (req : Request) (target : Word)
    (next : MState) : Prop where
  executed : run platform 3 initial = .handlerEntry next
  request : argument next.core = req
  rip : next.core.rip = target
  stack : next.core.read .rsp = initial.core.read .rsp - 8
  returnWord : next.memory.readBytes (stackSlot initial) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [continuation])
  frame : initial.memory.WritesOnly next.memory (stackSlot initial) 8

end Silmaril.Elf.Corpus.SqliteRead
