module

public import Silmaril.Elf.Exe.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.X86.MemEvent.Defs
public import Silmaril.X86.Open9.Thms

/-! One canonical one-byte varint through the real SQLite 3.54.1 table-interior cell caller. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteOneByteVarint

open Silmaril.Process (Memory addressLimit)
open Silmaril.X86

/-- The complete wrapper. The signed immediate of the direct call is the
only field that changes between these copies of the wrapper. -/
def wrapperCode (displacement : BitVec 32) : List Byte :=
  [0x48, 0x8d, 0x7e, 0x04, 0x48, 0x89, 0xd6, 0x49, 0x89, 0xd1, 0xe8] ++
  Ext.leBytes (displacement.setWidth 64) 4 ++
  [0x41, 0xc7, 0x41, 0x10, 0, 0, 0, 0, 0x83, 0xc0, 4, 0x49, 0xc7, 0x41, 8, 0, 0, 0, 0,
   0x0f, 0xb6, 0xc0, 0x66, 0x41, 0x89, 0x41, 0x16, 0x31, 0xc0, 0x66, 0x41, 0x89, 0x41, 0x14, 0xc3]

/-- The prefix at ELF VA `0x10a40` through the common return. It includes the
bytes skipped by the taken branch, which this contract never executes. -/
def calleeCode : List Byte :=
  [0x0f, 0xb6, 0x07, 0x48, 0x89, 0xf1, 0x48, 0x89, 0xfa, 0xbe, 1, 0, 0, 0, 0x48, 0x83, 0xf8,
   0x7f, 0x76, 0x1e, 0x0f, 0xb6, 0x7f, 1, 0x48, 0xc1, 0xe0, 7, 0xbe, 2, 0, 0, 0, 0x49, 0x89,
   0xf8, 0x48, 0x31, 0xc7, 0x48, 0x89, 0xf8, 0x80, 0xf4, 0x40, 0x45, 0x84, 0xc0, 0x78, 0x0e,
   0x48, 0x89, 0x01, 0x89, 0xf0, 0xc3]

inductive Window where
  | caller | callee
  deriving DecidableEq

/-- The two file addresses and the wrapper's encoded rel32. -/
structure Layout where
  callerVA : Nat
  calleeVA : Nat
  displacement : BitVec 32

def Layout.va (layout : Layout) : Window → Nat
  | .caller => layout.callerVA
  | .callee => layout.calleeVA

def Layout.code (layout : Layout) : Window → List Byte
  | .caller => wrapperCode layout.displacement
  | .callee => calleeCode

def Layout.pc (layout : Layout) (bias : Word) (window : Window) (offset : Nat) : Word :=
  (bias + BitVec.ofNat 64 (layout.va window)) + BitVec.ofNat 64 offset

/-- Address equality expressed exactly as a signed x86 rel32 transfer. -/
def Layout.DirectCall (layout : Layout) : Prop :=
  layout.pc 0 .caller 15 + layout.displacement.signExtend 64 = layout.pc 0 .callee 0

instance (layout : Layout) : Decidable layout.DirectCall := by unfold Layout.DirectCall; infer_instance

def corpusLayout : Layout := ⟨0x117b0, 0x10a40, 0xfffff281⟩

abbrev callerCode : List Byte := corpusLayout.code .caller
abbrev Window.va (w : Window) : Nat := corpusLayout.va w
abbrev Window.code (w : Window) : List Byte := corpusLayout.code w

def Window.symbolIndex : Window → Nat
  | .caller => 74
  | .callee => 27

def Window.symbolName : Window → String
  | .caller => "btreeParseCellPtrNoPayload"
  | .callee => "sqlite3GetVarint"

/-- A fixed program path. Offsets are relative to the corresponding ELF window. -/
abbrev Site := Window × Nat × Ext.Instr × Nat

def operand (r : Reg) (disp : BitVec 32 := 0) : Ext.Mem :=
  ⟨.reg r, none, disp, fun _ => rfl⟩

def varintPath (layout : Layout) : List Site :=
  [(.caller, 0, .lea .q .rdi (operand .rsi 4), 4),
   (.caller, 4, .mov .q (.reg .rsi) .rdx, 3),
   (.caller, 7, .mov .q (.reg .r9) .rdx, 3),
   (.caller, 10, .call layout.displacement, 5),
   (.callee, 0, .movx false .d .b .rax (.mem (operand .rdi)), 3),
   (.callee, 3, .mov .q (.reg .rcx) .rsi, 3),
   (.callee, 6, .mov .q (.reg .rdx) .rdi, 3),
   (.callee, 9, .movI32 .rsi 1, 5),
   (.callee, 14, .aluI8 .q .cmp (.reg .rax) 0x7f, 4),
   (.callee, 18, .jcc8 .be 0x1e, 2),
   (.callee, 50, .mov .q (.mem (operand .rcx)) .rax, 3),
   (.callee, 53, .mov .d (.reg .rax) .rsi, 2),
   (.callee, 55, .ret, 1),
   (.caller, 15, .movI .d (.mem (operand .r9 16)) 0, 8),
   (.caller, 23, .aluI8 .d .add (.reg .rax) 4, 3),
   (.caller, 26, .movI .q (.mem (operand .r9 8)) 0, 8),
   (.caller, 34, .movx false .d .b .rax (.reg .rax), 3),
   (.caller, 37, .store .w (.mem (operand .r9 22)) .rax, 5),
   (.caller, 42, .alu .d .xor (.reg .rax) .rax, 2),
   (.caller, 44, .store .w (.mem (operand .r9 20)) .rax, 5),
   (.caller, 49, .ret, 1)]

def Site.valid (layout : Layout) : Site → Prop
  | (w, offset, i, len) => offset + len ≤ (layout.code w).length ∧
      Open9.decode (((layout.code w).drop offset).take len) = some (.ext8 (.base i), len)

instance (layout : Layout) (site : Site) : Decidable (site.valid layout) := by
  rcases site with ⟨w, offset, i, len⟩
  unfold Site.valid
  infer_instance

/-- The listing must decode at all sites on the one-byte route. -/
def Layout.checkPath (layout : Layout) : Bool :=
  (varintPath layout).all (fun site => decide (site.valid layout))

/-- Successful decoded steps up to the outer return. The events describe data
accesses, with instruction fetch checked separately against its ELF window. -/
inductive TraceAt (layout : Layout) (bias : Word) (entry : MState) : MState → List MemEvent.Event → MState → Prop where
  | nil (s : MState) : TraceAt layout bias entry s [] s
  | cons {s t : MState} {c : State} {mem : Memory} {events : List MemEvent.Event}
      (window : Window) (offset length : Nat) (instruction : Ext9.Instr)
      (loaded : Ext.Loaded s.memory (bias + BitVec.ofNat 64 (layout.va window)) (layout.code window))
      (pc : s.core.rip = (bias + BitVec.ofNat 64 (layout.va window)) + BitVec.ofNat 64 offset)
      (fits : offset + length ≤ (layout.code window).length)
      (decode : Open9.decode (((layout.code window).drop offset).take length) = some (instruction, length))
      (exec : Ext9.exec instruction s.core s.memory length = .ok c mem)
      (beforeReturn : ¬ FnContract.Returned Open9.isa entry s)
      (rest : TraceAt layout bias entry ⟨c, mem⟩ events t) :
      TraceAt layout bias entry s (MemEvent.ext9Accesses instruction s.core length ++ events) t

abbrev Trace := TraceAt corpusLayout

def cellByte (s : MState) : Nat := (s.core.read .rsi + 4).toNat
def output (s : MState) : Nat := (s.core.read .rdx).toNat
def savedSlot (s : MState) : Nat := (s.core.read .rsp).toNat
def privateSlot (s : MState) : Nat := (s.core.read .rsp - 8).toNat

def within (start size address : Nat) : Prop := start ≤ address ∧ address < start + size

def writable (s : MState) (address : Nat) : Prop :=
  within (privateSlot s) 8 address ∨ within (output s) 24 address

/-- Admission for the mapped caller. The child-pointer bytes themselves are unused.
The caller supplies a live input byte, a separate writable CellInfo, a private call slot,
and an ABI return word. Coverage of the writes also excludes every fetched code byte. -/
structure EntryAt (layout : Layout) (bias : Word) (s : MState) (byte : Byte) : Prop where
  pc : s.core.rip = layout.pc bias .caller 0
  abi : FnContract.AbiEntry s.core s.memory
  stackBounds : 8 ≤ savedSlot s ∧ savedSlot s + 8 < addressLimit
  inputBound : (s.core.read .rsi).toNat + 4 < addressLimit
  outputBound : output s + 24 ≤ addressLimit
  canonical : byte.toNat < 128
  input : s.memory.readBytes (cellByte s) 1 = some [byte]
  callWrite : s.memory.Permitted .write (privateSlot s) 8
  callRead : s.memory.Permitted .read (privateSlot s) 8
  outputWrite : s.memory.Permitted .write (output s) 24
  inputSeparate : ¬ writable s (cellByte s)
  outerReturnSeparate : ∀ offset < 8, ¬ writable s (savedSlot s + offset)
  callSeparate : ∀ offset < 8, ¬ within (output s) 24 (privateSlot s + offset)
  codeSeparate : ∀ window : Window, ∀ offset < (layout.code window).length,
    ¬ writable s ((bias + BitVec.ofNat 64 (layout.va window)).toNat + offset)

abbrev Entry := EntryAt corpusLayout

/-- Exact ordered data events. CALL's return word is left in its private stack
slot after the matching RET. The outer return word is read once. -/
def events (s : MState) : List MemEvent.Event :=
  [⟨.store, privateSlot s, 8, false⟩,
   ⟨.load, cellByte s, 1, false⟩,
   ⟨.store, output s, 8, false⟩,
   ⟨.load, privateSlot s, 8, false⟩,
   ⟨.store, output s + 16, 4, false⟩,
   ⟨.store, output s + 8, 8, false⟩,
   ⟨.store, output s + 22, 2, false⟩,
   ⟨.store, output s + 20, 2, false⟩,
   ⟨.load, savedSlot s, 8, false⟩]

/-- CellInfo contains the decoded key, null payload pointer, zero payload and
local sizes, and cell size five. The frame includes mapping permissions. -/
structure ResultAt (layout : Layout) (bias : Word) (entry final : MState) (byte : Byte) : Prop where
  trace : TraceAt layout bias entry entry (events entry) final
  firstReturn : FnContract.FirstReturn Open9.isa entry final
  abi : FnContract.AbiReturn entry.core entry.memory final.core
  frame : entry.memory.WritesWithin final.memory (writable entry)
  cellInfo : ∀ i : Fin 24, final.memory.bytes.get? (output entry + i.val) =
    some (if i.val = 0 then byte else if i.val = 22 then 5 else 0)

abbrev Result := ResultAt corpusLayout

end Silmaril.Elf.Corpus.SqliteOneByteVarint
