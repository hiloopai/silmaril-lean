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

/-- The complete caller at ELF VA `0x117b0`, including its direct call and return. -/
def callerCode : List Byte :=
  [0x48, 0x8d, 0x7e, 0x04, 0x48, 0x89, 0xd6, 0x49, 0x89, 0xd1, 0xe8, 0x81, 0xf2, 0xff, 0xff,
   0x41, 0xc7, 0x41, 0x10, 0, 0, 0, 0, 0x83, 0xc0, 4, 0x49, 0xc7, 0x41, 8, 0, 0, 0, 0,
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

def Window.va : Window → Nat
  | .caller => 0x117b0
  | .callee => 0x10a40

def Window.code : Window → List Byte
  | .caller => callerCode
  | .callee => calleeCode

def Window.symbolIndex : Window → Nat
  | .caller => 74
  | .callee => 27

def Window.symbolName : Window → String
  | .caller => "btreeParseCellPtrNoPayload"
  | .callee => "sqlite3GetVarint"

/-- Successful decoded steps up to the outer return. The events describe data
accesses, with instruction fetch checked separately against its ELF window. -/
inductive Trace (bias : Word) (entry : MState) : MState → List MemEvent.Event → MState → Prop where
  | nil (s : MState) : Trace bias entry s [] s
  | cons {s t : MState} {c : State} {mem : Memory} {events : List MemEvent.Event}
      (window : Window) (offset length : Nat) (instruction : Ext9.Instr)
      (loaded : Ext.Loaded s.memory (bias + BitVec.ofNat 64 window.va) window.code)
      (pc : s.core.rip = (bias + BitVec.ofNat 64 window.va) + BitVec.ofNat 64 offset)
      (fits : offset + length ≤ window.code.length)
      (decode : Open9.decode ((window.code.drop offset).take length) = some (instruction, length))
      (exec : Ext9.exec instruction s.core s.memory length = .ok c mem)
      (beforeReturn : ¬ FnContract.Returned Open9.isa entry s)
      (rest : Trace bias entry ⟨c, mem⟩ events t) :
      Trace bias entry s (MemEvent.ext9Accesses instruction s.core length ++ events) t

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
structure Entry (bias : Word) (s : MState) (byte : Byte) : Prop where
  pc : s.core.rip = bias + 0x117b0
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
  codeSeparate : ∀ window : Window, ∀ offset < window.code.length,
    ¬ writable s ((bias + BitVec.ofNat 64 window.va).toNat + offset)

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
structure Result (bias : Word) (entry final : MState) (byte : Byte) : Prop where
  trace : Trace bias entry entry (events entry) final
  firstReturn : FnContract.FirstReturn Open9.isa entry final
  abi : FnContract.AbiReturn entry.core entry.memory final.core
  frame : entry.memory.WritesWithin final.memory (writable entry)
  cellInfo : ∀ i : Fin 24, final.memory.bytes.get? (output entry + i.val) =
    some (if i.val = 0 then byte else if i.val = 22 then 5 else 0)

end Silmaril.Elf.Corpus.SqliteOneByteVarint
