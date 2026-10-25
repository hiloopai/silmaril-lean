module

public import Silmaril.Wasm.Extensions.AtomicMemory.Types
public import Silmaril.Wasm.Text.Extensions.Structured.Instructions

@[expose] public section

namespace Silmaril.Wasm.Extensions.AtomicMemory

def Shape.valueName : Shape → String
  | .i32 | .i32_8 | .i32_16 => "i32"
  | .i64 | .i64_8 | .i64_16 | .i64_32 => "i64"

def Shape.packedName : Shape → String
  | .i32 | .i64 => ""
  | .i32_8 | .i64_8 => "8"
  | .i32_16 | .i64_16 => "16"
  | .i64_32 => "32"

def Shape.width : Shape → Nat
  | .i32 | .i64_32 => 4
  | .i64 => 8
  | .i32_8 | .i64_8 => 1
  | .i32_16 | .i64_16 => 2

def Shape.unsignedSuffix : Shape → String
  | .i32 | .i64 => ""
  | _ => "_u"

def RMW.name : RMW → String
  | .add => "add" | .sub => "sub" | .and => "and"
  | .or => "or" | .xor => "xor" | .xchg => "xchg"

def Access.mnemonic : Access → String
  | .notify => "memory.atomic.notify"
  | .wait32 => "memory.atomic.wait32"
  | .wait64 => "memory.atomic.wait64"
  | .load s => s.valueName ++ ".atomic.load" ++ s.packedName ++ s.unsignedSuffix
  | .store s => s.valueName ++ ".atomic.store" ++ s.packedName
  | .rmw op s => s.valueName ++ ".atomic.rmw" ++ s.packedName ++ "." ++ op.name ++ s.unsignedSuffix
  | .cmpxchg s => s.valueName ++ ".atomic.rmw" ++ s.packedName ++ ".cmpxchg" ++ s.unsignedSuffix

def Access.width : Access → Nat
  | .notify | .wait32 => 4
  | .wait64 => 8
  | .load s | .store s | .rmw _ s | .cmpxchg s => s.width

end Silmaril.Wasm.Extensions.AtomicMemory

namespace Silmaril.Wasm.Text.Extensions.AtomicMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Wasm.Extensions.AtomicMemory

inductive AtomicT (I : Core.IdCtx) : List SExp → AtomicInstr → Prop where
  | access {op : Access} {mx : SExp} {ax : List SExp} {m : MemIdx} {a : MemArg}
      (hm : Text.Idx I.mems mx m) (ha : Core.MemArgT op.width ax a) :
      AtomicT I (K op.mnemonic :: mx :: ax) (.access op m a)
  | fence : AtomicT I [K "atomic.fence"] .fence
  | pause : AtomicT I [K "pause"] .pause

inductive LeafT (I : Core.IdCtx) : List SExp → Leaf → Prop where
  | core {xs : List SExp} {i : Wasm.Instr} (h : Core.Plain I xs i []) : LeafT I xs (.core i)
  | atomic {xs : List SExp} {i : AtomicInstr} (h : AtomicT I xs i) : LeafT I xs (.atomic i)

abbrev InstrT := Structured.InstrT LeafT
abbrev InstrsT := Structured.InstrsT LeafT

end Silmaril.Wasm.Text.Extensions.AtomicMemory
