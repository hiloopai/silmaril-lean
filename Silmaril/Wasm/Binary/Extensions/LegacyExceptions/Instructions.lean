module

public import Silmaril.Wasm.Extensions.LegacyExceptions.Types
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions

open Core

mutual
  inductive Leaf (F : Forms) : Bytes → Wasm.Extensions.LegacyExceptions.Leaf → Prop where
    | base {b : Bytes} {i : Wasm.Extensions.BinaryenMemory.Leaf} (h : BinaryenMemory.Leaf F b i) :
        Leaf F b (.base i)
    | rethrow {b : Bytes} {label : LabelIdx} (h : Index b label) :
        Leaf F ([0x09] ++ b) (.rethrow label)
    | try_ {bt body handlers : Bytes} {type : BlockType}
        {is : Wasm.Extensions.LegacyExceptions.Expr}
        {catches : List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)}
        {all : Option Wasm.Extensions.LegacyExceptions.Expr}
        (ht : Core.BlockType F bt type) (hb : Structured.Instrs F (Leaf F) body is)
        (hh : Handlers F handlers (catches, all)) :
        Leaf F ([0x06] ++ bt ++ body ++ handlers) (.try_ type is catches all)
    | delegate {bt body bl : Bytes} {type : BlockType}
        {is : Wasm.Extensions.LegacyExceptions.Expr} {label : LabelIdx}
        (ht : Core.BlockType F bt type) (hb : Structured.Instrs F (Leaf F) body is) (hl : Index bl label) :
        Leaf F ([0x06] ++ bt ++ body ++ [0x18] ++ bl) (.delegate type is label)

  inductive Handlers (F : Forms) : Bytes →
      (List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)) × Option Wasm.Extensions.LegacyExceptions.Expr → Prop where
    | end_ : Handlers F [0x0b] ([], none)
    | catch_ {bt body rest : Bytes} {tag : TagIdx} {is : Wasm.Extensions.LegacyExceptions.Expr}
        {catches : List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)}
        {all : Option Wasm.Extensions.LegacyExceptions.Expr} (ht : Index bt tag)
        (hb : Structured.Instrs F (Leaf F) body is) (hr : Handlers F rest (catches, all)) :
        Handlers F ([0x07] ++ bt ++ body ++ rest) ((tag, is) :: catches, all)
    | catchAll {body : Bytes} {is : Wasm.Extensions.LegacyExceptions.Expr}
        (hb : Structured.Instrs F (Leaf F) body is) :
        Handlers F ([0x19] ++ body ++ [0x0b]) ([], some is)
end

abbrev Instr (F : Forms) := Structured.Instr F (Leaf F)
abbrev Instrs (F : Forms) := Structured.Instrs F (Leaf F)
abbrev Expr (F : Forms) := Structured.Expr F (Leaf F)

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions
