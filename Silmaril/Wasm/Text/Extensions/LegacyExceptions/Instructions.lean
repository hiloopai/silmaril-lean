module

public import Silmaril.Wasm.Extensions.LegacyExceptions.Types
public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.Instructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.LegacyExceptions

open Silmaril Silmaril.Formats.SExpEncoding

mutual
  inductive LeafT : Core.IdCtx → List SExp → Wasm.Extensions.LegacyExceptions.Leaf → Prop where
    | base {I : Core.IdCtx} {xs : List SExp} {i : Wasm.Extensions.BinaryenMemory.Leaf}
        (h : BinaryenMemory.LeafT I xs i) : LeafT I xs (.base i)
    | rethrow {I : Core.IdCtx} {ix : SExp} {label : LabelIdx} (h : Text.Idx I.labels ix label) :
        LeafT I [K "rethrow", ix] (.rethrow label)
    | try_ {I : Core.IdCtx} {header body cs fs : List SExp} {type : BlockType}
        {is : Wasm.Extensions.LegacyExceptions.Expr}
        {catches : List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)}
        {all : Option Wasm.Extensions.LegacyExceptions.Expr}
        (ht : Core.BlockTypeT I header type [])
        (hb : Structured.InstrsT LeafT { I with labels := none :: I.labels } body is)
        (hc : CatchesT I cs catches) (hf : FinalT I fs all) :
        LeafT I [L (K "try" :: (header ++ [L (K "do" :: body)] ++ cs ++ fs))] (.try_ type is catches all)
    | delegate {I : Core.IdCtx} {header body : List SExp} {ix : SExp} {type : BlockType}
        {is : Wasm.Extensions.LegacyExceptions.Expr} {label : LabelIdx}
        (ht : Core.BlockTypeT I header type [])
        (hb : Structured.InstrsT LeafT { I with labels := none :: I.labels } body is)
        (hl : Text.Idx I.labels ix label) :
        LeafT I [L (K "try" :: (header ++ [L (K "do" :: body), L [K "delegate", ix]]))] (.delegate type is label)

  inductive CatchT : Core.IdCtx → SExp → TagIdx × Wasm.Extensions.LegacyExceptions.Expr → Prop where
    | mk {I : Core.IdCtx} {ix : SExp} {body : List SExp} {tag : TagIdx}
        {is : Wasm.Extensions.LegacyExceptions.Expr} (hi : Text.Idx I.tags ix tag)
        (hb : Structured.InstrsT LeafT { I with labels := none :: I.labels } body is) :
        CatchT I (L (K "catch" :: ix :: body)) (tag, is)

  inductive CatchesT : Core.IdCtx → List SExp → List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr) → Prop where
    | nil {I : Core.IdCtx} : CatchesT I [] []
    | cons {I : Core.IdCtx} {x : SExp} {xs : List SExp}
        {c : TagIdx × Wasm.Extensions.LegacyExceptions.Expr}
        {cs : List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)}
        (hc : CatchT I x c) (hs : CatchesT I xs cs) : CatchesT I (x :: xs) (c :: cs)

  inductive FinalT : Core.IdCtx → List SExp → Option Wasm.Extensions.LegacyExceptions.Expr → Prop where
    | none {I : Core.IdCtx} : FinalT I [] none
    | catchAll {I : Core.IdCtx} {body : List SExp} {is : Wasm.Extensions.LegacyExceptions.Expr}
        (hb : Structured.InstrsT LeafT { I with labels := none :: I.labels } body is) :
        FinalT I [L (K "catch_all" :: body)] (some is)
end

abbrev InstrT := Structured.InstrT LeafT
abbrev InstrsT := Structured.InstrsT LeafT

end Silmaril.Wasm.Text.Extensions.LegacyExceptions
