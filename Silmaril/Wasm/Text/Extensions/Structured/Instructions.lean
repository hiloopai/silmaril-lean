module

public import Silmaril.Wasm.Extensions.StructuredInstructions
public import Silmaril.Wasm.Text.Core.Modules

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding

mutual
  inductive InstrT {Leaf : Type} (G : Core.IdCtx → List SExp → Leaf → Prop) :
      (I : Core.IdCtx) → List SExp → Wasm.Extensions.Structured.Instr Leaf → Prop where
    | leaf {I : Core.IdCtx} {xs : List SExp} {i : Leaf} (h : G I xs i) : InstrT G I xs (.leaf i)
    | block {I : Core.IdCtx} {header body : List SExp} {t : BlockType} {is : Wasm.Extensions.Structured.Expr Leaf}
        (ht : Core.BlockTypeT I header t [])
        (hb : InstrsT G { I with labels := none :: I.labels } body is) :
        InstrT G I [L (K "block" :: (header ++ body))] (.block t is)
    | loop {I : Core.IdCtx} {header body : List SExp} {t : BlockType} {is : Wasm.Extensions.Structured.Expr Leaf}
        (ht : Core.BlockTypeT I header t [])
        (hb : InstrsT G { I with labels := none :: I.labels } body is) :
        InstrT G I [L (K "loop" :: (header ++ body))] (.loop t is)
    | if_ {I : Core.IdCtx} {header left right : List SExp} {t : BlockType} {a b : Wasm.Extensions.Structured.Expr Leaf}
        (ht : Core.BlockTypeT I header t [])
        (ha : InstrsT G { I with labels := none :: I.labels } left a)
        (hb : InstrsT G { I with labels := none :: I.labels } right b) :
        InstrT G I [L (K "if" :: (header ++ [L (K "then" :: left), L (K "else" :: right)]))] (.if_ t a b)
    | tryTable {I : Core.IdCtx} {header cs body : List SExp} {t : BlockType} {catches : List Catch}
        {is : Wasm.Extensions.Structured.Expr Leaf} (ht : Core.BlockTypeT I header t [])
        (hc : List.Forall₂ (Core.CatchT I) cs catches)
        (hb : InstrsT G { I with labels := none :: I.labels } body is) :
        InstrT G I [L (K "try_table" :: (header ++ cs ++ body))] (.tryTable t catches is)

  inductive InstrsT {Leaf : Type} (G : Core.IdCtx → List SExp → Leaf → Prop) :
      (I : Core.IdCtx) → List SExp → Wasm.Extensions.Structured.Expr Leaf → Prop where
    | nil {I : Core.IdCtx} : InstrsT G I [] []
    | cons {I : Core.IdCtx} {xs ys : List SExp} {i : Wasm.Extensions.Structured.Instr Leaf}
        {is : Wasm.Extensions.Structured.Expr Leaf} (hi : InstrT G I xs i) (hs : InstrsT G I ys is) :
        InstrsT G I (xs ++ ys) (i :: is)
end

end Silmaril.Wasm.Text.Extensions.Structured
