module

public import Silmaril.Wasm.Extensions.StructuredInstructions
public import Silmaril.Wasm.Binary.Core.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured

open Core

mutual
  inductive Instr {Leaf : Type} (F : Forms) (G : Bytes → Leaf → Prop) :
      Bytes → Wasm.Extensions.Structured.Instr Leaf → Prop where
    | leaf {b : Bytes} {i : Leaf} (h : G b i) : Instr F G b (.leaf i)
    /-- `0x02 bt:Bblocktype (in:Binstr)* 0x0B => BLOCK bt in*` (5.3:32). -/
    | block {bt b : Bytes} {t : Wasm.BlockType} {body : List (Wasm.Extensions.Structured.Instr Leaf)}
        (ht : Core.BlockType F bt t) (hb : Instrs F G b body) :
        Instr F G ([0x02] ++ bt ++ b ++ [0x0B]) (.block t body)
    /-- `0x03 bt:Bblocktype (in:Binstr)* 0x0B => LOOP bt in*` (5.3:33). -/
    | loop {bt b : Bytes} {t : Wasm.BlockType} {body : List (Wasm.Extensions.Structured.Instr Leaf)}
        (ht : Core.BlockType F bt t) (hb : Instrs F G b body) :
        Instr F G ([0x03] ++ bt ++ b ++ [0x0B]) (.loop t body)
    /-- `0x04 bt:Bblocktype (in:Binstr)* 0x0B => IF bt in* ELSE eps` (5.3:34). -/
    | if_ {bt b : Bytes} {t : Wasm.BlockType} {body : List (Wasm.Extensions.Structured.Instr Leaf)}
        (ht : Core.BlockType F bt t) (hb : Instrs F G b body) :
        Instr F G ([0x04] ++ bt ++ b ++ [0x0B]) (.if_ t body [])
    /-- `0x04 bt:Bblocktype (in_1:Binstr)* 0x05 (in_2:Binstr)* 0x0B => IF bt in_1* ELSE in_2*`
    (5.3:35–36). -/
    | ifElse {bt b₁ b₂ : Bytes} {t : Wasm.BlockType} {body₁ body₂ : List (Wasm.Extensions.Structured.Instr Leaf)}
        (ht : Core.BlockType F bt t) (h₁ : Instrs F G b₁ body₁) (h₂ : Instrs F G b₂ body₂) :
        Instr F G ([0x04] ++ bt ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B]) (.if_ t body₁ body₂)
    | tryTable {bt bc b : Bytes} {t : Wasm.BlockType} {cs : List Wasm.Catch}
        {body : List (Wasm.Extensions.Structured.Instr Leaf)} (ht : Core.BlockType F bt t) (hc : Vec Core.Catch bc cs)
        (hb : Instrs F G b body) : Instr F G ([0x1F] ++ bt ++ bc ++ b ++ [0x0B]) (.tryTable t cs body)

  inductive Instrs {Leaf : Type} (F : Forms) (G : Bytes → Leaf → Prop) :
      Bytes → List (Wasm.Extensions.Structured.Instr Leaf) → Prop where
    | nil : Instrs F G [] []
    | cons {b bs : Bytes} {i : Wasm.Extensions.Structured.Instr Leaf}
        {is : List (Wasm.Extensions.Structured.Instr Leaf)} (h : Instr F G b i)
        (hs : Instrs F G bs is) : Instrs F G (b ++ bs) (i :: is)
end

inductive Expr {Leaf : Type} (F : Forms) (G : Bytes → Leaf → Prop) :
    Bytes → Wasm.Extensions.Structured.Expr Leaf → Prop where
  | mk {b : Bytes} {is : List (Wasm.Extensions.Structured.Instr Leaf)}
      (h : Instrs F G b is) : Expr F G (b ++ [0x0B]) is

end Silmaril.Wasm.Binary.Extensions.Structured
