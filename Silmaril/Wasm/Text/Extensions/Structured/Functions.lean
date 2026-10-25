module

public import Silmaril.Wasm.Text.Extensions.Structured.Instructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding

/-- Explicit function syntax with an independent leaf grammar. Types and locals
use Core's declarative protocol; the retained body uses the extension grammar.
Module-level exports are declared separately in canonical disassembly. -/
inductive FuncT {Leaf : Type} (G : Core.IdCtx → List SExp → Leaf → Prop) (I : Core.IdCtx) :
    SExp → Declaration.Func ValType (Wasm.Extensions.Structured.Expr Leaf) → Prop where
  | func {tu lx body : List SExp} {t : TypeIdx} {params : List (Option String)}
      {locs : List (ValType × Option String)} {e : Wasm.Extensions.Structured.Expr Leaf}
      (ht : Core.TypeUseT I tu t params []) (hl : Core.Concat (Core.LocalT I) lx locs)
      (hok : (I ++ { locals := params ++ locs.map Prod.snd }).Ok)
      (hb : InstrsT G (I ++ { locals := params ++ locs.map Prod.snd }) body e) :
      FuncT G I (L (K "func" :: (tu ++ lx ++ body))) ⟨t, locs.map Prod.fst, e⟩

end Silmaril.Wasm.Text.Extensions.Structured
