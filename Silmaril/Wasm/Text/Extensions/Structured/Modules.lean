module

public import Silmaril.Wasm.Extensions.StructuredInstructions
public import Silmaril.Wasm.Text.Extensions.SharedMemory.Modules
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

/-! # Canonical module syntax with a separate function-body language

Every retained module field is related to its text by an independent declarative
grammar. Only anonymous identifier/type context construction is shared with the
Core printer. In particular no Core grammar on an erased function body certifies
an extended function: `F` must relate the complete original body to its text.
This canonical grammar uses explicit type uses and separate export fields.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def ModuleT {Body : Type} (F : Core.IdCtx → SExp → Declaration.Func ValType Body → Prop)
    (shape : Body → Wasm.Expr) (x : SExp) (m : Wasm.Extensions.Structured.FunctionModule Body) : Prop :=
  let I := Wat.moduleContextAll (m.contextShape shape).coreShape
  I.Ok ∧ ∃ ts ims tags ms gs tables fs ds elems ss es : List SExp,
    x = doc [L (K "module" :: (ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es))] ∧
    List.Forall₂ (fun x t => Core.DeclT I x [.type t] (Wat.typeContext t) []) ts m.types ∧
    List.Forall₂ (fun x (im : Wasm.Extensions.SharedMemory.Import) => SharedMemory.DeclT I x
      (([.import_ im.coreShape], Wat.importContext im.coreShape, []), [im.type.isShared], [])) ims m.imports ∧
    List.Forall₂ (fun x t => Core.DeclT I x [.tag t] { tags := [none] } []) tags m.tags ∧
    List.Forall₂ (fun x (mem : Wasm.Extensions.SharedMemory.MemoryType) => SharedMemory.DeclT I x
      (([.mem mem.core], { mems := [none] }, []), [], [mem.shared])) ms m.memories ∧
    List.Forall₂ (fun x g => Core.DeclT I x [.global g] { globals := [none] } []) gs m.globals ∧
    List.Forall₂ (fun x t => Core.DeclT I x [.table t] { tables := [none] } []) tables m.tables ∧
    List.Forall₂ (F I) fs m.funcs ∧
    List.Forall₂ (fun x d => Core.DeclT I x [.data d] { datas := [none] } []) ds m.data ∧
    List.Forall₂ (fun x e => Core.DeclT I x [.elem e] { elems := [none] } []) elems m.elems ∧
    List.Forall₂ (fun x s => Core.DeclT I x [.start s] {} []) ss m.start.toList ∧
    List.Forall₂ (fun x e => Core.DeclT I x [.export_ e] {} []) es m.exports

def Encodes {Body : Type} (F : Core.IdCtx → SExp → Declaration.Func ValType Body → Prop)
    (shape : Body → Wasm.Expr) : EncRel String (Wasm.Extensions.Structured.FunctionModule Body) :=
  Formats.SExpEncoding.Wat.sexpWat3 ⨾ ModuleT F shape

end Silmaril.Wasm.Text.Extensions.Structured
