module

public import Silmaril.Wasm.Binary.Extensions.Structured.Instructions
public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Modules

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured

open Core

inductive Func {Body : Type} (F : Forms) (E : Bytes → Body → Prop) :
    Bytes → List Wasm.ValType × Body → Prop where
  | mk {bl be : Bytes} {lss : List (List Wasm.ValType)} {e : Body}
      (hl : Vec (Core.Locals F) bl lss) (he : E be e) (hlen : lss.flatten.length < 2 ^ 32) :
      Func F E (bl ++ be) (lss.flatten, e)

inductive Code {Body : Type} (F : Forms) (E : Bytes → Body → Prop) :
    Bytes → List Wasm.ValType × Body → Prop where
  | mk {bl c : Bytes} {len : Nat} {code : List Wasm.ValType × Body} (hl : U32 bl len)
      (hlen : len = c.length) (h : Func F E c code) : Code F E (bl ++ c) code

abbrev CodeSec {Body : Type} (F : Forms) (E : Bytes → Body → Prop) :=
  Section 10 (Vec (Code F E))

def zipFuncs {Body : Type} (xs : List TypeIdx) (codes : List (List Wasm.ValType × Body)) :
    List (Wasm.Declaration.Func Wasm.ValType Body) :=
  List.zipWith (fun x c => ⟨x, c.1, c.2⟩) xs codes

def codesDataIdxs {Body : Type} (dataIdxs : Body → List DataIdx)
    (codes : List (List Wasm.ValType × Body)) : List DataIdx := codes.flatMap fun c => dataIdxs c.2

inductive Module {Body : Type} (F : Forms) (E : Bytes → Body → Prop) (dataIdxs : Body → List DataIdx) :
    Bytes → Wasm.Extensions.Structured.FunctionModule Body → Prop where
  | mk {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes}
      {bty bim bfn btb bme btg bgl bex bst bel bdc bco bda : Bytes}
      {types : List Wasm.RecType} {imports : List Wasm.Extensions.SharedMemory.Import} {typeidxs : List TypeIdx}
      {tables : List Wasm.Table} {mems : List Wasm.Extensions.SharedMemory.MemoryType} {tags : List Wasm.TagType}
      {globals : List Wasm.Global} {exports : List Wasm.Export} {start : Option FuncIdx}
      {elems : List Wasm.Elem} {nopt : Option Nat}
      {codes : List (List Wasm.ValType × Body)} {data : List Wasm.Data}
      (h₀ : Customs c₀) (hty : TypeSec F bty types)
      (h₁ : Customs c₁) (him : SharedMemory.ImportSec F bim imports)
      (h₂ : Customs c₂) (hfn : FuncSec bfn typeidxs)
      (h₃ : Customs c₃) (htb : TableSec F btb tables)
      (h₄ : Customs c₄) (hme : Section 5 (Vec (SharedMemory.MemType F)) bme mems)
      (h₅ : Customs c₅) (htg : TagSec F btg tags)
      (h₆ : Customs c₆) (hgl : GlobalSec F bgl globals)
      (h₇ : Customs c₇) (hex : ExportSec bex exports)
      (h₈ : Customs c₈) (hst : StartSec bst start)
      (h₉ : Customs c₉) (hel : ElemSec F bel elems)
      (h₁₀ : Customs c₁₀) (hdc : DataCntSec F bdc nopt)
      (h₁₁ : Customs c₁₁) (hco : CodeSec F E bco codes)
      (h₁₂ : Customs c₁₂) (hda : DataSec F bda data)
      (h₁₃ : Customs c₁₃)
      (hcount : ∀ n ∈ nopt, n = data.length)
      (hdataidx : nopt.isSome ∨ codesDataIdxs dataIdxs codes = [])
      (hfuncs : typeidxs.length = codes.length) :
      Module F E dataIdxs (magic ++ version ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfn ++ c₃ ++ btb ++
          c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++
          c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃)
        { types, imports, tags, globals, memories := mems, tables,
          funcs := zipFuncs typeidxs codes, data, elems, start, exports }

end Silmaril.Wasm.Binary.Extensions.Structured
