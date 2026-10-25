module

public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Types
public import Silmaril.Wasm.Binary.Core.Modules

/-! # Original module bytes with shared memories and compact imports

Only memory types and the import descriptors containing them are extended.
All instructions and every other section reuse their independent Core grammar.
The compact-import grouping forms are those of Binaryen version_133; grouping
counts groups and preserves the expanded order. This relation carries shared
metadata in the output and makes no claim about concurrent execution.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory

open Core

inductive ExternType (F : Forms) : Bytes → Wasm.Extensions.SharedMemory.ExternType → Prop where
  | func {b : Bytes} {x : TypeIdx} (h : Index b x) : ExternType F ([0x00] ++ b) (.func x)
  | table {b : Bytes} {tt : Wasm.TableType} (h : Core.TableType F b tt) :
      ExternType F ([0x01] ++ b) (.table tt)
  | memory {b : Bytes} {mt : Wasm.Extensions.SharedMemory.MemoryType} (h : MemType F b mt) :
      ExternType F ([0x02] ++ b) (.memory mt)
  | global {b : Bytes} {gt : Wasm.GlobalType} (h : Core.GlobalType F b gt) :
      ExternType F ([0x03] ++ b) (.global gt)
  | tag {b : Bytes} {jt : Wasm.TagType} (h : Core.TagType b jt) : ExternType F ([0x04] ++ b) (.tag jt)

inductive Item (F : Forms) : Bytes → (String × Wasm.Extensions.SharedMemory.ExternType) → Prop where
  | mk {bn bt : Bytes} {n : String} {t : Wasm.Extensions.SharedMemory.ExternType}
      (hn : Name bn n) (ht : ExternType F bt t) : Item F (bn ++ bt) (n, t)

def expandItems (m : String) (xs : List (String × Wasm.Extensions.SharedMemory.ExternType)) : List Wasm.Extensions.SharedMemory.Import :=
  xs.map fun (n, t) => ⟨m, n, t⟩

def expandNames (m : String) (t : Wasm.Extensions.SharedMemory.ExternType) (ns : List String) : List Wasm.Extensions.SharedMemory.Import :=
  ns.map fun n => ⟨m, n, t⟩

inductive Tail (F : Forms) (m : String) : String → Bytes → List Wasm.Extensions.SharedMemory.Import → Prop where
  | single {n : String} {b : Bytes} {t : Wasm.Extensions.SharedMemory.ExternType} (ht : ExternType F b t) :
      Tail F m n b [⟨m, n, t⟩]
  | sharedModule {b : Bytes} {xs : List (String × Wasm.Extensions.SharedMemory.ExternType)}
      (h : Vec (Item F) b xs) : Tail F m "" ([0x7f] ++ b) (expandItems m xs)
  | sharedAll {bt bn : Bytes} {t : Wasm.Extensions.SharedMemory.ExternType} {ns : List String}
      (ht : ExternType F bt t) (hn : Vec Name bn ns) :
      Tail F m "" ([0x7e] ++ bt ++ bn) (expandNames m t ns)

inductive Group (F : Forms) : Bytes → List Wasm.Extensions.SharedMemory.Import → Prop where
  | mk {bm bn bt : Bytes} {m n : String} {xs : List Wasm.Extensions.SharedMemory.Import}
      (hm : Name bm m) (hn : Name bn n) (ht : Tail F m n bt xs) :
      Group F (bm ++ bn ++ bt) xs

inductive ImportBody (F : Forms) : Bytes → List Wasm.Extensions.SharedMemory.Import → Prop where
  | mk {b : Bytes} {groups : List (List Wasm.Extensions.SharedMemory.Import)}
      (h : Vec (Group F) b groups) : ImportBody F b groups.flatten

abbrev ImportSec (F : Forms) := Section 2 (ImportBody F)

inductive Module (F : Forms) :
    Bytes → Wasm.Extensions.SharedMemory.Module → Prop where
  | mk {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes}
      {bty bim bfn btb bme btg bgl bex bst bel bdc bco bda : Bytes}
      {types : List Wasm.RecType} {imports : List Wasm.Extensions.SharedMemory.Import} {typeidxs : List TypeIdx}
      {tables : List Wasm.Table} {mems : List Wasm.Extensions.SharedMemory.MemoryType} {tags : List Wasm.TagType}
      {globals : List Wasm.Global} {exports : List Wasm.Export} {start : Option FuncIdx}
      {elems : List Wasm.Elem} {nopt : Option Nat}
      {codes : List (List Wasm.ValType × Wasm.Expr)} {data : List Wasm.Data}
      (h₀ : Customs c₀) (hty : TypeSec F bty types)
      (h₁ : Customs c₁) (him : ImportSec F bim imports)
      (h₂ : Customs c₂) (hfn : FuncSec bfn typeidxs)
      (h₃ : Customs c₃) (htb : TableSec F btb tables)
      (h₄ : Customs c₄) (hme : Section 5 (Vec (MemType F)) bme mems)
      (h₅ : Customs c₅) (htg : TagSec F btg tags)
      (h₆ : Customs c₆) (hgl : GlobalSec F bgl globals)
      (h₇ : Customs c₇) (hex : ExportSec bex exports)
      (h₈ : Customs c₈) (hst : StartSec bst start)
      (h₉ : Customs c₉) (hel : ElemSec F bel elems)
      (h₁₀ : Customs c₁₀) (hdc : DataCntSec F bdc nopt)
      (h₁₁ : Customs c₁₁) (hco : CodeSec F bco codes)
      (h₁₂ : Customs c₁₂) (hda : DataSec F bda data)
      (h₁₃ : Customs c₁₃)
      (hcount : ∀ n ∈ nopt, n = data.length)
      (hdataidx : nopt.isSome ∨ codesDataIdxs codes = [])
      (hfuncs : typeidxs.length = codes.length) :
      Module F (magic ++ version ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfn ++ c₃ ++ btb ++
          c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++
          c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃)
        { types, imports, tags, globals, memories := mems, tables,
          funcs := zipFuncs typeidxs codes, data, elems, start, exports }

/-- Exact original bytes in the supported shared-memory/compact-import syntax. -/
abbrev Encodes : Bytes → Wasm.Extensions.SharedMemory.Module → Prop := Module Forms.all

end Silmaril.Wasm.Binary.Extensions.SharedMemory
