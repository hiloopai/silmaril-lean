module

public import Silmaril.Wasm.Binary.Core.Instructions
public import Silmaril.Wasm.Modules
public import Silmaril.Encoding

/-! # Core 3.0 binary format: modules

Transcribed rule by rule from `5.4-binary.modules.spectec` (cited `5.4:n`),
including section order, interleaved custom sections, the data count section and
the module rule's side conditions:

* the data count, when present, equals the number of data segments;
* without a data count section, the code mentions no data index;
* the function and code sections have equal lengths (the spec's iteration
  `(if func = FUNC typeidx local* expr)*` zips them).

Custom sections are not part of the abstract syntax, so their contents are
unconstrained beyond their own grammar.

`Encoding Wasm.Module` is `Module Forms.all`, the specification's grammar.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Core

/-! ## Sections -/

/-- `Btype = qt:Brectype => TYPE qt`; `Btypesec = Bsection_(1, Blist(Btype))` (5.4:25–29). -/
abbrev TypeSec (F : Forms) := Section 1 (Vec (RecType F))

/-- `Bimport = nm_1:Bname nm_2:Bname xt:Bexterntype => IMPORT nm_1 nm_2 xt` (5.4:34–35). -/
inductive Import (F : Forms) : Bytes → Wasm.Import → Prop where
  | mk {b₁ b₂ b₃ : Bytes} {m n : String} {xt : Wasm.ExternType} (h₁ : Name b₁ m) (h₂ : Name b₂ n)
      (h₃ : ExternType F b₃ xt) : Import F (b₁ ++ b₂ ++ b₃) ⟨m, n, xt⟩

/-- `Bimportsec = Bsection_(2, Blist(Bimport))` (5.4:37–38). -/
abbrev ImportSec (F : Forms) := Section 2 (Vec (Import F))

/-- `Bfuncsec = x*:Bsection_(3, Blist(Btypeidx))` (5.4:43–44). -/
abbrev FuncSec := Section 3 (Vec (Index (k := .type_)))

/-- `Btable` (5.4:49–51): a bare table type initializes with `REF.NULL ht`; the
explicit form `0x40 0x00 tt e` is `Form.tableInit`. -/
inductive Table (F : Forms) : Bytes → Wasm.Table → Prop where
  | implicit {b : Bytes} {tt : Wasm.TableType} (h : TableType F b tt) :
      Table F b ⟨tt, [.refNull tt.element.heap]⟩
  | explicit {b be : Bytes} {tt : Wasm.TableType} {e : Wasm.Expr} (g : F .tableInit = true)
      (h : TableType F b tt) (he : Expr F be e) : Table F ([0x40, 0x00] ++ b ++ be) ⟨tt, e⟩

/-- `Btablesec = Bsection_(4, Blist(Btable))` (5.4:53–54). -/
abbrev TableSec (F : Forms) := Section 4 (Vec (Table F))

/-- `Bmem = mt:Bmemtype => MEMORY mt` (5.4:59–60). -/
abbrev Mem (F : Forms) := MemType F

/-- `Bmemsec = Bsection_(5, Blist(Bmem))` (5.4:62–63). -/
abbrev MemSec (F : Forms) := Section 5 (Vec (Mem F))

/-- `Bglobal = gt:Bglobaltype e:Bexpr => GLOBAL gt e` (5.4:68–69). -/
inductive Global (F : Forms) : Bytes → Wasm.Global → Prop where
  | mk {b be : Bytes} {gt : Wasm.GlobalType} {e : Wasm.Expr} (h : GlobalType F b gt)
      (he : Expr F be e) : Global F (b ++ be) ⟨gt, e⟩

/-- `Bglobalsec = Bsection_(6, Blist(Bglobal))` (5.4:71–72). -/
abbrev GlobalSec (F : Forms) := Section 6 (Vec (Global F))

/-- `Bexternidx` (5.1:84–89). -/
inductive ExternIdx : Bytes → Wasm.ExternIdx → Prop where
  | func {b : Bytes} {x : FuncIdx} (h : Index b x) : ExternIdx ([0x00] ++ b) (.func x)
  | table {b : Bytes} {x : TableIdx} (h : Index b x) : ExternIdx ([0x01] ++ b) (.table x)
  | memory {b : Bytes} {x : MemIdx} (h : Index b x) : ExternIdx ([0x02] ++ b) (.memory x)
  | global {b : Bytes} {x : GlobalIdx} (h : Index b x) : ExternIdx ([0x03] ++ b) (.global x)
  | tag {b : Bytes} {x : TagIdx} (h : Index b x) : ExternIdx ([0x04] ++ b) (.tag x)

/-- `Bexport = nm:Bname xx:Bexternidx => EXPORT nm xx` (5.4:77–78). -/
inductive Export : Bytes → Wasm.Export → Prop where
  | mk {b b' : Bytes} {n : String} {x : Wasm.ExternIdx} (h : Name b n) (h' : ExternIdx b' x) :
      Export (b ++ b') ⟨n, x⟩

/-- `Bexportsec = Bsection_(7, Blist(Bexport))` (5.4:80–81). -/
abbrev ExportSec := Section 7 (Vec Export)

/-- `Belemkind = 0x00 => REF FUNC` (5.4:97–98). Note: the non-null `(ref func)`. -/
inductive ElemKind : Bytes → Wasm.RefType → Prop where
  | func : ElemKind [0x00] ⟨false, .abstract .func⟩

/-- `(REF.FUNC y)*`, the initializers of a function-index element segment. -/
def refFuncs (ys : List FuncIdx) : List Wasm.Expr := ys.map fun y => [.refFunc y]

/-- `Belem` (5.4:100–116). Kinds other than `0` are `Form.elemKinds`. -/
inductive Elem (F : Forms) : Bytes → Wasm.Elem → Prop where
  /-- `0:Bu32 e_o:Bexpr y*:Blist(Bfuncidx) => ELEM (REF FUNC) (REF.FUNC y)* (ACTIVE 0 e_o)`. -/
  | k0 {bk be bys : Bytes} {e : Wasm.Expr} {ys : List FuncIdx} (hk : U32 bk 0)
      (he : Expr F be e) (hy : Vec Index bys ys) :
      Elem F (bk ++ be ++ bys) ⟨⟨false, .abstract .func⟩, refFuncs ys, .active ⟨0⟩ e⟩
  /-- `1:Bu32 rt:Belemkind y*:Blist(Bfuncidx) => ELEM rt (REF.FUNC y)* PASSIVE`. -/
  | k1 {bk br bys : Bytes} {rt : Wasm.RefType} {ys : List FuncIdx} (g : F .elemKinds = true)
      (hk : U32 bk 1) (hr : ElemKind br rt) (hy : Vec Index bys ys) :
      Elem F (bk ++ br ++ bys) ⟨rt, refFuncs ys, .passive⟩
  /-- `2:Bu32 x:Btableidx e:Bexpr rt:Belemkind y*:Blist(Bfuncidx) => ELEM rt (REF.FUNC y)* (ACTIVE
      x e)`. -/
  | k2 {bk bx be br bys : Bytes} {x : TableIdx} {e : Wasm.Expr} {rt : Wasm.RefType}
      {ys : List FuncIdx} (g : F .elemKinds = true) (hk : U32 bk 2) (hx : Index bx x)
      (he : Expr F be e) (hr : ElemKind br rt) (hy : Vec Index bys ys) :
      Elem F (bk ++ bx ++ be ++ br ++ bys) ⟨rt, refFuncs ys, .active x e⟩
  /-- `3:Bu32 rt:Belemkind y*:Blist(Bfuncidx) => ELEM rt (REF.FUNC y)* DECLARE`. -/
  | k3 {bk br bys : Bytes} {rt : Wasm.RefType} {ys : List FuncIdx} (g : F .elemKinds = true)
      (hk : U32 bk 3) (hr : ElemKind br rt) (hy : Vec Index bys ys) :
      Elem F (bk ++ br ++ bys) ⟨rt, refFuncs ys, .declarative⟩
  /-- `4:Bu32 e_O:Bexpr e*:Blist(Bexpr) => ELEM (REF NULL FUNC) e* (ACTIVE 0 e_O)`. -/
  | k4 {bk be bes : Bytes} {e : Wasm.Expr} {es : List Wasm.Expr} (g : F .elemKinds = true)
      (hk : U32 bk 4) (he : Expr F be e) (hes : Vec (Expr F) bes es) :
      Elem F (bk ++ be ++ bes) ⟨⟨true, .abstract .func⟩, es, .active ⟨0⟩ e⟩
  /-- `5:Bu32 rt:Breftype e*:Blist(Bexpr) => ELEM rt e* PASSIVE`. -/
  | k5 {bk br bes : Bytes} {rt : Wasm.RefType} {es : List Wasm.Expr} (g : F .elemKinds = true)
      (hk : U32 bk 5) (hr : RefType F br rt) (hes : Vec (Expr F) bes es) :
      Elem F (bk ++ br ++ bes) ⟨rt, es, .passive⟩
  /-- `6:Bu32 x:Btableidx e_O:Bexpr rt:Breftype e*:Blist(Bexpr) => ELEM rt e* (ACTIVE x e_O)`. -/
  | k6 {bk bx be br bes : Bytes} {x : TableIdx} {e : Wasm.Expr} {rt : Wasm.RefType}
      {es : List Wasm.Expr} (g : F .elemKinds = true) (hk : U32 bk 6) (hx : Index bx x)
      (he : Expr F be e) (hr : RefType F br rt) (hes : Vec (Expr F) bes es) :
      Elem F (bk ++ bx ++ be ++ br ++ bes) ⟨rt, es, .active x e⟩
  /-- `7:Bu32 rt:Breftype e*:Blist(Bexpr) => ELEM rt e* DECLARE`. -/
  | k7 {bk br bes : Bytes} {rt : Wasm.RefType} {es : List Wasm.Expr} (g : F .elemKinds = true)
      (hk : U32 bk 7) (hr : RefType F br rt) (hes : Vec (Expr F) bes es) :
      Elem F (bk ++ br ++ bes) ⟨rt, es, .declarative⟩

/-- `Belemsec = Bsection_(9, Blist(Belem))` (5.4:118–119). -/
abbrev ElemSec (F : Forms) := Section 9 (Vec (Elem F))

/-- `Blocals = n:Bu32 t:Bvaltype => (LOCAL t)^n` (5.4:126–127). -/
inductive Locals (F : Forms) : Bytes → List Wasm.ValType → Prop where
  | mk {bn bt : Bytes} {n : Nat} {t : Wasm.ValType} (hn : U32 bn n) (ht : ValType F bt t) :
      Locals F (bn ++ bt) (List.replicate n t)

/-- `Bfunc = loc**:Blist(Blocals) e:Bexpr => ($concat_(local, loc**), e)
-- if |$concat_(local, loc**)| < 2^32` (5.4:129–131). -/
inductive Func (F : Forms) : Bytes → List Wasm.ValType × Wasm.Expr → Prop where
  | mk {bl be : Bytes} {lss : List (List Wasm.ValType)} {e : Wasm.Expr}
      (hl : Vec (Locals F) bl lss) (he : Expr F be e) (hlen : lss.flatten.length < 2 ^ 32) :
      Func F (bl ++ be) (lss.flatten, e)

/-- `Bcode = len:Bu32 code:Bfunc => code -- if len = ||Bfunc||` (5.4:133–134). -/
inductive Code (F : Forms) : Bytes → List Wasm.ValType × Wasm.Expr → Prop where
  | mk {bl c : Bytes} {len : Nat} {code : List Wasm.ValType × Wasm.Expr} (hl : U32 bl len)
      (hlen : len = c.length) (h : Func F c code) : Code F (bl ++ c) code

/-- `Bcodesec = Bsection_(10, Blist(Bcode))` (5.4:136–137). -/
abbrev CodeSec (F : Forms) := Section 10 (Vec (Code F))

/-- A data segment's bytes. -/
def dataBytes (bs : List UInt8) : ByteArray := ⟨bs.toArray⟩

/-- `Bdata` (5.4:142–145). Kinds `1` and `2` are `Form.dataKinds`. -/
inductive Data (F : Forms) : Bytes → Wasm.Data → Prop where
  /-- `0:Bu32 e:Bexpr b*:Blist(Bbyte) => DATA b* (ACTIVE 0 e)`. -/
  | k0 {bk be bb : Bytes} {e : Wasm.Expr} {bs : List UInt8} (hk : U32 bk 0) (he : Expr F be e)
      (hb : ByteVec bb bs) : Data F (bk ++ be ++ bb) ⟨dataBytes bs, .active ⟨0⟩ e⟩
  /-- `1:Bu32 b*:Blist(Bbyte) => DATA b* PASSIVE`. -/
  | k1 {bk bb : Bytes} {bs : List UInt8} (g : F .dataKinds = true) (hk : U32 bk 1)
      (hb : ByteVec bb bs) : Data F (bk ++ bb) ⟨dataBytes bs, .passive⟩
  /-- `2:Bu32 x:Bmemidx e:Bexpr b*:Blist(Bbyte) => DATA b* (ACTIVE x e)`. -/
  | k2 {bk bx be bb : Bytes} {x : MemIdx} {e : Wasm.Expr} {bs : List UInt8}
      (g : F .dataKinds = true) (hk : U32 bk 2) (hx : Index bx x) (he : Expr F be e)
      (hb : ByteVec bb bs) : Data F (bk ++ bx ++ be ++ bb) ⟨dataBytes bs, .active x e⟩

/-- `Bdatasec = Bsection_(11, Blist(Bdata))` (5.4:147–148). -/
abbrev DataSec (F : Forms) := Section 11 (Vec (Data F))

/-- `Bdatacnt : u32* = n:Bu32 => n` (5.4:153–154). -/
inductive DataCnt : Bytes → List Nat → Prop where
  | mk {b : Bytes} {n : Nat} (h : U32 b n) : DataCnt b [n]

/-- `Bdatacntsec : u32? = nopt:Bsection_(12, Bdatacnt) => $opt_(u32, nopt)` (5.4:158–159);
a present section is `Form.dataCount`. -/
inductive DataCntSec (F : Forms) : Bytes → Option Nat → Prop where
  | present {b : Bytes} {ns : List Nat} (g : F .dataCount = true) (h : Section 12 DataCnt b ns) :
      DataCntSec F b ns.head?
  | absent : DataCntSec F [] none

/-- `Btag = jt:Btagtype => TAG jt` (5.4:164–165). -/
abbrev Tag := TagType

/-- `Btagsec = Bsection_(13, Blist(Btag))` (5.4:167–168); a present section is
`Form.tagSection`. -/
inductive TagSec (F : Forms) : Bytes → List Wasm.TagType → Prop where
  | present {b : Bytes} {ts : List Wasm.TagType} (g : F .tagSection = true)
      (h : Section 13 (Vec Tag) b ts) : TagSec F b ts
  | absent : TagSec F [] []

/-- The functions of a module from its function and code sections. -/
def zipFuncs (xs : List TypeIdx) (codes : List (List Wasm.ValType × Wasm.Expr)) :
    List Wasm.Func :=
  List.zipWith (fun x c => ⟨x, c.1, c.2⟩) xs codes

/-- `$dataidx_funcs(func*)`: the data indices mentioned by function bodies. -/
def codesDataIdxs (codes : List (List Wasm.ValType × Wasm.Expr)) : List DataIdx :=
  codes.flatMap fun c => Expr.dataIdxs c.2

/-! ## Modules (5.4:173–195) -/

/-- `Bmodule` (5.4:175–195). -/
inductive ModuleWithImports (F : Forms) (I : Bytes → List Wasm.Import → Prop) :
    Bytes → Wasm.Module → Prop where
  | mk {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes}
      {bty bim bfn btb bme btg bgl bex bst bel bdc bco bda : Bytes}
      {types : List Wasm.RecType} {imports : List Wasm.Import} {typeidxs : List TypeIdx}
      {tables : List Wasm.Table} {mems : List Wasm.MemoryType} {tags : List Wasm.TagType}
      {globals : List Wasm.Global} {exports : List Wasm.Export} {start : Option FuncIdx}
      {elems : List Wasm.Elem} {nopt : Option Nat}
      {codes : List (List Wasm.ValType × Wasm.Expr)} {data : List Wasm.Data}
      (h₀ : Customs c₀) (hty : TypeSec F bty types)
      (h₁ : Customs c₁) (him : Section 2 I bim imports)
      (h₂ : Customs c₂) (hfn : FuncSec bfn typeidxs)
      (h₃ : Customs c₃) (htb : TableSec F btb tables)
      (h₄ : Customs c₄) (hme : MemSec F bme mems)
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
      ModuleWithImports F I (magic ++ version ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfn ++ c₃ ++ btb ++
          c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++
          c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃)
        { types, imports, tags, globals, memories := mems, tables,
          funcs := zipFuncs typeidxs codes, data, elems, start, exports }

/-- The standard module grammar retains its ordinary import-section body. -/
abbrev Module (F : Forms) := ModuleWithImports F (Vec (Import F))

/-- The original standard-module constructor, specialized to ordinary imports. -/
abbrev Module.mk {F : Forms} := @ModuleWithImports.mk F (Vec (Import F))

/-- Preserve the public eliminators of the original standard module grammar. -/
abbrev Module.rec {F : Forms} := @ModuleWithImports.rec F (Vec (Import F))

abbrev Module.recOn {F : Forms} := @ModuleWithImports.recOn F (Vec (Import F))

abbrev Module.casesOn {F : Forms} := @ModuleWithImports.casesOn F (Vec (Import F))

/-- The specification's relation: every Core 3.0 encoding form is enabled. -/
abbrev Encodes : Bytes → Wasm.Module → Prop := Module Forms.all

end Silmaril.Wasm.Binary.Core

namespace Silmaril.Wasm

instance : Encoding Module := ⟨Binary.Core.Encodes⟩

end Silmaril.Wasm

namespace Silmaril.Wasm.Binary.Core

/-! ## Properties -/

/-! ### Generic helpers -/

/-- One step of a left-to-right parse: a prefix-free production fixes its bytes, its
value and the remaining input. -/
private theorem step {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) {b b' r r' : Bytes}
    {a a' : α} (e : b ++ r = b' ++ r') (ha : G b a) (ha' : G b' a') :
    b = b' ∧ a = a' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := h ha ha' e
  exact ⟨rfl, rfl, List.append_cancel_left e⟩

private theorem seq_mono {α : Type} {G G' : Bytes → α → Prop} (hG : ∀ {b a}, G b a → G' b a)
    {b : Bytes} {xs : List α} (h : Seq G b xs) : Seq G' b xs := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (hG ha) ih

private theorem vec_mono {α : Type} {G G' : Bytes → α → Prop} (hG : ∀ {b a}, G b a → G' b a)
    {b : Bytes} {xs : List α} (h : Vec G b xs) : Vec G' b xs := by
  cases h with
  | mk hn hs => exact .mk hn (seq_mono hG hs)

private theorem seq_append {α : Type} {G : Bytes → α → Prop} {b₁ b₂ : Bytes} {l₁ l₂ : List α}
    (h₁ : Seq G b₁ l₁) (h₂ : Seq G b₂ l₂) : Seq G (b₁ ++ b₂) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons ha _ ih => simpa only [List.append_assoc, List.cons_append] using Seq.cons ha ih

/-! ### Sections -/

theorem Section.iff {α : Type} {N : UInt8} {G : Bytes → List α → Prop} {b : Bytes}
    {xs : List α} :
    Section N G b xs ↔ (b = [] ∧ xs = []) ∨
      ∃ lb c len, U32 lb len ∧ len = c.length ∧ G c xs ∧ b = [N] ++ lb ++ c := by
  constructor
  · rintro (⟨hl, hlen, hc⟩ | _)
    · exact .inr ⟨_, _, _, hl, hlen, hc, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨lb, c, len, hl, hlen, hc, rfl⟩)
    · exact .empty
    · exact .mk hl hlen hc

theorem Section.mono {α : Type} {N : UInt8} {G G' : Bytes → List α → Prop}
    (hG : ∀ {b xs}, G b xs → G' b xs) {b : Bytes} {xs : List α} (h : Section N G b xs) :
    Section N G' b xs := by
  cases h with
  | mk hl hlen hc => exact .mk hl hlen (hG hc)
  | empty => exact .empty

theorem Section.functional {α : Type} {N : UInt8} {G : Bytes → List α → Prop}
    (hG : Functional G) : Functional (Section N G) := by
  intro b xs xs' h h'
  rcases Section.iff.mp h with ⟨rfl, rfl⟩ | ⟨lb, c, len, hl, hlen, hc, rfl⟩ <;>
    rcases Section.iff.mp h' with ⟨he, rfl⟩ | ⟨lb', c', len', hl', hlen', hc', he⟩
  · rfl
  · simp at he
  · simp at he
  · simp only [List.cons_append, List.cons.injEq, true_and] at he
    obtain ⟨rfl, rfl, he⟩ := step (UN.prefixFree 32) he hl hl'
    obtain rfl := he
    exact hG hc hc'

private theorem section_eq {α : Type} {N : UInt8} {G : Bytes → List α → Prop}
    (hG : Functional G) {b b' : Bytes} {xs xs' : List α} (h : Section N G b xs)
    (h' : Section N G b' xs') (hb : b = b') : xs = xs' := by
  subst hb
  exact Section.functional hG h h'

/-! ### Imports, tables, memories, globals, exports -/

/-- A table type never begins with `0x40`, the explicit table form's tag. -/
private theorem TableType.head {F : Forms} {b : Bytes} {t : Wasm.TableType}
    (ht : TableType F b t) : ∃ x rest, b = x :: rest ∧ x ≠ 0x40 := by
  cases ht with
  | mk hr _ =>
    cases hr with
    | null _ _ => exact ⟨_, _, rfl, by decide⟩
    | nonNull _ _ => exact ⟨_, _, rfl, by decide⟩
    | abs h => cases h <;> exact ⟨_, _, rfl, by decide⟩

theorem Import.mono {F G : Forms} (h : F.Le G) {b : Bytes} {i : Wasm.Import}
    (hi : Import F b i) : Import G b i := by
  cases hi with
  | mk h₁ h₂ h₃ => exact .mk h₁ h₂ (ExternType.mono h h₃)

theorem Import.prefixFree (F : Forms) : PrefixFree (Import F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk h₁ h₂ h₃ =>
    cases ha' with
    | mk h₁' h₂' h₃' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e h₁ h₁'
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e h₂ h₂'
      obtain ⟨rfl, rfl, -⟩ := step (ExternType.prefixFree F) e h₃ h₃'
      exact ⟨rfl, rfl⟩

theorem Table.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.Table}
    (ht : Table F b t) : Table G b t := by
  cases ht with
  | implicit ht => exact .implicit (TableType.mono h ht)
  | explicit g ht he => exact .explicit (h _ g) (TableType.mono h ht) (Expr.mono h he)

theorem Table.prefixFree (F : Forms) : PrefixFree (Table F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | implicit ht =>
    cases ha' with
    | implicit ht' =>
      obtain ⟨rfl, rfl⟩ := TableType.prefixFree F ht ht' e
      exact ⟨rfl, rfl⟩
    | explicit _ _ _ =>
      obtain ⟨x, rest, rfl, hx⟩ := ht.head
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e
      exact absurd e.1 hx
  | explicit _ ht he =>
    cases ha' with
    | implicit ht' =>
      obtain ⟨x, rest, rfl, hx⟩ := ht'.head
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e
      exact absurd e.1.symm hx
    | explicit _ ht' he' =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and,
        List.nil_append] at e
      obtain ⟨rfl, rfl, e⟩ := step (TableType.prefixFree F) e ht ht'
      obtain ⟨rfl, rfl, -⟩ := step (Expr.prefixFree F) e he he'
      exact ⟨rfl, rfl⟩

theorem Global.mono {F G : Forms} (h : F.Le G) {b : Bytes} {g : Wasm.Global}
    (hg : Global F b g) : Global G b g := by
  cases hg with
  | mk ht he => exact .mk (GlobalType.mono h ht) (Expr.mono h he)

theorem Global.prefixFree (F : Forms) : PrefixFree (Global F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk ht he =>
    cases ha' with
    | mk ht' he' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step (GlobalType.prefixFree F) e ht ht'
      obtain ⟨rfl, rfl, -⟩ := step (Expr.prefixFree F) e he he'
      exact ⟨rfl, rfl⟩

theorem ExternIdx.prefixFree : PrefixFree ExternIdx := by
  intro _ _ r r' _ _ ha ha' e
  cases ha <;> cases ha' <;>
    simp only [List.cons_append, List.cons.injEq] at e <;>
    first
    | exact absurd e.1 (by decide)
    | obtain ⟨rfl, rfl, -⟩ := step Index.prefixFree e.2 (by assumption) (by assumption)
      exact ⟨rfl, rfl⟩

theorem Export.prefixFree : PrefixFree Export := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk h₁ h₂ =>
    cases ha' with
    | mk h₁' h₂' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e h₁ h₁'
      obtain ⟨rfl, rfl, -⟩ := step ExternIdx.prefixFree e h₂ h₂'
      exact ⟨rfl, rfl⟩

/-! ### Element segments -/

theorem ElemKind.prefixFree : PrefixFree ElemKind := by
  intro _ _ r r' _ _ ha ha' _
  cases ha
  cases ha'
  exact ⟨rfl, rfl⟩

theorem Elem.mono {F G : Forms} (h : F.Le G) {b : Bytes} {e : Wasm.Elem}
    (he : Elem F b e) : Elem G b e := by
  cases he with
  | k0 hk he hy => exact .k0 hk (Expr.mono h he) hy
  | k1 g hk hr hy => exact .k1 (h _ g) hk hr hy
  | k2 g hk hx he hr hy => exact .k2 (h _ g) hk hx (Expr.mono h he) hr hy
  | k3 g hk hr hy => exact .k3 (h _ g) hk hr hy
  | k4 g hk he hes => exact .k4 (h _ g) hk (Expr.mono h he) (vec_mono (Expr.mono h) hes)
  | k5 g hk hr hes => exact .k5 (h _ g) hk (RefType.mono h hr) (vec_mono (Expr.mono h) hes)
  | k6 g hk hx he hr hes =>
    exact .k6 (h _ g) hk hx (Expr.mono h he) (RefType.mono h hr) (vec_mono (Expr.mono h) hes)
  | k7 g hk hr hes => exact .k7 (h _ g) hk (RefType.mono h hr) (vec_mono (Expr.mono h) hes)

/-- The leading `u32` fixes the kind; the remaining fields then parse in order. -/
theorem Elem.prefixFree (F : Forms) : PrefixFree (Elem F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha <;> cases ha' <;> simp only [List.append_assoc] at e <;>
    obtain ⟨rfl, hk, e⟩ := step (UN.prefixFree 32) e (by assumption) (by assumption) <;>
    (try omega) <;>
    repeat (first
      | obtain ⟨rfl, rfl, e⟩ := step (Expr.prefixFree F) e (by assumption) (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (Vec.prefixFree (Expr.prefixFree F)) e (by assumption)
          (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (Index.prefixFree (k := .table)) e (by assumption)
          (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (Vec.prefixFree (Index.prefixFree (k := .func))) e
          (by assumption) (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step ElemKind.prefixFree e (by assumption) (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (RefType.prefixFree F) e (by assumption) (by assumption))
  all_goals exact ⟨rfl, rfl⟩

/-! ### Code -/

theorem Locals.mono {F G : Forms} (h : F.Le G) {b : Bytes} {ts : List Wasm.ValType}
    (hl : Locals F b ts) : Locals G b ts := by
  cases hl with
  | mk hn ht => exact .mk hn (ValType.mono h ht)

theorem Locals.prefixFree (F : Forms) : PrefixFree (Locals F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk hn ht =>
    cases ha' with
    | mk hn' ht' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step (UN.prefixFree 32) e hn hn'
      obtain ⟨rfl, rfl, -⟩ := step (ValType.prefixFree F) e ht ht'
      exact ⟨rfl, rfl⟩

theorem Func.mono {F G : Forms} (h : F.Le G) {b : Bytes} {f : List Wasm.ValType × Wasm.Expr}
    (hf : Func F b f) : Func G b f := by
  cases hf with
  | mk hl he hlen => exact .mk (vec_mono (Locals.mono h) hl) (Expr.mono h he) hlen

theorem Func.prefixFree (F : Forms) : PrefixFree (Func F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk hl he _ =>
    cases ha' with
    | mk hl' he' _ =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step (Vec.prefixFree (Locals.prefixFree F)) e hl hl'
      obtain ⟨rfl, rfl, -⟩ := step (Expr.prefixFree F) e he he'
      exact ⟨rfl, rfl⟩

theorem Code.mono {F G : Forms} (h : F.Le G) {b : Bytes} {f : List Wasm.ValType × Wasm.Expr}
    (hc : Code F b f) : Code G b f := by
  cases hc with
  | mk hl hlen hf => exact .mk hl hlen (Func.mono h hf)

theorem Code.prefixFree (F : Forms) : PrefixFree (Code F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk hl hlen hf =>
    cases ha' with
    | mk hl' hlen' hf' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step (UN.prefixFree 32) e hl hl'
      obtain ⟨rfl, -⟩ := List.append_inj e (hlen.symm.trans hlen')
      exact ⟨rfl, (Func.prefixFree F).functional hf hf'⟩

/-! ### Data segments and the data count -/

theorem Data.mono {F G : Forms} (h : F.Le G) {b : Bytes} {d : Wasm.Data}
    (hd : Data F b d) : Data G b d := by
  cases hd with
  | k0 hk he hb => exact .k0 hk (Expr.mono h he) hb
  | k1 g hk hb => exact .k1 (h _ g) hk hb
  | k2 g hk hx he hb => exact .k2 (h _ g) hk hx (Expr.mono h he) hb

theorem Data.prefixFree (F : Forms) : PrefixFree (Data F) := by
  intro _ _ r r' _ _ ha ha' e
  cases ha <;> cases ha' <;> simp only [List.append_assoc] at e <;>
    obtain ⟨rfl, hk, e⟩ := step (UN.prefixFree 32) e (by assumption) (by assumption) <;>
    (try omega) <;>
    repeat (first
      | obtain ⟨rfl, rfl, e⟩ := step (Expr.prefixFree F) e (by assumption) (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (Index.prefixFree (k := .memory)) e (by assumption)
          (by assumption)
      | obtain ⟨rfl, rfl, e⟩ := step (Vec.prefixFree Byte.prefixFree) e (by assumption)
          (by assumption))
  all_goals exact ⟨rfl, rfl⟩

theorem DataCnt.prefixFree : PrefixFree DataCnt := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk h =>
    cases ha' with
    | mk h' =>
      obtain ⟨rfl, rfl⟩ := UN.prefixFree 32 h h' e
      exact ⟨rfl, rfl⟩

theorem DataCntSec.mono {F G : Forms} (h : F.Le G) {b : Bytes} {n : Option Nat}
    (hd : DataCntSec F b n) : DataCntSec G b n := by
  cases hd with
  | present g hs => exact .present (h _ g) hs
  | absent => exact .absent

theorem DataCntSec.toSection {F : Forms} {b : Bytes} {n : Option Nat} (hd : DataCntSec F b n) :
    ∃ ns, Section 12 DataCnt b ns ∧ n = ns.head? := by
  cases hd with
  | present _ hs => exact ⟨_, hs, rfl⟩
  | absent => exact ⟨[], .empty, rfl⟩

theorem DataCntSec.functional (F : Forms) : Functional (DataCntSec F) := by
  intro _ _ _ h h'
  obtain ⟨ns, hs, rfl⟩ := h.toSection
  obtain ⟨ns', hs', rfl⟩ := h'.toSection
  rw [Section.functional DataCnt.prefixFree.functional hs hs']

/-! ### Start and tag sections -/

theorem Start.prefixFree : PrefixFree Start := by
  intro _ _ r r' _ _ ha ha' e
  cases ha with
  | mk h =>
    cases ha' with
    | mk h' =>
      obtain ⟨rfl, rfl⟩ := Index.prefixFree h h' e
      exact ⟨rfl, rfl⟩

theorem StartSec.toSection {b : Bytes} {x : Option FuncIdx} (hs : StartSec b x) :
    ∃ xs, Section 8 Start b xs ∧ x = xs.head? := by
  cases hs with
  | mk h => exact ⟨_, h, rfl⟩

theorem StartSec.functional : Functional StartSec := by
  intro _ _ _ h h'
  obtain ⟨xs, hs, rfl⟩ := StartSec.toSection h
  obtain ⟨xs', hs', rfl⟩ := StartSec.toSection h'
  rw [Section.functional Start.prefixFree.functional hs hs']

theorem TagSec.mono {F G : Forms} (h : F.Le G) {b : Bytes} {ts : List Wasm.TagType}
    (ht : TagSec F b ts) : TagSec G b ts := by
  cases ht with
  | present g hs => exact .present (h _ g) hs
  | absent => exact .absent

theorem TagSec.toSection {F : Forms} {b : Bytes} {ts : List Wasm.TagType} (ht : TagSec F b ts) :
    Section 13 (Vec Tag) b ts := by
  cases ht with
  | present _ hs => exact hs
  | absent => exact .empty

theorem TagSec.functional (F : Forms) : Functional (TagSec F) := fun _ _ _ h h' =>
  Section.functional (Vec.prefixFree TagType.prefixFree).functional h.toSection h'.toSection

/-! ### Raw sections

Every section, custom or not, is a *raw section* `N:Bbyte len:Bu32 c` with
`len = ||c||`. Raw sections are prefix-free, so the bytes after the header split
uniquely into raw sections; since the non-custom section ids of a module are
distinct, each section's bytes are the raw sections carrying its id. -/

/-- A raw section, valued in its own bytes. -/
private def RawSec (b s : Bytes) : Prop :=
  s = b ∧ ∃ (N : UInt8) (lb c : Bytes) (len : Nat), U32 lb len ∧ len = c.length ∧
    b = [N] ++ lb ++ c

private theorem RawSec.prefixFree : PrefixFree RawSec := by
  rintro _ _ r r' _ _ ⟨rfl, N, lb, c, len, hl, hlen, rfl⟩
    ⟨rfl, N', lb', c', len', hl', hlen', rfl⟩ e
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at e
  obtain ⟨rfl, e⟩ := e
  obtain ⟨rfl, rfl, e⟩ := step (UN.prefixFree 32) e hl hl'
  obtain ⟨rfl, -⟩ := List.append_inj e (hlen.symm.trans hlen')
  exact ⟨rfl, rfl⟩

private theorem RawSec.ne_nil : ∀ a, ¬ RawSec [] a := by
  rintro _ ⟨-, _, _, _, _, _, _, h⟩
  simp at h

/-- The bytes of an optional section with id `N`. -/
private def SecShape (N : UInt8) (b : Bytes) : Prop := b = [] ∨ (RawSec b b ∧ b.head? = some N)

private theorem SecShape.of_section {α : Type} {N : UInt8} {G : Bytes → List α → Prop}
    {b : Bytes} {xs : List α} (h : Section N G b xs) : SecShape N b := by
  cases h with
  | mk hl hlen _ => exact .inr ⟨⟨rfl, _, _, _, _, hl, hlen, rfl⟩, rfl⟩
  | empty => exact .inl rfl

/-- The raw sections of an optional section. -/
private def secList (b : Bytes) : List Bytes := if b = [] then [] else [b]

private theorem SecShape.seq {N : UInt8} {b : Bytes} (h : SecShape N b) :
    Seq RawSec b (secList b) := by
  rcases h with rfl | ⟨hr, -⟩
  · exact .nil
  · have hb : b ≠ [] := fun hb => RawSec.ne_nil _ (hb ▸ hr)
    simpa [secList, hb] using Seq.cons hr .nil

/-- The concatenation of the raw sections with id `N`. -/
private def sel (N : UInt8) (L : List Bytes) : Bytes :=
  (L.filter fun s => decide (s.head? = some N)).flatten

private theorem sel_append (N : UInt8) (L₁ L₂ : List Bytes) :
    sel N (L₁ ++ L₂) = sel N L₁ ++ sel N L₂ := by
  simp [sel, List.filter_append]

private theorem sel_self {N : UInt8} {b : Bytes} (h : SecShape N b) : sel N (secList b) = b := by
  rcases h with rfl | ⟨hr, hN⟩
  · simp [sel, secList]
  · have hb : b ≠ [] := fun hb => RawSec.ne_nil _ (hb ▸ hr)
    simp [sel, secList, hb, hN]

private theorem sel_other {M N : UInt8} {b : Bytes} (h : SecShape M b) (hMN : M ≠ N) :
    sel N (secList b) = [] := by
  rcases h with rfl | ⟨hr, hM⟩
  · simp [sel, secList]
  · have hb : b ≠ [] := fun hb => RawSec.ne_nil _ (hb ▸ hr)
    simp [sel, secList, hb, hM, hMN]

/-- Custom sections split into raw sections with id `0`. -/
private theorem Customs.raw {c : Bytes} (h : Customs c) :
    ∃ L, Seq RawSec c L ∧ ∀ s ∈ L, s.head? = some 0 := by
  induction h with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons hs _ ih =>
    obtain ⟨xs, hs⟩ := hs
    obtain ⟨L, hL, hL0⟩ := ih
    have hsh := SecShape.of_section hs
    refine ⟨secList _ ++ L, seq_append hsh.seq hL, ?_⟩
    intro s hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases hsh with rfl | ⟨_, h0⟩
      · simp [secList] at hm
      · unfold secList at hm
        split at hm
        · simp at hm
        · simp only [List.mem_singleton] at hm
          exact hm ▸ h0
    · exact hL0 s hm

private theorem sel_customs {N : UInt8} {L : List Bytes} (hL : ∀ s ∈ L, s.head? = some 0)
    (hN : N ≠ 0) : sel N L = [] := by
  simp only [sel, List.flatten_eq_nil_iff, List.mem_filter, decide_eq_true_eq, and_imp]
  intro s hs hsN
  rw [hL s hs] at hsN
  exact absurd (Option.some.inj hsN).symm hN

/-- The bytes after the header determine each non-custom section's bytes. -/
private theorem sections {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes}
    {s1 s2 s3 s4 s5 s13 s6 s7 s8 s9 s12 s10 s11 : Bytes}
    (h₀ : Customs c₀) (t1 : SecShape 1 s1) (h₁ : Customs c₁) (t2 : SecShape 2 s2)
    (h₂ : Customs c₂) (t3 : SecShape 3 s3) (h₃ : Customs c₃) (t4 : SecShape 4 s4)
    (h₄ : Customs c₄) (t5 : SecShape 5 s5) (h₅ : Customs c₅) (t13 : SecShape 13 s13)
    (h₆ : Customs c₆) (t6 : SecShape 6 s6) (h₇ : Customs c₇) (t7 : SecShape 7 s7)
    (h₈ : Customs c₈) (t8 : SecShape 8 s8) (h₉ : Customs c₉) (t9 : SecShape 9 s9)
    (h₁₀ : Customs c₁₀) (t12 : SecShape 12 s12) (h₁₁ : Customs c₁₁) (t10 : SecShape 10 s10)
    (h₁₂ : Customs c₁₂) (t11 : SecShape 11 s11) (h₁₃ : Customs c₁₃) :
    ∃ L, Seq RawSec (c₀ ++ (s1 ++ (c₁ ++ (s2 ++ (c₂ ++ (s3 ++ (c₃ ++ (s4 ++ (c₄ ++ (s5 ++
        (c₅ ++ (s13 ++ (c₆ ++ (s6 ++ (c₇ ++ (s7 ++ (c₈ ++ (s8 ++ (c₉ ++ (s9 ++ (c₁₀ ++
        (s12 ++ (c₁₁ ++ (s10 ++ (c₁₂ ++ (s11 ++ c₁₃)))))))))))))))))))))))))) L ∧
      sel 1 L = s1 ∧ sel 2 L = s2 ∧ sel 3 L = s3 ∧ sel 4 L = s4 ∧ sel 5 L = s5 ∧
      sel 13 L = s13 ∧ sel 6 L = s6 ∧ sel 7 L = s7 ∧ sel 8 L = s8 ∧ sel 9 L = s9 ∧
      sel 12 L = s12 ∧ sel 10 L = s10 ∧ sel 11 L = s11 := by
  obtain ⟨L₀, q₀, r₀⟩ := Customs.raw h₀
  obtain ⟨L₁, q₁, r₁⟩ := Customs.raw h₁
  obtain ⟨L₂, q₂, r₂⟩ := Customs.raw h₂
  obtain ⟨L₃, q₃, r₃⟩ := Customs.raw h₃
  obtain ⟨L₄, q₄, r₄⟩ := Customs.raw h₄
  obtain ⟨L₅, q₅, r₅⟩ := Customs.raw h₅
  obtain ⟨L₆, q₆, r₆⟩ := Customs.raw h₆
  obtain ⟨L₇, q₇, r₇⟩ := Customs.raw h₇
  obtain ⟨L₈, q₈, r₈⟩ := Customs.raw h₈
  obtain ⟨L₉, q₉, r₉⟩ := Customs.raw h₉
  obtain ⟨L₁₀, q₁₀, r₁₀⟩ := Customs.raw h₁₀
  obtain ⟨L₁₁, q₁₁, r₁₁⟩ := Customs.raw h₁₁
  obtain ⟨L₁₂, q₁₂, r₁₂⟩ := Customs.raw h₁₂
  obtain ⟨L₁₃, q₁₃, r₁₃⟩ := Customs.raw h₁₃
  refine ⟨_, seq_append q₀ (seq_append t1.seq (seq_append q₁ (seq_append t2.seq
    (seq_append q₂ (seq_append t3.seq (seq_append q₃ (seq_append t4.seq (seq_append q₄
    (seq_append t5.seq (seq_append q₅ (seq_append t13.seq (seq_append q₆ (seq_append t6.seq
    (seq_append q₇ (seq_append t7.seq (seq_append q₈ (seq_append t8.seq (seq_append q₉
    (seq_append t9.seq (seq_append q₁₀ (seq_append t12.seq (seq_append q₁₁
    (seq_append t10.seq (seq_append q₁₂ (seq_append t11.seq q₁₃))))))))))))))))))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := decide) only [sel_append, sel_customs r₀, sel_customs r₁, sel_customs r₂,
    sel_customs r₃,
    sel_customs r₄, sel_customs r₅, sel_customs r₆, sel_customs r₇, sel_customs r₈,
    sel_customs r₉, sel_customs r₁₀, sel_customs r₁₁, sel_customs r₁₂, sel_customs r₁₃,
    sel_self t1, sel_self t2, sel_self t3, sel_self t4, sel_self t5, sel_self t13, sel_self t6,
    sel_self t7, sel_self t8, sel_self t9, sel_self t12, sel_self t10, sel_self t11,
    sel_other t1, sel_other t2, sel_other t3, sel_other t4, sel_other t5, sel_other t13,
    sel_other t6, sel_other t7, sel_other t8, sel_other t9, sel_other t12, sel_other t10,
    sel_other t11, List.nil_append, List.append_nil]

/-! ### Modules -/

theorem Module.mono {F G : Forms} (h : F.Le G) {b : Bytes} {m : Wasm.Module}
    (hm : Module F b m) : Module G b m := by
  cases hm with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco
      h₁₂ hda h₁₃ hcount hdataidx hfuncs =>
    exact .mk h₀ (Section.mono (vec_mono (RecType.mono h)) hty)
      h₁ (Section.mono (vec_mono (Import.mono h)) him) h₂ hfn
      h₃ (Section.mono (vec_mono (Table.mono h)) htb)
      h₄ (Section.mono (vec_mono (MemType.mono h)) hme) h₅ (TagSec.mono h htg)
      h₆ (Section.mono (vec_mono (Global.mono h)) hgl) h₇ hex h₈ hst
      h₉ (Section.mono (vec_mono (Elem.mono h)) hel) h₁₀ (DataCntSec.mono h hdc)
      h₁₁ (Section.mono (vec_mono (Code.mono h)) hco)
      h₁₂ (Section.mono (vec_mono (Data.mono h)) hda) h₁₃ hcount hdataidx hfuncs

/-- Sized section framing preserves module functionality for any functional
import-section body, without changing the other Core productions. -/
theorem ModuleWithImports.functional (F : Forms)
    (I : Bytes → List Wasm.Import → Prop) (hI : Functional I) :
    Functional (ModuleWithImports F I) := by
  suffices H : ∀ {b b' : Bytes} {m m' : Wasm.Module}, ModuleWithImports F I b m → ModuleWithImports F I b' m' → b = b' →
      m = m' from fun _ _ _ h h' => H h h' rfl
  intro b b' m m' h h' e
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco
      h₁₂ hda h₁₃ =>
  cases h' with
  | mk h₀' hty' h₁' him' h₂' hfn' h₃' htb' h₄' hme' h₅' htg' h₆' hgl' h₇' hex' h₈' hst' h₉'
      hel' h₁₀' hdc' h₁₁' hco' h₁₂' hda' h₁₃' =>
  simp only [List.append_assoc] at e
  have e' := List.append_cancel_left (List.append_cancel_left e)
  obtain ⟨dc, hdcs, -⟩ := hdc.toSection
  obtain ⟨dc', hdcs', -⟩ := hdc'.toSection
  obtain ⟨st, hsts, hst⟩ := StartSec.toSection hst
  obtain ⟨st', hsts', hst'⟩ := StartSec.toSection hst'
  obtain ⟨L, hL, e1, e2, e3, e4, e5, e13, e6, e7, e8, e9, -, e10, e11⟩ := sections h₀
    (.of_section hty) h₁ (.of_section him) h₂ (.of_section hfn) h₃ (.of_section htb) h₄
    (.of_section hme) h₅ (.of_section htg.toSection) h₆ (.of_section hgl) h₇ (.of_section hex)
    h₈ (.of_section hsts) h₉ (.of_section hel) h₁₀ (.of_section hdcs) h₁₁ (.of_section hco)
    h₁₂ (.of_section hda) h₁₃
  obtain ⟨L', hL', e1', e2', e3', e4', e5', e13', e6', e7', e8', e9', -, e10', e11'⟩ := sections
    h₀' (.of_section hty') h₁' (.of_section him') h₂' (.of_section hfn') h₃'
    (.of_section htb') h₄' (.of_section hme') h₅' (.of_section htg'.toSection) h₆'
    (.of_section hgl') h₇' (.of_section hex') h₈' (.of_section hsts') h₉' (.of_section hel')
    h₁₀' (.of_section hdcs') h₁₁' (.of_section hco') h₁₂' (.of_section hda') h₁₃'
  rw [e'] at hL
  obtain rfl := Seq.functional RawSec.prefixFree RawSec.ne_nil hL hL'
  obtain rfl := section_eq (Vec.prefixFree (RecType.prefixFree F)).functional hty hty'
    (e1.symm.trans e1')
  obtain rfl := section_eq hI him him'
    (e2.symm.trans e2')
  obtain rfl := section_eq (Vec.prefixFree Index.prefixFree).functional hfn hfn'
    (e3.symm.trans e3')
  obtain rfl := section_eq (Vec.prefixFree (Table.prefixFree F)).functional htb htb'
    (e4.symm.trans e4')
  obtain rfl := section_eq (Vec.prefixFree (MemType.prefixFree F)).functional hme hme'
    (e5.symm.trans e5')
  obtain rfl := section_eq (Vec.prefixFree TagType.prefixFree).functional htg.toSection
    htg'.toSection (e13.symm.trans e13')
  obtain rfl := section_eq (Vec.prefixFree (Global.prefixFree F)).functional hgl hgl'
    (e6.symm.trans e6')
  obtain rfl := section_eq (Vec.prefixFree Export.prefixFree).functional hex hex'
    (e7.symm.trans e7')
  obtain rfl := section_eq Start.prefixFree.functional hsts hsts' (e8.symm.trans e8')
  obtain rfl := section_eq (Vec.prefixFree (Elem.prefixFree F)).functional hel hel'
    (e9.symm.trans e9')
  obtain rfl := section_eq (Vec.prefixFree (Code.prefixFree F)).functional hco hco'
    (e10.symm.trans e10')
  obtain rfl := section_eq (Vec.prefixFree (Data.prefixFree F)).functional hda hda'
    (e11.symm.trans e11')
  rw [hst, hst']

/-- Core 3.0 bytes determine the standard module. -/
theorem Module.functional (F : Forms) : Functional (Module F) :=
  ModuleWithImports.functional F _ (Vec.prefixFree (Import.prefixFree F)).functional

theorem functional : Encoding.Functional Wasm.Module := fun _ _ _ h h' =>
  Module.functional Forms.all h h'

/-- The magic number and version alone encode the empty module, for every `F`. -/
theorem Module.empty (F : Forms) : Module F (magic ++ version) {} := by
  have h := Module.mk (F := F) (types := []) (imports := []) (typeidxs := []) (tables := [])
    (mems := []) (tags := []) (globals := []) (exports := []) (elems := [])
    (nopt := none) (codes := []) (data := [])
    (h₀ := .nil) (hty := .empty) (h₁ := .nil) (him := .empty) (h₂ := .nil) (hfn := .empty)
    (h₃ := .nil) (htb := .empty) (h₄ := .nil) (hme := .empty) (h₅ := .nil) (htg := .absent)
    (h₆ := .nil) (hgl := .empty) (h₇ := .nil) (hex := .empty) (h₈ := .nil) (hst := .mk .empty)
    (h₉ := .nil) (hel := .empty) (h₁₀ := .nil) (hdc := .absent) (h₁₁ := .nil) (hco := .empty)
    (h₁₂ := .nil) (hda := .empty) (h₁₃ := .nil)
    (hcount := by simp) (hdataidx := .inr rfl) (hfuncs := rfl)
  exact h

end Silmaril.Wasm.Binary.Core
