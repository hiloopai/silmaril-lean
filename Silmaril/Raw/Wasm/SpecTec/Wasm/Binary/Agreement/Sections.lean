module

public import Silmaril.Wasm.Binary.Core.Modules
public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary
public import Silmaril.Wasm.Lime1.ToCore.Modules

/-! # Section-level correspondence of the 1.0/Lime1 and Core 3.0 grammars

Helpers for `Binary/Agreement.lean`, independent of the instruction grammars:

* transport of `Seq`/`Vec`/`Section` along a map of abstract syntax, in both directions;
* the type productions (value, function, limits, table, memory, global, extern types)
  of Wasm 1.0 against those of Core 3.0 with the gated forms closed;
* `Core.NumLocalsModule`, the Core module grammar with `Blocals` restricted to number
  types (see its docstring for why the plain Core grammar is not enough);
* the function/code zip and the data indices of Lime1 code.

The converse lemmas take `F.Le Forms.lime1`: every gate other than `tableIdxImm` is
closed, which covers `Forms.ofOverlong ov` for both values of `ov`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary

/-! ## Transport along maps -/

section Transport

variable {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop} {f : α → β}

theorem Seq.map_of {P : α → Prop} (hf : ∀ b x, P x → G b x → H b (f x)) {b : Bytes}
    {xs : List α} (hP : ∀ x ∈ xs, P x) (h : Seq G b xs) : Seq H b (xs.map f) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hP
    exact .cons (hf _ _ hP.1 hx) (ih hP.2)

theorem Seq.of_map (hf : ∀ b x, H b (f x) → G b x) {b : Bytes} {xs : List α}
    (h : Seq H b (xs.map f)) : Seq G b xs := by
  induction xs generalizing b with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    cases h with
    | cons hx hs => exact .cons (hf _ _ hx) (ih hs)

theorem Vec.map_of {P : α → Prop} (hf : ∀ b x, P x → G b x → H b (f x)) {b : Bytes}
    {xs : List α} (hP : ∀ x ∈ xs, P x) (h : Vec G b xs) : Vec H b (xs.map f) := by
  obtain ⟨hn, hs⟩ := h
  exact .mk (by simpa using hn) (Seq.map_of hf hP hs)

theorem Vec.map (hf : ∀ b x, G b x → H b (f x)) {b : Bytes} {xs : List α}
    (h : Vec G b xs) : Vec H b (xs.map f) :=
  Vec.map_of (P := fun _ => True) (fun b x _ hx => hf b x hx) (fun _ _ => trivial) h

theorem Vec.of_map (hf : ∀ b x, H b (f x) → G b x) {b : Bytes} {xs : List α}
    (h : Vec H b (xs.map f)) : Vec G b xs := by
  obtain ⟨hn, hs⟩ := h
  exact .mk (by simpa using hn) (Seq.of_map hf hs)

theorem Section.map {N : UInt8} {G : Bytes → List α → Prop} {H : Bytes → List β → Prop}
    {xs : List α} (hf : ∀ c, G c xs → H c (xs.map f)) {b : Bytes}
    (h : Section N G b xs) : Section N H b (xs.map f) := by
  cases h with
  | mk hl hlen hc => exact .mk hl hlen (hf _ hc)
  | empty => exact .empty

theorem Section.of_map {N : UInt8} {G : Bytes → List α → Prop} {H : Bytes → List β → Prop}
    {xs : List α} (hf : ∀ c, H c (xs.map f) → G c xs) {b : Bytes}
    (h : Section N H b (xs.map f)) : Section N G b xs := by
  generalize hy : xs.map f = ys at h
  cases h with
  | mk hl hlen hc => subst hy; exact .mk hl hlen (hf _ hc)
  | empty =>
    rw [List.map_eq_nil_iff] at hy
    subst hy
    exact .empty

theorem Section.imp {N : UInt8} {G G' : Bytes → List α → Prop} {xs : List α}
    (hf : ∀ c, G c xs → G' c xs) {b : Bytes} (h : Section N G b xs) : Section N G' b xs := by
  cases h with
  | mk hl hlen hc => exact .mk hl hlen (hf _ hc)
  | empty => exact .empty

end Transport

theorem Customs.append {b b' : Bytes} (h : Customs b) (h' : Customs b') : Customs (b ++ b') := by
  induction h with
  | nil => simpa using h'
  | cons hc _ ih => simpa using Customs.cons hc ih

namespace Core

/-! ## Gates -/

/-- A form other than `tableIdxImm` is closed in every `F ≤ lime1`. -/
theorem Forms.not_gate {F : Forms} (hF : F.Le Forms.lime1) {f : Form} (g : F f = true)
    (hf : f ≠ .tableIdxImm) : False :=
  hf (by simpa [Forms.lime1] using hF f g)

theorem Forms.ofOverlong_le_lime1 (ov : Bool) : (Forms.ofOverlong ov).Le Forms.lime1 := by
  cases ov
  · exact Forms.v1_le_lime1
  · exact Forms.Le.refl _

/-! ## Types -/

variable {F : Forms} {b : Bytes}

theorem NumType.of_v1 {t : V1.ValType} (h : V1.Binary.ValType b t) : NumType b t := by
  cases h <;> constructor

theorem NumType.to_v1 {t : V1.ValType} (h : NumType b t) : V1.Binary.ValType b t := by
  cases h <;> constructor

theorem ValType.of_v1 {t : V1.ValType} (h : V1.Binary.ValType b t) :
    ValType F b (V1.ValType.toCore t) :=
  .num (NumType.of_v1 h)

theorem ValType.to_v1 {t : V1.ValType} (h : ValType F b (V1.ValType.toCore t)) :
    V1.Binary.ValType b t := by
  change ValType F b (.num t) at h
  cases h with
  | num h => exact NumType.to_v1 h

theorem RecType.of_v1 {ft : V1.FuncType} (h : V1.Binary.FuncType b ft) :
    RecType F b ft.toCoreRec := by
  obtain ⟨h₁, h₂⟩ := h
  exact .single (.plain (.func (Vec.map (fun _ _ h => ValType.of_v1 h) h₁)
    (Vec.map (fun _ _ h => ValType.of_v1 h) h₂)))

theorem RecType.to_v1 (hF : F.Le Forms.lime1) {ft : V1.FuncType} (h : RecType F b ft.toCoreRec) :
    V1.Binary.FuncType b ft := by
  obtain ⟨ps, rs⟩ := ft
  change RecType F b ⟨[⟨true, [], .func ⟨ps.map V1.ValType.toCore, rs.map V1.ValType.toCore⟩⟩]⟩
    at h
  cases h with
  | group g _ => exact (Forms.not_gate hF g (by decide)).elim
  | single h =>
    cases h with
    | final g _ _ => exact (Forms.not_gate hF g (by decide)).elim
    | plain h =>
      cases h with
      | func h₁ h₂ =>
        exact .mk (Vec.of_map (G := V1.Binary.ValType) (fun _ _ h => ValType.to_v1 h) h₁)
          (Vec.of_map (G := V1.Binary.ValType) (fun _ _ h => ValType.to_v1 h) h₂)

theorem Limits.of_v1 {l : V1.Limits} (h : V1.Binary.Limits b l) :
    Limits F b (.i32, l.toCore) := by
  cases h with
  | min h => exact .i32 (.u32 h)
  | minMax h h' => exact .i32Max (.u32 h) (.u32 h')

theorem Bound.to_u32 (hF : F.Le Forms.lime1) {n : Fin (2 ^ 32)} (h : Bound F b (V1.widen32 n)) :
    U32 b n.val := by
  cases h with
  | u64 g _ => exact (Forms.not_gate hF g (by decide)).elim
  | u32 h => exact h

theorem Limits.to_v1 (hF : F.Le Forms.lime1) {l : V1.Limits} (h : Limits F b (.i32, l.toCore)) :
    V1.Binary.Limits b l := by
  obtain ⟨n, _ | m⟩ := l
  · change Limits F b (.i32, ⟨V1.widen32 n, none⟩) at h
    cases h with
    | i32 h => exact .min (Bound.to_u32 hF h)
  · change Limits F b (.i32, ⟨V1.widen32 n, some (V1.widen32 m)⟩) at h
    cases h with
    | i32Max h h' => exact .minMax (Bound.to_u32 hF h) (Bound.to_u32 hF h')

theorem TableType.of_v1 {t : V1.TableType} (h : V1.Binary.TableType b t) :
    TableType F b t.toCore := by
  obtain ⟨h⟩ := h
  exact .mk (b := [0x70]) (.abs .func) (Limits.of_v1 h)

theorem TableType.to_v1 (hF : F.Le Forms.lime1) {t : V1.TableType}
    (h : TableType F b t.toCore) : V1.Binary.TableType b t := by
  obtain ⟨l⟩ := t
  change TableType F b ⟨.i32, l.toCore, ⟨true, .abstract .func⟩⟩ at h
  cases h with
  | mk hr hl =>
    cases hr with
    | null g _ => exact (Forms.not_gate hF g (by decide)).elim
    | abs hh =>
      cases hh
      exact .mk (Limits.to_v1 hF hl)

theorem MemType.of_v1 {t : V1.MemoryType} (h : V1.Binary.MemType b t) :
    MemType F b t.toCore := by
  obtain ⟨h⟩ := h
  exact .mk (Limits.of_v1 h)

theorem MemType.to_v1 (hF : F.Le Forms.lime1) {t : V1.MemoryType} (h : MemType F b t.toCore) :
    V1.Binary.MemType b t := by
  obtain ⟨l⟩ := t
  change MemType F b ⟨.i32, l.toCore⟩ at h
  cases h with
  | mk h => exact .mk (Limits.to_v1 hF h)

theorem Mut.of_v1 {m : Mutability} (h : V1.Binary.Mut b m) : Mut b m := by
  cases h <;> constructor

theorem Mut.to_v1 {m : Mutability} (h : Mut b m) : V1.Binary.Mut b m := by
  cases h <;> constructor

theorem GlobalType.of_v1 {t : V1.GlobalType} (h : V1.Binary.GlobalType b t) :
    GlobalType F b t.toCore := by
  obtain ⟨ht, hm⟩ := h
  exact .mk (ValType.of_v1 ht) (Mut.of_v1 hm)

theorem GlobalType.to_v1 {t : V1.GlobalType} (h : GlobalType F b t.toCore) :
    V1.Binary.GlobalType b t := by
  obtain ⟨mu, v⟩ := t
  change GlobalType F b ⟨mu, V1.ValType.toCore v⟩ at h
  cases h with
  | mk ht hm => exact .mk (ValType.to_v1 ht) (Mut.to_v1 hm)

theorem ExternType.of_v1 {d : V1.ImportDesc} (h : Scalar.Binary.ImportDesc b d) :
    ExternType F b d.toCore := by
  cases h with
  | func h => exact .func h
  | table h => exact .table (TableType.of_v1 h)
  | memory h => exact .memory (MemType.of_v1 h)
  | global h => exact .global (GlobalType.of_v1 h)

theorem ExternType.to_v1 (hF : F.Le Forms.lime1) {d : V1.ImportDesc}
    (h : ExternType F b d.toCore) : Scalar.Binary.ImportDesc b d := by
  cases d with
  | func x =>
    change ExternType F b (.func x) at h
    cases h with
    | func h => exact .func h
  | table t =>
    change ExternType F b (.table t.toCore) at h
    cases h with
    | table h => exact .table (TableType.to_v1 hF h)
  | memory t =>
    change ExternType F b (.memory t.toCore) at h
    cases h with
    | memory h => exact .memory (MemType.to_v1 hF h)
  | global t =>
    change ExternType F b (.global t.toCore) at h
    cases h with
    | global h => exact .global (GlobalType.to_v1 h)

theorem Import.of_v1 {i : V1.Import} (h : Scalar.Binary.Import b i) : Import F b i.toCore := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact .mk h₁ h₂ (ExternType.of_v1 h₃)

theorem Import.to_v1 (hF : F.Le Forms.lime1) {i : V1.Import} (h : Import F b i.toCore) :
    Scalar.Binary.Import b i := by
  obtain ⟨mn, n, d⟩ := i
  change Import F b ⟨mn, n, d.toCore⟩ at h
  cases h with
  | mk h₁ h₂ h₃ => exact .mk h₁ h₂ (ExternType.to_v1 hF h₃)

theorem ExternIdx.of_v1 {x : V1.ExternIdx} (h : Scalar.Binary.ExportDesc b x) :
    ExternIdx b x.toCore := by
  cases h with
  | func h => exact .func h
  | table h => exact .table h
  | memory h => exact .memory h
  | global h => exact .global h

theorem ExternIdx.to_v1 {x : V1.ExternIdx} (h : ExternIdx b x.toCore) :
    Scalar.Binary.ExportDesc b x := by
  cases x with
  | func x =>
    change ExternIdx b (.func x) at h
    cases h with
    | func h => exact .func h
  | table x =>
    change ExternIdx b (.table x) at h
    cases h with
    | table h => exact .table h
  | memory x =>
    change ExternIdx b (.memory x) at h
    cases h with
    | memory h => exact .memory h
  | global x =>
    change ExternIdx b (.global x) at h
    cases h with
    | global h => exact .global h

theorem Export.of_v1 {e : V1.Export} (h : Scalar.Binary.Export b e) : Export b e.toCore := by
  obtain ⟨h, h'⟩ := h
  exact .mk h (ExternIdx.of_v1 h')

theorem Export.to_v1 {e : V1.Export} (h : Export b e.toCore) : Scalar.Binary.Export b e := by
  obtain ⟨n, x⟩ := e
  change Export b ⟨n, x.toCore⟩ at h
  cases h with
  | mk h h' => exact .mk h (ExternIdx.to_v1 h')

/-- Bare table types are the only Lime1 tables. -/
theorem Table.of_v1 {t : V1.TableType} (h : V1.Binary.TableType b t) :
    Table F b (Lime1.tableToCore t) :=
  .implicit (TableType.of_v1 h)

theorem Table.to_v1 (hF : F.Le Forms.lime1) {t : V1.TableType}
    (h : Table F b (Lime1.tableToCore t)) : V1.Binary.TableType b t := by
  change Table F b ⟨t.toCore, [.refNull (.abstract .func)]⟩ at h
  cases h with
  | implicit h => exact TableType.to_v1 hF h
  | explicit g _ _ => exact (Forms.not_gate hF g (by decide)).elim

/-! ## Numeric locals

Core 3.0's `Blocals = n:Bu32 t:Bvaltype` admits every value type, and an entry with
`n = 0` contributes no local. So a code entry may carry a declaration such as `00 7B`
(zero `v128` locals) or `00 70` (zero `funcref` locals) that is invisible in the abstract
syntax: Core decodes it to an image module, while the 1.0/Lime1 grammar (whose `valtype`
is numeric) rejects the bytes. No `Form` gates this production, so the reflection
direction is stated against `NumLocalsModule`, the Core module grammar with `Blocals`
restricted to number types (and otherwise identical, rule by rule, to `Core.Module`). -/

/-- `Blocals` with a number type. -/
inductive NumLocals : Bytes → List Wasm.ValType → Prop where
  | mk {bn bt : Bytes} {n : Nat} {t : Wasm.NumType} (hn : U32 bn n) (ht : NumType bt t) :
      NumLocals (bn ++ bt) (List.replicate n (.num t))

/-- `Bfunc` over `NumLocals`. -/
inductive NumFunc (F : Forms) : Bytes → List Wasm.ValType × Wasm.Expr → Prop where
  | mk {bl be : Bytes} {lss : List (List Wasm.ValType)} {e : Wasm.Expr}
      (hl : Vec NumLocals bl lss) (he : Expr F be e) (hlen : lss.flatten.length < 2 ^ 32) :
      NumFunc F (bl ++ be) (lss.flatten, e)

/-- `Bcode` over `NumFunc`. -/
inductive NumCode (F : Forms) : Bytes → List Wasm.ValType × Wasm.Expr → Prop where
  | mk {bl c : Bytes} {len : Nat} {code : List Wasm.ValType × Wasm.Expr} (hl : U32 bl len)
      (hlen : len = c.length) (h : NumFunc F c code) : NumCode F (bl ++ c) code

/-- `Bmodule` (5.4:175–195) with the code section over `NumCode`. -/
inductive NumLocalsModule (F : Forms) : Bytes → Wasm.Module → Prop where
  | mk {c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ : Bytes}
      {bty bim bfn btb bme btg bgl bex bst bel bdc bco bda : Bytes}
      {types : List Wasm.RecType} {imports : List Wasm.Import} {typeidxs : List TypeIdx}
      {tables : List Wasm.Table} {mems : List Wasm.MemoryType} {tags : List Wasm.TagType}
      {globals : List Wasm.Global} {exports : List Wasm.Export} {start : Option FuncIdx}
      {elems : List Wasm.Elem} {nopt : Option Nat}
      {codes : List (List Wasm.ValType × Wasm.Expr)} {data : List Wasm.Data}
      (h₀ : Customs c₀) (hty : TypeSec F bty types)
      (h₁ : Customs c₁) (him : ImportSec F bim imports)
      (h₂ : Customs c₂) (hfn : FuncSec bfn typeidxs)
      (h₃ : Customs c₃) (htb : TableSec F btb tables)
      (h₄ : Customs c₄) (hme : MemSec F bme mems)
      (h₅ : Customs c₅) (htg : TagSec F btg tags)
      (h₆ : Customs c₆) (hgl : GlobalSec F bgl globals)
      (h₇ : Customs c₇) (hex : ExportSec bex exports)
      (h₈ : Customs c₈) (hst : StartSec bst start)
      (h₉ : Customs c₉) (hel : ElemSec F bel elems)
      (h₁₀ : Customs c₁₀) (hdc : DataCntSec F bdc nopt)
      (h₁₁ : Customs c₁₁) (hco : Section 10 (Vec (NumCode F)) bco codes)
      (h₁₂ : Customs c₁₂) (hda : DataSec F bda data)
      (h₁₃ : Customs c₁₃)
      (hcount : ∀ n ∈ nopt, n = data.length)
      (hdataidx : nopt.isSome ∨ codesDataIdxs codes = [])
      (hfuncs : typeidxs.length = codes.length) :
      NumLocalsModule F (magic ++ version ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfn ++ c₃ ++
          btb ++ c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++
          c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃)
        { types, imports, tags, globals, memories := mems, tables,
          funcs := zipFuncs typeidxs codes, data, elems, start, exports }

theorem NumLocals.toLocals {ts : List Wasm.ValType} (h : NumLocals b ts) : Locals F b ts := by
  cases h with
  | mk hn ht => exact .mk hn (.num ht)

theorem NumCode.toCode {c : List Wasm.ValType × Wasm.Expr} (h : NumCode F b c) : Code F b c := by
  obtain ⟨hl, hlen, ⟨hv, he, hlen'⟩⟩ := h
  exact .mk hl hlen (.mk (Vec.imp hv fun h => NumLocals.toLocals h) he hlen')

/-- The restricted grammar is contained in the Core grammar. -/
theorem NumLocalsModule.toModule {m : Wasm.Module} (h : NumLocalsModule F b m) :
    Module F b m := by
  obtain ⟨h₀, hty, h₁, him, h₂, hfn, h₃, htb, h₄, hme, h₅, htg, h₆, hgl, h₇, hex, h₈, hst, h₉,
    hel, h₁₀, hdc, h₁₁, hco, h₁₂, hda, h₁₃, hcount, hdataidx, hfuncs⟩ := h
  exact .mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁
    (Section.imp (fun _ h => Vec.imp h fun h => NumCode.toCode h) hco) h₁₂ hda h₁₃ hcount
    hdataidx hfuncs

theorem NumLocals.of_v1 {ts : List V1.ValType} (h : Scalar.Binary.Locals b ts) :
    NumLocals b (ts.map V1.ValType.toCore) := by
  cases h with
  | mk hn ht =>
    rw [List.map_replicate]
    exact .mk hn (NumType.of_v1 ht)

theorem NumLocals.to_v1 {ts : List Wasm.ValType} (h : NumLocals b ts) :
    ∃ ts₀, ts = ts₀.map V1.ValType.toCore ∧ Scalar.Binary.Locals b ts₀ := by
  cases h with
  | mk hn ht =>
    exact ⟨_, by rw [List.map_replicate]; rfl, .mk hn (NumType.to_v1 ht)⟩

theorem Seq.numLocals_to_v1 {lss : List (List Wasm.ValType)} (h : Seq NumLocals b lss) :
    ∃ lss₀, lss = lss₀.map (List.map V1.ValType.toCore) ∧ Seq Scalar.Binary.Locals b lss₀ := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hx _ ih =>
    obtain ⟨ts₀, rfl, hts⟩ := hx.to_v1
    obtain ⟨lss₀, rfl, hs⟩ := ih
    exact ⟨ts₀ :: lss₀, rfl, .cons hts hs⟩

theorem Vec.numLocals_to_v1 {lss : List (List Wasm.ValType)} (h : Vec NumLocals b lss) :
    ∃ lss₀, lss = lss₀.map (List.map V1.ValType.toCore) ∧ Vec Scalar.Binary.Locals b lss₀ := by
  obtain ⟨hn, hs⟩ := h
  obtain ⟨lss₀, rfl, hs₀⟩ := Seq.numLocals_to_v1 hs
  exact ⟨lss₀, rfl, .mk (by simpa using hn) hs₀⟩

theorem ValType.toCore_map_injective :
    Function.Injective (List.map V1.ValType.toCore) :=
  List.map_injective_iff.mpr fun _ _ h => Wasm.ValType.num.inj h

/-! ## Functions and code -/

theorem zipFuncs_map {xs : List TypeIdx} {cs : List (List V1.ValType × Lime1.Expr)} :
    zipFuncs xs (cs.map fun c => (c.1.map V1.ValType.toCore, Lime1.Expr.toCore c.2)) =
      (Scalar.Binary.zipFuncs xs cs).map Lime1.Func.toCore := by
  induction xs generalizing cs with
  | nil => simp [zipFuncs, Scalar.Binary.zipFuncs]
  | cons x xs ih =>
    cases cs with
    | nil => simp [zipFuncs, Scalar.Binary.zipFuncs]
    | cons c cs =>
      simp only [zipFuncs, Scalar.Binary.zipFuncs] at ih ⊢
      simp [ih, Lime1.Func.toCore]

theorem zipFuncs_eq_map {xs : List TypeIdx} {cs : List (List Wasm.ValType × Wasm.Expr)}
    {fs : List Lime1.Func} (hl : xs.length = cs.length)
    (h : fs.map Lime1.Func.toCore = zipFuncs xs cs) :
    xs = fs.map (·.type) ∧
      cs = fs.map fun f => (f.locals.map V1.ValType.toCore, Lime1.Expr.toCore f.body) := by
  induction fs generalizing xs cs with
  | nil =>
    cases xs with
    | nil => cases cs with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => simp at hl
    | cons x xs =>
      cases cs with
      | nil => simp at hl
      | cons c cs => simp [zipFuncs] at h
  | cons f fs ih =>
    cases xs with
    | nil => simp [zipFuncs] at h
    | cons x xs =>
      cases cs with
      | nil => simp [zipFuncs] at h
      | cons c cs =>
        simp only [List.map_cons, zipFuncs, List.zipWith_cons_cons, List.cons.injEq] at h
        obtain ⟨h₁, h₂⟩ := h
        obtain ⟨ih₁, ih₂⟩ := ih (by simpa using hl) h₂
        obtain ⟨c₁, c₂⟩ := c
        simp only [Lime1.Func.toCore, Declaration.Func.mk.injEq] at h₁
        obtain ⟨rfl, rfl, rfl⟩ := h₁
        exact ⟨by simp [ih₁], by simp [ih₂]⟩

theorem zipFuncs_self (fs : List Lime1.Func) :
    Scalar.Binary.zipFuncs (fs.map (·.type)) (fs.map fun f => (f.locals, f.body)) = fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [Scalar.Binary.zipFuncs, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

theorem mem_zipFuncs {E : Type} {xs : List TypeIdx} {cs : List (List V1.ValType × E)}
    (hl : xs.length = cs.length) {c : List V1.ValType × E} (hc : c ∈ cs) :
    ∃ x, (⟨x, c.1, c.2⟩ : Declaration.Func V1.ValType E) ∈ Scalar.Binary.zipFuncs xs cs := by
  induction xs generalizing cs with
  | nil => cases cs with
    | nil => simp at hc
    | cons _ _ => simp at hl
  | cons x xs ih =>
    cases cs with
    | nil => simp at hc
    | cons c' cs =>
      simp only [List.mem_cons] at hc
      simp only [Scalar.Binary.zipFuncs, List.zipWith_cons_cons, List.mem_cons]
      rcases hc with rfl | hc
      · exact ⟨x, .inl rfl⟩
      · obtain ⟨y, hy⟩ := ih (by simpa using hl) hc
        exact ⟨y, .inr hy⟩

/-! ## Data indices of Lime1 code -/

mutual
theorem Instr.dataIdxs_toCore (i : Lime1.Instr) : Instr.dataIdxs i.toCore = [] := by
  cases i with
  | block t body =>
    have := Expr.dataIdxs_toCore body
    simp only [Lime1.Instr.toCore, Instr.dataIdxs, List.flatMap_eq_nil_iff]
    exact fun j _ => this j.1 j.2
  | loop t body =>
    have := Expr.dataIdxs_toCore body
    simp only [Lime1.Instr.toCore, Instr.dataIdxs, List.flatMap_eq_nil_iff]
    exact fun j _ => this j.1 j.2
  | if_ t left right =>
    have hl := Expr.dataIdxs_toCore left
    have hr := Expr.dataIdxs_toCore right
    simp only [Lime1.Instr.toCore, Instr.dataIdxs, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff]
    exact ⟨fun j _ => hl j.1 j.2, fun j _ => hr j.1 j.2⟩
  | _ => simp [Lime1.Instr.toCore, Instr.dataIdxs]
termination_by sizeOf i

theorem Expr.dataIdxs_toCore (es : Lime1.Expr) :
    ∀ j ∈ Lime1.Expr.toCore es, Instr.dataIdxs j = [] := by
  cases es with
  | nil => simp [Lime1.Expr.toCore]
  | cons i es =>
    have hi := Instr.dataIdxs_toCore i
    have hs := Expr.dataIdxs_toCore es
    simp only [Lime1.Expr.toCore, List.mem_cons, forall_eq_or_imp]
    exact ⟨hi, hs⟩
termination_by sizeOf es
end

theorem codesDataIdxs_toCore (cs : List (List V1.ValType × Lime1.Expr)) :
    codesDataIdxs (cs.map fun c => (c.1.map V1.ValType.toCore, Lime1.Expr.toCore c.2)) = [] := by
  simp only [codesDataIdxs, List.flatMap_eq_nil_iff, List.mem_map, Expr.dataIdxs]
  rintro _ ⟨c, _, rfl⟩
  exact Expr.dataIdxs_toCore c.2

end Core

end Silmaril.Wasm.Binary
