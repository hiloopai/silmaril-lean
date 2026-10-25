module

public import Silmaril.Wasm.Binary.Basic

/-! # Core 3.0 binary format: types

Transcribed rule by rule from `5.2-binary.types.spectec` (cited as `5.2:n`).

## Encoding forms

The relations are parameterized by `F : Forms`, a set of *encoding forms* that
Core 3.0 has but WebAssembly 1.0 (and Lime1) lack. A rule that exists only
because of such a form carries the premise `F f = true`; where 1.0 had a reserved
byte or a narrower integer, the relation has an extra *ungated* rule for the
1.0 shape. The specification's grammar is `F = Forms.all`, where every gate is
open and every ungated 1.0 rule is subsumed by its general counterpart
(e.g. `Bound.u32` by `Bound.u64`, via `UN.mono`). Other values of `F` disable
the gated forms, which is how the agreement theorems state the converse direction
("these bytes use no gated form"). Monotonicity in `F` (`Forms.Le`) is stated for
every relation.

The gates are *not* a complete account of Core-only syntax. Only the forms that can
produce the image of a Wasm 1.0 or Lime1 module are gated; every other Core-only
production (`v128`, GC heap and composite types, typed `select`, the `0xFB`/`0xFC`/
`0xFD` instructions beyond Lime1's, `s33` block-type indices, `try_table`,
`return_call*`, tag extern types and export indices, …) is admitted for every `F`,
because its abstract syntax lies outside that image. So `Module Forms.v1` is the
1.0 grammar only *on the image of* `V1.Module.toCoreBinary`; e.g. a function body
`FD 0C <16 bytes> 1A 0B` (`v128.const; drop`) is accepted by `Module Forms.v1`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.Core

/-- Core 3.0 encoding freedoms absent from the Wasm 1.0 binary format. -/
inductive Form where
  /-- `memarg` flag bit 6 with an explicit memory index (multi-memory). -/
  | memargMemIdx
  /-- `memarg` offsets as `Bu64` rather than `u32` (memory64). -/
  | memargOffset64
  /-- `memory.size/grow/init/copy/fill` index immediates as `Bu32`, not the reserved `0x00`. -/
  | memIdxImm
  /-- `call_indirect`'s table index as `Bu32`, not the reserved `0x00` (reference types;
  Lime1's call-indirect-overlong). -/
  | tableIdxImm
  /-- Limits bounds as `Bu64`, and the 64-bit address-type flags `0x04`/`0x05`. -/
  | limits64
  /-- Explicit reference types `0x63 ht`/`0x64 ht` (function references). -/
  | refTypePrefix
  /-- Recursive groups `0x4E` and explicit subtypes `0x4F`/`0x50` (GC). -/
  | subTypes
  /-- Tables with an explicit initializer `0x40 0x00 tt e`. -/
  | tableInit
  /-- Element segment kinds `1`–`7` (bulk memory, reference types). -/
  | elemKinds
  /-- Data segment kinds `1`, `2` (bulk memory, multi-memory). -/
  | dataKinds
  /-- The data count section, id 12 (bulk memory). -/
  | dataCount
  /-- The tag section, id 13 (exception handling). -/
  | tagSection
  deriving DecidableEq, Repr

/-- A set of enabled encoding forms. -/
abbrev Forms := Form → Bool

namespace Forms

/-- The Core 3.0 grammar: every form enabled. -/
def all : Forms := fun _ => true

/-- Every gated form disabled. Restricted to the image of `V1.Module.toCoreBinary`, this
is the Wasm 1.0 grammar; ungated Core-only productions remain (see the module header). -/
def v1 : Forms := fun _ => false

/-- The gated forms Lime1 adds over Wasm 1.0: only the `u32` table index of
`call_indirect` (call-indirect-overlong). Restricted to the image of
`Lime1.Module.toCoreBinary`, this is the Lime1 grammar. -/
def lime1 : Forms := fun f => decide (f = .tableIdxImm)

/-- The gated forms WebAssembly 2.0 has: `tableIdxImm`, `elemKinds`, `dataKinds` and
`dataCount`. Restricted to the image of `V2.Module.toCoreBinary`, this is the 2.0
grammar. Checked form by form against the pinned 2.0 `A-binary.spectec`
(WebAssembly/spec `60871110`, hash-pinned in `specs/wasm/core-2.0.json`):

* `tableIdxImm`: `0x11 y:Btypeidx x:Btableidx => CALL_INDIRECT x y` (`A-binary:171`)
  — a real `Bu32` table index, not 1.0's reserved `0x00` (reference types).
* `elemKinds`: `Belem` has the eight kinds `0`–`7` (`A-binary:860-876`)
  (bulk memory, reference types).
* `dataKinds`: `Bdata` has the three kinds `0`, `1`, `2` (`A-binary:901-904`)
  (bulk memory). Kind `2`'s memory index is a full `Bmemidx` in both 2.0 and
  Core 3.0, so `memIdxImm` is not involved.
* `dataCount`: `Bdatacntsec`, section id 12 (`A-binary:917-918`) (bulk memory).

Every other form is absent from 2.0:

* `memargMemIdx`, `memargOffset64`: `Bmemarg = n:Bu32 m:Bu32` (`A-binary:220-221`)
  — no flag bit 6, and a 32-bit offset.
* `memIdxImm`: `0x3F 0x00`, `0x40 0x00`, `0xFC 8 x 0x00`, `0xFC 10 0x00 0x00`,
  `0xFC 11 0x00` (`A-binary:247-252`) — reserved bytes, as in 1.0.
* `limits64`: `Blimits = 0x00 n:Bu32 | 0x01 n:Bu32 m:Bu32` (`A-binary:124-126`).
* `refTypePrefix`: `Breftype = 0x70 | 0x6F` (`A-binary:98-100`) — no heap types.
* `subTypes`: `Btype = ft:Bfunctype` (`A-binary:786-787`) and
  `Bfunctype = 0x60 …` (`A-binary:114-115`) — no recursive groups, no explicit
  subtyping.
* `tableInit`: `Btable = tt:Btabletype` (`A-binary:810-811`) — no initializer.
* `tagSection`: `Bmodule` (`A-binary:923-942`) has no tag section. -/
def v2 : Forms
  | .tableIdxImm | .elemKinds | .dataKinds | .dataCount => true
  | _ => false

/-- The forms matching Lime1's `overlong` flag: `lime1` with call-indirect-overlong,
`v1` without. -/
def ofOverlong : Bool → Forms
  | true => lime1
  | false => v1

@[simp] theorem ofOverlong_true : ofOverlong true = lime1 := rfl

@[simp] theorem ofOverlong_false : ofOverlong false = v1 := rfl

/-- Pointwise inclusion of enabled forms. -/
def Le (F G : Forms) : Prop := ∀ f, F f = true → G f = true

theorem Le.refl (F : Forms) : Le F F := fun _ h => h

theorem Le.trans {F G H : Forms} (h₁ : Le F G) (h₂ : Le G H) : Le F H :=
  fun f h => h₂ f (h₁ f h)

theorem le_all (F : Forms) : Le F all := fun _ _ => rfl

theorem v1_le (F : Forms) : Le v1 F := fun _ h => nomatch h

theorem v1_le_lime1 : Le v1 lime1 := v1_le _

theorem v1_le_v2 : Le v1 v2 := v1_le _

/-- Lime1's one extra form, call-indirect-overlong, is 2.0's real table index. -/
theorem lime1_le_v2 : Le lime1 v2 := by
  intro f hf
  cases f <;> simp_all [lime1, v2]

theorem v2_le_all : Le v2 all := le_all _

end Forms

/-! ## Value types (5.2:7–37) -/

/-- `Bnumtype` (5.2:7–11). -/
inductive NumType : Bytes → Wasm.NumType → Prop where
  | f64 : NumType [0x7C] (.float .f64)
  | f32 : NumType [0x7D] (.float .f32)
  | i64 : NumType [0x7E] (.int .i64)
  | i32 : NumType [0x7F] (.int .i32)

/-- `Bvectype` (5.2:13–14). -/
inductive VecType : Bytes → Wasm.VecType → Prop where
  | v128 : VecType [0x7B] .v128

/-- `Babsheaptype` (5.2:16–28). -/
inductive AbsHeapType : Bytes → Wasm.AbsHeapType → Prop where
  | exn : AbsHeapType [0x69] .exn
  | array : AbsHeapType [0x6A] .array
  | struct : AbsHeapType [0x6B] .struct
  | i31 : AbsHeapType [0x6C] .i31
  | eq : AbsHeapType [0x6D] .eq
  | any : AbsHeapType [0x6E] .any
  | extern : AbsHeapType [0x6F] .extern
  | func : AbsHeapType [0x70] .func
  | none : AbsHeapType [0x71] .none
  | noextern : AbsHeapType [0x72] .noextern
  | nofunc : AbsHeapType [0x73] .nofunc
  | noexn : AbsHeapType [0x74] .noexn

/-- `Bheaptype` (5.2:30–32). The `s33` index rule `x33 >= 0 => _IDX $s33_to_u32(x33)`
is stated by reading the type index's value as a non-negative `s33`. -/
inductive HeapType : Bytes → Wasm.HeapType → Prop where
  | abs {b : Bytes} {ht : Wasm.AbsHeapType} (h : AbsHeapType b ht) : HeapType b (.abstract ht)
  | idx {b : Bytes} (x : TypeIdx) (h : S33 b x.toNat) : HeapType b (.typeIdx x)

/-- `Breftype` (5.2:34–37). The prefixed forms are `Form.refTypePrefix`. -/
inductive RefType (F : Forms) : Bytes → Wasm.RefType → Prop where
  | null {b : Bytes} {ht : Wasm.HeapType} (g : F .refTypePrefix = true) (h : HeapType b ht) :
      RefType F ([0x63] ++ b) ⟨true, ht⟩
  | nonNull {b : Bytes} {ht : Wasm.HeapType} (g : F .refTypePrefix = true) (h : HeapType b ht) :
      RefType F ([0x64] ++ b) ⟨false, ht⟩
  | abs {b : Bytes} {ht : Wasm.AbsHeapType} (h : AbsHeapType b ht) :
      RefType F b ⟨true, .abstract ht⟩

/-- `Bvaltype` (5.2:39–42). -/
inductive ValType (F : Forms) : Bytes → Wasm.ValType → Prop where
  | num {b : Bytes} {t : Wasm.NumType} (h : NumType b t) : ValType F b (.num t)
  | vec {b : Bytes} {t : Wasm.VecType} (h : VecType b t) : ValType F b (.vec t)
  | ref {b : Bytes} {t : Wasm.RefType} (h : RefType F b t) : ValType F b (.ref t)

/-- `Bresulttype = t*:Blist(Bvaltype)` (5.2:45–46). -/
abbrev ResultType (F : Forms) := Vec (ValType F)

/-! ## Type definitions (5.2:51–79) -/

/-- `Bmut` (5.2:51–53). -/
inductive Mut : Bytes → Mutability → Prop where
  | const : Mut [0x00] .const
  | var : Mut [0x01] .var

/-- `Bpacktype` (5.2:55–57). -/
inductive PackType : Bytes → Wasm.PackType → Prop where
  | i16 : PackType [0x77] .i16
  | i8 : PackType [0x78] .i8

/-- `Bstoragetype` (5.2:59–61). -/
inductive StorageType (F : Forms) : Bytes → Wasm.StorageType → Prop where
  | val {b : Bytes} {t : Wasm.ValType} (h : ValType F b t) : StorageType F b (.val t)
  | packed {b : Bytes} {t : Wasm.PackType} (h : PackType b t) : StorageType F b (.packed t)

/-- `Bfieldtype = zt:Bstoragetype mut?:Bmut => mut? zt` (5.2:63–64). -/
inductive FieldType (F : Forms) : Bytes → Wasm.FieldType → Prop where
  | mk {b b' : Bytes} {zt : Wasm.StorageType} {m : Mutability}
      (hz : StorageType F b zt) (hm : Mut b' m) : FieldType F (b ++ b') ⟨m, zt⟩

/-- `Bcomptype` (5.2:66–69). -/
inductive CompType (F : Forms) : Bytes → Wasm.CompositeType → Prop where
  | array {b : Bytes} {ft : Wasm.FieldType} (h : FieldType F b ft) :
      CompType F ([0x5E] ++ b) (.array ft)
  | struct {b : Bytes} {fts : List Wasm.FieldType} (h : Vec (FieldType F) b fts) :
      CompType F ([0x5F] ++ b) (.struct fts)
  | func {b₁ b₂ : Bytes} {t₁ t₂ : List Wasm.ValType} (h₁ : ResultType F b₁ t₁)
      (h₂ : ResultType F b₂ t₂) : CompType F ([0x60] ++ b₁ ++ b₂) (.func ⟨t₁, t₂⟩)

/-- `Bsubtype` (5.2:71–74). The explicit forms are `Form.subTypes`. -/
inductive SubType (F : Forms) : Bytes → Wasm.SubType → Prop where
  | final {bx bc : Bytes} {xs : List TypeIdx} {ct : Wasm.CompositeType}
      (g : F .subTypes = true) (hx : Vec Index bx xs) (hc : CompType F bc ct) :
      SubType F ([0x4F] ++ bx ++ bc) ⟨true, xs, ct⟩
  | open_ {bx bc : Bytes} {xs : List TypeIdx} {ct : Wasm.CompositeType}
      (g : F .subTypes = true) (hx : Vec Index bx xs) (hc : CompType F bc ct) :
      SubType F ([0x50] ++ bx ++ bc) ⟨false, xs, ct⟩
  | plain {b : Bytes} {ct : Wasm.CompositeType} (hc : CompType F b ct) :
      SubType F b ⟨true, [], ct⟩

/-- `Brectype` (5.2:76–78). The group form is `Form.subTypes`. -/
inductive RecType (F : Forms) : Bytes → Wasm.RecType → Prop where
  | group {b : Bytes} {sts : List Wasm.SubType} (g : F .subTypes = true)
      (h : Vec (SubType F) b sts) : RecType F ([0x4E] ++ b) ⟨sts⟩
  | single {b : Bytes} {st : Wasm.SubType} (h : SubType F b st) : RecType F b ⟨[st]⟩

/-! ## External types (5.2:83–107) -/

/-- A limits bound: `Bu64` (5.2:84–87), or, as in Wasm 1.0, `u32` (always admitted,
and subsumed by `u64` when `Form.limits64` is enabled). -/
inductive Bound (F : Forms) : Bytes → Fin (2 ^ 64) → Prop where
  | u64 {b : Bytes} {n : Fin (2 ^ 64)} (g : F .limits64 = true) (h : U64 b n.val) : Bound F b n
  | u32 {b : Bytes} {n : Fin (2 ^ 64)} (h : U32 b n.val) : Bound F b n

/-- `Blimits` (5.2:83–87). -/
inductive Limits (F : Forms) : Bytes → AddrType × Wasm.Limits → Prop where
  | i32 {b : Bytes} {n : Fin (2 ^ 64)} (h : Bound F b n) :
      Limits F ([0x00] ++ b) (.i32, ⟨n, none⟩)
  | i32Max {b b' : Bytes} {n m : Fin (2 ^ 64)} (h : Bound F b n) (h' : Bound F b' m) :
      Limits F ([0x01] ++ b ++ b') (.i32, ⟨n, some m⟩)
  | i64 {b : Bytes} {n : Fin (2 ^ 64)} (g : F .limits64 = true) (h : U64 b n.val) :
      Limits F ([0x04] ++ b) (.i64, ⟨n, none⟩)
  | i64Max {b b' : Bytes} {n m : Fin (2 ^ 64)} (g : F .limits64 = true) (h : U64 b n.val)
      (h' : U64 b' m.val) : Limits F ([0x05] ++ b ++ b') (.i64, ⟨n, some m⟩)

/-- `Btagtype = 0x00 x:Btypeidx => _IDX x` (5.2:89–90). -/
inductive TagType : Bytes → Wasm.TagType → Prop where
  | mk {b : Bytes} {x : TypeIdx} (h : Index b x) : TagType ([0x00] ++ b) x

/-- `Bglobaltype = t:Bvaltype mut?:Bmut => mut? t` (5.2:92–93). -/
inductive GlobalType (F : Forms) : Bytes → Wasm.GlobalType → Prop where
  | mk {b b' : Bytes} {t : Wasm.ValType} {m : Mutability} (ht : ValType F b t) (hm : Mut b' m) :
      GlobalType F (b ++ b') ⟨m, t⟩

/-- `Bmemtype = (at,lim):Blimits => at lim PAGE` (5.2:95–96). -/
inductive MemType (F : Forms) : Bytes → Wasm.MemoryType → Prop where
  | mk {b : Bytes} {a : AddrType} {lim : Wasm.Limits} (h : Limits F b (a, lim)) :
      MemType F b ⟨a, lim⟩

/-- `Btabletype = rt:Breftype (at,lim):Blimits => at lim rt` (5.2:98–99). -/
inductive TableType (F : Forms) : Bytes → Wasm.TableType → Prop where
  | mk {b b' : Bytes} {rt : Wasm.RefType} {a : AddrType} {lim : Wasm.Limits}
      (hr : RefType F b rt) (hl : Limits F b' (a, lim)) : TableType F (b ++ b') ⟨a, lim, rt⟩

/-- `Bexterntype` (5.2:102–107). -/
inductive ExternType (F : Forms) : Bytes → Wasm.ExternType → Prop where
  | func {b : Bytes} {x : TypeIdx} (h : Index b x) : ExternType F ([0x00] ++ b) (.func x)
  | table {b : Bytes} {tt : Wasm.TableType} (h : TableType F b tt) :
      ExternType F ([0x01] ++ b) (.table tt)
  | memory {b : Bytes} {mt : Wasm.MemoryType} (h : MemType F b mt) :
      ExternType F ([0x02] ++ b) (.memory mt)
  | global {b : Bytes} {gt : Wasm.GlobalType} (h : GlobalType F b gt) :
      ExternType F ([0x03] ++ b) (.global gt)
  | tag {b : Bytes} {jt : Wasm.TagType} (h : TagType b jt) : ExternType F ([0x04] ++ b) (.tag jt)

/-! ## Properties -/

/-! ### Helpers -/

/-- `Seq` is monotone in its element production. -/
private theorem seq_imp {α : Type} {G H : Bytes → α → Prop} (f : ∀ {b a}, G b a → H b a)
    {b : Bytes} {xs : List α} (h : Seq G b xs) : Seq H b xs := by
  induction h with
  | nil => exact .nil
  | cons hg _ ih => exact .cons (f hg) ih

/-- `Vec` is monotone in its element production. -/
private theorem vec_imp {α : Type} {G H : Bytes → α → Prop} (f : ∀ {b a}, G b a → H b a)
    {b : Bytes} {xs : List α} (h : Vec G b xs) : Vec H b xs := by
  cases h with
  | mk hn hs => exact .mk hn (seq_imp f hs)

/-- Two prefix-free productions in sequence. -/
private theorem prefixFree_append {α β : Type} {G : Bytes → α → Prop}
    {H : Bytes → β → Prop} (hG : PrefixFree G) (hH : PrefixFree H)
    {b₁ b₂ b₁' b₂' r r' : Bytes} {a₁ a₁' : α} {a₂ a₂' : β} (h₁ : G b₁ a₁) (h₂ : H b₂ a₂) (h₁' : G b₁' a₁') (h₂' : H b₂' a₂')
    (h : b₁ ++ (b₂ ++ r) = b₁' ++ (b₂' ++ r')) : b₁ = b₁' ∧ b₂ = b₂' ∧ a₁ = a₁' ∧ a₂ = a₂' := by
  obtain ⟨rfl, rfl⟩ := hG h₁ h₁' h
  obtain ⟨rfl, rfl⟩ := hH h₂ h₂' (List.append_cancel_left h)
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Encodings sharing a prefix of the input start with the same byte. -/
private theorem head_eq {b b' r r' t t' : Bytes} {c c' : UInt8} (hb : b = c :: t)
    (hb' : b' = c' :: t') (h : b ++ r = b' ++ r') : c.toNat = c'.toNat := by
  subst hb hb'
  simp only [List.cons_append, List.cons.injEq] at h
  rw [h.1]

private theorem sn_ne_nil {N : Nat} {i : Int} (h : SN N [] i) : False := by
  cases h

/-- A signed LEB128 encoding whose first byte is in `[0x40, 0x80)` is negative. -/
private theorem sn_head_absurd {N : Nat} {c : UInt8} {t : Bytes} {x : Nat}
    (hc₁ : 0x40 ≤ c.toNat) (hc₂ : c.toNat < 0x80) (h : SN N (c :: t) (x : Int)) : False := by
  generalize hv : (x : Int) = v at h
  cases h with
  | pos _ h₁ _ => omega
  | neg _ _ h₂ _ => omega
  | cont _ h₁ _ _ => omega

/-! ### Monotonicity in the encoding forms -/

theorem Bound.mono {F G : Forms} (h : F.Le G) {b : Bytes} {n : Fin (2 ^ 64)}
    (hb : Bound F b n) : Bound G b n := by
  cases hb with
  | u64 g hu => exact .u64 (h _ g) hu
  | u32 hu => exact .u32 hu

theorem Bound.all_iff (b : Bytes) (n : Fin (2 ^ 64)) : Bound Forms.all b n ↔ U64 b n.val := by
  constructor
  · intro hb
    cases hb with
    | u64 _ hu => exact hu
    | u32 hu => exact UN.mono (by decide) hu
  · exact .u64 rfl

theorem RefType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.RefType}
    (hr : RefType F b t) : RefType G b t := by
  cases hr with
  | null g hh => exact .null (h _ g) hh
  | nonNull g hh => exact .nonNull (h _ g) hh
  | abs ha => exact .abs ha

theorem ValType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.ValType}
    (hv : ValType F b t) : ValType G b t := by
  cases hv with
  | num hn => exact .num hn
  | vec hv => exact .vec hv
  | ref hr => exact .ref (hr.mono h)

theorem StorageType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.StorageType}
    (hs : StorageType F b t) : StorageType G b t := by
  cases hs with
  | val hv => exact .val (hv.mono h)
  | packed hp => exact .packed hp

theorem FieldType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.FieldType}
    (hf : FieldType F b t) : FieldType G b t := by
  cases hf with
  | mk hz hm => exact .mk (hz.mono h) hm

theorem CompType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.CompositeType}
    (hc : CompType F b t) : CompType G b t := by
  cases hc with
  | array hf => exact .array (hf.mono h)
  | struct hf => exact .struct (vec_imp (fun hx => hx.mono h) hf)
  | func h₁ h₂ =>
    exact .func (vec_imp (fun hx => hx.mono h) h₁) (vec_imp (fun hx => hx.mono h) h₂)

theorem SubType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.SubType}
    (hs : SubType F b t) : SubType G b t := by
  cases hs with
  | final g hx hc => exact .final (h _ g) hx (hc.mono h)
  | open_ g hx hc => exact .open_ (h _ g) hx (hc.mono h)
  | plain hc => exact .plain (hc.mono h)

theorem RecType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.RecType}
    (hr : RecType F b t) : RecType G b t := by
  cases hr with
  | group g hs => exact .group (h _ g) (vec_imp (fun hx => hx.mono h) hs)
  | single hs => exact .single (hs.mono h)

theorem Limits.mono {F G : Forms} (h : F.Le G) {b : Bytes} {l : AddrType × Wasm.Limits}
    (hl : Limits F b l) : Limits G b l := by
  cases hl with
  | i32 hb => exact .i32 (hb.mono h)
  | i32Max hb hb' => exact .i32Max (hb.mono h) (hb'.mono h)
  | i64 g hu => exact .i64 (h _ g) hu
  | i64Max g hu hu' => exact .i64Max (h _ g) hu hu'

theorem GlobalType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.GlobalType}
    (hg : GlobalType F b t) : GlobalType G b t := by
  cases hg with
  | mk hv hm => exact .mk (hv.mono h) hm

theorem MemType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.MemoryType}
    (hm : MemType F b t) : MemType G b t := by
  cases hm with
  | mk hl => exact .mk (hl.mono h)

theorem TableType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.TableType}
    (ht : TableType F b t) : TableType G b t := by
  cases ht with
  | mk hr hl => exact .mk (hr.mono h) (hl.mono h)

theorem ExternType.mono {F G : Forms} (h : F.Le G) {b : Bytes} {t : Wasm.ExternType}
    (hx : ExternType F b t) : ExternType G b t := by
  cases hx with
  | func hi => exact .func hi
  | table ht => exact .table (ht.mono h)
  | memory hm => exact .memory (hm.mono h)
  | global hg => exact .global (hg.mono h)
  | tag hj => exact .tag hj

/-! ### First bytes -/

theorem NumType.head {b : Bytes} {t : Wasm.NumType} (h : NumType b t) :
    ∃ c rest, b = c :: rest ∧ 0x7C ≤ c.toNat ∧ c.toNat ≤ 0x7F := by
  cases h <;> exact ⟨_, _, rfl, by decide, by decide⟩

theorem VecType.head {b : Bytes} {t : Wasm.VecType} (h : VecType b t) :
    ∃ c rest, b = c :: rest ∧ c.toNat = 0x7B := by
  cases h; exact ⟨_, _, rfl, by decide⟩

theorem AbsHeapType.head {b : Bytes} {t : Wasm.AbsHeapType} (h : AbsHeapType b t) :
    ∃ c, b = [c] ∧ 0x69 ≤ c.toNat ∧ c.toNat ≤ 0x74 := by
  cases h <;> exact ⟨_, rfl, by decide, by decide⟩

theorem RefType.head {F : Forms} {b : Bytes} {t : Wasm.RefType} (h : RefType F b t) :
    ∃ c rest, b = c :: rest ∧ 0x63 ≤ c.toNat ∧ c.toNat ≤ 0x74 ∧
      (c.toNat ≤ 0x64 ∨ 0x69 ≤ c.toNat) := by
  cases h with
  | null => exact ⟨_, _, rfl, by decide⟩
  | nonNull => exact ⟨_, _, rfl, by decide⟩
  | abs ha =>
    obtain ⟨c, rfl, h₁, h₂⟩ := ha.head
    exact ⟨c, [], rfl, by omega⟩

theorem ValType.head {F : Forms} {b : Bytes} {t : Wasm.ValType} (h : ValType F b t) :
    ∃ c rest, b = c :: rest ∧ 0x63 ≤ c.toNat ∧ c.toNat ≤ 0x7F ∧
      (c.toNat ≤ 0x64 ∨ 0x69 ≤ c.toNat) ∧ c.toNat ≠ 0x77 ∧ c.toNat ≠ 0x78 := by
  cases h with
  | num hn =>
    obtain ⟨c, rest, rfl, h₁, h₂⟩ := hn.head
    exact ⟨c, rest, rfl, by omega⟩
  | vec hv =>
    obtain ⟨c, rest, rfl, h₁⟩ := hv.head
    exact ⟨c, rest, rfl, by omega⟩
  | ref hr =>
    obtain ⟨c, rest, rfl, h₁⟩ := hr.head
    exact ⟨c, rest, rfl, by omega⟩

theorem CompType.head {F : Forms} {b : Bytes} {t : Wasm.CompositeType} (h : CompType F b t) :
    ∃ c rest, b = c :: rest ∧ 0x5E ≤ c.toNat ∧ c.toNat ≤ 0x60 := by
  cases h <;> exact ⟨_, _, rfl, by decide, by decide⟩

theorem SubType.head {F : Forms} {b : Bytes} {t : Wasm.SubType} (h : SubType F b t) :
    ∃ c rest, b = c :: rest ∧ 0x4F ≤ c.toNat ∧ c.toNat ≤ 0x60 := by
  cases h with
  | final => exact ⟨_, _, rfl, by decide, by decide⟩
  | open_ => exact ⟨_, _, rfl, by decide, by decide⟩
  | plain hc =>
    obtain ⟨c, rest, rfl, h₁, h₂⟩ := hc.head
    exact ⟨c, rest, rfl, by omega, by omega⟩

/-! ### Prefix-freedom -/

theorem NumType.prefixFree : PrefixFree NumType := by
  intro b b' r r' a a' ha ha' h
  cases ha <;> cases ha' <;> first | exact ⟨rfl, rfl⟩ | simp at h

theorem VecType.prefixFree : PrefixFree VecType := by
  intro b b' r r' a a' ha ha' _
  cases ha; cases ha'; exact ⟨rfl, rfl⟩

theorem AbsHeapType.prefixFree : PrefixFree AbsHeapType := by
  intro b b' r r' a a' ha ha' h
  cases ha <;> cases ha' <;> first | exact ⟨rfl, rfl⟩ | simp at h

theorem HeapType.prefixFree : PrefixFree HeapType := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | abs ha =>
    cases ha' with
    | abs ha' =>
      obtain ⟨rfl, rfl⟩ := AbsHeapType.prefixFree ha ha' h
      exact ⟨rfl, rfl⟩
    | idx x hs =>
      exfalso
      obtain ⟨c, rfl, h₁, h₂⟩ := ha.head
      rcases b' with _ | ⟨c', t⟩
      · exact sn_ne_nil hs
      · have := head_eq rfl rfl h
        exact sn_head_absurd (c := c') (by omega) (by omega) hs
  | idx x hs =>
    cases ha' with
    | abs ha' =>
      exfalso
      obtain ⟨c, rfl, h₁, h₂⟩ := ha'.head
      rcases b with _ | ⟨c', t⟩
      · exact sn_ne_nil hs
      · have := head_eq rfl rfl h
        exact sn_head_absurd (c := c') (by omega) (by omega) hs
    | idx x' hs' =>
      obtain ⟨rfl, hx⟩ := SN.prefixFree 33 hs hs' h
      exact ⟨rfl, by rw [Idx.toNat_injective (Int.ofNat.inj hx)]⟩

theorem RefType.prefixFree (F : Forms) : PrefixFree (RefType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | null _ hh =>
    cases ha' with
    | null _ hh' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := HeapType.prefixFree hh hh' h
      exact ⟨rfl, rfl⟩
    | nonNull => simp at h
    | abs ha' =>
      obtain ⟨c, rfl, h₁, h₂⟩ := ha'.head
      have := head_eq rfl rfl h
      simp at this; omega
  | nonNull _ hh =>
    cases ha' with
    | null => simp at h
    | nonNull _ hh' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := HeapType.prefixFree hh hh' h
      exact ⟨rfl, rfl⟩
    | abs ha' =>
      obtain ⟨c, rfl, h₁, h₂⟩ := ha'.head
      have := head_eq rfl rfl h
      simp at this; omega
  | abs ha =>
    obtain ⟨c, rfl, h₁, h₂⟩ := ha.head
    cases ha' with
    | null =>
      have := head_eq rfl rfl h
      simp at this; omega
    | nonNull =>
      have := head_eq rfl rfl h
      simp at this; omega
    | abs ha' =>
      obtain ⟨rfl, rfl⟩ := AbsHeapType.prefixFree ha ha' h
      exact ⟨rfl, rfl⟩

theorem ValType.prefixFree (F : Forms) : PrefixFree (ValType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | num hn =>
    cases ha' with
    | num hn' =>
      obtain ⟨rfl, rfl⟩ := NumType.prefixFree hn hn' h
      exact ⟨rfl, rfl⟩
    | vec hv' =>
      obtain ⟨c, _, rfl, hc⟩ := hn.head
      obtain ⟨c', _, rfl, hc'⟩ := hv'.head
      have := head_eq rfl rfl h
      omega
    | ref hr' =>
      obtain ⟨c, _, rfl, hc⟩ := hn.head
      obtain ⟨c', _, rfl, hc'⟩ := hr'.head
      have := head_eq rfl rfl h
      omega
  | vec hv =>
    cases ha' with
    | num hn' =>
      obtain ⟨c, _, rfl, hc⟩ := hv.head
      obtain ⟨c', _, rfl, hc'⟩ := hn'.head
      have := head_eq rfl rfl h
      omega
    | vec hv' =>
      obtain ⟨rfl, rfl⟩ := VecType.prefixFree hv hv' h
      exact ⟨rfl, rfl⟩
    | ref hr' =>
      obtain ⟨c, _, rfl, hc⟩ := hv.head
      obtain ⟨c', _, rfl, hc'⟩ := hr'.head
      have := head_eq rfl rfl h
      omega
  | ref hr =>
    cases ha' with
    | num hn' =>
      obtain ⟨c, _, rfl, hc⟩ := hr.head
      obtain ⟨c', _, rfl, hc'⟩ := hn'.head
      have := head_eq rfl rfl h
      omega
    | vec hv' =>
      obtain ⟨c, _, rfl, hc⟩ := hr.head
      obtain ⟨c', _, rfl, hc'⟩ := hv'.head
      have := head_eq rfl rfl h
      omega
    | ref hr' =>
      obtain ⟨rfl, rfl⟩ := RefType.prefixFree F hr hr' h
      exact ⟨rfl, rfl⟩

theorem Mut.prefixFree : PrefixFree Mut := by
  intro b b' r r' a a' ha ha' h
  cases ha <;> cases ha' <;> first | exact ⟨rfl, rfl⟩ | simp at h

theorem PackType.prefixFree : PrefixFree PackType := by
  intro b b' r r' a a' ha ha' h
  cases ha <;> cases ha' <;> first | exact ⟨rfl, rfl⟩ | simp at h

theorem PackType.head {b : Bytes} {t : Wasm.PackType} (h : PackType b t) :
    ∃ c rest, b = c :: rest ∧ (c.toNat = 0x77 ∨ c.toNat = 0x78) := by
  cases h <;> exact ⟨_, _, rfl, by decide⟩

theorem StorageType.prefixFree (F : Forms) : PrefixFree (StorageType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | val hv =>
    cases ha' with
    | val hv' =>
      obtain ⟨rfl, rfl⟩ := ValType.prefixFree F hv hv' h
      exact ⟨rfl, rfl⟩
    | packed hp' =>
      obtain ⟨c, _, rfl, hc⟩ := hv.head
      obtain ⟨c', _, rfl, hc'⟩ := hp'.head
      have := head_eq rfl rfl h
      omega
  | packed hp =>
    cases ha' with
    | val hv' =>
      obtain ⟨c, _, rfl, hc⟩ := hp.head
      obtain ⟨c', _, rfl, hc'⟩ := hv'.head
      have := head_eq rfl rfl h
      omega
    | packed hp' =>
      obtain ⟨rfl, rfl⟩ := PackType.prefixFree hp hp' h
      exact ⟨rfl, rfl⟩

theorem FieldType.prefixFree (F : Forms) : PrefixFree (FieldType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | mk hz hm =>
    cases ha' with
    | mk hz' hm' =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (StorageType.prefixFree F) Mut.prefixFree
        hz hm hz' hm' h
      exact ⟨rfl, rfl⟩

theorem CompType.prefixFree (F : Forms) : PrefixFree (CompType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | array hf =>
    cases ha' with
    | array hf' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := FieldType.prefixFree F hf hf' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | struct hf =>
    cases ha' with
    | struct hf' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree (FieldType.prefixFree F) hf hf' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | func h₁ h₂ =>
    cases ha' with
    | func h₁' h₂' =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (Vec.prefixFree (ValType.prefixFree F))
        (Vec.prefixFree (ValType.prefixFree F)) h₁ h₂ h₁' h₂' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h

theorem SubType.prefixFree (F : Forms) : PrefixFree (SubType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | final _ hx hc =>
    cases ha' with
    | final _ hx' hc' =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (Vec.prefixFree Index.prefixFree)
        (CompType.prefixFree F) hx hc hx' hc' h
      exact ⟨rfl, rfl⟩
    | open_ => simp at h
    | plain hc' =>
      obtain ⟨c', _, rfl, hc'⟩ := hc'.head
      have := head_eq (List.cons_append ..) rfl h
      simp at this
      omega
  | open_ _ hx hc =>
    cases ha' with
    | final => simp at h
    | open_ _ hx' hc' =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (Vec.prefixFree Index.prefixFree)
        (CompType.prefixFree F) hx hc hx' hc' h
      exact ⟨rfl, rfl⟩
    | plain hc' =>
      obtain ⟨c', _, rfl, hc'⟩ := hc'.head
      have := head_eq (List.cons_append ..) rfl h
      simp at this
      omega
  | plain hc =>
    cases ha' with
    | final =>
      obtain ⟨c, _, rfl, hc⟩ := hc.head
      have := head_eq rfl (List.cons_append ..) h
      simp at this
      omega
    | open_ =>
      obtain ⟨c, _, rfl, hc⟩ := hc.head
      have := head_eq rfl (List.cons_append ..) h
      simp at this
      omega
    | plain hc' =>
      obtain ⟨rfl, rfl⟩ := CompType.prefixFree F hc hc' h
      exact ⟨rfl, rfl⟩

theorem RecType.prefixFree (F : Forms) : PrefixFree (RecType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | group _ hs =>
    cases ha' with
    | group _ hs' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree (SubType.prefixFree F) hs hs' h
      exact ⟨rfl, rfl⟩
    | single hs' =>
      obtain ⟨c', _, rfl, hc'⟩ := hs'.head
      have := head_eq rfl rfl h
      simp at this
      omega
  | single hs =>
    cases ha' with
    | group _ hs' =>
      obtain ⟨c, _, rfl, hc⟩ := hs.head
      have := head_eq rfl rfl h
      simp at this
      omega
    | single hs' =>
      obtain ⟨rfl, rfl⟩ := SubType.prefixFree F hs hs' h
      exact ⟨rfl, rfl⟩

theorem Bound.toU64 {F : Forms} {b : Bytes} {n : Fin (2 ^ 64)} (h : Bound F b n) :
    U64 b n.val := by
  cases h with
  | u64 _ hu => exact hu
  | u32 hu => exact UN.mono (by decide) hu

theorem Bound.prefixFree (F : Forms) : PrefixFree (Bound F) := by
  intro b b' r r' a a' ha ha' h
  obtain ⟨rfl, hv⟩ := UN.prefixFree 64 ha.toU64 ha'.toU64 h
  exact ⟨rfl, Fin.ext hv⟩

theorem Limits.prefixFree (F : Forms) : PrefixFree (Limits F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | i32 hb =>
    cases ha' with
    | i32 hb' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := Bound.prefixFree F hb hb' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | i32Max hb hm =>
    cases ha' with
    | i32Max hb' hm' =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (Bound.prefixFree F) (Bound.prefixFree F)
        hb hm hb' hm' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | i64 _ hu =>
    cases ha' with
    | i64 _ hu' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, hv⟩ := UN.prefixFree 64 hu hu' h
      obtain rfl := Fin.ext hv
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | i64Max _ hu hm =>
    cases ha' with
    | i64Max _ hu' hm' =>
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, rfl, hv, hw⟩ := prefixFree_append (UN.prefixFree 64) (UN.prefixFree 64)
        hu hm hu' hm' h
      obtain rfl := Fin.ext hv
      obtain rfl := Fin.ext hw
      exact ⟨rfl, rfl⟩
    | _ => simp at h

theorem TagType.prefixFree : PrefixFree TagType := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | mk hi =>
    cases ha' with
    | mk hi' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hi hi' h
      exact ⟨rfl, rfl⟩

theorem GlobalType.prefixFree (F : Forms) : PrefixFree (GlobalType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | mk hv hm =>
    cases ha' with
    | mk hv' hm' =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := prefixFree_append (ValType.prefixFree F) Mut.prefixFree
        hv hm hv' hm' h
      exact ⟨rfl, rfl⟩

theorem MemType.prefixFree (F : Forms) : PrefixFree (MemType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | mk hl =>
    cases ha' with
    | mk hl' =>
      obtain ⟨rfl, hal⟩ := Limits.prefixFree F hl hl' h
      simp only [Prod.mk.injEq] at hal
      obtain ⟨rfl, rfl⟩ := hal
      exact ⟨rfl, rfl⟩

theorem TableType.prefixFree (F : Forms) : PrefixFree (TableType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | mk hr hl =>
    cases ha' with
    | mk hr' hl' =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, rfl, rfl, hal⟩ := prefixFree_append (RefType.prefixFree F)
        (Limits.prefixFree F) hr hl hr' hl' h
      simp only [Prod.mk.injEq] at hal
      obtain ⟨rfl, rfl⟩ := hal
      exact ⟨rfl, rfl⟩

theorem ExternType.prefixFree (F : Forms) : PrefixFree (ExternType F) := by
  intro b b' r r' a a' ha ha' h
  cases ha with
  | func hi =>
    cases ha' with
    | func hi' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := Index.prefixFree hi hi' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | table ht =>
    cases ha' with
    | table ht' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := TableType.prefixFree F ht ht' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | memory hm =>
    cases ha' with
    | memory hm' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := MemType.prefixFree F hm hm' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | global hg =>
    cases ha' with
    | global hg' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := GlobalType.prefixFree F hg hg' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h
  | tag hj =>
    cases ha' with
    | tag hj' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := TagType.prefixFree hj hj' h
      exact ⟨rfl, rfl⟩
    | _ => simp at h

end Silmaril.Wasm.Binary.Core
