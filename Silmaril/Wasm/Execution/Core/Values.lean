module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Validation.Subtyping.Extern
public import Silmaril.Wasm.Validation.TypeOk
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Runtime value typing (§4.1)

`Num_ok`, `Vec_ok`, `Ref_ok` (9 rules), `Val_ok`, `Packval_ok`, `Fieldval_ok`,
`Externaddr_ok` (6 rules). The `sub` rules use subtyping and well-formedness in
the empty context `{}` (runtime types are closed).

`Ref_ok` is what `ref.test`, `ref.cast` and `br_on_cast*` consult at run time.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- `Ref_ok: s ⊢ ref : reftype`. -/
inductive RefOk (s : Store H) : Ref → CRefType → Prop where
  /-- `Ref_ok/null`. -/
  | null : RefOk s .null (.ref true .bot)
  /-- `Ref_ok/i31`. -/
  | i31 (b : BitVec 31) : RefOk s (.i31 b) (.ref false (.abs .i31))
  /-- `Ref_ok/struct`. -/
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      RefOk s (.struct a) (.ref false (.defHeap si.type))
  /-- `Ref_ok/array`. -/
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      RefOk s (.array a) (.ref false (.defHeap ai.type))
  /-- `Ref_ok/func`. -/
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      RefOk s (.func a) (.ref false (.defHeap fi.type))
  /-- `Ref_ok/exn`. -/
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      RefOk s (.exn a) (.ref false (.abs .exn))
  /-- `Ref_ok/host`. -/
  | host (a : Nat) : RefOk s (.host a) (.ref false (.abs .any))
  /-- `Ref_ok/extern`. -/
  | extern {r : Ref} (h : RefOk s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      RefOk s (.extern r) (.ref false (.abs .extern))
  /-- `Ref_ok/sub`. -/
  | sub {r : Ref} {rt rt' : CRefType} (h : RefOk s r rt') (hok : TyOk {} rt)
      (hs : Sub {} rt' rt) : RefOk s r rt

/-- `Val_ok` (with `Num_ok`, `Vec_ok`). -/
inductive ValOk (s : Store H) : Val → CValType → Prop where
  | num (v : NumVal) : ValOk s (.num v) (.num v.type)
  | vec (b : BitVec 128) : ValOk s (.vec b) (.vec .v128)
  | ref {r : Ref} {rt : CRefType} (h : RefOk s r rt) : ValOk s (.ref r) (.refv rt)

/-- `Fieldval_ok` (with `Packval_ok`). -/
inductive FieldValOk (s : Store H) : FieldVal → CStorageType → Prop where
  | val {v : Val} {t : CValType} (h : ValOk s v t) : FieldValOk s (.val v) (.val t)
  | pack (p : PackType) (b : BitVec p.width) : FieldValOk s (.pack p b) (.pack p)

/-- `Externaddr_ok`. -/
inductive ExternAddrOk (s : Store H) : ExternAddr → CExternType → Prop where
  | tag {a : Nat} {ti : TagInst} (h : s.tags[a]? = some ti) : ExternAddrOk s (.tag a) (.tag ti.type)
  | global {a : Nat} {gi : GlobalInst} (h : s.globals[a]? = some gi) :
      ExternAddrOk s (.global a) (.global gi.type)
  | mem {a : Nat} {mi : MemInst} (h : s.mems[a]? = some mi) : ExternAddrOk s (.mem a) (.mem mi.type)
  | table {a : Nat} {ti : TableInst} (h : s.tables[a]? = some ti) :
      ExternAddrOk s (.table a) (.table ti.type)
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      ExternAddrOk s (.func a) (.func fi.type)
  | sub {xa : ExternAddr} {xt xt' : CExternType} (h : ExternAddrOk s xa xt')
      (hok : ExternTypeOk {} xt) (hs : ExternSub {} xt' xt) : ExternAddrOk s xa xt

/-- The precise (principal) type of a reference, when it exists. -/
def Ref.type? (s : Store H) : Ref → Option CRefType
  | .null => some (.ref true .bot)
  | .i31 _ => some (.ref false (.abs .i31))
  | .struct a => s.structs[a]?.map fun si => .ref false (.defHeap si.type)
  | .array a => s.arrays[a]?.map fun ai => .ref false (.defHeap ai.type)
  | .func a => s.funcs[a]?.map fun fi => .ref false (.defHeap fi.type)
  | .exn a => s.exns[a]?.map fun _ => .ref false (.abs .exn)
  | .host _ => some (.ref false (.abs .any))
  | .extern _ => some (.ref false (.abs .extern))

theorem _root_.Silmaril.Wasm.Validation.TypeCtx.ok_empty : TypeCtx.Ok {} := by
  simp [TypeCtx.Ok]

/-- Every typing of a reference is its principal type, or a well-formed supertype of it. -/
theorem RefOk.principal {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∃ rt₀, Ref.type? s r = some rt₀ ∧ (rt = rt₀ ∨ (TyOk {} rt ∧ Sub {} rt₀ rt)) ∧
      (∀ r', r = .extern r' → RefOk s r' (.ref false (.abs .any)) ∧ r' ≠ .null) := by
  induction h with
  | null => exact ⟨_, rfl, .inl rfl, by intro r' h; cases h⟩
  | i31 b => exact ⟨_, rfl, .inl rfl, by intro r' h; cases h⟩
  | struct h => exact ⟨_, by simp [Ref.type?, h], .inl rfl, by intro r' h; cases h⟩
  | array h => exact ⟨_, by simp [Ref.type?, h], .inl rfl, by intro r' h; cases h⟩
  | func h => exact ⟨_, by simp [Ref.type?, h], .inl rfl, by intro r' h; cases h⟩
  | exn h => exact ⟨_, by simp [Ref.type?, h], .inl rfl, by intro r' h; cases h⟩
  | host a => exact ⟨_, rfl, .inl rfl, by intro r' h; cases h⟩
  | extern h hn _ => exact ⟨_, rfl, .inl rfl, fun r' e => by cases e; exact ⟨h, hn⟩⟩
  | sub _ hok hs ih =>
    obtain ⟨rt₀, e, hrt, hx⟩ := ih
    refine ⟨rt₀, e, .inr ⟨hok, ?_⟩, hx⟩
    rcases hrt with rfl | ⟨hok', hs'⟩
    · exact hs
    · exact Sub.trans TypeCtx.ok_empty hok' hs' hs

/-- The principal type is a type. -/
theorem RefOk.of_type? {s : Store H} {r : Ref} {rt₀ : CRefType} (e : Ref.type? s r = some rt₀)
    (hx : ∀ r', r = .extern r' → RefOk s r' (.ref false (.abs .any)) ∧ r' ≠ .null) :
    RefOk s r rt₀ := by
  cases r with
  | null => cases e; exact .null
  | i31 b => cases e; exact .i31 b
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, h, rfl⟩ := e; exact .struct h
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, h, rfl⟩ := e; exact .array h
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, rfl⟩ := e; exact .func h
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ei, h, rfl⟩ := e; exact .exn h
  | host a => cases e; exact .host a
  | extern r' =>
    cases e
    obtain ⟨h, hn⟩ := hx r' rfl
    exact .extern h hn

/-- Casts are decidable given decidable subtyping: `Ref_ok s r rt` iff the
principal type is a subtype of a well-formed `rt`. -/
theorem RefOk.iff_principal (s : Store H) (r : Ref) (rt : CRefType) (hrt : TyOk {} rt) :
    RefOk s r rt ↔ ∃ rt₀, Ref.type? s r = some rt₀ ∧ Sub {} rt₀ rt ∧
      (∀ r', r = .extern r' → RefOk s r' (.ref false (.abs .any)) ∧ r' ≠ .null) := by
  constructor
  · intro h
    obtain ⟨rt₀, e, hrt, hx⟩ := h.principal
    refine ⟨rt₀, e, ?_, hx⟩
    rcases hrt with rfl | ⟨_, hs⟩
    · exact Sub.refl _ (k := .ref) trivial _
    · exact hs
  · rintro ⟨rt₀, e, hs, hx⟩
    exact .sub (RefOk.of_type? e hx) hrt hs

end Silmaril.Wasm.Execution.Core
