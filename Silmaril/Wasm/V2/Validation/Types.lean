module

public import Silmaril.Wasm.V2.Types
public import Mathlib.Data.List.Forall2

/-!
# WebAssembly 2.0 type validation and subtyping

Transcribed from the official SpecTec source
`specification/wasm-2.0/6-typing.spectec`, sections `Types` (`6-typing:15-61`)
and `Subtyping` (`6-typing:65-134`), at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `6-typing:NN` point into that file.

## The validation-only value type

`valtype ::= numtype | vectype | reftype | BOT` (`1-syntax:138`). The `BOT`
alternative is reachable only during validation — no module can mention it, the
binary format has no production for it, and `Func_ok` (`6-typing:592`) rules it
out of local types with `(if t =/= BOT)*`. `Silmaril.Wasm.V2.ValType` therefore
omits it and `CValType` adds it back, exactly as the Core 3.0 layer splits
`ValType` from `Silmaril.Wasm.Validation.CValType` (whose `botv` constructor is
the same idea). 2.0 has no heap types and no recursive types, so `CValType` is a
two-constructor wrapper rather than a type former.

## Namespaces

The declarations that are *about validation* (`CValType`, `CResultType` and
their subtyping) live in `Silmaril.Wasm.V2.Validation`. The judgments that are
predicates on the plain 2.0 syntax types — `Limits.Ok`, `FuncType.Ok`,
`TableType.Sub`, … — are declared in `Silmaril.Wasm.V2` so that dot notation
(`lim.Ok k`, `tt.Sub tt'`) works on them, following
`Silmaril/Wasm/Validation/Types.lean`, which puts `Limits.Valid` in
`Silmaril.Wasm` for the same reason.

## Points of care

* `Limits_ok` (`6-typing:27`) has **two** premises, `n <= k` and
  `(if n <= m <= k)?`. The second is an *iterated* premise over the optional
  maximum: when there is no maximum it is vacuous, and when there is one it
  asserts **both** `n <= m` and `m <= k`. In particular an absent maximum is
  *not* treated as `k`.
* The two bounds differ and neither is `2^32`: `Tabletype_ok` (`6-typing:38`)
  bounds a table by `$(2^32-1)` entries, `Memtype_ok` (`6-typing:42`) bounds a
  memory by `$(2^16)` *pages*.
* `Limits_sub` (`6-typing:95-102`) has two rules. `/max` concludes
  `` `[n_1 .. m_1] <: `[n_2 .. m_2?] `` from `n_1 >= n_2` and the iterated
  premise `(if m_1 <= m_2)?`: the left-hand side must have a maximum, while the
  right-hand maximum is optional and the premise is **vacuous when it is
  absent**, so a bounded limit is a subtype of an unbounded one. `/eps` relates
  two *unbounded* limits. No rule has an unbounded left-hand side and a bounded
  right-hand side, so `` `[0 .. eps] `` is not a subtype of `` `[0 .. 1] ``,
  which is the intended direction (see `Limits.sub_iff`).

No deviation from the pinned SpecTec source is taken in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-! ## Validation value types -/

namespace Validation

/-- The validation value type: `valtype ::= numtype | vectype | reftype | BOT`
(`1-syntax:138`), with `BOT` separated out as `CValType.bot`. The syntactic part
is `Silmaril.Wasm.V2.ValType`. -/
inductive CValType where
  /-- A syntactic value type. -/
  | val (type : ValType)
  /-- `BOT`, the least value type (`Valtype_sub/bot`, `6-typing:77`). -/
  | bot
  deriving DecidableEq, Repr

instance : Inhabited CValType := ⟨.bot⟩

/-- `resulttype = list(valtype)` (`1-syntax:146`) over the validation value
type. Stacks are written bottom-first, as in SpecTec. -/
abbrev CResultType := List CValType

/-- Lift a syntactic value type into `CValType`. -/
abbrev liftVal (t : ValType) : CValType := .val t

/-- Lifting is a coercion: every syntactic value type is a validation value
type. -/
instance : Coe ValType CValType := ⟨CValType.val⟩

/-- Lift a syntactic result type into `CResultType`. -/
abbrev liftResult (ts : ResultType) : CResultType := ts.map CValType.val

@[simp] theorem liftResult_nil : liftResult [] = [] := rfl

@[simp] theorem liftResult_cons (t : ValType) (ts : ResultType) :
    liftResult (t :: ts) = .val t :: liftResult ts := rfl

@[simp] theorem liftResult_append (ts us : ResultType) :
    liftResult (ts ++ us) = liftResult ts ++ liftResult us := List.map_append ..

@[simp] theorem length_liftResult (ts : ResultType) :
    (liftResult ts).length = ts.length := List.length_map ..

/-! ### Subtyping of value and result types -/

/-- `Valtype_sub` (`6-typing:74-78`): the two rules `/refl` (`|- t <: t`) and
`/bot` (`|- BOT <: t`). -/
inductive CValType.Sub : CValType → CValType → Prop where
  /-- `Valtype_sub/refl` (`6-typing:74`). -/
  | refl (t : CValType) : CValType.Sub t t
  /-- `Valtype_sub/bot` (`6-typing:77`). -/
  | bot (t : CValType) : CValType.Sub .bot t

/-- The two rules of `Valtype_sub` spelled out as a decidable condition. -/
theorem CValType.sub_iff {a b : CValType} : a.Sub b ↔ a = b ∨ a = .bot := by
  constructor
  · intro h
    cases h with
    | refl _ => exact Or.inl rfl
    | bot _ => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .refl _
    · exact .bot _

instance (a b : CValType) : Decidable (a.Sub b) :=
  decidable_of_iff _ CValType.sub_iff.symm

theorem CValType.sub_refl (t : CValType) : t.Sub t := .refl t

theorem CValType.sub_trans {a b c : CValType} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c := by
  rcases CValType.sub_iff.mp h₁ with rfl | rfl
  · exact h₂
  · exact .bot _

theorem CValType.sub_antisymm {a b : CValType} (h₁ : a.Sub b) (h₂ : b.Sub a) : a = b := by
  rcases CValType.sub_iff.mp h₁ with rfl | rfl
  · rfl
  · rcases CValType.sub_iff.mp h₂ with rfl | rfl <;> rfl

/-- Nothing but `t` itself is above a syntactic value type. -/
@[simp] theorem CValType.sub_val_iff {t : ValType} {u : CValType} :
    CValType.Sub (.val t) u ↔ u = .val t := by
  rw [CValType.sub_iff]
  constructor
  · rintro (rfl | h)
    · rfl
    · exact absurd h (by simp)
  · rintro rfl
    exact Or.inl rfl

/-- `BOT` is the least value type. -/
@[simp] theorem CValType.sub_bot_iff {t : CValType} : t.Sub .bot ↔ t = .bot := by
  rw [CValType.sub_iff]
  constructor
  · rintro (rfl | rfl) <;> rfl
  · rintro rfl
    exact Or.inr rfl

/-- `Resulttype_sub` (`6-typing:80`): pointwise `Valtype_sub`, which forces the
two sequences to have the same length. -/
def CResultType.Sub (ts us : CResultType) : Prop := List.Forall₂ CValType.Sub ts us

instance (ts us : CResultType) : Decidable (CResultType.Sub ts us) :=
  inferInstanceAs (Decidable (List.Forall₂ CValType.Sub ts us))

@[simp] theorem CResultType.sub_nil_nil : CResultType.Sub [] [] := List.Forall₂.nil

theorem CResultType.sub_cons {t u : CValType} {ts us : CResultType}
    (h : t.Sub u) (hs : CResultType.Sub ts us) : CResultType.Sub (t :: ts) (u :: us) :=
  List.Forall₂.cons h hs

theorem CResultType.sub_refl : ∀ ts : CResultType, CResultType.Sub ts ts
  | [] => List.Forall₂.nil
  | t :: ts => List.Forall₂.cons (.refl t) (sub_refl ts)

theorem CResultType.sub_trans : ∀ {a b c : CResultType},
    CResultType.Sub a b → CResultType.Sub b c → CResultType.Sub a c
  | _, _, _, .nil, .nil => List.Forall₂.nil
  | _, _, _, .cons h₁ h₂, .cons h₃ h₄ =>
      List.Forall₂.cons (CValType.sub_trans h₁ h₃) (sub_trans h₂ h₄)

/-- Subtyping of result types is compatible with concatenation; this is the
form in which `Instrs_ok/frame` (`6-typing:175`) and `Instrs_ok/sub`
(`6-typing:168`) interact. -/
theorem CResultType.sub_append {a b c d : CResultType}
    (h₁ : CResultType.Sub a b) (h₂ : CResultType.Sub c d) :
    CResultType.Sub (a ++ c) (b ++ d) := List.rel_append h₁ h₂

theorem CResultType.sub_length {a b : CResultType} (h : CResultType.Sub a b) :
    a.length = b.length := List.Forall₂.length_eq h

/-- A lifted result type is a subtype only of itself. -/
theorem CResultType.sub_liftResult_iff {ts : ResultType} {us : CResultType} :
    CResultType.Sub (liftResult ts) us ↔ us = liftResult ts := by
  induction ts generalizing us with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact List.Forall₂.nil
  | cons t ts ih =>
    constructor
    · intro h
      cases h with
      | cons h hs => simp only [CValType.sub_val_iff] at h; subst h; rw [ih.mp hs]; rfl
    · rintro rfl
      exact List.Forall₂.cons (.refl _) (ih.mpr rfl)

end Validation

/-! ## Well-formedness of types

`Limits_ok`, `Functype_ok`, `Globaltype_ok`, `Tabletype_ok`, `Memtype_ok` and
`Externtype_ok` (`6-typing:19-61`). -/

/-- `Limits_ok: |- `[n .. m?] : k` (`6-typing:27`). The premises are `n <= k`
and the iterated `(if n <= m <= k)?`: vacuous when the maximum is absent, and
*both* `n <= m` and `m <= k` when it is present. -/
def Limits.Ok (k : Nat) (lim : Limits) : Prop :=
  lim.min.val ≤ k ∧ match lim.max with
    | none => True
    | some m => lim.min.val ≤ m.val ∧ m.val ≤ k

instance (k : Nat) (lim : Limits) : Decidable (Limits.Ok k lim) := by
  unfold Limits.Ok
  cases lim.max <;> infer_instance

theorem Limits.Ok.min_le {k : Nat} {lim : Limits} (h : Limits.Ok k lim) :
    lim.min.val ≤ k := h.1

theorem Limits.Ok.max_bounds {k : Nat} {lim : Limits} (h : Limits.Ok k lim)
    {m : Fin (2 ^ 32)} (hm : lim.max = some m) : lim.min.val ≤ m.val ∧ m.val ≤ k := by
  have := h.2
  rw [hm] at this
  exact this

/-- `Functype_ok: |- t_1* -> t_2* : OK` (`6-typing:32`). The rule has no
premises: in 2.0 every function type is well formed. -/
def FuncType.Ok (_ft : FuncType) : Prop := True

instance (ft : FuncType) : Decidable (FuncType.Ok ft) := by
  unfold FuncType.Ok; infer_instance

theorem FuncType.ok (ft : FuncType) : FuncType.Ok ft := trivial

/-- `Globaltype_ok: |- MUT? t : OK` (`6-typing:35`). No premises. -/
def GlobalType.Ok (_gt : GlobalType) : Prop := True

instance (gt : GlobalType) : Decidable (GlobalType.Ok gt) := by
  unfold GlobalType.Ok; infer_instance

theorem GlobalType.ok (gt : GlobalType) : GlobalType.Ok gt := trivial

/-- `Tabletype_ok: |- limits reftype : OK` (`6-typing:38`), whose premise is
`Limits_ok: |- limits : $(2^32-1)`. Note the bound is `2^32-1`, one less than
the size of the index space. -/
def TableType.Ok (tt : TableType) : Prop := Limits.Ok (2 ^ 32 - 1) tt.limits

instance (tt : TableType) : Decidable (TableType.Ok tt) :=
  inferInstanceAs (Decidable (Limits.Ok (2 ^ 32 - 1) tt.limits))

/-- `Memtype_ok: |- limits PAGE : OK` (`6-typing:42`), whose premise is
`Limits_ok: |- limits : $(2^16)`. The bound counts *pages*, and unlike the table
bound it is not decremented. -/
def MemoryType.Ok (mt : MemoryType) : Prop := Limits.Ok (2 ^ 16) mt.limits

instance (mt : MemoryType) : Decidable (MemoryType.Ok mt) :=
  inferInstanceAs (Decidable (Limits.Ok (2 ^ 16) mt.limits))

/-- `Externtype_ok` (`6-typing:47-61`): the four rules `/func`, `/global`,
`/table`, `/mem`. -/
def ExternType.Ok : ExternType → Prop
  | .func ft => FuncType.Ok ft
  | .global gt => GlobalType.Ok gt
  | .table tt => TableType.Ok tt
  | .memory mt => MemoryType.Ok mt

instance (xt : ExternType) : Decidable (ExternType.Ok xt) := by
  cases xt <;> simp only [ExternType.Ok] <;> infer_instance

/-! ## Subtyping of external types

`Limits_sub`, `Functype_sub`, `Globaltype_sub`, `Tabletype_sub`, `Memtype_sub`
and `Externtype_sub` (`6-typing:87-134`). -/

/-- `Limits_sub` (`6-typing:95-102`), both rules.

* `/max` (`6-typing:95`): `` `[n_1 .. m_1] <: `[n_2 .. m_2?] `` with `n_1 >= n_2`
  and the iterated premise `(if m_1 <= m_2)?`. The *left* maximum is mandatory;
  the *right* one is optional, and when it is absent the premise is vacuous.
* `/eps` (`6-typing:100`): `` `[n_1 .. eps] <: `[n_2 .. eps] `` with
  `n_1 >= n_2`. -/
inductive Limits.Sub : Limits → Limits → Prop where
  /-- `Limits_sub/max` (`6-typing:95`). -/
  | max {n₁ m₁ n₂ : Fin (2 ^ 32)} {m₂ : Option (Fin (2 ^ 32))}
      (hmin : n₂.val ≤ n₁.val) (hmax : ∀ m ∈ m₂, m₁.val ≤ m.val) :
      Limits.Sub ⟨n₁, some m₁⟩ ⟨n₂, m₂⟩
  /-- `Limits_sub/eps` (`6-typing:100`). -/
  | eps {n₁ n₂ : Fin (2 ^ 32)} (hmin : n₂.val ≤ n₁.val) :
      Limits.Sub ⟨n₁, none⟩ ⟨n₂, none⟩

/-- The decision procedure behind `Limits.Sub`. -/
def Limits.subCheck (a b : Limits) : Bool :=
  decide (b.min.val ≤ a.min.val) &&
    match b.max with
      | none => true
      | some m₂ => match a.max with
        | none => false
        | some m₁ => decide (m₁.val ≤ m₂.val)

theorem Limits.subCheck_eq_true {a b : Limits} : a.subCheck b = true ↔ a.Sub b := by
  obtain ⟨n₁, m₁⟩ := a
  obtain ⟨n₂, m₂⟩ := b
  cases m₁ <;> cases m₂ <;> simp only [subCheck, Bool.and_eq_true, decide_eq_true_eq] <;>
    constructor
  · rintro ⟨h, -⟩; exact .eps h
  · intro h; cases h with | eps h => exact ⟨h, trivial⟩
  · rintro ⟨-, h⟩; exact absurd h (by simp)
  · intro h; cases h
  · rintro ⟨h, -⟩; exact .max h (by simp)
  · intro h; cases h with | max h _ => exact ⟨h, trivial⟩
  · rintro ⟨h, h'⟩; exact .max h (by simpa using h')
  · intro h
    cases h with
    | max h hm => exact ⟨h, by simpa using hm _ rfl⟩

instance (a b : Limits) : Decidable (a.Sub b) :=
  decidable_of_iff _ Limits.subCheck_eq_true

/-- The content of `Limits_sub`: the minimum may grow, and a maximum may only
appear or shrink. -/
theorem Limits.sub_iff {a b : Limits} :
    a.Sub b ↔ b.min.val ≤ a.min.val ∧ ∀ m₂ ∈ b.max, ∃ m₁ ∈ a.max, m₁.val ≤ m₂.val := by
  rw [← Limits.subCheck_eq_true]
  obtain ⟨n₁, m₁⟩ := a
  obtain ⟨n₂, m₂⟩ := b
  cases m₁ <;> cases m₂ <;> simp [subCheck]

theorem Limits.sub_refl (lim : Limits) : lim.Sub lim := by
  obtain ⟨n, m⟩ := lim
  cases m with
  | none => exact .eps (Nat.le_refl _)
  | some m => exact .max (Nat.le_refl _) (by simp)

theorem Limits.sub_trans {a b c : Limits} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c := by
  cases h₁ with
  | max hmin hmax =>
    cases h₂ with
    | max hmin' hmax' =>
      exact .max (Nat.le_trans hmin' hmin) fun m hm =>
        Nat.le_trans (hmax _ rfl) (hmax' m hm)
    | eps hmin' => exact .max (Nat.le_trans hmin' hmin) (by simp)
  | eps hmin =>
    cases h₂ with
    | eps hmin' => exact .eps (Nat.le_trans hmin' hmin)

/-- `Functype_sub: |- ft <: ft` (`6-typing:105`): 2.0 function types are
related only to themselves. -/
def FuncType.Sub (a b : FuncType) : Prop := a = b

instance (a b : FuncType) : Decidable (FuncType.Sub a b) :=
  inferInstanceAs (Decidable (a = b))

/-- `Globaltype_sub: |- gt <: gt` (`6-typing:108`). -/
def GlobalType.Sub (a b : GlobalType) : Prop := a = b

instance (a b : GlobalType) : Decidable (GlobalType.Sub a b) :=
  inferInstanceAs (Decidable (a = b))

/-- `Tabletype_sub: |- lim_1 rt <: lim_2 rt` (`6-typing:111`): the element type
is shared syntactically, so it must be equal. -/
def TableType.Sub (a b : TableType) : Prop := a.limits.Sub b.limits ∧ a.element = b.element

instance (a b : TableType) : Decidable (TableType.Sub a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Memtype_sub: |- lim_1 PAGE <: lim_2 PAGE` (`6-typing:115`). -/
def MemoryType.Sub (a b : MemoryType) : Prop := a.limits.Sub b.limits

instance (a b : MemoryType) : Decidable (MemoryType.Sub a b) :=
  inferInstanceAs (Decidable (a.limits.Sub b.limits))

/-- `Externtype_sub` (`6-typing:120-134`): the four rules `/func`, `/global`,
`/table`, `/mem`. Different external-type shapes are never related. -/
inductive ExternType.Sub : ExternType → ExternType → Prop where
  /-- `Externtype_sub/func` (`6-typing:120`). -/
  | func {a b : FuncType} (h : FuncType.Sub a b) : ExternType.Sub (.func a) (.func b)
  /-- `Externtype_sub/global` (`6-typing:124`). -/
  | global {a b : GlobalType} (h : GlobalType.Sub a b) : ExternType.Sub (.global a) (.global b)
  /-- `Externtype_sub/table` (`6-typing:128`). -/
  | table {a b : TableType} (h : TableType.Sub a b) : ExternType.Sub (.table a) (.table b)
  /-- `Externtype_sub/mem` (`6-typing:132`). -/
  | memory {a b : MemoryType} (h : MemoryType.Sub a b) : ExternType.Sub (.memory a) (.memory b)

/-- The decision procedure behind `ExternType.Sub`; this is the test an embedder
performs when matching a supplied import against a declared one. -/
def ExternType.subCheck : ExternType → ExternType → Bool
  | .func a, .func b => a == b
  | .global a, .global b => a == b
  | .table a, .table b => a.limits.subCheck b.limits && a.element == b.element
  | .memory a, .memory b => a.limits.subCheck b.limits
  | _, _ => false

theorem ExternType.subCheck_eq_true {a b : ExternType} : a.subCheck b = true ↔ a.Sub b := by
  cases a <;> cases b <;>
    simp only [subCheck, Bool.and_eq_true, beq_iff_eq, Limits.subCheck_eq_true,
      Bool.false_eq_true, false_iff] <;>
    first
      | (intro h; cases h)
      | (constructor
         · intro h; exact .func h
         · intro h; cases h with | func h => exact h)
      | (constructor
         · intro h; exact .global h
         · intro h; cases h with | global h => exact h)
      | (constructor
         · intro h; exact .table h
         · intro h; cases h with | table h => exact h)
      | (constructor
         · intro h; exact .memory h
         · intro h; cases h with | memory h => exact h)

instance (a b : ExternType) : Decidable (ExternType.Sub a b) :=
  decidable_of_iff _ ExternType.subCheck_eq_true

theorem ExternType.sub_refl (xt : ExternType) : xt.Sub xt := by
  cases xt with
  | func a => exact .func rfl
  | global a => exact .global rfl
  | table a => exact .table ⟨Limits.sub_refl _, rfl⟩
  | memory a => exact .memory (Limits.sub_refl _)

theorem ExternType.sub_trans {a b c : ExternType} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c := by
  cases h₁ with
  | func h => cases h₂ with | func h' => exact .func (Eq.trans h h')
  | global h => cases h₂ with | global h' => exact .global (Eq.trans h h')
  | table h => cases h₂ with
    | table h' => exact .table ⟨Limits.sub_trans h.1 h'.1, Eq.trans h.2 h'.2⟩
  | memory h => cases h₂ with | memory h' => exact .memory (Limits.sub_trans h h')

end Silmaril.Wasm.V2
