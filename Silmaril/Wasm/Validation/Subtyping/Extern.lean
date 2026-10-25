module

public import Silmaril.Wasm.Validation.Subtyping

@[expose] public section

/-! # Subtyping of external types (§2.2, "External types")

`Limits_sub`, `Tagtype_sub`, `Globaltype_sub`, `Memtype_sub`, `Tabletype_sub`,
`Externtype_sub`, one constructor per spec rule. These are not recursive in
themselves; they use `Sub` from `Validation/Subtyping.lean`. Import matching at
instantiation (`Externaddr_ok/sub`, §4.1) and the component-model `ExternSub` are
both `ExternSub {}` on closed extern types.
-/

namespace Silmaril.Wasm.Validation

/-- `Limits_sub`. -/
inductive LimitsSub : Limits → Limits → Prop where
  /-- `Limits_sub/max`: `[n_1 .. m_1] <: [n_2 .. m_2?]`. -/
  | max {n₁ m₁ n₂ : Fin (2 ^ 64)} {m₂ : Option (Fin (2 ^ 64))}
      (hn : n₂.val ≤ n₁.val) (hm : ∀ m, m₂ = some m → m₁.val ≤ m.val) :
      LimitsSub ⟨n₁, some m₁⟩ ⟨n₂, m₂⟩
  /-- `Limits_sub/eps`: `[n_1 .. eps] <: [n_2 .. eps]`. -/
  | eps {n₁ n₂ : Fin (2 ^ 64)} (hn : n₂.val ≤ n₁.val) : LimitsSub ⟨n₁, none⟩ ⟨n₂, none⟩

/-- `Tagtype_sub`: mutual subtyping of the defined types. -/
def TagSub (Δ : TypeCtx) (d₁ d₂ : DefType) : Prop := Sub Δ d₁ d₂ ∧ Sub Δ d₂ d₁

/-- `Globaltype_sub`. -/
inductive GlobalSub (Δ : TypeCtx) : CGlobalType → CGlobalType → Prop where
  /-- `Globaltype_sub/const`. -/
  | const {t₁ t₂ : CValType} (h : Sub Δ t₁ t₂) : GlobalSub Δ ⟨.const, t₁⟩ ⟨.const, t₂⟩
  /-- `Globaltype_sub/var`. -/
  | var {t₁ t₂ : CValType} (h₁ : Sub Δ t₁ t₂) (h₂ : Sub Δ t₂ t₁) :
      GlobalSub Δ ⟨.var, t₁⟩ ⟨.var, t₂⟩

/-- `Memtype_sub`. -/
inductive MemSub : MemoryType → MemoryType → Prop where
  | mk {a : AddrType} {l₁ l₂ : Limits} (h : LimitsSub l₁ l₂) : MemSub ⟨a, l₁⟩ ⟨a, l₂⟩

/-- `Tabletype_sub`. -/
inductive TableSub (Δ : TypeCtx) : CTableType → CTableType → Prop where
  | mk {a : AddrType} {l₁ l₂ : Limits} {r₁ r₂ : CRefType}
      (hl : LimitsSub l₁ l₂) (h₁ : Sub Δ r₁ r₂) (h₂ : Sub Δ r₂ r₁) :
      TableSub Δ ⟨a, l₁, r₁⟩ ⟨a, l₂, r₂⟩

/-- `Externtype_sub`. -/
inductive ExternSub (Δ : TypeCtx) : CExternType → CExternType → Prop where
  | tag {d₁ d₂ : DefType} (h : TagSub Δ d₁ d₂) : ExternSub Δ (.tag d₁) (.tag d₂)
  | global {g₁ g₂ : CGlobalType} (h : GlobalSub Δ g₁ g₂) : ExternSub Δ (.global g₁) (.global g₂)
  | mem {m₁ m₂ : MemoryType} (h : MemSub m₁ m₂) : ExternSub Δ (.mem m₁) (.mem m₂)
  | table {t₁ t₂ : CTableType} (h : TableSub Δ t₁ t₂) : ExternSub Δ (.table t₁) (.table t₂)
  | func {d₁ d₂ : DefType} (h : Sub Δ d₁ d₂) : ExternSub Δ (.func d₁) (.func d₂)

instance (l₁ l₂ : Limits) : Decidable (LimitsSub l₁ l₂) := by
  rcases l₁ with ⟨n₁, _ | m₁⟩ <;> rcases l₂ with ⟨n₂, _ | m₂⟩
  · exact decidable_of_iff (n₂.val ≤ n₁.val)
      ⟨fun h => .eps h, fun h => by cases h; assumption⟩
  · exact isFalse (fun h => by cases h)
  · exact decidable_of_iff (n₂.val ≤ n₁.val)
      ⟨fun h => .max h (by simp), fun h => by cases h; assumption⟩
  · exact decidable_of_iff (n₂.val ≤ n₁.val ∧ m₁.val ≤ m₂.val)
      ⟨fun h => .max h.1 (by simpa using h.2),
       fun h => by cases h with | max hn hm => exact ⟨hn, hm _ rfl⟩⟩

end Silmaril.Wasm.Validation
