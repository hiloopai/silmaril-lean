module

public import Silmaril.Wasm.Validation.Check.AtomicABot
public import Silmaril.Wasm.Validation.Check.AtomicBComplete
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Check.InstrsCompleteStep
public import Silmaril.Wasm.Validation.Check.TyOkDerivedComplete

@[expose] public section

/-! # Completeness of the fallthrough oracle `atomC`

`atomC = atomicA? tyOkC <|> atomicB? tyOkC` is complete in the shape of
`StepComplete.AtomComplete`, relative to two hypotheses proved elsewhere:
completeness of `TyOk.check` (`hT`) and BOT-tolerant completeness of `atomicB?`
(`AtomicBBotComplete`).
-/

namespace Silmaril.Wasm.Validation

open Silmaril.Wasm.Validation.StepComplete

/-- The statement of `atomicB?_complete_bot`. -/
def AtomicBBotComplete : Prop :=
  ∀ {tyOk : {k : TKind} → Ty k → Bool} {C : Context}, C.toTypeCtx.Ok → C.recs = [] →
    (∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true) → TablesOk C → ElemsOk C →
    ∀ {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat},
      (TableInstrOk C i ⟨t₁, xs, t₂⟩ ∨ MemoryInstrOk C i ⟨t₁, xs, t₂⟩ ∨
        RefInstrOk C i ⟨t₁, xs, t₂⟩) →
      t₁.length ≤ stk.length →
      ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁ →
      (∀ t ∈ stk, TyOk C.toTypeCtx t) →
      ∃ out', atomicB? tyOk C stk i = some (t₁.length, xs, out') ∧
        ResultSub C.toTypeCtx out' t₂

/-- A non-control instruction typing falls in one of the atomic families. -/
theorem InstrOk.atomic_classify {C : Context} {i : Instr} {it : InstrType}
    (h : InstrOk C i it) (hc : isCtl i = false) :
    AtomicAInstrOk C i it ∨ TableInstrOk C i it ∨ MemoryInstrOk C i it ∨
      RefInstrOk C i it := by
  cases h with
  | parametric h =>
    refine .inl (.param ?_ h)
    rintro rfl; simp [isCtl] at hc
  | numeric h => exact .inl (.num h)
  | vector h => exact .inl (.vec h)
  | «variable» h => exact .inl (.var h)
  | memory h => exact .inr (.inr (.inl h))
  | table h => exact .inr (.inl h)
  | reference h => exact .inr (.inr (.inr h))
  | _ => simp [isCtl] at hc

theorem atomicA?_none_of_B {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    {stk : List CValType} {i : Instr} {it : InstrType}
    (h : TableInstrOk C i it ∨ MemoryInstrOk C i it ∨ RefInstrOk C i it) :
    atomicA? tyOk C stk i = none := by
  rcases h with h | h | h <;> cases h <;> rfl

theorem atomC_complete_elems
    (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ) (hB : AtomicBBotComplete) :
    ∀ (C : Context) (S : List CValType) (i : Instr) (t₁ t₂ : List CValType) (xs : List Nat),
      C.Wf → ElemsOk C → C.recs = [] → isCtl i = false →
      ¬ (i = .select none ∧ ∃ S₀ c, S = S₀ ++ [.botv, .botv, c]) →
      InstrOk C i ⟨t₁, xs, t₂⟩ → ResultOk C.toTypeCtx S → t₁.length ≤ S.length →
      ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁ →
      ∃ out, atomC C S i = some (t₁.length, xs, out) ∧ ResultOk C.toTypeCtx out ∧
        ResultSub C.toTypeCtx out t₂ := by
  intro C S i t₁ t₂ xs hC hE hr hc hexcl h hS hlen hsub
  have hty : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → @tyOkC C.toTypeCtx k t = true :=
    fun ht => hT C.toTypeCtx hC.types hr ht
  -- the checker's result `out'` has `ResultSub out' t₂`; we still need `ResultOk out'`.
  have hfin : ∀ out', atomC C S i = some (t₁.length, xs, out') →
      ResultSub C.toTypeCtx out' t₂ →
      ∃ out, atomC C S i = some (t₁.length, xs, out) ∧ ResultOk C.toTypeCtx out ∧
        ResultSub C.toTypeCtx out t₂ := by
    intro out' ho hs
    obtain ⟨_, t₁', _, hi, _⟩ := atomC_sound C S i _ _ _ ho
    exact ⟨out', ho, (hi.regular hC).2.1, hs⟩
  rcases h.atomic_classify hc with ha | hb
  · obtain ⟨out', h1, h2⟩ := atomicA?_complete_bot (tyOk := @tyOkC C.toTypeCtx) hC.types hr
      hty hC.locals hC.globals ha hlen hsub hS hexcl
    exact hfin out' (by simp [atomC, h1]) h2
  · obtain ⟨out', h1, h2⟩ := hB (tyOk := @tyOkC C.toTypeCtx) hC.types hr hty hC.tables hE
      hb hlen hsub hS
    have h0 : atomicA? (@tyOkC C.toTypeCtx) C S i = none := atomicA?_none_of_B hb
    exact hfin out' (by simp [atomC, h0, h1]) h2

theorem atomC_complete_of
    (hT : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ) (hB : AtomicBBotComplete)
    (hE : ∀ C : Context, C.Wf → ElemsOk C) : AtomComplete atomC :=
  fun C S i t₁ t₂ xs hC hr hc hexcl h hS hlen hsub =>
    atomC_complete_elems hT hB C S i t₁ t₂ xs hC (hE C hC) hr hc hexcl h hS hlen hsub

end Silmaril.Wasm.Validation
