module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.StoreAgree.Eval
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Type

/-!
# Typing grows when uninhabitable cases are repaired (unrefined)

`e₁` and `e₂` are environments the evaluator cannot tell apart (`EnvSame`). Their type tables
agree except that some variant types `x` of `e₁`, of the form `[] [] (variantT cs)`, become
`variantT (cs.map g)` in `e₂`, where `g` keeps every case's operator and changes only cases that
no payload inhabits in `e₁` from the empty scope (`TypRepair`). Then every member of the typing
block that answers `true` in `e₁` answers `true` in `e₂`, at the same fuel (`sameTypAt`), and so
`HasTyp e₁ ρ t v → HasTyp e₂ ρ t v` (`hasTyp_repair`).

The proof follows `Sem.monoTypAt_succ` (`Raw/…/SpecTec/Sem/Type.lean`) with the order "`ok true`
implies `ok true`" in place of `Res.Le`, and three extra members (`gcase`, `gdef`, `ginsts`) for
the repaired types: the repaired types are read from the scope `matchArgs` builds for an instance
without parameters, which is empty. Kept unrefined, like its model. The use is the 2.0 `STORE`
erratum, where `g` is `StoreFix.fixCase`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res

/-- The operator of a case. -/
def caseOp : TypCase → MixopS
  | .mk op _ _ _ => op

/-- A case that no payload inhabits in `env` from the empty scope, at any fuel. -/
def DeadCase (env : Env) (c : TypCase) : Prop :=
  ∀ n w, hasTypCase n env VarEnv.empty [c] (caseOp c) w ≠ .ok true

/-- **The type tables of `e₂` repair those of `e₁` by `g`.** -/
structure TypRepair (e₁ e₂ : Env) (g : TypCase → TypCase) : Prop where
  op : ∀ c, caseOp (g c) = caseOp c
  find : ∀ x td, e₁.findTyp? x = some td → e₂.findTyp? x = some td ∨
    ∃ cs, td = ([], [.instD [] [] (.variantT cs)]) ∧
      e₂.findTyp? x = some ([], [.instD [] [] (.variantT (cs.map g))]) ∧
      ∀ c ∈ cs, g c = c ∨ DeadCase e₁ c

/-- `ok true` in `e₁` gives `ok true` in `e₂`. -/
def TLe (r₁ r₂ : Res Bool) : Prop := r₁ = .ok true → r₂ = .ok true

/-- **Typing at fuel `n`**: the seven members, and the three repaired readings. -/
structure SameTypAt (e₁ e₂ : Env) (g : TypCase → TypCase) (n : Nat) : Prop where
  typ : ∀ ρ t v, TLe (hasTyp n e₁ ρ t v) (hasTyp n e₂ ρ t v)
  tup : ∀ ρ bs vs, TLe (hasTypTup n e₁ ρ bs vs) (hasTypTup n e₂ ρ bs vs)
  list : ∀ ρ t vs, TLe (hasTypList n e₁ ρ t vs) (hasTypList n e₂ ρ t vs)
  defTyp : ∀ ρ dt v, TLe (hasTypDef n e₁ ρ dt v) (hasTypDef n e₂ ρ dt v)
  fields : ∀ ρ fs gs, TLe (hasTypFields n e₁ ρ fs gs) (hasTypFields n e₂ ρ fs gs)
  case : ∀ ρ cs op w, TLe (hasTypCase n e₁ ρ cs op w) (hasTypCase n e₂ ρ cs op w)
  insts : ∀ is ws v, TLe (hasTypInsts n e₁ is ws v) (hasTypInsts n e₂ is ws v)
  gcase : ∀ cs op w, (∀ c ∈ cs, g c = c ∨ DeadCase e₁ c) →
    TLe (hasTypCase n e₁ VarEnv.empty cs op w) (hasTypCase n e₂ VarEnv.empty (cs.map g) op w)
  gdef : ∀ cs v, (∀ c ∈ cs, g c = c ∨ DeadCase e₁ c) →
    TLe (hasTypDef n e₁ VarEnv.empty (.variantT cs) v)
      (hasTypDef n e₂ VarEnv.empty (.variantT (cs.map g)) v)
  ginsts : ∀ cs ws v, (∀ c ∈ cs, g c = c ∨ DeadCase e₁ c) →
    TLe (hasTypInsts n e₁ [.instD [] [] (.variantT cs)] ws v)
      (hasTypInsts n e₂ [.instD [] [] (.variantT (cs.map g))] ws v)

theorem sameTypAt_zero (e₁ e₂ : Env) (g : TypCase → TypCase) : SameTypAt e₁ e₂ g 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros; intro h; simp [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase,
      hasTypInsts] at h)

/-- `do let b ← r; if b then x else false`, read through `TLe`. -/
theorem tle_bindIf {r₁ r₂ x₁ x₂ : Res Bool} (hr : TLe r₁ r₂) (hx : TLe x₁ x₂) :
    TLe (do let b ← r₁; if b then x₁ else .ok false) (do let b ← r₂; if b then x₂ else .ok false) := by
  intro h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨b, hb, h⟩ := h
  cases b
  · simp at h
  · rw [hr hb]
    exact hx h

/-- `bindQuants` succeeds alike when its type oracle only grows. -/
theorem bindQuants_tle {ev : VarEnv → Exp → Res Value}
    {ty₁ ty₂ : VarEnv → Typ → Value → Res Bool} (hty : ∀ ρ t v, TLe (ty₁ ρ t v) (ty₂ ρ t v)) :
    ∀ ρ ds ρq, bindQuants ev ty₁ ρ ds = .ok (some ρq) → bindQuants ev ty₂ ρ ds = .ok (some ρq)
  | _, [], _, h => h
  | ρ, (x, t, e) :: ds, ρq, h => by
      simp only [bindQuants, Res.bind_eq_ok] at h ⊢
      obtain ⟨v, hv, b, hb, h⟩ := h
      cases b
      · simp at h
      · exact ⟨v, hv, true, hty _ _ _ hb, bindQuants_tle hty _ _ _ h⟩

/-- `matchArgs` against no patterns answers only with the scope it was given. -/
theorem matchArgs_nil_ok {n : Nat} {env : Env} {ρ ρ' : VarEnv} {ws : List ArgV}
    (h : matchArgs n env ρ [] ws = .ok ρ') : ρ' = ρ ∧ ws = [] := by
  cases n with
  | zero => simp [matchArgs] at h
  | succ n =>
    cases ws with
    | nil => simp only [matchArgs, Except.ok.injEq] at h; exact ⟨h.symm, rfl⟩
    | cons w ws => simp [matchArgs] at h

/-- `matchArgs` against no patterns is never out of fuel past fuel `0`, and otherwise `undef`. -/
theorem hasTypInsts_nil_ne {n : Nat} {env : Env} {ws : List ArgV} {v : Value} :
    hasTypInsts n env [] ws v ≠ .ok true := by
  cases n <;> simp [hasTypInsts]

/-- The hit branch of `hasTypCase`. -/
theorem caseHit_tle {e₁ e₂ : Env} {g : TypCase → TypCase} (hS : EnvSame e₁ e₂) {m : Nat} (ih : SameTypAt e₁ e₂ g m)
    (ρ : VarEnv) (t : Typ) (qs : List Param) (prems : List Prem) (w : Value) :
    TLe (do
          let b ← hasTyp m e₁ ρ t w
          if b then
            Res.elimUndef
              (bindQuants (fun ρ e => evalExp m e₁ ρ e) (fun ρ t v => hasTyp m e₁ ρ t v)
                (caseScope ρ t w) (quantDefs qs prems))
              (fun o => match o with
                | some ρq => premsOk m e₁ ρq prems
                | none => .ok false)
              (fun _ => .ok false)
          else .ok false)
      (do
          let b ← hasTyp m e₂ ρ t w
          if b then
            Res.elimUndef
              (bindQuants (fun ρ e => evalExp m e₂ ρ e) (fun ρ t v => hasTyp m e₂ ρ t v)
                (caseScope ρ t w) (quantDefs qs prems))
              (fun o => match o with
                | some ρq => premsOk m e₂ ρq prems
                | none => .ok false)
              (fun _ => .ok false)
          else .ok false) := by
  refine tle_bindIf (ih.typ _ _ _) ?_
  intro h
  have hpo : ∀ ρq, premsOk m e₂ ρq prems = premsOk m e₁ ρq prems := by
    intro ρq; simp only [premsOk, premsHold_eq hS]
  simp only [evalExp_eq hS, hpo]
  cases hq : bindQuants (fun ρ e => evalExp m e₁ ρ e) (fun ρ t v => hasTyp m e₁ ρ t v)
    (caseScope ρ t w) (quantDefs qs prems) with
  | error err =>
    rw [hq] at h
    cases err <;> simp [Res.elimUndef] at h
  | ok o =>
    rw [hq] at h
    cases o with
    | none => simp at h
    | some ρq =>
      rw [bindQuants_tle (fun ρ t v => ih.typ ρ t v) _ _ _ hq]
      exact h

theorem sameTypAt_succ {e₁ e₂ : Env} {g : TypCase → TypCase} (hS : EnvSame e₁ e₂)
    (hT : TypRepair e₁ e₂ g) (m : Nat) (ih : SameTypAt e₁ e₂ g m) : SameTypAt e₁ e₂ g (m + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v h
    cases t with
    | boolT => simpa only [hasTyp] using h
    | numT t => simpa only [hasTyp] using h
    | textT => simpa only [hasTyp] using h
    | tupT bs =>
      simp only [hasTyp] at h ⊢
      cases hv : v.asTuple? with
      | none => rw [hv] at h; exact h
      | some vs => rw [hv] at h; exact ih.tup _ _ _ h
    | iterT t it =>
      cases it with
      | opt =>
        simp only [hasTyp] at h ⊢
        cases hv : v.asOpt? with
        | none => rw [hv] at h; exact h
        | some o =>
          rw [hv] at h
          cases o with
          | none => exact h
          | some w => exact ih.typ _ _ _ h
      | list =>
        simp only [hasTyp] at h ⊢
        cases hv : v.asList? with
        | none => rw [hv] at h; exact h
        | some vs => rw [hv] at h; exact ih.list _ _ _ h
      | list1 =>
        simp only [hasTyp] at h ⊢
        cases hv : v.asList? with
        | none => rw [hv] at h; exact h
        | some vs =>
          rw [hv] at h
          cases he : vs.isEmpty
          · simp only [he, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact ih.list _ _ _ h
          · simp [he] at h
      | listN e x =>
        simp only [hasTyp] at h ⊢
        cases hv : v.asList? with
        | none => rw [hv] at h; exact h
        | some vs =>
          rw [hv] at h
          rw [evalExp_eq hS]
          simp only [Res.bind_eq_ok] at h ⊢
          obtain ⟨kv, hkv, k, hk, h⟩ := h
          refine ⟨kv, hkv, k, hk, ?_⟩
          split at h
          · rw [ite_eq_left (by assumption)]; exact ih.list _ _ _ h
          · simp at h
    | varT x args =>
      simp only [hasTyp] at h ⊢
      cases hl : localTyp? ρ x args with
      | some t => rw [hl] at h; exact ih.typ _ _ _ h
      | none =>
        rw [hl] at h
        rw [evalArgs_eq hS]
        simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h ⊢
        obtain ⟨td, htd, ws, hws, h⟩ := h
        rcases hT.find x td htd with h₂ | ⟨cs, rfl, h₂, hg⟩
        · exact ⟨td, h₂, ws, hws, ih.insts _ _ _ h⟩
        · exact ⟨_, h₂, ws, hws, ih.ginsts _ _ _ hg h⟩
  -- `hasTypTup`
  · intro ρ bs vs h
    cases bs with
    | nil => cases vs <;> simp [hasTypTup] at h ⊢
    | cons b bs =>
      cases b with
      | mk x t =>
        cases vs with
        | nil => simp [hasTypTup] at h
        | cons v vs =>
          simp only [hasTypTup] at h ⊢
          exact tle_bindIf (ih.typ _ _ _) (ih.tup _ _ _) h
  -- `hasTypList`
  · intro ρ t vs h
    cases vs with
    | nil => simp only [hasTypList]
    | cons v vs =>
      simp only [hasTypList] at h ⊢
      exact tle_bindIf (ih.typ _ _ _) (ih.list _ _ _) h
  -- `hasTypDef`
  · intro ρ dt v h
    cases dt with
    | aliasT t => simp only [hasTypDef] at h ⊢; exact ih.typ _ _ _ h
    | structT fs =>
      simp only [hasTypDef] at h ⊢
      cases hv : v.asStruct? with
      | none => rw [hv] at h; exact h
      | some gs => rw [hv] at h; exact ih.fields _ _ _ h
    | variantT cs =>
      simp only [hasTypDef] at h ⊢
      cases hv : v.asCase? with
      | none => rw [hv] at h; exact h
      | some p => rw [hv] at h; exact ih.case _ _ _ _ h
  -- `hasTypFields`
  · intro ρ fs gs h
    cases fs with
    | nil => cases gs <;> simp [hasTypFields] at h ⊢
    | cons f fs =>
      cases f with
      | mk a t qs prems =>
        cases gs with
        | nil => simp [hasTypFields] at h
        | cons g' gs =>
          obtain ⟨a', w⟩ := g'
          simp only [hasTypFields] at h ⊢
          split at h
          · rw [ite_eq_left (by assumption)]
            refine tle_bindIf (ih.typ _ _ _) ?_ h
            have hpo : premsOk m e₂ (caseScope ρ t w) prems = premsOk m e₁ (caseScope ρ t w) prems := by
              simp only [premsOk, premsHold_eq hS]
            rw [hpo]
            exact tle_bindIf (fun h => h) (ih.fields _ _ _)
          · simp at h
  -- `hasTypCase`
  · intro ρ cs op w h
    cases cs with
    | nil => simpa only [hasTypCase] using h
    | cons c cs =>
      cases c with
      | mk op' t qs prems =>
        simp only [hasTypCase] at h ⊢
        split at h
        · rw [ite_eq_left (by assumption)]
          exact caseHit_tle hS ih ρ t qs prems w h
        · rw [ite_eq_right (by assumption)]
          exact ih.case _ _ _ _ h
  -- `insts`
  · intro is ws v h
    cases is with
    | nil => simpa only [hasTypInsts] using h
    | cons i is =>
      cases i with
      | instD qs pats dt =>
        simp only [hasTypInsts] at h ⊢
        rw [matchArgs_eq hS]
        cases hm : matchArgs m e₁ VarEnv.empty pats ws with
        | error err =>
          rw [hm] at h
          cases err
          · exact ih.insts _ _ _ h
          · simp [Res.elimUndef] at h
        | ok ρ' => rw [hm] at h; exact ih.defTyp _ _ _ h
  -- `gcase`
  · intro cs op w hg h
    cases cs with
    | nil => simpa only [hasTypCase, List.map_nil] using h
    | cons c cs =>
      have hg' : ∀ c ∈ cs, g c = c ∨ DeadCase e₁ c := fun c hc => hg c (List.mem_cons_of_mem _ hc)
      rw [List.map_cons]
      rcases hg c List.mem_cons_self with hc | hd
      · rw [hc]
        cases c with
        | mk op' t qs prems =>
          simp only [hasTypCase] at h ⊢
          split at h
          · rw [ite_eq_left (by assumption)]
            exact caseHit_tle hS ih _ t qs prems w h
          · rw [ite_eq_right (by assumption)]
            exact ih.gcase _ _ _ hg' h
      · have hop := hT.op c
        cases c with
        | mk op' t qs prems =>
          by_cases ho : op' = op
          · subst ho
            exfalso
            refine hd (m + 1) w ?_
            simp only [hasTypCase, caseOp, ↓reduceIte] at h ⊢
            exact h
          · have h₁ : hasTypCase m e₁ VarEnv.empty cs op w = .ok true := by
              simpa only [hasTypCase, ho, ↓reduceIte] using h
            generalize g (.mk op' t qs prems) = c' at hop ⊢
            obtain ⟨op'', t', qs', prems'⟩ := c'
            simp only [caseOp] at hop
            subst hop
            simp only [hasTypCase, ho, ↓reduceIte]
            exact ih.gcase _ _ _ hg' h₁
  -- `gdef`
  · intro cs v hg h
    simp only [hasTypDef] at h ⊢
    cases hv : v.asCase? with
    | none => rw [hv] at h; exact h
    | some p => rw [hv] at h; exact ih.gcase _ _ _ hg h
  -- `ginsts`
  · intro cs ws v hg h
    simp only [hasTypInsts] at h ⊢
    rw [matchArgs_eq hS]
    cases hm : matchArgs m e₁ VarEnv.empty [] ws with
    | error err =>
      rw [hm] at h
      cases err
      · exact absurd h hasTypInsts_nil_ne
      · simp [Res.elimUndef] at h
    | ok ρ' =>
      rw [hm] at h
      obtain ⟨rfl, -⟩ := matchArgs_nil_ok hm
      exact ih.gdef _ _ hg h
/-- **Typing grows**, at every fuel. -/
theorem sameTypAt {e₁ e₂ : Env} {g : TypCase → TypCase} (hS : EnvSame e₁ e₂)
    (hT : TypRepair e₁ e₂ g) : ∀ n, SameTypAt e₁ e₂ g n
  | 0 => sameTypAt_zero e₁ e₂ g
  | n + 1 => sameTypAt_succ hS hT n (sameTypAt hS hT n)

/-- **`HasTyp` grows.** -/
theorem hasTyp_repair {e₁ e₂ : Env} {g : TypCase → TypCase} (hS : EnvSame e₁ e₂)
    (hT : TypRepair e₁ e₂ g) {ρ : VarEnv} {t : Typ} {v : Value} (h : HasTyp e₁ ρ t v) :
    HasTyp e₂ ρ t v :=
  let ⟨n, hn⟩ := h
  ⟨n, (sameTypAt hS hT n).typ ρ t v hn⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
