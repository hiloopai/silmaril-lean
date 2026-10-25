module

public import Silmaril.Wasm.Validation.Check.AtomicA

@[expose] public section

/-! # Completeness of the stack-directed checkers in `Check/AtomicA`

Instruction-level typing has no subsumption, so each family relation assigns a fixed
type; completeness is principal-type style: if `i : t₁ →_xs t₂` and the top of the
stack matches `t₁`, the checker accepts, consuming `t₁.length` operands and producing
some `out'` with `out' <: t₂`.

The variable family additionally needs the local and global types of `C` to be valid
(`hloc`, `hglob`): otherwise `Sub.check` cannot be shown complete against them.
-/

namespace Silmaril.Wasm.Validation

/-! ## Generic operand matching -/

theorem checkResultSub_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) :
    {as bs : List CValType} → ResultSub Δ as bs → (∀ t ∈ as, TyOk Δ t) →
      (∀ t ∈ bs, TyOk Δ t) → checkResultSub Δ as bs = true
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, h, ha, hb => by
    cases h with
    | cons h₁ h₂ =>
      simp only [checkResultSub, Bool.and_eq_true]
      exact ⟨Sub.check_complete hΔ hr h₁ (ha a (by simp)) (hb b (by simp)),
        checkResultSub_complete hΔ hr h₂ (fun t ht => ha t (by simp [ht]))
          (fun t ht => hb t (by simp [ht]))⟩
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h

theorem popOk_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {stk t₁ : List CValType} (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub Δ (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk Δ t) (ht₁ : ∀ t ∈ t₁, TyOk Δ t) : popOk Δ stk t₁ = true := by
  simp only [popOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlen, checkResultSub_complete hΔ hr hsub
    (fun t ht => hstk t (List.mem_of_mem_drop ht)) ht₁⟩

theorem finishCheck_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {it : InstrType} (hlen : it.params.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - it.params.length)) it.params)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (ht₁ : ∀ t ∈ it.params, TyOk C.toTypeCtx t) :
    finishCheck C stk it = some (it.params.length, it.inits, it.results) := by
  unfold finishCheck
  rw [ite_eq_left (popOk_complete hC hr hlen hsub hstk ht₁)]

/-- Generic completeness when the type-producing function returns exactly the
derivation's type. -/
theorem bind_finishCheck_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {o : Option InstrType} {t₁ t₂ : List CValType} {xs : List Nat}
    (ho : o = some ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (ht₁ : ∀ t ∈ t₁, TyOk C.toTypeCtx t) :
    ∃ out', o.bind (finishCheck C stk) = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  subst ho
  exact ⟨t₂, finishCheck_complete (it := ⟨t₁, xs, t₂⟩) hC hr hlen hsub hstk ht₁,
    ResultSub.refl _ _⟩

/-! ## Value-type subtyping inversions -/

theorem Sub.val_botv_inv {Δ : TypeCtx} {a : CValType} (h : Sub Δ a .botv) : a = .botv := by
  cases h; rfl

theorem Sub.val_num_inv {Δ : TypeCtx} {a : CValType} {n : NumType} (h : Sub Δ a (.num n)) :
    a = .num n ∨ a = .botv := by
  cases h <;> simp

theorem Sub.val_vec_inv {Δ : TypeCtx} {a : CValType} {v : VecType} (h : Sub Δ a (.vec v)) :
    a = .vec v ∨ a = .botv := by
  cases h <;> simp

/-- A non-bottom subtype of a numeric/vector type is that type. -/
theorem Sub.eq_of_isNumOrVec {Δ : TypeCtx} {a t : CValType} (h : Sub Δ a t)
    (ht : t.IsNumOrVec) (ha : a ≠ .botv) : a = t := by
  cases t with
  | num n => exact (Sub.val_num_inv h).resolve_right ha
  | vec v => exact (Sub.val_vec_inv h).resolve_right ha
  | _ => simp [Ty.IsNumOrVec] at ht

/-! ## Parametric -/

/-- Split off the consumed suffix of the stack as an explicit list. -/
theorem stk_split {stk d : List CValType} {n : Nat} (hd : stk.drop (stk.length - n) = d) :
    stk = stk.take (stk.length - n) ++ d := by
  rw [← hd, List.take_append_drop]

theorem mem_of_drop_eq {stk d : List CValType} {n : Nat} (hd : stk.drop n = d) {t : CValType}
    (ht : t ∈ d) : t ∈ stk := by
  subst hd; exact List.mem_of_mem_drop ht

/-- `unreachable` is excluded (`hnu`): the checker returns `none` for it, since stack
polymorphism is handled by the sequence checker. -/
theorem parametricCheck?_complete {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk' : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (hnu : i ≠ .unreachable)
    (h : ParametricInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (hbot : ∀ t ∈ stk, t ≠ .botv) :
    ∃ out', parametricCheck? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  cases h with
  | nop =>
    exact bind_finishCheck_complete hC hr rfl hlen hsub hstk (by simp)
  | unreachable _ => exact absurd rfl hnu
  | drop ht =>
    rename_i t
    have hsub0 := hsub
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hsub hlen ⊢
    generalize hd : stk.drop (stk.length - 1) = d at hsub
    rcases hsub with _ | ⟨ha, hnil⟩
    rename_i a l
    cases hnil
    have hlast : stk.getLast? = some a := by
      rw [stk_split hd]; simp
    have haok : TyOk C.toTypeCtx a := hstk a (mem_of_drop_eq hd (by simp))
    refine ⟨[], ?_, ResultSub.refl _ _⟩
    unfold parametricCheck? parametricType?
    simp only [hlast, htyOk' haok, ite_true, Option.bind_some]
    have := finishCheck_complete (it := .plain [a] []) hC hr (by simpa using hlen)
      (by simpa [hd] using ResultSub.refl C.toTypeCtx [a]) hstk (by simpa using haok)
    simpa using this
  | selectExpl ht =>
    refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
    · simp [parametricType?, htyOk' ht]
    · intro t ht'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl
      · exact ht
      · exact ht
      · exact .num _
  | selectImpl htok hs hnv =>
    rename_i t t'
    have hsub0 := hsub
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hsub
    generalize hd : stk.drop (stk.length - (1 + 1 + 1)) = d at hsub
    rcases hsub with _ | @⟨a, _, _, _, ha, _ | @⟨b, _, _, _, hb, _ | @⟨c, _, _, _, hc, hnil⟩⟩⟩
    cases hnil
    have ha' : a ≠ .botv := hbot a (mem_of_drop_eq hd (by simp))
    have htb : t ≠ .botv := by
      rintro rfl; exact ha' (Sub.val_botv_inv ha)
    have htt : t = t' := Sub.eq_of_isNumOrVec hs hnv htb
    subst htt
    have hat : a = t := Sub.eq_of_isNumOrVec ha hnv ha'
    subst hat
    have hrev : stk.reverse = c :: b :: a :: (stk.take (stk.length - (1 + 1 + 1))).reverse := by
      conv => lhs; rw [stk_split hd]
      simp
    have hsel : selectImplType? stk = some a := by
      unfold selectImplType?; rw [hrev]; simp [hnv]
    refine bind_finishCheck_complete hC hr ?_ hlen hsub0 hstk ?_
    · simp [parametricType?, hsel]
    · intro t ht'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl
      · exact htok
      · exact htok
      · exact .num _

/-! ## Numeric -/

theorem numericCheck?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : NumericInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (_hbot : ∀ t ∈ stk, t ≠ .botv) :
    ∃ out', numericCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
  · cases h <;> simp_all [numericType?]
  · intro t ht
    apply tyOk_of_isNumOrVec
    cases h <;> simp at ht <;> (try rcases ht with rfl | rfl) <;>
      simp [Ty.IsNumOrVec]

/-! ## Variable -/

/-- Needs the local and global types of `C` to be valid (`hloc`, `hglob`). -/
theorem variableCheck?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (hloc : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type)
    (hglob : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : VariableInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (_hbot : ∀ t ∈ stk, t ≠ .botv) :
    ∃ out', variableCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
  · cases h <;> simp_all [variableType?]
  · intro t ht
    cases h with
    | localGet _ => simp at ht
    | localSet hx =>
      simp at ht; subst ht
      exact hloc _ (List.mem_of_getElem? hx)
    | localTee hx =>
      simp at ht; subst ht
      exact hloc _ (List.mem_of_getElem? hx)
    | globalGet _ => simp at ht
    | globalSet hx =>
      simp at ht; subst ht
      exact hglob _ (List.mem_of_getElem? hx)

/-! ## Vector -/

theorem vectorCheck?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : VectorInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (_hbot : ∀ t ∈ stk, t ≠ .botv) :
    ∃ out', vectorCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
  · cases h <;> simp_all [vectorType?]; omega
  · intro t ht
    apply tyOk_of_isNumOrVec
    cases h <;> simp at ht <;> (try rcases ht with rfl | rfl | rfl) <;>
      simp [Ty.IsNumOrVec, Ty.i32, Ty.v128]

/-! ## Dispatch -/

/-- The four families handled by `atomicA?`, with `unreachable` excluded. -/
inductive AtomicAInstrOk (C : Context) (i : Instr) (it : InstrType) : Prop where
  | param (hnu : i ≠ .unreachable) (h : ParametricInstrOk C i it)
  | num (h : NumericInstrOk C i it)
  | var (h : VariableInstrOk C i it)
  | vec (h : VectorInstrOk C i it)

theorem AtomicAInstrOk.instrOk {C : Context} {i : Instr} {it : InstrType}
    (h : AtomicAInstrOk C i it) : InstrOk C i it := by
  cases h with
  | param _ h => exact .parametric h
  | num h => exact .numeric h
  | var h => exact InstrOk.«variable» h
  | vec h => exact .vector h

theorem atomicA?_complete {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk' : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    (hloc : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type)
    (hglob : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : AtomicAInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) (hbot : ∀ t ∈ stk, t ≠ .botv) :
    ∃ out', atomicA? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  cases h with
  | param hnu h =>
    obtain ⟨out', h1, h2⟩ := parametricCheck?_complete hC hr htyOk' hnu h hlen hsub hstk hbot
    exact ⟨out', by simp [atomicA?, h1], h2⟩
  | num h =>
    obtain ⟨out', h1, h2⟩ := numericCheck?_complete hC hr h hlen hsub hstk hbot
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, h1], h2⟩
  | var h =>
    obtain ⟨out', h1, h2⟩ := variableCheck?_complete hC hr hloc hglob h hlen hsub hstk hbot
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    have hn : numericCheck? C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, hn, h1], h2⟩
  | vec h =>
    obtain ⟨out', h1, h2⟩ := vectorCheck?_complete hC hr h hlen hsub hstk hbot
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    have hn : numericCheck? C stk i = none := by
      cases h <;> rfl
    have hv : variableCheck? C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, hn, hv, h1], h2⟩

end Silmaril.Wasm.Validation
