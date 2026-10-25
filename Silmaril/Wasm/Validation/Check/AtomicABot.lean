module

public import Silmaril.Wasm.Validation.Check.AtomicAComplete

@[expose] public section

/-! # Completeness of `atomicA?` on stacks that may contain BOT

The sequence checker produces `.botv` entries in polymorphic mode. `atomicA?_complete`
assumes no BOT on the stack; this file drops that hypothesis. The only case that
genuinely needs care is implicit `select`: with exactly one BOT value operand the
checker picks the other (numeric/vector) one, and `botv <: t`; with both value
operands BOT, `selectImplType?` returns `none`, so that shape is excluded (`hexcl`).
-/

namespace Silmaril.Wasm.Validation

theorem parametricCheck?_complete_bot {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk' : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (hnu : i ≠ .unreachable)
    (h : ParametricInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t)
    (hexcl : ¬ (i = .select none ∧ ∃ S₀ c, stk = S₀ ++ [.botv, .botv, c])) :
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
    have hrev : stk.reverse = c :: b :: a :: (stk.take (stk.length - (1 + 1 + 1))).reverse := by
      conv => lhs; rw [stk_split hd]
      simp
    have hfin : ∀ u, selectImplType? stk = some u → u = t →
        ∃ out', parametricCheck? tyOk C stk (.select none) =
          some (3, [], out') ∧ ResultSub C.toTypeCtx out' [t] := by
      intro u hsel hu
      subst hu
      refine bind_finishCheck_complete hC hr ?_ hlen hsub0 hstk ?_
      · simp [parametricType?, hsel]
      · intro t ht'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
        rcases ht' with rfl | rfl | rfl
        · exact htok
        · exact htok
        · exact .num _
    by_cases ha' : a = .botv
    · subst ha'
      by_cases hb' : b = .botv
      · subst hb'
        exact absurd ⟨rfl, _, c, stk_split hd⟩ hexcl
      · have htb : t ≠ .botv := by
          rintro rfl; exact hb' (Sub.val_botv_inv hb)
        have htt : t = t' := Sub.eq_of_isNumOrVec hs hnv htb
        subst htt
        have hbt : b = t := Sub.eq_of_isNumOrVec hb hnv hb'
        subst hbt
        refine hfin b ?_ rfl
        have hnb : ¬ (Ty.botv : CValType).IsNumOrVec := by simp [Ty.IsNumOrVec]
        unfold selectImplType?; rw [hrev]; simp [hnb, hnv]
    · have htb : t ≠ .botv := by
        rintro rfl; exact ha' (Sub.val_botv_inv ha)
      have htt : t = t' := Sub.eq_of_isNumOrVec hs hnv htb
      subst htt
      have hat : a = t := Sub.eq_of_isNumOrVec ha hnv ha'
      subst hat
      refine hfin a ?_ rfl
      unfold selectImplType?; rw [hrev]; simp [hnv]

theorem numericCheck?_complete_bot {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : NumericInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', numericCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
  · cases h <;> simp_all [numericType?]
  · intro t ht
    apply tyOk_of_isNumOrVec
    cases h <;> simp at ht <;> (try rcases ht with rfl | rfl) <;>
      simp [Ty.IsNumOrVec]

theorem variableCheck?_complete_bot {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (hloc : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type)
    (hglob : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : VariableInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
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

theorem vectorCheck?_complete_bot {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : VectorInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', vectorCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  refine bind_finishCheck_complete hC hr ?_ hlen hsub hstk ?_
  · (cases h <;> simp_all [vectorType?]); omega
  · intro t ht
    apply tyOk_of_isNumOrVec
    cases h <;> simp at ht <;> (try rcases ht with rfl | rfl | rfl) <;>
      simp [Ty.IsNumOrVec, Ty.i32, Ty.v128]

/-- `atomicA?_complete` without the no-BOT hypothesis; implicit `select` whose two value
operands are both BOT is excluded (`hexcl`), as `selectImplType?` returns `none` there. -/
theorem atomicA?_complete_bot {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk' : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    (hloc : ∀ lt ∈ C.locals, TyOk C.toTypeCtx lt.type)
    (hglob : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : AtomicAInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hsub : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t)
    (hexcl : ¬ (i = .select none ∧ ∃ S₀ c, stk = S₀ ++ [.botv, .botv, c])) :
    ∃ out', atomicA? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  cases h with
  | param hnu h =>
    obtain ⟨out', h1, h2⟩ :=
      parametricCheck?_complete_bot hC hr htyOk' hnu h hlen hsub hstk hexcl
    exact ⟨out', by simp [atomicA?, h1], h2⟩
  | num h =>
    obtain ⟨out', h1, h2⟩ := numericCheck?_complete_bot hC hr h hlen hsub hstk
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, h1], h2⟩
  | var h =>
    obtain ⟨out', h1, h2⟩ := variableCheck?_complete_bot hC hr hloc hglob h hlen hsub hstk
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    have hn : numericCheck? C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, hn, h1], h2⟩
  | vec h =>
    obtain ⟨out', h1, h2⟩ := vectorCheck?_complete_bot hC hr h hlen hsub hstk
    have hp : parametricCheck? tyOk C stk i = none := by
      cases h <;> rfl
    have hn : numericCheck? C stk i = none := by
      cases h <;> rfl
    have hv : variableCheck? C stk i = none := by
      cases h <;> rfl
    exact ⟨out', by simp [atomicA?, hp, hn, hv, h1], h2⟩

end Silmaril.Wasm.Validation
