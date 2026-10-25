module

public import Silmaril.Wasm.Validation.Check.AtomicBComplete

@[expose] public section

/-! # Completeness of `atomicB?` on stacks that may contain BOT

The sequence checker produces `.botv` entries in polymorphic mode. `atomicB?_complete`
assumes no BOT on the stack; this file drops that hypothesis. Table and memory
signatures are stack independent. Among reference instructions, those inspecting the
top of stack (`ref.is_null`, `ref.as_non_null`, `ref.test`, `ref.cast`,
`extern.convert_any`, `any.convert_extern`) read a BOT top as `(ref bot)`.
-/

namespace Silmaril.Wasm.Validation

theorem tableCheck?_complete_bot {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htab : TablesOk C) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : TableInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', tableCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ :=
  checkBySig_complete_of_eq hC (by exact hr) (tableSig?_complete hC hr htab helem h)
    (h.paramsOk htab) hlen hs hstk

theorem memoryCheck?_complete_bot {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : MemoryInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', memoryCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ :=
  checkBySig_complete_of_eq hC (by exact hr) (memorySig?_complete h)
    h.paramsOk hlen hs hstk

/-- `castTarget?` finds a candidate for any valid operand, including BOT. -/
theorem castTarget?_exists_bot {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    {t : CValType} {r rt' : CRefType} (hrok : TyOk C.toTypeCtx r)
    (hrt' : TyOk C.toTypeCtx rt') (ht : TyOk C.toTypeCtx t)
    (hs₁ : Sub.check C.toTypeCtx r rt' = true)
    (hs₂ : Sub.check C.toTypeCtx t (.refv rt') = true) :
    ∃ c, castTarget? tyOk C t r = some c := by
  by_cases hb : t = .botv
  · subst hb
    apply Option.isSome_iff_exists.mp
    unfold castTarget?
    rw [List.find?_isSome]
    cases r with
    | ref nr hrr =>
    refine ⟨.ref nr hrr, by simp [castCandidates], ?_⟩
    simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, TypeCtx.checkHeap_refl,
      htyOk hrok]
  · exact castTarget?_exists hC hr htyOk hrok hrt' ht hb hs₁ hs₂

theorem refCheck?_complete_bot {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : RefInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', refCheck? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  have hr' : C.toTypeCtx.recs = [] := hr
  have hstk' : ResultOk C.toTypeCtx stk := hstk
  have hty : ∀ {x : TypeIdx} {d : DefType}, C.type? x = some d → TyOk C.toTypeCtx d :=
    fun hd => (hC _ (List.mem_of_getElem? hd)).2
  cases h with
  | refNull h =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, htyOk h]) (by simp [ResultOk])
      hlen hs hstk'
  | refFunc h hr₀ =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, h, hr₀]) (by simp [ResultOk])
      hlen hs hstk'
  | refI31 =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?]) (by simp [ResultOk])
      hlen hs hstk'
  | refEq =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?]) (by simp [ResultOk])
      hlen hs hstk'
  | i31Get sx =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?]) (by simp [ResultOk])
      hlen hs hstk'
  | arrayLen =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?]) (by simp [ResultOk])
      hlen hs hstk'
  | structNew hd he =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he])
      (by
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨f, hf, rfl⟩ := ht
        exact TyOk.fieldUnpack (Expand.struct_ok (hty hd) he f hf))
      hlen hs hstk'
  | structNewDefault hd he hdef =>
    exact checkBySig_complete_of_eq hC hr'
      (by simp only [refSig?, hd, Expand.iff.mp he]; split <;> rfl)
      (by simp [ResultOk]) hlen hs hstk'
  | structGet hd he hi hsx =>
    exact checkBySig_complete_of_eq hC hr'
      (by simp [refSig?, hd, Expand.iff.mp he, hi, hsx])
      (by simp [ResultOk, hty hd]) hlen hs hstk'
  | structSet hd he hi =>
    have hz := Expand.struct_ok (hty hd) he _ (List.mem_of_getElem? hi)
    exact checkBySig_complete_of_eq hC hr'
      (by simp [refSig?, hd, Expand.iff.mp he, hi])
      (by simp [ResultOk, hty hd, TyOk.unpack hz.field_inv]) hlen hs hstk'
  | arrayNew hd he =>
    have hz := Expand.array_ok (hty hd) he
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he])
      (by simp [ResultOk, TyOk.unpack hz]) hlen hs hstk'
  | arrayNewDefault hd he hdef =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hdef])
      (by simp [ResultOk]) hlen hs hstk'
  | arrayNewFixed hd he =>
    have hz := Expand.array_ok (hty hd) he
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he])
      (by simp [ResultOk.replicate_iff, TyOk.unpack hz]) hlen hs hstk'
  | arrayNewElem hd he hy hs₀ =>
    have hz := Expand.array_ok (hty hd) he
    have hc := Sub.check_complete hC hr' hs₀ (helem _ (List.mem_of_getElem? hy))
      hz.val_inv.refv_inv
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hy, hc])
      (by simp [ResultOk]) hlen hs hstk'
  | arrayNewData hd he hnv hy =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hy, hnv])
      (by simp [ResultOk]) hlen hs hstk'
  | arrayGet hd he hsx =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hsx])
      (by simp [ResultOk, hty hd]) hlen hs hstk'
  | arraySet hd he =>
    have hz := Expand.array_ok (hty hd) he
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he])
      (by simp [ResultOk, hty hd, TyOk.unpack hz]) hlen hs hstk'
  | arrayFill hd he =>
    have hz := Expand.array_ok (hty hd) he
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he])
      (by simp [ResultOk, hty hd, TyOk.unpack hz]) hlen hs hstk'
  | arrayCopy hd₁ he₁ hd₂ he₂ hs₀ =>
    have hc := Sub.check_complete hC hr' hs₀ (Expand.array_ok (hty hd₂) he₂)
      (Expand.array_ok (hty hd₁) he₁)
    exact checkBySig_complete_of_eq hC hr'
      (by simp [refSig?, hd₁, hd₂, Expand.iff.mp he₁, Expand.iff.mp he₂, hc])
      (by simp [ResultOk, hty hd₁, hty hd₂]) hlen hs hstk'
  | arrayInitElem hd he hy hs₀ =>
    have hc := Sub.check_complete hC hr' hs₀
      (.val (.refv (helem _ (List.mem_of_getElem? hy)))) (Expand.array_ok (hty hd) he)
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hy, hc])
      (by simp [ResultOk, hty hd]) hlen hs hstk'
  | arrayInitData hd he hnv hy =>
    exact checkBySig_complete_of_eq hC hr' (by simp [refSig?, hd, Expand.iff.mp he, hy, hnv])
      (by simp [ResultOk, hty hd]) hlen hs hstk'
  | refIsNull hh =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    by_cases hb : t = .botv
    · subst hb
      refine ⟨[.i32], refCheck?_single (c := .refT true .bot)
        (by
          have hb0 := htyOk (TyOk.bot (Δ := C.toTypeCtx))
          simp [refSig?, refOperandHeap?, hb0])
        (by simp [Sub.check, Sub.checkK, TypeCtx.checkVal]), ResultSub.refl _ _⟩
    have hc := Sub.check_complete hC hr' hsub htok (by simp [hh])
    obtain ⟨n, ht, rfl⟩ := refv_of_check hc hb
    have hok := htok.refv_inv.ref_inv
    refine ⟨[.i32], refCheck?_single (c := .refT true ht)
      (by simp [refSig?, refOperandHeap?, htyOk hok]) ?_,
      ResultSub.refl _ _⟩
    simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
      TypeCtx.checkHeap_refl]
  | refAsNonNull hh =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    by_cases hb : t = .botv
    · subst hb
      refine ⟨[.refT false .bot], refCheck?_single (c := .refT true .bot)
        (by
          have hb0 := htyOk (TyOk.bot (Δ := C.toTypeCtx))
          simp [refSig?, refOperandHeap?, hb0])
        (by simp [Sub.check, Sub.checkK, TypeCtx.checkVal]), ?_⟩
      refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
        TypeCtx.checkHeap]
    have hc := Sub.check_complete hC hr' hsub htok (by simp [hh])
    obtain ⟨n, ht, rfl⟩ := refv_of_check hc hb
    have hok := htok.refv_inv.ref_inv
    refine ⟨[.refT false ht], refCheck?_single (c := .refT true ht)
      (by simp [refSig?, refOperandHeap?, htyOk hok]) ?_, ?_⟩
    · simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
        TypeCtx.checkHeap_refl]
    · simp only [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
        Bool.and_eq_true] at hc
      refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.2]
  | refTest h h' hs₀ =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    have hc₂ := Sub.check_complete hC hr' hsub htok (.refv h')
    have hc₁ := Sub.check_complete hC hr' hs₀ h h'
    obtain ⟨c, hcast⟩ := castTarget?_exists_bot hC hr htyOk h h' htok hc₁ hc₂
    exact ⟨[.i32], refCheck?_single (by simp [refSig?, htyOk h, hcast])
      (castTarget?_check hcast), ResultSub.refl _ _⟩
  | refCast h h' hs₀ =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    have hc₂ := Sub.check_complete hC hr' hsub htok (.refv h')
    have hc₁ := Sub.check_complete hC hr' hs₀ h h'
    obtain ⟨c, hcast⟩ := castTarget?_exists_bot hC hr htyOk h h' htok hc₁ hc₂
    exact ⟨_, refCheck?_single (by simp [refSig?, htyOk h, hcast])
      (castTarget?_check hcast), ResultSub.refl _ _⟩
  | externConvertAny n =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    by_cases hb : t = .botv
    · subst hb
      refine ⟨[.refT false (.abs .extern)], refCheck?_single (c := .refT false (.abs .any))
        (by simp [refSig?, refOperandNull?])
        (by simp [Sub.check, Sub.checkK, TypeCtx.checkVal]), ?_⟩
      refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
        TypeCtx.checkHeap_refl]
    have hc := Sub.check_complete hC hr' hsub htok (by simp)
    obtain ⟨n', ht, rfl⟩ := refv_of_check hc hb
    simp only [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
      Bool.and_eq_true] at hc
    refine ⟨[.refT n' (.abs .extern)], refCheck?_single (c := .refT n' (.abs .any))
      (by simp [refSig?, refOperandNull?]) ?_, ?_⟩
    · simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.2]
    · refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.1,
        TypeCtx.checkHeap_refl]
  | anyConvertExtern n =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := hstk t (by simp)
    by_cases hb : t = .botv
    · subst hb
      refine ⟨[.refT false (.abs .any)], refCheck?_single (c := .refT false (.abs .extern))
        (by simp [refSig?, refOperandNull?])
        (by simp [Sub.check, Sub.checkK, TypeCtx.checkVal]), ?_⟩
      refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
        TypeCtx.checkHeap_refl]
    have hc := Sub.check_complete hC hr' hsub htok (by simp)
    obtain ⟨n', ht, rfl⟩ := refv_of_check hc hb
    simp only [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
      Bool.and_eq_true] at hc
    refine ⟨[.refT n' (.abs .any)], refCheck?_single (c := .refT n' (.abs .extern))
      (by simp [refSig?, refOperandNull?]) ?_, ?_⟩
    · simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.2]
    · refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.1,
        TypeCtx.checkHeap_refl]

theorem atomicB?_complete_bot {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    (htab : TablesOk C) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : TableInstrOk C i ⟨t₁, xs, t₂⟩ ∨ MemoryInstrOk C i ⟨t₁, xs, t₂⟩ ∨
      RefInstrOk C i ⟨t₁, xs, t₂⟩)
    (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t) :
    ∃ out', atomicB? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  rcases h with h | h | h
  · obtain ⟨out', ho, hsub⟩ := tableCheck?_complete_bot hC hr htab helem h hlen hs hstk
    exact ⟨out', by simp [atomicB?, ho], hsub⟩
  · obtain ⟨out', ho, hsub⟩ := memoryCheck?_complete_bot hC hr h hlen hs hstk
    have hn : tableCheck? C stk i = none := by
      simp [tableCheck?, tableSig?_eq_none_of_memory h, checkBySig]
    exact ⟨out', by simp [atomicB?, hn, ho], hsub⟩
  · obtain ⟨out', ho, hsub⟩ := refCheck?_complete_bot hC hr htyOk helem h hlen hs hstk
    have hn : tableCheck? C stk i = none := by
      simp [tableCheck?, tableSig?_eq_none_of_ref h, checkBySig]
    have hm : memoryCheck? C stk i = none := by
      simp [memoryCheck?, memorySig?_eq_none_of_ref h, checkBySig]
    exact ⟨out', by simp [atomicB?, hn, hm, ho], hsub⟩

end Silmaril.Wasm.Validation
