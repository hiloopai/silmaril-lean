module

public import Silmaril.Wasm.Validation.Check.AtomicB
public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Completeness of the table, memory and reference checkers

Completeness of `tableCheck?`, `memoryCheck?`, `refCheck?` and the dispatch
`atomicB?` (`Validation/Check/AtomicB.lean`), in a context whose type section is
well formed (`C.toTypeCtx.Ok`, `C.recs = []`), for a complete `tyOk`, and for an
operand stack of valid non-`BOT` entries whose top matches the declared
parameters.

Besides these, completeness needs the table element types and the element-segment
types of the context to be valid (`TablesOk`, `ElemsOk`; both implied by
`Context_ok`): the checker decides `Sub` via `Sub.check`, which is only complete
on valid types.
-/

namespace Silmaril.Wasm.Validation

/-- The table element types of the context are valid. -/
def TablesOk (C : Context) : Prop := ∀ t ∈ C.tables, TyOk C.toTypeCtx t.element

/-- The element-segment types of the context are valid. -/
def ElemsOk (C : Context) : Prop := ∀ rt ∈ C.elems, TyOk C.toTypeCtx rt

/-! ## Stack matching -/

theorem listSubCheck_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {l l' : List CValType} (h : ResultSub Δ l l') (hl : ResultOk Δ l)
    (hl' : ResultOk Δ l') : listSubCheck Δ l l' = true := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [ResultOk.cons_iff] at hl hl'
    simp only [listSubCheck, Bool.and_eq_true]
    exact ⟨Sub.check_complete hΔ hr hab hl.1 hl'.1, ih hl.2 hl'.2⟩

theorem popsOk_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {stk ts : List CValType} (hlen : ts.length ≤ stk.length)
    (hs : ResultSub Δ (stk.drop (stk.length - ts.length)) ts) (hstk : ResultOk Δ stk)
    (hts : ResultOk Δ ts) : popsOk Δ stk ts = true := by
  simp only [popsOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlen, listSubCheck_complete hΔ hr hs
    (fun t ht => hstk t (List.mem_of_mem_drop ht)) hts⟩

theorem checkBySig_complete {Δ : TypeCtx} {it : InstrType} {stk : List CValType}
    (hp : popsOk Δ stk it.params = true) :
    checkBySig Δ (some it) stk = some (it.params.length, it.inits, it.results) := by
  simp [checkBySig, hp]

/-- The generic completeness step: a stack-independent signature that is the
declared type. -/
theorem checkBySig_complete_of_eq {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {sig : Option InstrType} {stk t₁ t₂ : List CValType} {xs : List Nat}
    (hsig : sig = some ⟨t₁, xs, t₂⟩) (hok : ResultOk Δ t₁)
    (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub Δ (stk.drop (stk.length - t₁.length)) t₁) (hstk : ResultOk Δ stk) :
    ∃ out', checkBySig Δ sig stk = some (t₁.length, xs, out') ∧ ResultSub Δ out' t₂ := by
  subst hsig
  exact ⟨t₂, checkBySig_complete (popsOk_complete hΔ hr hlen hs hstk hok),
    ResultSub.refl Δ t₂⟩

/-! ## Table instructions -/

theorem tableSig?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htab : TablesOk C) (helem : ElemsOk C) {i : Instr} {it : InstrType}
    (h : TableInstrOk C i it) : tableSig? C i = some it := by
  cases h with
  | tableGet h => simp [tableSig?, h]
  | tableSet h => simp [tableSig?, h]
  | tableSize h => simp [tableSig?, h]
  | tableGrow h => simp [tableSig?, h]
  | tableFill h => simp [tableSig?, h]
  | tableCopy h₁ h₂ hs =>
    have hc := Sub.check_complete hC hr hs (htab _ (List.mem_of_getElem? h₂))
      (htab _ (List.mem_of_getElem? h₁))
    simp [tableSig?, h₁, h₂, hc]
  | tableInit h he hs =>
    have hc := Sub.check_complete hC hr hs (helem _ (List.mem_of_getElem? he))
      (htab _ (List.mem_of_getElem? h))
    simp [tableSig?, h, he, hc]
  | elemDrop he => simp [tableSig?, he]

theorem TableInstrOk.paramsOk {C : Context} (htab : TablesOk C) {i : Instr} {it : InstrType}
    (h : TableInstrOk C i it) : ResultOk C.toTypeCtx it.params := by
  cases h with
  | tableSet h | tableGrow h | tableFill h =>
    have := htab _ (List.mem_of_getElem? h)
    simp_all [ResultOk]
  | _ => simp [ResultOk]

theorem tableCheck?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htab : TablesOk C) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : TableInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t ∧ t ≠ .botv) :
    ∃ out', tableCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ :=
  checkBySig_complete_of_eq hC (by exact hr) (tableSig?_complete hC hr htab helem h)
    (h.paramsOk htab) hlen hs (fun t ht => (hstk t ht).1)

/-! ## Memory instructions -/

theorem memorySig?_complete {C : Context} {i : Instr} {it : InstrType}
    (h : MemoryInstrOk C i it) : memorySig? C i = some it := by
  cases h <;> simp_all [memorySig?]

theorem MemoryInstrOk.paramsOk {C : Context} {i : Instr} {it : InstrType}
    (h : MemoryInstrOk C i it) : ResultOk C.toTypeCtx it.params := by
  cases h <;> simp [ResultOk]

theorem memoryCheck?_complete {C : Context} (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : MemoryInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t ∧ t ≠ .botv) :
    ∃ out', memoryCheck? C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ :=
  checkBySig_complete_of_eq hC (by exact hr) (memorySig?_complete h)
    h.paramsOk hlen hs (fun t ht => (hstk t ht).1)

/-! ## Reference instructions -/

/-- Every valid non-`BOT` heap type is below the top of one of the four hierarchies. -/
theorem exists_top {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {h : CHeapType}
    (hok : TyOk Δ h) (hb : h ≠ .bot) :
    ∃ τ : AbsHeapType, (τ = .any ∨ τ = .func ∨ τ = .extern ∨ τ = .exn) ∧
      Δ.checkHeap h (.abs τ) = true := by
  cases h with
  | bot => exact absurd rfl hb
  | abs a =>
    cases a
    all_goals first
      | exact ⟨.any, by simp, rfl⟩
      | exact ⟨.func, by simp, rfl⟩
      | exact ⟨.extern, by simp, rfl⟩
      | exact ⟨.exn, by simp, rfl⟩
  | use u =>
    obtain ⟨d, hd, okd⟩ := TypeCtx.resolve_ok hΔ hr hok.use_inv
    cases okd with
    | @defn _ subs i hg hi =>
      have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
      obtain ⟨st, hst⟩ : ∃ st, subs.toList[i]? = some st := ⟨_, List.getElem?_eq_getElem hi'⟩
      cases st with
      | sub fin sups ct =>
        have hu : unrolldt (.defn (.group subs) i) =
            some (.sub fin (sups.subst (unrollSubst subs)) (ct.subst (unrollSubst subs))) := by
          rw [unrolldt_defn, hst]; rfl
        have hk : defKind (.defn (.group subs) i) =
            some (compAbs (ct.subst (unrollSubst subs))) := by
          simp [defKind, hu, Ty.body]
        rw [compAbs_subst] at hk
        cases ct with
        | struct fs =>
          refine ⟨.any, by simp, ?_⟩
          simp [TypeCtx.checkHeap, TypeCtx.checkUseAbs, hd, hk, compAbs, absSub]
        | array f =>
          refine ⟨.any, by simp, ?_⟩
          simp [TypeCtx.checkHeap, TypeCtx.checkUseAbs, hd, hk, compAbs, absSub]
        | func ps rs =>
          refine ⟨.func, by simp, ?_⟩
          simp [TypeCtx.checkHeap, TypeCtx.checkUseAbs, hd, hk, compAbs, absSub]

theorem checkHeap_bot_right {Δ : TypeCtx} {h : CHeapType} (hc : Δ.checkHeap h .bot = true) :
    h = .bot := by
  cases h with
  | bot => rfl
  | abs a => simp [TypeCtx.checkHeap] at hc
  | use u => simp [TypeCtx.checkHeap] at hc

/-- A value type below a reference type that is not `BOT` is a reference type. -/
theorem refv_of_check {Δ : TypeCtx} {t : CValType} {r : CRefType}
    (hc : Sub.check Δ t (.refv r) = true) (hne : t ≠ .botv) :
    ∃ n ht, t = .refv (.ref n ht) := by
  cases t with
  | refv r' => cases r' with | ref n ht => exact ⟨n, ht, rfl⟩
  | botv => exact absurd rfl hne
  | _ => simp [Sub.check, Sub.checkK, TypeCtx.checkVal] at hc

/-- `castTarget?` finds a candidate whenever the target and the operand have a
common valid supertype `rt'`. -/
theorem castTarget?_exists {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    {t : CValType} {r rt' : CRefType} (hrok : TyOk C.toTypeCtx r)
    (hrt' : TyOk C.toTypeCtx rt') (ht : TyOk C.toTypeCtx t) (hne : t ≠ .botv)
    (hs₁ : Sub.check C.toTypeCtx r rt' = true)
    (hs₂ : Sub.check C.toTypeCtx t (.refv rt') = true) :
    ∃ c, castTarget? tyOk C t r = some c := by
  have hr' : C.toTypeCtx.recs = [] := hr
  obtain ⟨nt, htt, rfl⟩ := refv_of_check hs₂ hne
  cases r with
  | ref nr hrr =>
  cases rt' with
  | ref n' h' =>
  have hokr := hrok.ref_inv
  have hokt := ht.refv_inv.ref_inv
  have hok' := hrt'.ref_inv
  simp only [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Bool.and_eq_true]
    at hs₁ hs₂
  apply Option.isSome_iff_exists.mp
  unfold castTarget?
  rw [List.find?_isSome]
  by_cases hb : h' = .bot
  · subst hb
    have e₁ := checkHeap_bot_right hs₁.2
    have e₂ := checkHeap_bot_right hs₂.2
    subst e₁ e₂
    cases nt
    · refine ⟨.ref nr .bot, by simp [castCandidates], ?_⟩
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, TypeCtx.checkHeap,
        htyOk hrok]
    · refine ⟨.ref true .bot, by simp [castCandidates], ?_⟩
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, TypeCtx.checkHeap,
        htyOk (.ref .bot : TyOk C.toTypeCtx (Ty.ref true .bot))]
  · obtain ⟨τ, hτ, hc⟩ := exists_top hC hr' hok' hb
    have c₁ := TypeCtx.checkHeap_trans hC hr' hokr hok' hs₁.2 hc
    have c₂ := TypeCtx.checkHeap_trans hC hr' hokt hok' hs₂.2 hc
    refine ⟨.ref true (.abs τ), ?_, ?_⟩
    · rcases hτ with rfl | rfl | rfl | rfl <;> simp [castCandidates]
    · simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, c₁, c₂,
        htyOk (.ref (.abs τ) : TyOk C.toTypeCtx (Ty.ref true (.abs τ)))]

theorem castTarget?_check {tyOk : {k : TKind} → Ty k → Bool} {C : Context} {t : CValType}
    {r c : CRefType} (h : castTarget? tyOk C t r = some c) :
    Sub.check C.toTypeCtx t (.refv c) = true := by
  have := List.find?_some h
  simp only [Bool.and_eq_true] at this
  exact this.2

/-- Split the last stack entry off. -/
theorem stack_last {Δ : TypeCtx} {stk : List CValType} {p : CValType}
    (hlen : [p].length ≤ stk.length)
    (hs : ResultSub Δ (stk.drop (stk.length - [p].length)) [p]) :
    ∃ l t, stk = l ++ [t] ∧ Sub Δ t p := by
  obtain ⟨l, t, rfl⟩ : ∃ l t, stk = l ++ [t] := by
    rcases List.eq_nil_or_concat' stk with h | ⟨l, t, h⟩
    · subst h; simp at hlen
    · exact ⟨l, t, h⟩
  refine ⟨l, t, rfl, ?_⟩
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.drop_left, ResultSub, List.forall₂_cons] at hs
  exact hs.1

theorem refCheck?_single {tyOk : {k : TKind} → Ty k → Bool} {C : Context} {i : Instr}
    {l : List CValType} {t c r : CValType}
    (hsig : refSig? tyOk C (some t) i = some (.plain [c] [r]))
    (hc : Sub.check C.toTypeCtx t c = true) :
    refCheck? tyOk C (l ++ [t]) i = some (1, [], [r]) := by
  simp [refCheck?, hsig, checkBySig, popsOk, listSubCheck, hc]

theorem refCheck?_complete {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : RefInstrOk C i ⟨t₁, xs, t₂⟩) (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t ∧ t ≠ .botv) :
    ∃ out', refCheck? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  have hr' : C.toTypeCtx.recs = [] := hr
  have hstk' : ResultOk C.toTypeCtx stk := fun t ht => (hstk t ht).1
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
    have htok := (hstk t (by simp)).1
    have hc := Sub.check_complete hC hr' hsub htok (by simp [hh])
    obtain ⟨n, ht, rfl⟩ := refv_of_check hc (hstk _ (by simp)).2
    have hok := htok.refv_inv.ref_inv
    refine ⟨[.i32], refCheck?_single (c := .refT true ht)
      (by simp [refSig?, refOperandHeap?, htyOk hok]) ?_,
      ResultSub.refl _ _⟩
    simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
      TypeCtx.checkHeap_refl]
  | refAsNonNull hh =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := (hstk t (by simp)).1
    have hc := Sub.check_complete hC hr' hsub htok (by simp [hh])
    obtain ⟨n, ht, rfl⟩ := refv_of_check hc (hstk _ (by simp)).2
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
    have htok := (hstk t (by simp)).1
    have hc₂ := Sub.check_complete hC hr' hsub htok (.refv h')
    have hc₁ := Sub.check_complete hC hr' hs₀ h h'
    obtain ⟨c, hcast⟩ := castTarget?_exists hC hr htyOk h h' htok (hstk _ (by simp)).2 hc₁ hc₂
    exact ⟨[.i32], refCheck?_single (by simp [refSig?, htyOk h, hcast])
      (castTarget?_check hcast), ResultSub.refl _ _⟩
  | refCast h h' hs₀ =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := (hstk t (by simp)).1
    have hc₂ := Sub.check_complete hC hr' hsub htok (.refv h')
    have hc₁ := Sub.check_complete hC hr' hs₀ h h'
    obtain ⟨c, hcast⟩ := castTarget?_exists hC hr htyOk h h' htok (hstk _ (by simp)).2 hc₁ hc₂
    exact ⟨_, refCheck?_single (by simp [refSig?, htyOk h, hcast])
      (castTarget?_check hcast), ResultSub.refl _ _⟩
  | externConvertAny n =>
    obtain ⟨l, t, rfl, hsub⟩ := stack_last hlen hs
    have htok := (hstk t (by simp)).1
    have hc := Sub.check_complete hC hr' hsub htok (by simp)
    obtain ⟨n', ht, rfl⟩ := refv_of_check hc (hstk _ (by simp)).2
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
    have htok := (hstk t (by simp)).1
    have hc := Sub.check_complete hC hr' hsub htok (by simp)
    obtain ⟨n', ht, rfl⟩ := refv_of_check hc (hstk _ (by simp)).2
    simp only [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT,
      Bool.and_eq_true] at hc
    refine ⟨[.refT n' (.abs .any)], refCheck?_single (c := .refT n' (.abs .extern))
      (by simp [refSig?, refOperandNull?]) ?_, ?_⟩
    · simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.2]
    · refine List.Forall₂.cons (Sub.check_sound (k := .val) ?_) .nil
      simp [Sub.check, Sub.checkK, TypeCtx.checkVal, TypeCtx.checkRef, Ty.refT, hc.1,
        TypeCtx.checkHeap_refl]

/-! ## Dispatch -/

theorem tableSig?_eq_none_of_memory {C : Context} {i : Instr} {it : InstrType}
    (h : MemoryInstrOk C i it) : tableSig? C i = none := by
  cases h <;> rfl

theorem tableSig?_eq_none_of_ref {C : Context} {i : Instr} {it : InstrType}
    (h : RefInstrOk C i it) : tableSig? C i = none := by
  cases h <;> rfl

theorem memorySig?_eq_none_of_ref {C : Context} {i : Instr} {it : InstrType}
    (h : RefInstrOk C i it) : memorySig? C i = none := by
  cases h <;> rfl

/-- Completeness of `atomicB?` for any instruction typed by the table, memory or
reference family. -/
theorem atomicB?_complete {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (hC : C.toTypeCtx.Ok) (hr : C.recs = [])
    (htyOk : ∀ {k} {t : Ty k}, TyOk C.toTypeCtx t → tyOk t = true)
    (htab : TablesOk C) (helem : ElemsOk C)
    {stk : List CValType} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (h : TableInstrOk C i ⟨t₁, xs, t₂⟩ ∨ MemoryInstrOk C i ⟨t₁, xs, t₂⟩ ∨
      RefInstrOk C i ⟨t₁, xs, t₂⟩)
    (hlen : t₁.length ≤ stk.length)
    (hs : ResultSub C.toTypeCtx (stk.drop (stk.length - t₁.length)) t₁)
    (hstk : ∀ t ∈ stk, TyOk C.toTypeCtx t ∧ t ≠ .botv) :
    ∃ out', atomicB? tyOk C stk i = some (t₁.length, xs, out') ∧
      ResultSub C.toTypeCtx out' t₂ := by
  rcases h with h | h | h
  · obtain ⟨out', ho, hsub⟩ := tableCheck?_complete hC hr htab helem h hlen hs hstk
    exact ⟨out', by simp [atomicB?, ho], hsub⟩
  · obtain ⟨out', ho, hsub⟩ := memoryCheck?_complete hC hr h hlen hs hstk
    have hn : tableCheck? C stk i = none := by
      simp [tableCheck?, tableSig?_eq_none_of_memory h, checkBySig]
    exact ⟨out', by simp [atomicB?, hn, ho], hsub⟩
  · obtain ⟨out', ho, hsub⟩ := refCheck?_complete hC hr htyOk helem h hlen hs hstk
    have hn : tableCheck? C stk i = none := by
      simp [tableCheck?, tableSig?_eq_none_of_ref h, checkBySig]
    have hm : memoryCheck? C stk i = none := by
      simp [memoryCheck?, memorySig?_eq_none_of_ref h, checkBySig]
    exact ⟨out', by simp [atomicB?, hn, hm, ho], hsub⟩

end Silmaril.Wasm.Validation
