module

public import Silmaril.Wasm.Resource.Client.Defs

/-!
# The client typestate analysis: basic facts

* Unfolding `okA` on one element: values in and out of the prefix (`okA_val_pre`,
  `okA_val_npre`), source instructions (`okA_plain`), references, `trap`, nested elements.
* `CLe`: the order on abstract states (more facts, a more precise top, the prefix mode is more
  permissive); `okI_mono`, `okL_mono`, `okA_mono`; `okA_bot`: every state is above
  `⟨[], other, false⟩`.
* `okA_npre_indep`: outside the prefix the check depends neither on the protocol state nor on the
  store.
* Value prefixes (`okA_vals_pre`, `okA_vals_last`, `okA_vals_other`), source code
  (`okA_expr`, `okA_body`), right-hand sides keeping or dropping the facts (`okA_keep`,
  `okA_free`).
* `pairOf` and the semantics: monotonicity in the live list.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.Client

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {C : Cfg} {L : List Val} {gl : List GlobalInst} {gs : List Nat} {lc : List (Option Val)}

/-! ## Values -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem val?_eq_some {x : Admin} {v : Val} (h : x.val? = some v) : x = v.toAdmin := by
  cases x with
  | plain i => cases i <;> simp [Admin.val?] at h <;> (subst h; rfl)
  | ref r => simp [Admin.val?] at h; subst h; rfl
  | _ => simp [Admin.val?] at h

/-- The syntactic top of a value outside the prefix. -/
def synTop : Val → CTop
  | .num ⟨.int .i32, c⟩ => if c == 0 then .zero else .nz
  | _ => .other

theorem Ab_synTop (ps : List (Nat × Nat)) (v : Val) : Ab ps L gl (synTop v) v := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int t =>
      cases t
      · simp only [synTop]
        split
        · rename_i h; simp only [Ab]; rw [eq_of_beq h]; rfl
        · rename_i h
          exact ⟨c, rfl, fun h' => h (by rw [h']; rfl)⟩
      · trivial
    | float t => trivial
  | vec b => trivial
  | ref r => trivial

theorem synTop_ne_ex (v : Val) : synTop v ≠ .ex := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int t =>
      cases t
      · simp only [synTop]; split <;> exact nofun
      · exact nofun
    | float t => exact nofun
  | vec b => exact nofun
  | ref r => exact nofun

theorem nextI_val {i : Instr} {v : Val} (h : (Admin.plain i).val? = some v) (F : List Fact)
    (t : CTop) : nextI C gs F t i = (F, synTop v) ∧ okI C gs F t i = true := by
  cases i <;> simp [Admin.val?] at h <;> subst h
  · rename_i t' c
    cases t' <;> exact ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-! ## One element -/

theorem okA_cons_ex (F : List Fact) (p : Bool) (x : Admin) (l : List Admin) :
    okA C L gl gs lc ⟨F, .ex, p⟩ (x :: l) := by
  simp [okA]

theorem okA_trap (st : CSt) (l : List Admin) : okA C L gl gs lc st (.trap :: l) := by
  simp [okA, Admin.val?]

theorem okA_val_pre {F : List Fact} {t : CTop} (ht : t ≠ .ex) (v : Val) (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (v.toAdmin :: l) ↔
      ∃ t', Ab C.ps L gl t' v ∧ okA C L gl gs lc ⟨F, t', true⟩ l := by
  simp [okA, ht]

theorem okA_plain {F : List Fact} {t : CTop} {p : Bool} {i : Instr} (ht : t ≠ .ex)
    (hi : p = false ∨ (Admin.plain i).val? = none) (l : List Admin) :
    okA C L gl gs lc ⟨F, t, p⟩ (.plain i :: l) ↔ okI C gs F t i = true ∧
      okA C L gl gs lc ⟨(nextI C gs F t i).1, (nextI C gs F t i).2, false⟩ l := by
  rcases hi with rfl | hi
  · simp [okA, ht, NestA]
  · simp [okA, ht, hi, NestA]

theorem okA_ref_npre {F : List Fact} {t : CTop} (ht : t ≠ .ex) (r : Ref) (l : List Admin) :
    okA C L gl gs lc ⟨F, t, false⟩ (.ref r :: l) ↔ okA C L gl gs lc ⟨F, .other, false⟩ l := by
  simp [okA, ht, Admin.val?, NestA]

theorem okA_val_npre {F : List Fact} {t : CTop} (ht : t ≠ .ex) (v : Val) (l : List Admin) :
    okA C L gl gs lc ⟨F, t, false⟩ (v.toAdmin :: l) ↔ okA C L gl gs lc ⟨F, synTop v, false⟩ l := by
  cases v with
  | ref r => exact okA_ref_npre ht r l
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int it =>
      change okA C L gl gs lc _ (.plain (.intConst it c) :: l) ↔ _
      rw [okA_plain ht (.inl rfl)]
      cases it <;> exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
    | float ft =>
      change okA C L gl gs lc _ (.plain (.floatConst ft c) :: l) ↔ _
      rw [okA_plain ht (.inl rfl)]
      exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  | vec b =>
    change okA C L gl gs lc _ (.plain (.vecConst b) :: l) ↔ _
    rw [okA_plain ht (.inl rfl)]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem okA_nest_pre {F : List Fact} {t : CTop} (ht : t ≠ .ex) {x : Admin} (hx : NestA x)
    (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (x :: l) ↔ okX C L gl gs lc x ∧ okA C L gl gs lc ⟨[], .other, false⟩ l := by
  cases x <;> simp_all [okA, Admin.val?, NestA]

theorem okA_nest_npre {F : List Fact} {t : CTop} (ht : t ≠ .ex) {x : Admin} (hx : NestA x)
    (l : List Admin) : ¬ okA C L gl gs lc ⟨F, t, false⟩ (x :: l) := by
  cases x <;> simp_all [okA, Admin.val?, NestA]

theorem val?_none_of_nest {x : Admin} (hx : NestA x) : x.val? = none := by
  cases x <;> simp_all [Admin.val?, NestA]

/-! ## The order on states -/

/-- The order on tops: `t'` is at least as precise as `t`. -/
def TLe (t t' : CTop) : Prop := t = t' ∨ t = .other ∨ (t = .gg ∧ t' = .fr)

/-- The order on states: `st'` is dead, or knows more, has a more precise top and is in the
prefix if `st` is. -/
def CLe (st st' : CSt) : Prop :=
  st'.top = .ex ∨ ((∀ f ∈ st.F, f ∈ st'.F) ∧ TLe st.top st'.top ∧ (st.pre = true → st'.pre = true))

theorem TLe.refl (t : CTop) : TLe t t := .inl rfl

theorem TLe.ex {t' : CTop} (h : TLe .ex t') : t' = .ex := by
  rcases h with h | h | ⟨h, -⟩ <;> first | exact h.symm | cases h

theorem TLe.zero {t' : CTop} (h : TLe .zero t') : t' = .zero := by
  rcases h with h | h | ⟨h, -⟩ <;> first | exact h.symm | cases h

theorem TLe.nz {t' : CTop} (h : TLe .nz t') : t' = .nz := by
  rcases h with h | h | ⟨h, -⟩ <;> first | exact h.symm | cases h

theorem TLe.fr {t' : CTop} (h : TLe .fr t') : t' = .fr := by
  rcases h with h | h | ⟨h, -⟩ <;> first | exact h.symm | cases h

theorem TLe.flag {k : Nat} {t' : CTop} (h : TLe (.flag k) t') : t' = .flag k := by
  rcases h with h | h | ⟨h, -⟩ <;> first | exact h.symm | cases h

theorem TLe.gg {t' : CTop} (h : TLe .gg t') : t' = .gg ∨ t' = .fr := by
  rcases h with h | h | ⟨-, h⟩
  · exact .inl h.symm
  · cases h
  · exact .inr h

/-! ## Monotonicity of the source checks -/

section
variable {F F' : List Fact}

theorem contains_mono (hF : ∀ f ∈ F, f ∈ F') : ∀ f, F.contains f = true → F'.contains f = true :=
  fun f h => by
    have h' : f ∈ F := by simpa only [List.contains_iff_mem] using h
    simpa only [List.contains_iff_mem] using hF _ h'

theorem handTop_mono (hF : ∀ f ∈ F, f ∈ F') (k : Nat) : TLe (handTop F k) (handTop F' k) := by
  have hc := contains_mono hF
  unfold handTop
  by_cases h₁ : (F.contains (.live k) && F.contains (.off k)) = true
  · have h₁' : (F'.contains (.live k) && F'.contains (.off k)) = true := by
      simp only [Bool.and_eq_true] at h₁ ⊢
      exact ⟨hc _ h₁.1, hc _ h₁.2⟩
    rw [ite_t h₁, ite_t h₁']; exact .inl rfl
  · rw [ite_f h₁]
    by_cases h₂ : (F.contains (.on k) || F.contains (.live k)) = true
    · have h₂' : (F'.contains (.on k) || F'.contains (.live k)) = true := by
        simp only [Bool.or_eq_true] at h₂ ⊢
        exact h₂.imp (hc _) (hc _)
      rw [ite_t h₂]
      by_cases h₃ : (F'.contains (.live k) && F'.contains (.off k)) = true
      · rw [ite_t h₃]; exact .inr (.inr ⟨rfl, rfl⟩)
      · rw [ite_f h₃, ite_t h₂']; exact .inl rfl
    · rw [ite_f h₂]; exact .inr (.inl rfl)

theorem getTop_mono (hF : ∀ f ∈ F, f ∈ F') (a : Nat) : TLe (getTop C F a) (getTop C F' a) := by
  unfold getTop
  split
  · exact .inl rfl
  · exact handTop_mono hF _
  · exact .inl rfl

theorem liveAfterClear_mono (hF : ∀ f ∈ F, f ∈ F') {k : Nat}
    (h : liveAfterClear C F k = true) : liveAfterClear C F' k = true := by
  have hc := contains_mono hF
  simp only [liveAfterClear, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h ⊢
  exact ⟨hc _ h.1, fun j hj => (h.2 j hj).imp id (hc _)⟩

/-- The new facts of a flag write are monotone. -/
theorem setPre_mono (hF : ∀ f ∈ F, f ∈ F') (k : Nat) (t : CTop) :
    ∀ f ∈ (if t == .zero then Fact.off k :: (if liveAfterClear C F k then [Fact.live k] else [])
      else if t == .nz then [Fact.on k] else []),
    f ∈ (if t == .zero then Fact.off k :: (if liveAfterClear C F' k then [Fact.live k] else [])
      else if t == .nz then [Fact.on k] else []) := by
  intro f hf
  by_cases hz : (t == .zero) = true
  · rw [ite_t hz] at hf ⊢
    rcases List.mem_cons.1 hf with rfl | hf
    · exact List.mem_cons_self
    · by_cases hl : liveAfterClear C F k = true
      · rw [ite_t hl] at hf
        rw [ite_t (liveAfterClear_mono hF hl)]
        exact List.mem_cons_of_mem _ hf
      · rw [ite_f hl] at hf; simp at hf
  · rw [ite_f hz] at hf ⊢; exact hf

/-- The facts kept by a flag write are monotone in the top. -/
theorem setFilt_mono {k : Nat} {t t' : CTop} (ht : TLe t t') (f : Fact)
    (hp : (f != .on k && f != .off k && (t == .zero || !isLive f || f == .live k)) = true) :
    (f != .on k && f != .off k && (t' == .zero || !isLive f || f == .live k)) = true := by
  rcases ht with rfl | rfl | ⟨rfl, rfl⟩
  · exact hp
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hp ⊢
    tauto
  · simpa using hp

theorem setF_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') (a : Nat) :
    ∀ f ∈ setF C F t a, f ∈ setF C F' t' a := by
  unfold setF
  split
  · rename_i k _
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · refine List.mem_append_left _ ?_
      rcases ht with rfl | rfl | ⟨rfl, rfl⟩
      · exact setPre_mono hF k t f hf
      · simp at hf
      · simp at hf
    · obtain ⟨hf, hp⟩ := List.mem_filter.1 hf
      exact List.mem_append_right _ (List.mem_filter.2 ⟨hF _ hf, setFilt_mono ht f hp⟩)
  · intro f hf
    simp only [List.mem_cons, List.mem_filter] at hf ⊢
    exact hf.elim .inl fun h => .inr ⟨hF _ h.1, h.2⟩
  · exact hF

theorem filter_mono (hF : ∀ f ∈ F, f ∈ F') (p : Fact → Bool) :
    ∀ f ∈ F.filter p, f ∈ F'.filter p := by
  intro f hf
  obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hf
  exact List.mem_filter.2 ⟨hF _ h₁, h₂⟩

theorem thenF_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') :
    ∀ f ∈ thenF F t, f ∈ thenF F' t' := by
  rcases ht with rfl | rfl | ⟨rfl, rfl⟩
  · cases t <;> simp only [thenF] <;> first
      | exact hF
      | (intro f hf; rcases List.mem_cons.1 hf with h | h
         · exact h ▸ List.mem_cons_self
         · exact List.mem_cons_of_mem _ (hF _ h))
  · intro f hf
    cases t' <;> simp only [thenF] <;> first | exact hF _ hf | exact List.mem_cons_of_mem _ (hF _ hf)
  · exact hF

theorem elseF_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') :
    ∀ f ∈ elseF F t, f ∈ elseF F' t' := by
  rcases ht with rfl | rfl | ⟨rfl, rfl⟩
  · cases t <;> simp only [elseF] <;> first
      | exact hF
      | (intro f hf; rcases List.mem_cons.1 hf with h | h
         · exact h ▸ List.mem_cons_self
         · exact List.mem_cons_of_mem _ (hF _ h))
  · intro f hf
    cases t' <;> simp only [elseF] <;> first | exact hF _ hf | exact List.mem_cons_of_mem _ (hF _ hf)
  · exact hF

/-- The state after an instruction is monotone. -/
def NLe (n n' : List Fact × CTop) : Prop := (∀ f ∈ n.1, f ∈ n'.1) ∧ TLe n.2 n'.2

theorem callNext_mono (hF : ∀ f ∈ F, f ∈ F') (x : FuncIdx) :
    NLe (callNext C F x) (callNext C F' x) := by
  unfold callNext
  split
  · split
    · exact ⟨hF, .inl rfl⟩
    · split
      · exact ⟨filter_mono hF _, .inl rfl⟩
      · split
        · exact ⟨hF, .inl rfl⟩
        · exact ⟨fun _ h => h, .inl rfl⟩
  · exact ⟨fun _ h => h, .inl rfl⟩

theorem locF_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') (i : Nat) :
    ∀ f ∈ locF F t i, f ∈ locF F' t' i := by
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · refine List.mem_append_left _ ?_
    rcases ht with rfl | rfl | ⟨rfl, rfl⟩
    · exact hf
    · simp at hf
    · simp at hf
  · exact List.mem_append_right _ (filter_mono hF _ f hf)

theorem nextI_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') (i : Instr) :
    NLe (nextI C gs F t i) (nextI C gs F' t' i) := by
  cases i
  case localGet x =>
    refine ⟨hF, ?_⟩
    simp only [nextI]
    by_cases h : F.contains (.loc x.toNat) = true
    · rw [ite_t h, ite_t (contains_mono hF _ h)]; exact .inl rfl
    · rw [ite_f h]; exact .inr (.inl rfl)
  case localSet x => exact ⟨locF_mono hF ht _, .inl rfl⟩
  case localTee x => exact ⟨locF_mono hF ht _, .inl rfl⟩
  case globalGet x =>
    refine ⟨hF, ?_⟩
    simp only [nextI]
    split
    · exact getTop_mono hF _
    · exact .inl rfl
  case globalSet x =>
    refine ⟨?_, .inl rfl⟩
    simp only [nextI]
    split
    · exact setF_mono hF ht _
    · exact hF
  case call x => exact callNext_mono hF x
  all_goals first | exact ⟨hF, .inl rfl⟩ | exact ⟨fun _ h => h, .inl rfl⟩

theorem setReq_mono (hF : ∀ f ∈ F, f ∈ F') {t t' : CTop} (ht : TLe t t') (a : Nat)
    (h : setReq C F t a = true) : setReq C F' t' a = true := by
  unfold setReq at h ⊢
  split
  · rename_i k _
    simp only [*, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h ⊢
    rcases h with h | h
    · subst h; exact .inl ht.zero
    · exact .inr (hF _ h)
  · simp only [*, beq_iff_eq] at h ⊢
    subst h; exact ht.fr
  · rfl

theorem callReq_mono {t t' : CTop} (ht : TLe t t') (x : FuncIdx)
    (h : callReq C t x = true) : callReq C t' x = true := by
  rcases ht with rfl | rfl | ⟨rfl, rfl⟩
  · exact h
  all_goals
    unfold callReq at h ⊢
    split at h
    · rename_i a ha
      by_cases hu : C.isU a = true <;> by_cases hf : C.isF a = true <;> simp_all
    · simp_all

end

mutual

/-- **The check of an instruction is monotone.** -/
theorem okI_mono : ∀ (i : Instr) {F F' : List Fact} {t t' : CTop}, (∀ f ∈ F, f ∈ F') →
    TLe t t' → okI C gs F t i = true → okI C gs F' t' i = true
  | i, F, F', t, t', hF, ht, h => by
    cases i with
    | block _ b => exact okL_mono b hF (.inl rfl) h
    | loop _ b => exact h
    | tryTable _ _ b => exact okL_mono b hF (.inl rfl) h
    | if_ _ b₁ b₂ =>
      simp only [okI, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
      refine ⟨?_, ?_⟩
      · rcases h.1 with h₁ | h₁
        · exact .inl (h₁ ▸ ht).zero
        · by_cases hz : t' = .zero
          · exact .inl hz
          · exact .inr (okL_mono b₁ (thenF_mono hF ht) (.inl rfl) h₁)
      · rcases h.2 with h₁ | h₁
        · exact .inl (h₁ ▸ ht).nz
        · by_cases hz : t' = .nz
          · exact .inl hz
          · exact .inr (okL_mono b₂ (elseF_mono hF ht) (.inl rfl) h₁)
    | globalSet x =>
      simp only [okI] at h ⊢
      split
      · rename_i a ha
        rw [ha] at h
        exact setReq_mono hF ht a h
      · rfl
    | call x => exact callReq_mono ht x h
    | _ => rfl

/-- **The check of a sequence is monotone.** -/
theorem okL_mono : ∀ (is : List Instr) {F F' : List Fact} {t t' : CTop}, (∀ f ∈ F, f ∈ F') →
    TLe t t' → okL C gs F t is = true → okL C gs F' t' is = true
  | [], _, _, _, _, _, _, _ => by simp [okL]
  | i :: is, F, F', t, t', hF, ht, h => by
    by_cases hex : t = .ex
    · subst hex; simp [okL, ht.ex]
    · have h' : okI C gs F t i = true ∧
          okL C gs (nextI C gs F t i).1 (nextI C gs F t i).2 is = true := by
        simpa [okL, hex] using h
      obtain ⟨hn₁, hn₂⟩ := nextI_mono (C := C) (gs := gs) hF ht i
      have h₁ := okI_mono i hF ht h'.1
      have h₂ := okL_mono is hn₁ hn₂ h'.2
      simp [okL, h₁, h₂]

end

/-! ## Monotonicity of the administrative check -/

theorem CLe.of_top {st st' : CSt} (h : st.top = .ex) (hle : CLe st st') : st'.top = .ex := by
  rcases hle with h' | ⟨-, ht, -⟩
  · exact h'
  · rw [h] at ht; exact ht.ex

/-- **The administrative check is monotone.** -/
theorem okA_mono : ∀ (l : List Admin) {st : CSt}, okA C L gl gs lc st l → ∀ {st' : CSt},
    CLe st st' → okA C L gl gs lc st' l
  | [], _, _, _, _ => trivial
  | x :: l, ⟨F, t, p⟩, h, ⟨F', t', p'⟩, hle => by
    by_cases hex' : t' = .ex
    · subst hex'; exact okA_cons_ex _ _ _ _
    have hex : t ≠ .ex := fun he => hex' (CLe.of_top he hle)
    obtain ⟨hF, ht, hp⟩ := hle.resolve_left hex'
    simp only at hF ht hp
    rcases hv : x.val? with _ | v
    · cases x with
      | plain i =>
        rw [okA_plain hex (.inr hv)] at h
        rw [okA_plain hex' (.inr hv)]
        obtain ⟨hn₁, hn₂⟩ := nextI_mono (C := C) (gs := gs) hF ht i
        exact ⟨okI_mono i hF ht h.1, okA_mono l h.2 (Or.inr ⟨hn₁, hn₂, fun h => h⟩)⟩
      | ref r => simp [Admin.val?] at hv
      | trap => exact okA_trap _ _
      | _ =>
        cases p
        · exact absurd h (okA_nest_npre hex (by trivial) l)
        · rw [hp rfl]
          rw [okA_nest_pre hex (by trivial)] at h
          exact (okA_nest_pre hex' (by trivial) l).2 h
    · obtain rfl := val?_eq_some hv
      cases p
      · rw [okA_val_npre hex] at h
        cases p'
        · rw [okA_val_npre hex']
          exact okA_mono l h (Or.inr ⟨hF, .inl rfl, fun h => h⟩)
        · rw [okA_val_pre hex']
          exact ⟨_, Ab_synTop _ v, okA_mono l h (Or.inr ⟨hF, .inl rfl, fun _ => rfl⟩)⟩
      · rw [hp rfl]
        rw [okA_val_pre hex] at h
        rw [okA_val_pre hex']
        obtain ⟨t₁, hab, h⟩ := h
        exact ⟨t₁, hab, okA_mono l h (Or.inr ⟨hF, .inl rfl, fun h => h⟩)⟩

/-- Every state is above `⟨[], other, false⟩`. -/
theorem CLe.bot (st : CSt) : CLe ⟨[], .other, false⟩ st :=
  Or.inr ⟨fun _ h => by simp at h, .inr (.inl rfl), fun h => by cases h⟩

theorem okA_bot {l : List Admin} (h : okA C L gl gs lc ⟨[], .other, false⟩ l) (st : CSt) :
    okA C L gl gs lc st l :=
  okA_mono l h (CLe.bot st)

theorem okA_pre_of_npre {F : List Fact} {t : CTop} {l : List Admin}
    (h : okA C L gl gs lc ⟨F, t, false⟩ l) : okA C L gl gs lc ⟨F, t, true⟩ l :=
  okA_mono l h (Or.inr ⟨fun _ h => h, .inl rfl, fun _ => rfl⟩)

/-- **Outside the prefix the check depends neither on the live list nor on the globals.** -/
theorem okA_npre_indep {L' : List Val} {gl' : List GlobalInst} {lc' : List (Option Val)} :
    ∀ (l : List Admin) {F : List Fact} {t : CTop}, okA C L gl gs lc ⟨F, t, false⟩ l →
      okA C L' gl' gs lc' ⟨F, t, false⟩ l
  | [], _, _, _ => trivial
  | x :: l, F, t, h => by
    by_cases hex : t = .ex
    · subst hex; exact okA_cons_ex _ _ _ _
    rcases hv : x.val? with _ | v
    · cases x with
      | plain i =>
        rw [okA_plain hex (.inl rfl)] at h ⊢
        exact ⟨h.1, okA_npre_indep l h.2⟩
      | ref r => simp [Admin.val?] at hv
      | trap => exact okA_trap _ _
      | _ => exact absurd h (okA_nest_npre hex (by trivial) l)
    · obtain rfl := val?_eq_some hv
      rw [okA_val_npre hex] at h ⊢
      exact okA_npre_indep l h

/-! ## Value prefixes and source code -/

theorem okA_vals_pre {F : List Fact} {l : List Admin} :
    ∀ {t : CTop} (vs : List Val), t ≠ .ex → okA C L gl gs lc ⟨F, t, true⟩ (vals vs ++ l) →
      ∃ t', t' ≠ .ex ∧ okA C L gl gs lc ⟨F, t', true⟩ l
  | t, [], ht, h => ⟨t, ht, h⟩
  | t, v :: vs, ht, h => by
    rw [vals, List.map_cons, List.cons_append, okA_val_pre ht] at h
    obtain ⟨t', hab, h⟩ := h
    have ht' : t' ≠ .ex := by rintro rfl; exact hab
    exact okA_vals_pre vs ht' h

theorem okA_vals_last {F : List Fact} {t : CTop} {l : List Admin} (ht : t ≠ .ex)
    (vs : List Val) (v : Val) (h : okA C L gl gs lc ⟨F, t, true⟩ (vals (vs ++ [v]) ++ l)) :
    ∃ t', Ab C.ps L gl t' v ∧ okA C L gl gs lc ⟨F, t', true⟩ l := by
  rw [vals_append, List.append_assoc] at h
  obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre vs ht h
  simpa [vals, okA_val_pre ht₁] using h

theorem okA_vals_other {F : List Fact} {l : List Admin} (h : okA C L gl gs lc ⟨F, .other, true⟩ l) :
    ∀ (t : CTop) (vs : List Val), okA C L gl gs lc ⟨F, t, true⟩ (vals vs ++ l)
  | t, [] => okA_mono l h (Or.inr ⟨fun _ h => h, .inr (.inl rfl), fun h => h⟩)
  | t, v :: vs => by
    by_cases ht : t = .ex
    · subst ht; exact okA_cons_ex _ _ _ _
    rw [vals, List.map_cons, List.cons_append, okA_val_pre ht]
    exact ⟨.other, trivial, okA_vals_other h .other vs⟩

theorem okA_expr {l : List Admin} (hl : okA C L gl gs lc ⟨[], .other, false⟩ l) :
    ∀ (is : List Instr) {F : List Fact} {t : CTop}, okL C gs F t is = true →
      okA C L gl gs lc ⟨F, t, false⟩ (expression is ++ l)
  | [], _, _, _ => okA_bot hl _
  | i :: is, F, t, h => by
    by_cases ht : t = .ex
    · subst ht; exact okA_cons_ex _ _ _ _
    have h' : okI C gs F t i = true ∧
        okL C gs (nextI C gs F t i).1 (nextI C gs F t i).2 is = true := by
      simpa [okL, ht] using h
    simp only [expression, List.map_cons, List.cons_append]
    rw [okA_plain ht (.inl rfl)]
    exact ⟨h'.1, okA_expr hl is h'.2⟩

theorem okA_body {F : List Fact} {b : List Instr} (h : okL C gs F .other b = true)
    (t : CTop) (vs : List Val) : okA C L gl gs lc ⟨F, t, true⟩ (vals vs ++ expression b) := by
  refine okA_vals_other (okA_pre_of_npre ?_) t vs
  simpa using okA_expr (l := []) trivial b h

/-! ## Right-hand sides -/

/-- An element keeping the facts. -/
def KeepE (x : Admin) : Prop :=
  x.val? ≠ none ∨ x = .trap ∨ ∃ j, x = .plain j ∧ (Admin.plain j).val? = none ∧
    ∀ (C : Cfg) (gs : List Nat) (F : List Fact) (t : CTop), okI C gs F t j = true ∧
      (nextI C gs F t j).1 = F ∧ (nextI C gs F t j).2 ≠ .ex

/-- An element without requirement. -/
def FreeE (x : Admin) : Prop :=
  x.val? ≠ none ∨ x = .trap ∨
    ∃ j, x = .plain j ∧ ∀ (C : Cfg) (gs : List Nat) (F : List Fact) (t : CTop), okI C gs F t j = true

theorem okA_keep {F : List Fact} {l : List Admin} (hl : okA C L gl gs lc ⟨F, .other, false⟩ l) :
    ∀ (R : List Admin), (∀ x ∈ R, KeepE x) → ∀ (t : CTop) (p : Bool),
      okA C L gl gs lc ⟨F, t, p⟩ (R ++ l)
  | [], _, t, p => okA_mono l hl (Or.inr ⟨fun _ h => h, .inr (.inl rfl), fun h => by cases h⟩)
  | x :: R, hR, t, p => by
    by_cases ht : t = .ex
    · subst ht; exact okA_cons_ex _ _ _ _
    have ih := okA_keep hl R fun y hy => hR y (List.mem_cons_of_mem _ hy)
    rcases hR x List.mem_cons_self with hx | rfl | ⟨j, rfl, hv, hj⟩
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hx
      obtain rfl := val?_eq_some hv
      cases p
      · rw [List.cons_append, okA_val_npre ht]; exact ih _ _
      · rw [List.cons_append, okA_val_pre ht]; exact ⟨.other, trivial, ih _ _⟩
    · exact okA_trap _ _
    · rw [List.cons_append, okA_plain ht (.inr hv)]
      obtain ⟨h₁, h₂, -⟩ := hj C gs F t
      refine ⟨h₁, ?_⟩
      rw [h₂]
      exact ih _ false

theorem okA_free {l : List Admin} (hl : okA C L gl gs lc ⟨[], .other, false⟩ l) :
    ∀ (R : List Admin), (∀ x ∈ R, FreeE x) → ∀ (F : List Fact) (t : CTop) (p : Bool),
      okA C L gl gs lc ⟨F, t, p⟩ (R ++ l)
  | [], _, F, t, p => okA_bot hl _
  | x :: R, hR, F, t, p => by
    by_cases ht : t = .ex
    · subst ht; exact okA_cons_ex _ _ _ _
    have ih := okA_free hl R fun y hy => hR y (List.mem_cons_of_mem _ hy)
    rcases hR x List.mem_cons_self with hx | rfl | ⟨j, rfl, hj⟩
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hx
      obtain rfl := val?_eq_some hv
      cases p
      · rw [List.cons_append, okA_val_npre ht]; exact ih _ _ _
      · rw [List.cons_append, okA_val_pre ht]; exact ⟨.other, trivial, ih _ _ _⟩
    · exact okA_trap _ _
    · rcases hv : (Admin.plain j).val? with _ | v
      · rw [List.cons_append, okA_plain ht (.inr hv)]
        exact ⟨hj C gs F t, ih _ _ _⟩
      · obtain h := val?_eq_some hv
        rw [List.cons_append, h]
        cases p
        · rw [okA_val_npre ht]; exact ih _ _ _
        · rw [okA_val_pre ht]; exact ⟨.other, trivial, ih _ _ _⟩

/-! ## Pairs and semantics -/

theorem pairOf_true : ∀ {ps : List (Nat × Nat)} {a k : Nat}, pairOf ps a = some (k, true) →
    ∃ p, ps[k]? = some p ∧ p.1 = a
  | [], _, _, h => by simp [pairOf] at h
  | p :: ps, a, k, h => by
    simp only [pairOf] at h
    by_cases h1 : (p.1 == a) = true
    · rw [ite_t h1] at h; cases h; exact ⟨p, rfl, by simpa using h1⟩
    · rw [ite_f h1] at h
      by_cases h2 : (p.2 == a) = true
      · rw [ite_t h2] at h; cases h
      · rw [ite_f h2] at h
        obtain ⟨⟨k', b⟩, h₁, h₂⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at h₂
        obtain ⟨rfl, rfl⟩ := h₂
        obtain ⟨q, hq, hq'⟩ := pairOf_true h₁
        exact ⟨q, by simpa using hq, hq'⟩

theorem pairOf_false : ∀ {ps : List (Nat × Nat)} {a k : Nat}, pairOf ps a = some (k, false) →
    ∃ p, ps[k]? = some p ∧ p.2 = a
  | [], _, _, h => by simp [pairOf] at h
  | p :: ps, a, k, h => by
    simp only [pairOf] at h
    by_cases h1 : (p.1 == a) = true
    · rw [ite_t h1] at h; cases h
    · rw [ite_f h1] at h
      by_cases h2 : (p.2 == a) = true
      · rw [ite_t h2] at h; cases h; exact ⟨p, rfl, by simpa using h2⟩
      · rw [ite_f h2] at h
        obtain ⟨⟨k', b⟩, h₁, h₂⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at h₂
        obtain ⟨rfl, rfl⟩ := h₂
        obtain ⟨q, hq, hq'⟩ := pairOf_false h₁
        exact ⟨q, by simpa using hq, hq'⟩

theorem pairOf_none : ∀ {ps : List (Nat × Nat)} {a : Nat}, pairOf ps a = none →
    ∀ p ∈ ps, p.1 ≠ a ∧ p.2 ≠ a
  | [], _, _, p, hp => by cases hp
  | q :: ps, a, h, p, hp => by
    simp only [pairOf] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h₁ h₂
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨fun e => h₁ (by simp [e]), fun e => h₂ (by simp [e])⟩
        · exact pairOf_none (Option.map_eq_none_iff.1 h) p hp

section
variable {ps : List (Nat × Nat)} {L' : List Val}

theorem Ab_mono (hL : ∀ v ∈ L, v ∈ L') {t : CTop} {v : Val} (h : Ab ps L gl t v) :
    Ab ps L' gl t v := by
  cases t <;> simp only [Ab] at h ⊢ <;>
    first | exact hL _ h | exact ⟨hL _ h.1, h.2⟩ | exact h

theorem SoundF_mono (hL : ∀ v ∈ L, v ∈ L') {F : List Fact} (h : SoundF ps L gl lc F) :
    SoundF ps L' gl lc F := by
  intro f hf
  have h₁ := h f hf
  cases f <;> simp only [FactSem] at h₁ ⊢
  · exact h₁
  · exact h₁
  · obtain ⟨p, hp, v, hv, hvL, hother⟩ := h₁
    exact ⟨p, hp, v, hv, hL _ hvL, hother⟩
  · obtain ⟨v, hv, hvL, hother⟩ := h₁
    exact ⟨v, hv, hL _ hvL, hother⟩

theorem Sigma_mono (hL : ∀ v ∈ L, v ∈ L') (h : Sigma ps L gl) : Sigma ps L' gl := by
  intro p hp hon
  obtain ⟨v, hv, hvL⟩ := h p hp hon
  exact ⟨v, hv, hL _ hvL⟩

theorem SoundF_nil : SoundF ps L gl lc [] := fun _ h => by cases h

theorem SoundF_sub {F F' : List Fact} (hs : ∀ f ∈ F', f ∈ F) (h : SoundF ps L gl lc F) :
    SoundF ps L gl lc F' := fun f hf => h f (hs f hf)

theorem SoundF_filter {F : List Fact} (p : Fact → Bool) (h : SoundF ps L gl lc F) :
    SoundF ps L gl lc (F.filter p) := SoundF_sub (fun _ hf => (List.mem_filter.1 hf).1) h

theorem SoundF_cons {f : Fact} {F : List Fact} (h₁ : FactSem ps L gl lc f) (h : SoundF ps L gl lc F) :
    SoundF ps L gl lc (f :: F) := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact h₁
  · exact h g hg

end

end Silmaril.Wasm.Resource.Client
