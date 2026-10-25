module

public import Silmaril.Wasm.SingleThreaded.Thread
public import Silmaril.Wasm.SingleThreaded.CalloutSub

@[expose] public section

/-! # Typing of callout resumption (helpers for `Ctx.fill_callout_typed`)

Replacing the host-call redex `val* (REF.FUNC_ADDR a) (CALL_REF yy)` inside an
evaluation context `E` by values of the callee's result type preserves typing.

The proof is structural on the typing derivations, re-using every node of the
original derivation outside the redex, so that no regularity (well-formedness
of intermediate stacks) is needed:

* `co_vs1`, `co_vs2`: splitting typings of value sequences;
* `co_top`: the redex at the top of a sequence `vals W ++ yy :: R`, given a
  base fact `HB` about the typings of `yy` itself;
* `co_one`: replacing one administrative instruction in a sequence;
* `co_fill`: induction on the evaluation context (label, handler, frame);
* `co_callRef_base`: the base fact, from the function-subtyping lemma `co_K`.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Lists -/

theorem co_f2_split_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m : List β}, List.Forall₂ R (l₁ ++ l₂) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons hab h => by
    obtain ⟨m₁, m₂, rfl, h₁, h₂⟩ := co_f2_split_left h
    exact ⟨_ :: m₁, m₂, rfl, .cons hab h₁, h₂⟩

theorem co_f2_split_right {α β : Type} {R : α → β → Prop} {l : List α} {m₁ m₂ : List β}
    (h : List.Forall₂ R l (m₁ ++ m₂)) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ :=
  ⟨_, _, (List.take_append_drop _ _).symm, List.forall₂_take_append _ _ _ h,
    List.forall₂_drop_append _ _ _ h⟩

theorem co_valsTo_sub {s : Store H} {Δ : TypeCtx} :
    ∀ {vs : List Val} {ts ts' : List CValType}, ValsTo s Δ vs ts → ResultSub Δ ts ts' →
      ValsTo s Δ vs ts'
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons ⟨t₀, hv, hc⟩ h, .cons hs hs' =>
    .cons ⟨t₀, hv, .tail hc hs⟩ (co_valsTo_sub h hs')

theorem co_vals_eq_nil {W : List Val} (h : ([] : List Admin) = vals W) : W = [] := by
  cases W <;> simp_all [vals]

theorem co_vals_single {W : List Val} {a : Admin} (h : [a] = vals W) :
    ∃ w, W = [w] ∧ a = w.toAdmin := by
  match W, h with
  | [w], h => simp only [vals, List.map_cons, List.map_nil, List.cons.injEq] at h
              exact ⟨w, rfl, h.1⟩

theorem co_vals_cons {W : List Val} {a : Admin} {as : List Admin} (h : a :: as = vals W) :
    ∃ w W', W = w :: W' ∧ a = w.toAdmin ∧ as = vals W' := by
  match W, h with
  | w :: W', h => simp only [vals, List.map_cons, List.cons.injEq] at h
                  exact ⟨w, W', rfl, h.1, h.2⟩

theorem co_vals_append {W : List Val} {as₁ as₂ : List Admin} (h : as₁ ++ as₂ = vals W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ as₁ = vals W₁ ∧ as₂ = vals W₂ := by
  obtain ⟨W₁, W₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp h.symm
  exact ⟨W₁, W₂, rfl, e₁.symm, e₂.symm⟩

/-- Split `as₁ ++ as₂ = vals W ++ yy :: R` around `yy`. -/
theorem co_split3 {W : List Val} {yy : Admin} {R as₁ as₂ : List Admin}
    (e : as₁ ++ as₂ = vals W ++ yy :: R) :
    (∃ R₁, as₁ = vals W ++ yy :: R₁ ∧ R = R₁ ++ as₂) ∨
      (∃ W₁ W₂, W = W₁ ++ W₂ ∧ as₁ = vals W₁ ∧ as₂ = vals W₂ ++ yy :: R) := by
  rcases List.append_eq_append_iff.mp e with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · obtain ⟨W₁, W₂, rfl, e₁, e₂⟩ := co_vals_append h1.symm
    exact .inr ⟨W₁, W₂, rfl, e₁, by rw [h2, e₂]⟩
  · rcases c' with _ | ⟨c, c''⟩
    · simp only [List.append_nil, List.nil_append] at h1 h2
      exact .inr ⟨W, [], by simp, h1, by simp [h2]⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact .inl ⟨c'', h1, rfl⟩

theorem co_rok_left {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ a := fun t ht => h t (List.mem_append_left _ ht)

/-! ## Empty sequences and value sequences -/

theorem co_nil_len {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) : L = [] → it.params.length = it.results.length := by
  refine AdminsOk.rec' (motive := fun C L it => L = [] → it.params.length = it.results.length)
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C _; rfl
  · intro C a it _ e; cases e
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ ih₂ e
    obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp e
    exact (ih₁ e₁).trans (ih₂ e₂)
  · intro C a as _ _ _ _ _ _ _ _ _ e; cases e
  · intro C as it it' _ hs _ ih e
    rw [hs.1.length_eq, ← hs.2.1.length_eq]; exact ih e
  · intro C as ts t₁ t₂ xs _ _ ih e
    simp [ih e]

/-- Value sequences consuming (typed) values below them: the consumed prefix `Z`
of type `tvs` and the pushed values `W` end up at the top of the result stack;
what is below is related by a typing of the empty sequence. -/
theorem co_vs1 {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) :
    ∀ W, L = vals W → ∀ A' tvs Z, it.params = A' ++ tvs → ValsTo s C.toTypeCtx Z tvs →
      ∃ A'' tvs'', it.results = A'' ++ tvs'' ∧ ValsTo s C.toTypeCtx (Z ++ W) tvs'' ∧
        AdminsOk s C [] ⟨A', it.inits, A''⟩ := by
  refine AdminsOk.rec' (motive := fun C L it => ∀ W, L = vals W → ∀ A' tvs Z,
      it.params = A' ++ tvs → ValsTo s C.toTypeCtx Z tvs →
      ∃ A'' tvs'', it.results = A'' ++ tvs'' ∧ ValsTo s C.toTypeCtx (Z ++ W) tvs'' ∧
        AdminsOk s C [] ⟨A', it.inits, A''⟩) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C W e A' tvs Z hp hz
    have hW := co_vals_eq_nil e
    subst hW
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
    cases hz
    exact ⟨[], [], rfl, .nil, .nil⟩
  · intro C a it ha W e A' tvs Z hp hz
    obtain ⟨w, rfl, rfl⟩ := co_vals_single e
    obtain ⟨hp', t, hv, hr⟩ := AdminOk.toAdmin_inv ha
    have hi := AdminOk.inits_of_val ha (Admin.val?_toAdmin w)
    rw [hp'] at hp
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
    cases hz
    refine ⟨[], [t], by simp [hr], .cons ⟨t, hv, .refl⟩ .nil, ?_⟩
    rw [hi]; exact .nil
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ W e A' tvs Z hp hz
    obtain ⟨W₁, W₂, rfl, e₁, e₂⟩ := co_vals_append e
    obtain ⟨A₁, tv₁, hr₁, hz₁, hn₁⟩ := ih₁ W₁ e₁ A' tvs Z hp hz
    have hz₁' : ValsTo s (C.initLocals xs₁).toTypeCtx (Z ++ W₁) tv₁ := by simpa using hz₁
    obtain ⟨A₂, tv₂, hr₂, hz₂, hn₂⟩ := ih₂ W₂ e₂ A₁ tv₁ (Z ++ W₁) hr₁ hz₁'
    refine ⟨A₂, tv₂, hr₂, by simpa using hz₂, ?_⟩
    simpa using AdminsOk.seq hn₁ hx hn₂
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs ih W e A' tvs Z hp hz
    obtain ⟨w, W', rfl, rfl, e'⟩ := co_vals_cons e
    obtain ⟨hp', t, hv, hr⟩ := AdminOk.toAdmin_inv ha
    have hi := AdminOk.inits_of_val ha (Admin.val?_toAdmin w)
    simp only at hp' hr hi
    subst hp' hr hi
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
    cases hz
    obtain ⟨A'', tv'', hr'', hz'', hn''⟩ :=
      ih W' e' [] [t] [w] rfl (by simpa using (List.Forall₂.cons ⟨t, hv, .refl⟩ .nil :
        ValsTo s C.toTypeCtx [w] [t]))
    exact ⟨A'', tv'', hr'', by simpa using hz'', by simpa using hn''⟩
  · intro C as it it' h hsub hok ih W e A' tvs Z hp hz
    obtain ⟨hps, hrs, hin⟩ := hsub
    rw [hp] at hps
    obtain ⟨B, tvB, hB, hAB, htv⟩ := co_f2_split_left hps
    obtain ⟨A'', tv'', hr, hz', hn⟩ := ih W e B tvB Z hB (co_valsTo_sub hz htv)
    rw [hr] at hrs
    obtain ⟨A''', tv''', hr', hA, htv'⟩ := co_f2_split_left hrs
    refine ⟨A''', tv''', hr', co_valsTo_sub hz' htv', ?_⟩
    refine AdminsOk.sub hn ⟨hAB, hA, hin⟩ ⟨?_, ?_, hok.2.2⟩
    · exact co_rok_left (hp ▸ hok.1)
    · exact co_rok_left (hr' ▸ hok.2.1)
  · intro C as F t₁ t₂ xs h hF ih W e A' tvs Z hp hz
    have hp : F ++ t₁ = A' ++ tvs := hp
    rcases List.append_eq_append_iff.mp hp with ⟨A₀, rfl, rfl⟩ | ⟨F₂, rfl, rfl⟩
    · obtain ⟨A'', tv'', hr, hz', hn⟩ := ih W e A₀ tvs Z rfl hz
      exact ⟨F ++ A'', tv'', by simp only at hr; simp [hr], hz', AdminsOk.frame hn hF⟩
    · obtain ⟨Z₁, Z₂, rfl, hz₁, hz₂⟩ := co_f2_split_right hz
      obtain ⟨A'', tv'', hr, hz', hn⟩ := ih W e [] t₁ Z₂ rfl hz₂
      have hl := co_nil_len hn rfl
      have hA : A'' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst hA
      refine ⟨A', F₂ ++ tv'', by simp only at hr; simp [hr], ?_, ?_⟩
      · simpa [List.append_assoc] using forall₂_append hz₁ hz'
      · simpa using AdminsOk.frame hn (co_rok_left hF)

/-- A value sequence `U ++ W` splits into a typing of `vals U` and the (chains
of) types of `W` at the top. -/
theorem co_vs2 {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) :
    ∀ U W, L = vals (U ++ W) →
      ∃ A'' tvs'', it.results = A'' ++ tvs'' ∧ ValsTo s C.toTypeCtx W tvs'' ∧
        AdminsOk s C (vals U) ⟨it.params, it.inits, A''⟩ := by
  have key : ∀ {C L it}, AdminsOk s C L it → ∀ W, L = vals W →
      ∃ A'' tvs'', it.results = A'' ++ tvs'' ∧ ValsTo s C.toTypeCtx W tvs'' ∧
        AdminsOk s C (vals []) ⟨it.params, it.inits, A''⟩ := by
    intro C L it h W e
    obtain ⟨A'', tv'', hr, hz, hn⟩ := co_vs1 h W e it.params [] [] (by simp) .nil
    exact ⟨A'', tv'', hr, by simpa using hz, hn⟩
  refine AdminsOk.rec' (motive := fun C L it => ∀ U W, L = vals (U ++ W) →
      ∃ A'' tvs'', it.results = A'' ++ tvs'' ∧ ValsTo s C.toTypeCtx W tvs'' ∧
        AdminsOk s C (vals U) ⟨it.params, it.inits, A''⟩) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C U W e
    have hW := co_vals_eq_nil e
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hW
    exact ⟨[], [], rfl, .nil, .nil⟩
  · intro C a it ha U W e
    rcases U with _ | ⟨u, U'⟩
    · simpa using key (.single ha) W (by simpa using e)
    · obtain ⟨w, hw, rfl⟩ := co_vals_single e
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at hw
      obtain ⟨rfl, rfl, rfl⟩ := hw
      exact ⟨it.results, [], by simp, .nil, by simpa [vals] using AdminsOk.single ha⟩
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ U W e
    obtain ⟨V₁, V₂, hV, e₁, e₂⟩ := co_vals_append e
    rcases List.append_eq_append_iff.mp hV with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · obtain ⟨A₁, tv₁, hr₁, hz₁, hn₁⟩ := ih₁ U a' e₁
      have hz₁' : ValsTo s (C.initLocals xs₁).toTypeCtx a' tv₁ := by simpa using hz₁
      obtain ⟨A₂, tv₂, hr₂, hz₂, hn₂⟩ := co_vs1 h₂ V₂ e₂ A₁ tv₁ a' hr₁ hz₁'
      refine ⟨A₂, tv₂, hr₂, by simpa using hz₂, ?_⟩
      simpa using AdminsOk.seq hn₁ hx hn₂
    · obtain ⟨A'', tv'', hr, hz, hn⟩ := ih₂ c' W e₂
      refine ⟨A'', tv'', hr, by simpa using hz, ?_⟩
      have := AdminsOk.seq (e₁ ▸ h₁) hx hn
      simpa [vals_append] using this
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs ih U W e
    rcases U with _ | ⟨u, U'⟩
    · simpa using key (.cons ha hx hs) W (by simpa using e)
    · obtain ⟨w, W', hw, rfl, e'⟩ := co_vals_cons e
      simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨A'', tv'', hr, hz, hn⟩ := ih U' W e'
      refine ⟨A'', tv'', hr, by simpa using hz, ?_⟩
      exact AdminsOk.cons ha hx hn
  · intro C as it it' h hsub hok ih U W e
    obtain ⟨A'', tv'', hr, hz, hn⟩ := ih U W e
    obtain ⟨hps, hrs, hin⟩ := hsub
    rw [hr] at hrs
    obtain ⟨A''', tv''', hr', hA, htv'⟩ := co_f2_split_left hrs
    refine ⟨A''', tv''', hr', co_valsTo_sub hz htv', ?_⟩
    refine AdminsOk.sub hn ⟨hps, hA, hin⟩ ⟨hok.1, ?_, hok.2.2⟩
    exact co_rok_left (hr' ▸ hok.2.1)
  · intro C as F t₁ t₂ xs h hF ih U W e
    obtain ⟨A'', tv'', hr, hz, hn⟩ := ih U W e
    exact ⟨F ++ A'', tv'', by simp only at hr; simp [hr], hz, AdminsOk.frame hn hF⟩


/-! ## The redex at the top of a sequence -/

theorem co_getLast {pre Q X Z₁ Z₂ : List Val} {r : Val} (hX : pre ++ Q = X ++ [])
    (hZ : X = Z₁ ++ Z₂) (hne : Z₂ ≠ []) (hQ : Q.getLast? = some r) : Z₂.getLast? = some r := by
  have hQne : Q ≠ [] := by intro h; simp [h] at hQ
  simp only [List.append_nil] at hX
  have h1 : (Z₁ ++ Z₂).getLast? = Z₂.getLast? := List.getLast?_append_of_ne_nil _ hne
  have h2 : (pre ++ Q).getLast? = Q.getLast? := List.getLast?_append_of_ne_nil _ hQne
  rw [← h1, ← hZ, ← hX, h2, hQ]

/-- The induction hypothesis for a sequence `vals W ++ yy :: R` whose values `W`
are a suffix of `pre ++ Q` (the redex is `vals Q ++ [yy]`, to be replaced by
`vals vs`):
* the redex has an operand;
* operand count: at least `Q` operands are available;
* (`W` extends into `pre`) the replaced sequence has the same type;
* (`W` is inside `Q`; the consumed operands `Z` are on the stack) the
  replacement, typed without the consumed operands. -/
def CoMot (s s' : Store H) (pre Q vs : List Val) (yy : Admin) (CI : Context → Prop)
    (C : Context) (L : List Admin) (it : InstrType) : Prop :=
  CI C → ∀ W R, L = vals W ++ yy :: R →
    (1 ≤ it.params.length + W.length) ∧
    (∀ X Z₁ Z₂ A' tvs, pre ++ Q = X ++ W → X = Z₁ ++ Z₂ → it.params = A' ++ tvs →
      ValsTo s C.toTypeCtx Z₂ tvs → (Z₂ ≠ [] ∨ W ≠ []) →
      Q.length ≤ A'.length + Z₂.length + W.length) ∧
    (∀ U U', pre = U ++ U' → W = U' ++ Q → AdminsOk s' C (vals U' ++ vals vs ++ R) it) ∧
    (∀ Z A' tvs, Q = Z ++ W → it.params = A' ++ tvs → ValsTo s C.toTypeCtx Z tvs →
      AdminsOk s' C (vals vs ++ R) ⟨A', it.inits, it.results⟩)

theorem co_top {s s' : Store H} (hS : StoreOk s) (hE : Extend s s') {pre Q vs : List Val}
    {r : Val} {yy : Admin} (hQ : Q.getLast? = some r)
    (CI : Context → Prop) (hCI : ∀ C xs, CI C → CI (C.initLocals xs))
    (HB0 : ∀ C it₀, AdminOk s C yy it₀ → 1 ≤ it₀.params.length)
    (HB : ∀ C it₀ A' tvs Z₂, CI C → AdminOk s C yy it₀ → it₀.params = A' ++ tvs →
      ValsTo s C.toTypeCtx Z₂ tvs → Z₂.getLast? = some r →
      it₀.inits = [] ∧ Q.length = A'.length + Z₂.length ∧
        AdminsOk s' C (vals vs) ⟨[], [], it₀.results⟩)
    {C : Context} {L : List Admin} {it : InstrType} (h : AdminsOk s C L it) :
    CoMot s s' pre Q vs yy CI C L it := by
  have hQne : Q ≠ [] := by intro h; simp [h] at hQ
  refine AdminsOk.rec' (motive := fun C L it => CoMot s s' pre Q vs yy CI C L it)
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · -- nil
    intro C _ W R e
    have := congrArg List.length e
    simp at this
  · -- single
    intro C a it ha hC W R e
    obtain ⟨rfl, rfl, rfl⟩ : W = [] ∧ a = yy ∧ R = [] := by
      rcases W with _ | ⟨w, W⟩
      · simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at e
        exact ⟨rfl, e.1, e.2.symm⟩
      · have := congrArg List.length e
        simp at this
    refine ⟨by simpa using HB0 C it ha, ?_, ?_, ?_⟩
    · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
      have hne' : Z₂ ≠ [] := by simpa using hne
      obtain ⟨-, hlen, -⟩ := HB C it A' tvs Z₂ hC ha hp hz (co_getLast hX hZ hne' hQ)
      simp; omega
    · intro U U' _ hW
      exact absurd (List.append_eq_nil_iff.mp hW.symm).2 hQne
    · intro Z A' tvs hZ hp hz
      simp only [List.append_nil] at hZ
      subst hZ
      obtain ⟨hi, hlen, hv⟩ := HB C it A' tvs Q hC ha hp hz hQ
      have : A' = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [hi]; simpa using hv
  · -- seq
    intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ hC W R e
    have hC' := hCI C xs₁ hC
    rcases co_split3 e with ⟨R₁, e₁, rfl⟩ | ⟨W₁, W₂, rfl, e₁, e₂⟩
    · obtain ⟨L1, L2, O1, O2⟩ := ih₁ hC W R₁ e₁
      have h₂' := AdminsOk.extend hS hE h₂
      refine ⟨L1, L2, ?_, ?_⟩
      · intro U U' hpre hW
        have := AdminsOk.seq (O1 U U' hpre hW) hx h₂'
        simpa [List.append_assoc] using this
      · intro Z A' tvs hZ hp hz
        simpa [List.append_assoc] using AdminsOk.seq (O2 Z A' tvs hZ hp hz) hx h₂'
    · subst e₁
      obtain ⟨L1, L2, O1, O2⟩ := ih₂ hC' W₂ R e₂
      refine ⟨?_, ?_, ?_, ?_⟩
      · obtain ⟨A'', tv'', hr, hz, hn⟩ := co_vs1 h₁ W₁ rfl t₁ [] [] (by simp) .nil
        have hl := co_nil_len hn rfl
        have hl2 := hz.length_eq
        simp only at hr hl hl2 L1 ⊢
        subst hr
        simp at L1 hl hl2 ⊢; omega
      · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
        obtain ⟨A'', tv'', hr, hz', hn⟩ := co_vs1 h₁ W₁ rfl A' tvs Z₂ hp hz
        have hl := co_nil_len hn rfl
        have hc : Z₂ ++ W₁ ≠ [] ∨ W₂ ≠ [] := by
          rcases hne with hne | hne
          · exact .inl (by simp [hne])
          · by_cases hw : W₂ = []
            · subst hw; exact .inl (by intro h; apply hne; simp_all)
            · exact .inr hw
        have := L2 (X ++ W₁) Z₁ (Z₂ ++ W₁) A'' tv'' (by simpa [List.append_assoc] using hX)
          (by simp [hZ]) hr (by simpa using hz') hc
        simp at hl this ⊢; omega
      · intro U U' hpre hW
        rcases List.append_eq_append_iff.mp hW with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hQ'⟩
        · have := O1 (U ++ W₁) a' (by simp [hpre]) rfl
          have := AdminsOk.seq (AdminsOk.extend hS hE h₁) hx this
          simpa [List.append_assoc] using this
        · obtain ⟨A'', tv'', hr, hz, hn⟩ := co_vs2 h₁ U' c' rfl
          have := O2 c' A'' tv'' hQ' hr (by simpa using hz)
          have := AdminsOk.seq (AdminsOk.extend hS hE hn) hx this
          simpa [List.append_assoc] using this
      · intro Z A' tvs hZ hp hz
        obtain ⟨A'', tv'', hr, hz', hn⟩ := co_vs1 h₁ W₁ rfl A' tvs Z hp hz
        have := O2 (Z ++ W₁) A'' tv'' (by simpa [List.append_assoc] using hZ) hr
          (by simpa using hz')
        have := AdminsOk.seq (AdminsOk.extend hS hE hn) hx this
        simpa using this
  · -- cons
    intro C x as t₁ t₂ t₃ xs₁ xs₂ ha hx hs ih hC W R e
    rcases W with _ | ⟨w, W'⟩
    · simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨by simpa using HB0 C _ ha, ?_, ?_, ?_⟩
      · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
        have hne' : Z₂ ≠ [] := by simpa using hne
        obtain ⟨-, hlen, -⟩ := HB C _ A' tvs Z₂ hC ha hp hz (co_getLast hX hZ hne' hQ)
        simp; omega
      · intro U U' _ hW
        exact absurd (List.append_eq_nil_iff.mp hW.symm).2 hQne
      · intro Z A' tvs hZ hp hz
        simp only [List.append_nil] at hZ
        subst hZ
        obtain ⟨hi, hlen, hv⟩ := HB C _ A' tvs Q hC ha hp hz hQ
        have : A' = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        simp only at hi
        subst hi
        exact AdminsOk.seq hv (fun _ h => by cases h) (AdminsOk.extend hS hE hs)
    · obtain ⟨rfl, e'⟩ : x = w.toAdmin ∧ as = vals W' ++ yy :: R := by
        simpa [vals] using e
      obtain ⟨hp', tw, hv, hr⟩ := AdminOk.toAdmin_inv ha
      have hi := AdminOk.inits_of_val ha (Admin.val?_toAdmin w)
      simp only at hp' hr hi
      subst hp' hr hi
      obtain ⟨L1, L2, O1, O2⟩ := ih (hCI C [] hC) W' R e'
      have hw : ValsTo s C.toTypeCtx [w] [tw] := .cons ⟨tw, hv, .refl⟩ .nil
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp at L1 ⊢
      · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
        cases hz
        have := L2 (X ++ [w]) X [w] [] [tw] (by simpa using hX) rfl rfl hw (.inl (by simp))
        simp at this ⊢; omega
      · intro U U' hpre hW
        rcases U' with _ | ⟨u, U''⟩
        · have hQ' : Q = [w] ++ W' := by simpa using hW.symm
          have := O2 [w] [] [tw] hQ' rfl hw
          simpa [vals] using this
        · simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, rfl⟩ := hW
          have := O1 (U ++ [w]) U'' (by simp [hpre]) rfl
          have := AdminsOk.cons (AdminOk.extend_aux hS hE ha) (fun _ h => by cases h) this
          simpa [vals] using this
      · intro Z A' tvs hZ hp hz
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
        cases hz
        have := O2 [w] [] [tw] (by simpa using hZ) rfl hw
        simpa using this
  · -- sub
    intro C L it it' h hsub hok ih hC W R e
    obtain ⟨L1, L2, O1, O2⟩ := ih hC W R e
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsub.1.length_eq]; exact L1
    · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
      have hps := hsub.1
      rw [hp] at hps
      obtain ⟨B, tvB, hB, hAB, htv⟩ := co_f2_split_left hps
      have := L2 X Z₁ Z₂ B tvB hX hZ hB (co_valsTo_sub hz htv) hne
      rw [← hAB.length_eq] at this; exact this
    · intro U U' hpre hW
      exact AdminsOk.sub (O1 U U' hpre hW) hsub hok
    · intro Z A' tvs hZ hp hz
      obtain ⟨hps, hrs, hin⟩ := hsub
      rw [hp] at hps
      obtain ⟨B, tvB, hB, hAB, htv⟩ := co_f2_split_left hps
      exact AdminsOk.sub (O2 Z B tvB hZ hB (co_valsTo_sub hz htv)) ⟨hAB, hrs, hin⟩
        ⟨co_rok_left (hp ▸ hok.1), hok.2.1, hok.2.2⟩
  · -- frame
    intro C L F t₁ t₂ xs h hF ih hC W R e
    obtain ⟨L1, L2, O1, O2⟩ := ih hC W R e
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp at L1 ⊢; omega
    · intro X Z₁ Z₂ A' tvs hX hZ hp hz hne
      have hp : F ++ t₁ = A' ++ tvs := hp
      rcases List.append_eq_append_iff.mp hp with ⟨A₀, rfl, rfl⟩ | ⟨F₂, rfl, rfl⟩
      · have := L2 X Z₁ Z₂ A₀ tvs hX hZ rfl hz hne
        simp at this ⊢; omega
      · obtain ⟨Za, Zb, rfl, hza, hzb⟩ := co_f2_split_right hz
        by_cases hc : Zb ≠ [] ∨ W ≠ []
        · have := L2 X (Z₁ ++ Za) Zb [] t₁ hX (by simp [hZ]) rfl hzb hc
          simp at this ⊢; omega
        · push Not at hc
          obtain ⟨rfl, rfl⟩ := hc
          have := hzb.length_eq
          simp at L1 this; omega
    · intro U U' hpre hW
      exact AdminsOk.frame (O1 U U' hpre hW) hF
    · intro Z A' tvs hZ hp hz
      have hp : F ++ t₁ = A' ++ tvs := hp
      rcases List.append_eq_append_iff.mp hp with ⟨A₀, rfl, rfl⟩ | ⟨F₂, rfl, rfl⟩
      · exact AdminsOk.frame (O2 Z A₀ tvs hZ rfl hz) hF
      · obtain ⟨Za, Zb, rfl, hza, hzb⟩ := co_f2_split_right hz
        by_cases hF₂ : F₂ = []
        · subst hF₂
          have hza' : Za = [] := by cases hza; rfl
          subst hza'
          simpa using AdminsOk.frame (O2 Zb [] t₁ (by simpa using hZ) rfl hzb) hF
        · exfalso
          have hl1 := hza.length_eq
          have hl2 := hzb.length_eq
          have hFl : 0 < F₂.length := List.length_pos_iff.mpr hF₂
          by_cases hc : Zb ≠ [] ∨ W ≠ []
          · have := L2 (pre ++ Za ++ Zb) (pre ++ Za) Zb [] t₁ (by simp [hZ]) rfl rfl hzb hc
            have hQl : Q.length = Za.length + Zb.length + W.length := by rw [hZ]; simp; omega
            simp at this; omega
          · push Not at hc
            obtain ⟨rfl, rfl⟩ := hc
            simp at L1 hl2; omega

/-! ## One administrative instruction -/

theorem co_one {s s' : Store H} (hS : StoreOk s) (hE : Extend s s') {x x' : Admin}
    (CI : Context → Prop) (hCI : ∀ C xs, CI C → CI (C.initLocals xs))
    (hrep : ∀ C it, CI C → AdminOk s C x it → AdminOk s' C x' it)
    {C : Context} {L : List Admin} {it : InstrType} (h : AdminsOk s C L it) :
    CI C → ∀ X Y, L = X ++ x :: Y → AdminsOk s' C (X ++ x' :: Y) it := by
  refine AdminsOk.rec' (motive := fun C L it =>
      CI C → ∀ X Y, L = X ++ x :: Y → AdminsOk s' C (X ++ x' :: Y) it) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C _ X Y e
    have := congrArg List.length e
    simp at this
  · intro C a it ha hC X Y e
    rcases X with _ | ⟨b, X⟩
    · simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact .single (hrep C it hC ha)
    · have := congrArg List.length e
      simp at this
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ hC X Y e
    rcases List.append_eq_append_iff.mp e with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
    · have := AdminsOk.seq (AdminsOk.extend hS hE h₁) hx (ih₂ (hCI C xs₁ hC) a' Y h2)
      simpa [List.append_assoc] using this
    · rcases c' with _ | ⟨c, c''⟩
      · simp only [List.nil_append] at h2
        have := AdminsOk.seq (AdminsOk.extend hS hE h₁) hx (ih₂ (hCI C xs₁ hC) [] Y h2.symm)
        simpa using this
      · simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        have := AdminsOk.seq (ih₁ hC X c'' rfl) hx (AdminsOk.extend hS hE h₂)
        simpa [List.append_assoc] using this
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs ih hC X Y e
    rcases X with _ | ⟨b, X⟩
    · simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact .cons (hrep C _ hC ha) hx (AdminsOk.extend hS hE hs)
    · simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      exact .cons (AdminOk.extend_aux hS hE ha) hx (ih (hCI C xs₁ hC) X Y e)
  · intro C as it it' h hsub hok ih hC X Y e
    exact AdminsOk.sub (ih hC X Y e) hsub hok
  · intro C as F t₁ t₂ xs h hF ih hC X Y e
    exact AdminsOk.frame (ih hC X Y e) hF

/-! ## Evaluation contexts -/

/-- The context invariant: the defined types of the context are valid (closed). -/
def CoCI (C : Context) : Prop := ∀ d ∈ C.types, TyOk {} d

theorem CoCI.initLocals {C : Context} (h : CoCI C) (xs : List Nat) : CoCI (C.initLocals xs) := by
  have e : (C.initLocals xs).types = C.types := congrArg TypeCtx.types (C.initLocals_toTypeCtx xs)
  intro d hd; rw [e] at hd; exact h d hd

theorem CoCI.withLabel {C : Context} (h : CoCI C) (ts : List CValType) : CoCI (C.withLabel ts) :=
  h

theorem CoCI.ofFrame {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) : CoCI C := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk htypes => exact htypes

theorem co_fill {s s' : Store H} (hS : StoreOk s) (hE : Extend s s') {X₀ Y₀ : List Admin}
    (htop : ∀ C it pre rest, CoCI C → AdminsOk s C (vals pre ++ X₀ ++ rest) it →
      AdminsOk s' C (vals pre ++ Y₀ ++ rest) it) :
    ∀ (E : Ctx) (C : Context) (it : InstrType), CoCI C → AdminsOk s C (E.fill X₀) it →
      AdminsOk s' C (E.fill Y₀) it
  | .top pre rest, C, it, hC, h => htop C it pre rest hC h
  | .label pre n cont E rest, C, it, hC, h => by
    simp only [Ctx.fill] at h ⊢
    have h' : AdminsOk s C (vals pre ++ Admin.label n cont (E.fill X₀) :: rest) it := by
      simpa using h
    have := co_one hS hE (x := .label n cont (E.fill X₀)) (x' := .label n cont (E.fill Y₀))
      CoCI (fun C xs hC => hC.initLocals xs) (fun C it hC ha => by
        generalize hb : E.fill X₀ = body at ha
        cases ha with
        | label hn hc hb' =>
          subst hb
          exact .label hn (AdminsOk.extend hS hE hc)
            (co_fill hS hE htop E _ _ (hC.withLabel _) hb'))
      h' hC (vals pre) rest rfl
    simpa using this
  | .handler pre n cs E rest, C, it, hC, h => by
    simp only [Ctx.fill] at h ⊢
    have h' : AdminsOk s C (vals pre ++ Admin.handler n cs (E.fill X₀) :: rest) it := by
      simpa using h
    have := co_one hS hE (x := .handler n cs (E.fill X₀)) (x' := .handler n cs (E.fill Y₀))
      CoCI (fun C xs hC => hC.initLocals xs) (fun C it hC ha => by
        generalize hb : E.fill X₀ = body at ha
        cases ha with
        | handler hc hb' =>
          subst hb
          exact .handler hc (co_fill hS hE htop E _ _ hC hb'))
      h' hC (vals pre) rest rfl
    simpa using this
  | .frame pre n f E rest, C, it, hC, h => by
    simp only [Ctx.fill] at h ⊢
    have h' : AdminsOk s C (vals pre ++ Admin.frame n f (E.fill X₀) :: rest) it := by
      simpa using h
    have := co_one hS hE (x := .frame n f (E.fill X₀)) (x' := .frame n f (E.fill Y₀))
      CoCI (fun C xs hC => hC.initLocals xs) (fun C it hC ha => by
        generalize hb : E.fill X₀ = body at ha
        cases ha with
        | frame hf hn hb' hok =>
          subst hb
          exact .frame (FrameOk.extend_of_storeOk hS hE hf) hn
            (co_fill hS hE htop E _ _ (fun d hd => CoCI.ofFrame hf d hd) hb') hok)
      h' hC (vals pre) rest rfl
    simpa using this

/-! ## The call itself -/

/-- **Function subtyping, as seen by `call_ref`.** A function reference whose type
is a subtype of `ref null (defHeap d)` has a function type with as many parameters
as `d`'s and results that are subtypes of `d`'s. -/
theorem co_K {s : Store H} {Δ : TypeCtx} (hΔ : ∀ d ∈ Δ.types, TyOk {} d) (hS : StoreOk s)
    {a : Nat} {fi : FuncInst H} {ps rs ps' rs' : Ty (.list .val)} {d : DefType}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hr : ValTo s Δ (.ref (.func a)) (.refT true (.defHeap d))) (hd : TyOk Δ d)
    (he' : Expand d (.func ps' rs')) :
    ps.length = ps'.length ∧ ResultSub Δ rs.toList rs'.toList :=
  co_K' hΔ hS hf he hr hd he'

theorem co_fi_ok {s : Store H} (hS : StoreOk s) {a : Nat} {fi : FuncInst H}
    (hf : s.funcs[a]? = some fi) : TyOk {} fi.type := by
  have := hS.funcs fi (List.mem_of_getElem? hf)
  cases this with
  | wasm hdt => exact hdt
  | host hdt => exact hdt

/-- The base fact about `call_ref` for `co_top`. -/
theorem co_base {s s' : Store H} (hS : StoreOk s) {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {args vs : List Val} {yy : Admin}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hyy : yy.IsCallRef)
    (hn : args.length = ps.length) (hvs : List.Forall₂ (ValOk s') vs rs.toList)
    (C : Context) (it₀ : InstrType) (A' tvs : List CValType) (Z₂ : List Val) (hC : CoCI C)
    (ha : AdminOk s C yy it₀) (hp : it₀.params = A' ++ tvs)
    (hz : ValsTo s C.toTypeCtx Z₂ tvs) (hl : Z₂.getLast? = some (Val.ref (.func a))) :
    it₀.inits = [] ∧ (args ++ [Val.ref (.func a)]).length = A'.length + Z₂.length ∧
      AdminsOk s' C (vals vs) ⟨[], [], it₀.results⟩ := by
  -- the typing of `yy`
  obtain ⟨d, ps', rs', hd, he', rfl⟩ : ∃ d ps' rs', TyOk C.toTypeCtx d ∧
      Expand d (.func ps' rs') ∧
      it₀ = ⟨ps'.toList ++ [.refT true (.defHeap d)], [], rs'.toList⟩ := by
    cases yy with
    | plain i =>
      cases i <;> simp only [Admin.IsCallRef] at hyy
      cases ha with
      | plain hi =>
        cases hi
        case callRef he' hx =>
          exact ⟨_, _, _, TyOk.of_empty _ (hC _ (List.mem_of_getElem? hx)), he', rfl⟩
        all_goals (rename_i h; cases h)
    | callRefType d =>
      cases ha with
      | callRefType hok he' => exact ⟨_, _, _, TyOk.of_empty _ hok, he', rfl⟩
    | _ => simp [Admin.IsCallRef] at hyy
  simp only at hp ⊢
  -- the reference operand
  obtain ⟨Z₀, rfl⟩ : ∃ Z₀, Z₂ = Z₀ ++ [Val.ref (.func a)] := by
    rcases List.eq_nil_or_concat Z₂ with rfl | ⟨Z₀, z, rfl⟩
    · simp at hl
    · simp at hl; subst hl; exact ⟨Z₀, by simp⟩
  obtain ⟨m₁, m₂, rfl, hz₁, hz₂⟩ := co_f2_split_left hz
  obtain ⟨t, rfl, hr⟩ : ∃ t, m₂ = [t] ∧ ValTo s C.toTypeCtx (.ref (.func a)) t := by
    cases hz₂ with
    | cons h h' => cases h'; exact ⟨_, rfl, h⟩
  have hp' : ps'.toList ++ [Ty.refT true (Ty.defHeap d)] = (A' ++ m₁) ++ [t] := by simpa using hp
  obtain ⟨hps, ht⟩ := List.append_inj' hp' rfl
  simp only [List.cons.injEq, and_true] at ht
  subst ht
  obtain ⟨hlen, hsub⟩ := co_K hC hS hf he hr hd he'
  refine ⟨trivial, ?_, ?_⟩
  · have h1 := congrArg List.length hps
    have h2 := hz₁.length_eq
    simp only [Ty.length] at hn hlen
    simp only [List.length_append, List.length_singleton] at h1 ⊢
    omega
  · have hrs : ResultOk C.toTypeCtx rs.toList := fun t ht =>
      TyOk.of_empty _ ((Expand.resultOk (co_fi_ok hS hf) he).2 t ht)
    have h1 : AdminsOk s' C (vals vs) (.plain [] rs.toList) := AdminsOk.of_vals hvs hrs
    exact AdminsOk.sub h1 ⟨.nil, hsub, fun _ h _ => by cases h⟩
      ⟨by simp [ResultOk], (Expand.func_ok hd he').2, fun _ h => by cases h⟩

theorem co_base0 {s : Store H} {C : Context} {yy : Admin} {it₀ : InstrType}
    (hyy : yy.IsCallRef) (ha : AdminOk s C yy it₀) : 1 ≤ it₀.params.length := by
  cases yy with
  | plain i =>
    cases i <;> simp only [Admin.IsCallRef] at hyy
    cases ha with
    | plain hi =>
      cases hi
      case callRef => simp
      all_goals (rename_i h; cases h)
  | callRefType d =>
    cases ha with
    | callRefType hok he' => simp
  | _ => simp [Admin.IsCallRef] at hyy

end Silmaril.Wasm.SingleThreaded
