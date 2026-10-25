module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Generic preservation for pure redexes `val* instr`

The pure reduction families (`ParametricStep`, `NumericStep`, `VectorStep`) all
rewrite a redex `vals vs ++ [.plain i]`. Typing derivations of such a redex may
interleave `Instrs_ok2/sub` and `Instrs_ok2/frame` anywhere, so preservation is
proved once here, by induction on the derivation, re-using the original `sub`
and `frame` nodes (so no transitivity of subtyping and no regularity lemma is
needed). A family only supplies the *base* case: the instruction typed by
`InstrOk` directly, applied to operands that fit its parameter types, followed
by a typed empty tail.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## A non-mutual eliminator for `AdminsOk` -/

theorem AdminsOk.rec' {s : Store H} {motive : Context → List Admin → InstrType → Prop}
    (nil : ∀ {C : Context}, motive C [] (.plain [] []))
    (single : ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → motive C [a] it)
    (seq : ∀ {C : Context} {as₁ as₂ : List Admin} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}, AdminsOk s C as₁ ⟨t₁, xs₁, t₂⟩ →
      (∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt) →
      AdminsOk s (C.initLocals xs₁) as₂ ⟨t₂, xs₂, t₃⟩ →
      motive C as₁ ⟨t₁, xs₁, t₂⟩ → motive (C.initLocals xs₁) as₂ ⟨t₂, xs₂, t₃⟩ →
      motive C (as₁ ++ as₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩)
    (cons : ∀ {C : Context} {a : Admin} {as : List Admin} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}, AdminOk s C a ⟨t₁, xs₁, t₂⟩ →
      (∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt) →
      AdminsOk s (C.initLocals xs₁) as ⟨t₂, xs₂, t₃⟩ →
      motive (C.initLocals xs₁) as ⟨t₂, xs₂, t₃⟩ → motive C (a :: as) ⟨t₁, xs₁ ++ xs₂, t₃⟩)
    (sub : ∀ {C : Context} {as : List Admin} {it it' : InstrType},
      AdminsOk s C as it → InstrTypeSub C it it' → InstrTypeOk C it' → motive C as it →
      motive C as it')
    (frame : ∀ {C : Context} {as : List Admin} {ts t₁ t₂ : List CValType} {xs : List Nat},
      AdminsOk s C as ⟨t₁, xs, t₂⟩ → ResultOk C.toTypeCtx ts → motive C as ⟨t₁, xs, t₂⟩ →
      motive C as ⟨ts ++ t₁, xs, ts ++ t₂⟩)
    {C : Context} {L : List Admin} {it : InstrType} (h : AdminsOk s C L it) : motive C L it := by
  refine AdminsOk.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun C L it _ => motive C L it) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals first
    | (intros; trivial)
    | skip
  · exact nil
  · intro C a it ha _; exact single ha
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂; exact seq h₁ hx h₂ ih₁ ih₂
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs _ ih; exact cons ha hx hs ih
  · intro C as it it' h hs hok ih; exact sub h hs hok ih
  · intro C as ts t₁ t₂ xs h hok ih; exact frame h hok ih

/-! ## Small lemmas -/

@[simp] theorem Context.initLocals_nil' (C : Context) : C.initLocals [] = C := rfl

theorem ValOk.num_inv {s : Store H} {v : Val} {nt : NumType} (h : ValOk s v (.num nt)) :
    ∃ b, v = .num ⟨nt, b⟩ := by
  generalize e : (Ty.num nt : CValType) = T at h
  cases h with
  | num w =>
    rcases w with ⟨t', b⟩
    injection e with e
    subst e
    exact ⟨b, rfl⟩
  | vec => cases e
  | ref => cases e

theorem ValOk.vec_inv {s : Store H} {v : Val} {vt : VecType} (h : ValOk s v (.vec vt)) :
    ∃ b, v = .vec b := by
  generalize e : (Ty.vec vt : CValType) = T at h
  cases h with
  | num w => cases e
  | vec b => exact ⟨b, rfl⟩
  | ref => cases e

theorem ValOk.not_botv {s : Store H} {v : Val} (h : ValOk s v .botv) : False := by
  generalize e : (Ty.botv : CValType) = T at h
  cases h <;> cases e

theorem Sub.num_inv' {Δ : TypeCtx} {a : CValType} {nt : NumType} (h : Sub Δ a (.num nt)) :
    a = .num nt ∨ a = .botv := by
  generalize e : (Ty.num nt : CValType) = T at h
  cases h <;> first | (left; cases e; rfl) | (right; rfl) | cases e

theorem Sub.vec_inv' {Δ : TypeCtx} {a : CValType} {vt : VecType} (h : Sub Δ a (.vec vt)) :
    a = .vec vt ∨ a = .botv := by
  generalize e : (Ty.vec vt : CValType) = T at h
  cases h <;> first | (left; cases e; rfl) | (right; rfl) | cases e

theorem Sub.botv_inv' {Δ : TypeCtx} {a : CValType} (h : Sub Δ a .botv) : a = .botv := by
  generalize e : (Ty.botv : CValType) = T at h
  cases h <;> first | rfl | (cases e; rfl) | cases e

/-! ## Operands fitting a parameter type -/

/-- One subsumption step whose source is well formed. -/
def SubStep (Δ : TypeCtx) (a b : CValType) : Prop := Sub Δ a b ∧ TyOk Δ a

/-- One subsumption step whose target is well formed. -/
def TgtStep (Δ : TypeCtx) (a b : CValType) : Prop := Sub Δ a b ∧ TyOk Δ b

/-- A value fits a type: its own type reaches it by a chain of subsumption steps with
well-formed targets (realised on the value side) followed by a chain with well-formed
sources (realised on the consumer side). -/
def Fits (s : Store H) (Δ : TypeCtx) (v : Val) (t : CValType) : Prop :=
  ∃ t₀ t₁, ValOk s v t₀ ∧ Relation.ReflTransGen (TgtStep Δ) t₀ t₁ ∧
    Relation.ReflTransGen (SubStep Δ) t₁ t

theorem Fits.of_valOk {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (h : ValOk s v t) :
    Fits s Δ v t := ⟨t, t, h, .refl, .refl⟩

theorem Fits.step {s : Store H} {Δ : TypeCtx} {v : Val} {a b : CValType} (h : Fits s Δ v a)
    (hs : Sub Δ a b) (ha : TyOk Δ a) : Fits s Δ v b := by
  obtain ⟨t₀, t₁, hv, hc₀, hc⟩ := h
  exact ⟨t₀, t₁, hv, hc₀, hc.tail ⟨hs, ha⟩⟩

theorem chain_down {Δ : TypeCtx} {R : CValType → CValType → Prop}
    (hR : ∀ a b, R a b → Sub Δ a b) {P : CValType → Prop}
    (hP : ∀ a b, Sub Δ a b → P b → P a) {a b : CValType}
    (h : Relation.ReflTransGen R a b) (hb : P b) : P a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head hab _ ih => exact hP _ _ (hR _ _ hab) ih

theorem numP {Δ : TypeCtx} {nt : NumType} : ∀ a b : CValType, Sub Δ a b →
    (b = .num nt ∨ b = .botv) → (a = .num nt ∨ a = .botv) := by
  intro a b hab hb
  rcases hb with rfl | rfl
  · exact Sub.num_inv' hab
  · exact .inr (Sub.botv_inv' hab)

theorem vecP {Δ : TypeCtx} {vt : VecType} : ∀ a b : CValType, Sub Δ a b →
    (b = .vec vt ∨ b = .botv) → (a = .vec vt ∨ a = .botv) := by
  intro a b hab hb
  rcases hb with rfl | rfl
  · exact Sub.vec_inv' hab
  · exact .inr (Sub.botv_inv' hab)

theorem chain_num {Δ : TypeCtx} {a : CValType} {nt : NumType}
    (h : Relation.ReflTransGen (SubStep Δ) a (.num nt)) : a = .num nt ∨ a = .botv :=
  chain_down (fun _ _ h => h.1) numP h (.inl rfl)

theorem chain_vec {Δ : TypeCtx} {a : CValType} {vt : VecType}
    (h : Relation.ReflTransGen (SubStep Δ) a (.vec vt)) : a = .vec vt ∨ a = .botv :=
  chain_down (fun _ _ h => h.1) vecP h (.inl rfl)

theorem Fits.num_inv {s : Store H} {Δ : TypeCtx} {v : Val} {nt : NumType}
    (h : Fits s Δ v (.num nt)) : ∃ b, v = .num ⟨nt, b⟩ := by
  obtain ⟨t₀, t₁, hv, hc₀, hc⟩ := h
  have h1 := chain_down (fun _ _ h => h.1) numP hc (.inl rfl)
  rcases chain_down (fun _ _ h => h.1) numP hc₀ h1 with rfl | rfl
  · exact hv.num_inv
  · exact hv.not_botv.elim

theorem Fits.vec_inv {s : Store H} {Δ : TypeCtx} {v : Val} {vt : VecType}
    (h : Fits s Δ v (.vec vt)) : ∃ b, v = .vec b := by
  obtain ⟨t₀, t₁, hv, hc₀, hc⟩ := h
  have h1 := chain_down (fun _ _ h => h.1) vecP hc (.inl rfl)
  rcases chain_down (fun _ _ h => h.1) vecP hc₀ h1 with rfl | rfl
  · exact hv.vec_inv
  · exact hv.not_botv.elim

theorem Fits.i32_inv {s : Store H} {Δ : TypeCtx} {v : Val}
    (h : Fits s Δ v Ty.i32) : ∃ b, v = .num ⟨.int .i32, b⟩ := Fits.num_inv h

theorem Fits.v128_inv {s : Store H} {Δ : TypeCtx} {v : Val}
    (h : Fits s Δ v Ty.v128) : ∃ b, v = .vec b := Fits.vec_inv h

/-! ## Administrative typing of values and the empty tail -/

/-- (Since the `throwRefInits` deviation this needs `i ≠ throw_ref`; discharged
automatically for a concrete instruction.) -/
theorem AdminOk.plain_inv {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    (h : AdminOk s C (.plain i) it) (hne : i ≠ .throwRef := by intro h; cases h) :
    InstrOk C i it := h.plain_inv_ne hne

theorem AdminOk.of_valOk {s : Store H} {C : Context} {v : Val} {t : CValType}
    (h : ValOk s v t) : AdminOk s C v.toAdmin (.plain [] [t]) := by
  cases h with
  | num w =>
    rcases w with ⟨t | t, b⟩
    · exact .plain (.numeric (.intConst t b))
    · exact .plain (.numeric (.floatConst t b))
  | vec b => exact .plain (.vector (.vecConst b))
  | ref h => exact .ref h

theorem AdminOk.val_inv {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) :
    it.params = [] ∧ it.inits = [] ∧ ∃ tv, it.results = [tv] ∧ ValOk s v tv := by
  rcases v with ⟨t | t, b⟩ | b | r
  · have hi := AdminOk.plain_inv h
    cases hi <;> (rename_i h; cases h)
    exact ⟨rfl, rfl, _, rfl, by constructor⟩
  · have hi := AdminOk.plain_inv h
    cases hi <;> (rename_i h; cases h)
    exact ⟨rfl, rfl, _, rfl, by constructor⟩
  · have hi := AdminOk.plain_inv h
    cases hi <;> (rename_i h; cases h)
    exact ⟨rfl, rfl, _, rfl, by constructor⟩
  · cases h with
    | ref hr => exact ⟨rfl, rfl, _, rfl, .ref hr⟩

theorem ResultOk.append {Δ : TypeCtx} {a b : List CValType} (ha : ResultOk Δ a)
    (hb : ResultOk Δ b) : ResultOk Δ (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem ResultOk.left {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ a := fun t ht => h t (List.mem_append_left _ ht)

theorem ResultOk.right {Δ : TypeCtx} {a b : List CValType} (h : ResultOk Δ (a ++ b)) :
    ResultOk Δ b := fun t ht => h t (List.mem_append_right _ ht)

/-- Regularity of a typed empty sequence. -/
theorem AdminsOk.nil_ok {s : Store H} {C : Context} {it : InstrType}
    (h : AdminsOk s C [] it) : InstrTypeOk C it := by
  have key : ∀ {C L it}, AdminsOk s C L it → L = [] → InstrTypeOk C it := by
    intro C L it h
    refine AdminsOk.rec' (motive := fun C L it => L = [] → InstrTypeOk C it) ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro C _; refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;> simp at hx
    · intro C a it _ e; cases e
    · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ hx _ ih₁ ih₂ e
      obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp e
      obtain ⟨h₁, -, -⟩ := ih₁ e₁
      obtain ⟨-, h₃, h₄⟩ := ih₂ e₂
      rw [Context.initLocals_toTypeCtx] at h₃
      refine ⟨h₁, h₃, fun x hx' => ?_⟩
      rcases List.mem_append.mp hx' with h | h
      · exact hx x h
      · exact Context.initLocals_exists.mp (h₄ x h)
    · intro C a as _ _ _ _ _ _ _ _ _ e; cases e
    · intro C as it it' _ _ hok _ _; exact hok
    · intro C as ts t₁ t₂ xs _ hts ih e
      obtain ⟨h₁, h₂, h₃⟩ := ih e
      exact ⟨ResultOk.append hts h₁, ResultOk.append hts h₂, h₃⟩
  exact key h rfl

/-- A value pushes its exact type on a typed tail. -/
theorem AdminsOk.val_cons {s : Store H} {C : Context} {w : Val} {tw : CValType}
    {X : List Nat} {B : List CValType} (hw : ValOk s w tw)
    (D : AdminsOk s C [] ⟨[tw], X, B⟩) : AdminsOk s C [w.toAdmin] ⟨[], X, B⟩ :=
  AdminsOk.cons (xs₁ := []) (AdminOk.of_valOk hw) (fun _ h => by cases h) D

/-- A value fitting `t` pushes `t` on a typed tail. -/
theorem AdminsOk.fits_cons {s : Store H} {C : Context} {w : Val} {t : CValType}
    {X : List Nat} {B : List CValType} (hw : Fits s C.toTypeCtx w t)
    (D : AdminsOk s C [] ⟨[t], X, B⟩) : AdminsOk s C [w.toAdmin] ⟨[], X, B⟩ := by
  obtain ⟨t₀, t₁, hv, hc₀, hc⟩ := hw
  have hok := D.nil_ok
  have key : ∀ a, Relation.ReflTransGen (SubStep C.toTypeCtx) a t →
      AdminsOk s C [] ⟨[a], X, B⟩ := by
    intro a hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl => exact D
    | head hab _ ih =>
      refine AdminsOk.sub ih ⟨.cons hab.1 .nil, ?_, ?_⟩ ⟨?_, hok.2.1, hok.2.2⟩
      · exact ResultSub.refl _ _
      · intro x hx hn; exact absurd hx hn
      · intro u hu; simp at hu; subst hu; exact hab.2
  have D₁ := key t₁ hc
  have E : ∀ b, Relation.ReflTransGen (TgtStep C.toTypeCtx) t₀ b →
      AdminsOk s C [w.toAdmin] ⟨[], [], [b]⟩ := by
    intro b hb
    induction hb with
    | refl => exact .single (AdminOk.of_valOk hv)
    | @tail b c _ hbc ih =>
      refine AdminsOk.sub (it' := ⟨[], [], [c]⟩) ih ⟨.nil, .cons hbc.1 .nil, ?_⟩ ⟨?_, ?_, ?_⟩
      · intro x hx; cases hx
      · intro x hx; cases hx
      · intro u hu; simp at hu; subst hu; exact hbc.2
      · intro x hx; cases hx
  have := AdminsOk.seq (E t₁ hc₀) (fun _ h => by cases h) D₁
  simpa using this

/-- A trap has any well-formed type. -/
theorem AdminsOk.trap_cons {s : Store H} {C : Context} {A r : List CValType}
    {X : List Nat} {B : List CValType} (hA : ResultOk C.toTypeCtx A) (hr : ResultOk C.toTypeCtx r)
    (D : AdminsOk s C [] ⟨r, X, B⟩) : AdminsOk s C [.trap] ⟨A, X, B⟩ :=
  AdminsOk.cons (xs₁ := []) (AdminOk.trap ⟨hA, hr, fun _ h => by cases h⟩)
    (fun _ h => by cases h) D

/-! ## The generic replacement lemma -/

theorem vals_cons_eq {rv : List Val} {i : Instr} {a : Admin} {as : List Admin}
    (h : a :: as = vals rv ++ [.plain i]) :
    (rv = [] ∧ a = .plain i ∧ as = []) ∨
      ∃ w rv', rv = w :: rv' ∧ a = w.toAdmin ∧ as = vals rv' ++ [.plain i] := by
  cases rv with
  | nil => simp [vals] at h; exact .inl ⟨rfl, h.1, h.2⟩
  | cons w rv' =>
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    exact .inr ⟨w, rv', rfl, h.1, h.2⟩

theorem vals_ne_nil {rv : List Val} {i : Instr} : ([] : List Admin) ≠ vals rv ++ [.plain i] := by
  intro h
  have := congrArg List.length h
  simp at this

/-! ## Typings of value sequences -/

theorem split_redex {as₁ as₂ : List Admin} {rv : List Val} {i : Instr}
    (e : as₁ ++ as₂ = vals rv ++ [.plain i]) :
    (as₂ = [] ∧ as₁ = vals rv ++ [.plain i]) ∨
      ∃ r₁ r₂, rv = r₁ ++ r₂ ∧ as₁ = vals r₁ ∧ as₂ = vals r₂ ++ [.plain i] := by
  rcases List.append_eq_append_iff.mp e with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · obtain ⟨r₁, r₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp (show rv.map Val.toAdmin = _ from h1)
    exact .inr ⟨r₁, r₂, rfl, e₁.symm, by rw [h2, ← e₂]; rfl⟩
  · rcases c' with _ | ⟨c, c'⟩
    · simp only [List.append_nil, List.nil_append] at h1 h2
      exact .inr ⟨rv, [], by simp, h1, by rw [← h2]; rfl⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h2.symm
      exact .inl ⟨rfl, h1⟩

theorem vals_split {as₁ as₂ : List Admin} {rv : List Val} (e : as₁ ++ as₂ = vals rv) :
    ∃ r₁ r₂, rv = r₁ ++ r₂ ∧ as₁ = vals r₁ ∧ as₂ = vals r₂ := by
  obtain ⟨r₁, r₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp (show rv.map Val.toAdmin = _ from e.symm)
  exact ⟨r₁, r₂, rfl, e₁.symm, e₂.symm⟩

theorem vals_cons_inv {a : Admin} {as : List Admin} {rv : List Val} (e : a :: as = vals rv) :
    ∃ w rv', rv = w :: rv' ∧ a = w.toAdmin ∧ as = vals rv' := by
  cases rv with
  | nil => simp [vals] at e
  | cons w rv' =>
    simp only [vals, List.map_cons, List.cons.injEq] at e
    exact ⟨w, rv', rfl, e.1, e.2⟩

/-- Empty sequences preserve the stack height. -/
theorem AdminsOk.nil_len {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
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
    simp only [List.length_append]; have := ih e; simp only at this; omega

/-- Value sequences: the result height is the parameter height plus the values. -/
theorem AdminsOk.vals_len {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) : ∀ rv, L = vals rv →
      it.results.length = it.params.length + rv.length := by
  refine AdminsOk.rec' (motive := fun C L it => ∀ rv, L = vals rv →
      it.results.length = it.params.length + rv.length) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C rv e
    cases rv with
    | nil => rfl
    | cons => simp [vals] at e
  · intro C a it ha rv e
    obtain ⟨w, rv', rfl, rfl, e'⟩ := vals_cons_inv e
    obtain ⟨hp, -, tv, hr, -⟩ := AdminOk.val_inv ha
    cases rv' with
    | nil => rw [hp, hr]; rfl
    | cons => simp [vals] at e'
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ ih₂ rv e
    obtain ⟨r₁, r₂, rfl, rfl, rfl⟩ := vals_split e
    have h1 := ih₁ r₁ rfl; have h2 := ih₂ r₂ rfl
    simp only [List.length_append] at h1 h2 ⊢; omega
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha _ _ ih rv e
    obtain ⟨w, rv', rfl, rfl, rfl⟩ := vals_cons_inv e
    obtain ⟨hp, -, tv, hr, -⟩ := AdminOk.val_inv ha
    simp only at hp hr; subst hp hr
    have := ih rv' rfl
    simp only [List.length_cons, List.length_nil] at this ⊢; omega
  · intro C as it it' _ hs _ ih rv e
    rw [hs.1.length_eq, ← hs.2.1.length_eq]; exact ih rv e
  · intro C as ts t₁ t₂ xs _ _ ih rv e
    have := ih rv e; simp only at this
    simp only [List.length_append]; omega

/-- The parameters of a typing of a value sequence are well formed. -/
theorem AdminsOk.vals_params_ok {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) : ∀ rv, L = vals rv → ResultOk C.toTypeCtx it.params := by
  refine AdminsOk.rec' (motive := fun C L it => ∀ rv, L = vals rv →
      ResultOk C.toTypeCtx it.params) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C _ _; exact fun _ h => by cases h
  · intro C a it ha rv e
    obtain ⟨w, rv', rfl, rfl, -⟩ := vals_cons_inv e
    obtain ⟨hp, -⟩ := AdminOk.val_inv ha
    rw [hp]; exact fun _ h => by cases h
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ _ rv e
    obtain ⟨r₁, r₂, rfl, rfl, rfl⟩ := vals_split e
    exact ih₁ r₁ rfl
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha _ _ _ rv e
    obtain ⟨w, rv', rfl, rfl, rfl⟩ := vals_cons_inv e
    obtain ⟨hp, -⟩ := AdminOk.val_inv ha
    simp only at hp; subst hp; exact fun _ h => by cases h
  · intro C as it it' _ _ hok _ _ _; exact hok.1
  · intro C as ts t₁ t₂ xs _ hts ih rv e
    exact ResultOk.append hts (ih rv e)

/-- A value reaching a type through well-formed targets only. -/
def FitsT (s : Store H) (Δ : TypeCtx) (v : Val) (t : CValType) : Prop :=
  ∃ t₀, ValOk s v t₀ ∧ Relation.ReflTransGen (TgtStep Δ) t₀ t

/-- The invariant carried through value-sequence typings. -/
def FitsV (s : Store H) (Δ : TypeCtx) (v : Val) (t : CValType) : Prop :=
  (Fits s Δ v t ∧ TyOk Δ t) ∨ FitsT s Δ v t

theorem FitsT.fits {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (h : FitsT s Δ v t) :
    Fits s Δ v t := by
  obtain ⟨t₀, hv, hc⟩ := h; exact ⟨t₀, t, hv, hc, .refl⟩

theorem FitsV.fits {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (h : FitsV s Δ v t) :
    Fits s Δ v t := by
  rcases h with h | h
  · exact h.1
  · exact h.fits

/-- A step with a well-formed source (a parameter subsumption). -/
theorem FitsV.src {s : Store H} {Δ : TypeCtx} {v : Val} {a b : CValType} (h : FitsV s Δ v a)
    (hs : Sub Δ a b) (ha : TyOk Δ a) (hb : TyOk Δ b) : FitsV s Δ v b :=
  .inl ⟨h.fits.step hs ha, hb⟩

/-- A step with a well-formed target (a result subsumption). -/
theorem FitsV.tgt {s : Store H} {Δ : TypeCtx} {v : Val} {a b : CValType} (h : FitsV s Δ v a)
    (hs : Sub Δ a b) (hb : TyOk Δ b) : FitsV s Δ v b := by
  rcases h with ⟨hf, ha⟩ | ⟨t₀, hv, hc⟩
  · exact .inl ⟨hf.step hs ha, hb⟩
  · exact .inr ⟨t₀, hv, hc.tail ⟨hs, hb⟩⟩

theorem forall₂_split' {α β : Type} {R : α → β → Prop} {l : List α} {m₁ m₂ : List β}
    (h : List.Forall₂ R l (m₁ ++ m₂)) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ :=
  ⟨_, _, (List.take_append_drop _ _).symm, List.forall₂_take_append _ _ _ h,
    List.forall₂_drop_append _ _ _ h⟩

theorem forall₂_split_left {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m : List β}
    (h : List.Forall₂ R (l₁ ++ l₂) m) :
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ := by
  refine ⟨m.take l₁.length, m.drop l₁.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · have := List.forall₂_take l₁.length h
    simpa only [List.take_left'] using this
  · have := List.forall₂_drop l₁.length h
    simpa only [List.drop_left'] using this

theorem forall₂_zip3 {α β : Type} {R : α → β → Prop} {S : β → β → Prop} {T : α → β → Prop} :
    ∀ {l : List α} {m m' : List β}, List.Forall₂ R l m → List.Forall₂ S m m' →
      (∀ a b b', b ∈ m → b' ∈ m' → R a b → S b b' → T a b') → List.Forall₂ T l m'
  | [], [], [], .nil, .nil, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons g gs, f =>
    .cons (f _ _ _ (List.mem_cons_self ..) (List.mem_cons_self ..) h g)
      (forall₂_zip3 hs gs fun a b b' hb hb' hr hsb =>
        f a b b' (List.mem_cons_of_mem _ hb) (List.mem_cons_of_mem _ hb') hr hsb)

/-- **Typing of a value sequence.** Values below the sequence (`pv`) and the values of
the sequence (`rv`) end up fitting the top of the results, and the untouched bottom of
the stack is carried by an empty sequence. -/
theorem AdminsOk.vals_fit {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) : ∀ rv, L = vals rv → ∀ pv A T, it.params = A ++ T →
      List.Forall₂ (FitsV s C.toTypeCtx) pv T →
      ∃ A₁ T', it.results = A₁ ++ T' ∧ List.Forall₂ (FitsV s C.toTypeCtx) (pv ++ rv) T' ∧
        AdminsOk s C [] ⟨A, it.inits, A₁⟩ := by
  refine AdminsOk.rec' (motive := fun C L it => ∀ rv, L = vals rv → ∀ pv A T,
      it.params = A ++ T → List.Forall₂ (FitsV s C.toTypeCtx) pv T →
      ∃ A₁ T', it.results = A₁ ++ T' ∧ List.Forall₂ (FitsV s C.toTypeCtx) (pv ++ rv) T' ∧
        AdminsOk s C [] ⟨A, it.inits, A₁⟩) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C rv e pv A T hp hf
    cases rv with
    | cons => simp [vals] at e
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
      cases hf
      exact ⟨[], [], rfl, .nil, .nil⟩
  · intro C a it ha rv e pv A T hp hf
    obtain ⟨w, rv', rfl, rfl, e'⟩ := vals_cons_inv e
    cases rv' with
    | cons => simp [vals] at e'
    | nil =>
      obtain ⟨hp', hx', tv, hr, hv⟩ := AdminOk.val_inv ha
      rw [hp'] at hp
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
      cases hf
      refine ⟨[], [tv], hr, .cons (.inr ⟨tv, hv, .refl⟩) .nil, ?_⟩
      rw [hx']; exact .nil
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ _ hx _ ih₁ ih₂ rv e pv A T hp hf
    obtain ⟨r₁, r₂, rfl, rfl, rfl⟩ := vals_split e
    obtain ⟨A₁, T₁, h1, hf1, D₁⟩ := ih₁ r₁ rfl pv A T hp hf
    simp only [Context.initLocals_toTypeCtx] at ih₂
    obtain ⟨A₂, T₂, h2, hf2, D₂⟩ := ih₂ r₂ rfl (pv ++ r₁) A₁ T₁ h1 hf1
    refine ⟨A₂, T₂, h2, by simpa using hf2, ?_⟩
    have := AdminsOk.seq D₁ hx D₂
    simpa using this
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha _ _ ih rv e pv A T hp hf
    obtain ⟨w, rv', rfl, rfl, rfl⟩ := vals_cons_inv e
    obtain ⟨hp', hx', tv, hr, hv⟩ := AdminOk.val_inv ha
    simp only at hp' hx' hr; subst hp' hx' hr
    simp only at hp
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
    cases hf
    simp only [Context.initLocals_nil'] at ih
    obtain ⟨A₁, T', h1, hf1, D⟩ := ih rv' rfl [w] [] [tv] rfl (.cons (.inr ⟨tv, hv, .refl⟩) .nil)
    exact ⟨A₁, T', h1, by simpa using hf1, by simpa using D⟩
  · intro C as it it' hd hs hok ih rv e pv A T hp hf
    obtain ⟨hps, hrs, hin⟩ := hs
    rw [hp] at hps
    obtain ⟨A₀, T₀, hp0, hA, hT⟩ := forall₂_split_left hps
    have hok0 := AdminsOk.vals_params_ok hd rv e
    rw [hp0] at hok0
    have hokp : ResultOk C.toTypeCtx (A ++ T) := hp ▸ hok.1
    have hf0 : List.Forall₂ (FitsV s C.toTypeCtx) pv T₀ :=
      forall₂_zip3 hf hT fun _ b b' hb hb' hr hsb =>
        hr.src hsb (hokp b (List.mem_append_right _ hb)) (hok0 b' (List.mem_append_right _ hb'))
    obtain ⟨A₁, T', h1, hf1, D⟩ := ih rv e pv A₀ T₀ hp0 hf0
    rw [h1] at hrs
    obtain ⟨A₂, T'', hr2, hA2, hT2⟩ := forall₂_split_left hrs
    have hokr : ResultOk C.toTypeCtx (A₂ ++ T'') := hr2 ▸ hok.2.1
    refine ⟨A₂, T'', hr2, forall₂_zip3 hf1 hT2 fun _ b b' _ hb' hr hsb =>
      hr.tgt hsb (hokr b' (List.mem_append_right _ hb')), ?_⟩
    exact AdminsOk.sub D ⟨hA, hA2, hin⟩ ⟨ResultOk.left hokp, ResultOk.left hokr, hok.2.2⟩
  · intro C as ts t₁ t₂ xs hd hts ih rv e pv A T hp hf
    dsimp only at hp ⊢
    rcases List.append_eq_append_iff.mp hp with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · subst h1
      obtain ⟨A₁, T', e1, hf1, D⟩ := ih rv e pv a' T h2 hf
      exact ⟨ts ++ A₁, T', by simp only at e1; rw [e1]; simp, hf1, AdminsOk.frame D hts⟩
    · subst h1 h2
      obtain ⟨p₀, p₁, rfl, hf0, hf1⟩ := forall₂_split' hf
      obtain ⟨A₁, T', e1, hf1', D⟩ := ih rv e p₁ [] t₁ rfl hf1
      have hl := D.nil_len rfl
      simp only [List.length_nil] at hl
      have hA₁ : A₁ = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst hA₁
      refine ⟨A, c' ++ T', by simp only at e1; rw [e1]; simp, by simpa using List.rel_append hf0 hf1', ?_⟩
      have := AdminsOk.frame D (ResultOk.left hts)
      simpa using this

/-- Operand count: every typing of `vals rv ++ [i]` needs the missing operands. -/
theorem AdminsOk.redex_len {s : Store H} {vs : List Val} {i : Instr}
    (hlen : ∀ C it, InstrOk C i it → vs.length ≤ it.params.length) (hne : i ≠ .throwRef)
    {C : Context} {L : List Admin} {it : InstrType} (h : AdminsOk s C L it) :
    ∀ pv rv, L = vals rv ++ [.plain i] → vs = pv ++ rv → pv.length ≤ it.params.length := by
  refine AdminsOk.rec' (motive := fun C L it => ∀ pv rv, L = vals rv ++ [.plain i] →
    vs = pv ++ rv → pv.length ≤ it.params.length) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C pv rv e; exact absurd e vals_ne_nil
  · intro C a it ha pv rv e hv
    rcases vals_cons_eq e with ⟨rfl, rfl, -⟩ | ⟨w, rv', rfl, rfl, e'⟩
    · have := hlen _ _ (AdminOk.plain_inv ha hne)
      simp only [List.append_nil] at hv; subst hv; exact this
    · exact absurd e' vals_ne_nil
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ _ _ ih₁ ih₂ pv rv e hv
    rcases split_redex e with ⟨rfl, e₁⟩ | ⟨r₁, r₂, rfl, rfl, e₂⟩
    · exact ih₁ pv rv e₁ hv
    · have h2 := ih₂ (pv ++ r₁) r₂ e₂ (by simp [hv])
      have hl := h₁.vals_len r₁ rfl
      simp only [List.length_append] at h2 hl ⊢; omega
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha _ _ ih pv rv e hv
    rcases vals_cons_eq e with ⟨rfl, rfl, rfl⟩ | ⟨w, rv', rfl, rfl, rfl⟩
    · have := hlen _ _ (AdminOk.plain_inv ha hne)
      simp only [List.append_nil] at hv; subst hv; exact this
    · obtain ⟨hp, -, tv, hr, -⟩ := AdminOk.val_inv ha
      simp only at hp hr; subst hp hr
      have := ih (pv ++ [w]) rv' rfl (by simp [hv])
      simp at this; simp [this]
  · intro C as it it' _ hs _ ih pv rv e hv
    have := ih pv rv e hv
    rw [hs.1.length_eq]; exact this
  · intro C as ts t₁ t₂ xs _ _ ih pv rv e hv
    have := ih pv rv e hv
    dsimp only at this ⊢
    simp only [List.length_append]; omega

theorem forall₂_fits_step {s : Store H} {Δ : TypeCtx} :
    ∀ {pv : List Val} {tvs tvs' : List CValType}, List.Forall₂ (Fits s Δ) pv tvs →
      List.Forall₂ (Sub Δ) tvs tvs' → ResultOk Δ tvs → List.Forall₂ (Fits s Δ) pv tvs'
  | [], [], [], .nil, .nil, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons hf hfs, .cons hs hss, hok =>
    .cons (hf.step hs (hok _ (List.mem_cons_self ..)))
      (forall₂_fits_step hfs hss fun t ht => hok t (List.mem_cons_of_mem _ ht))

theorem forall₂_mono_mem' {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (∀ a b, b ∈ m → R a b → S a b) →
      List.Forall₂ S l m
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, f =>
    .cons (f _ _ (List.mem_cons_self ..) h)
      (forall₂_mono_mem' hs fun a b hb hr => f a b (List.mem_cons_of_mem _ hb) hr)

/-- Discharges the result-regularity side condition of `AdminsOk.pure_redex` for a
concrete parametric, numeric or vector instruction. -/
macro "pure_redex_reg" : tactic => `(tactic| (
  intro C it hi
  cases hi <;> rename_i hi <;>
    first
    | exact (NumericInstrOk.regular hi).2.1
    | exact (VectorInstrOk.regular hi).2.1
    | (cases hi <;> first
        | exact ‹InstrTypeOk _ _›.2.1
        | (intro x hx; cases hx; done)
        | (intro x hx; simp only [InstrType.plain, List.mem_singleton, List.not_mem_nil] at hx
           first | exact hx.elim | (subst hx; assumption)))))

/-- **Generic preservation for a pure redex `val* instr`.** -/
theorem AdminsOk.pure_redex {s : Store H} {vs : List Val} {i : Instr} {L' : List Admin}
    (hlen : ∀ C it, InstrOk C i it → vs.length ≤ it.params.length)
    (hbase : ∀ (C : Context) (A' tvs : List CValType) (it : InstrType) (xs₂ : List Nat)
      (B : List CValType), InstrOk C i it → it.params = A' ++ tvs →
      List.Forall₂ (Fits s C.toTypeCtx) vs tvs →
      AdminsOk s (C.initLocals it.inits) [] ⟨it.results, xs₂, B⟩ →
      AdminsOk s C L' ⟨A', it.inits ++ xs₂, B⟩)
    {C : Context} {it : InstrType} (h : AdminsOk s C (vals vs ++ [.plain i]) it)
    (hreg : ∀ (C : Context) (it : InstrType), InstrOk C i it → ResultOk C.toTypeCtx it.results :=
      by pure_redex_reg) (hne : i ≠ .throwRef := by intro h; cases h) :
    AdminsOk s C L' it := by
  have key : ∀ {C L it}, AdminsOk s C L it → ∀ pv rv, L = vals rv ++ [.plain i] →
      vs = pv ++ rv → ∀ A' tvs, it.params = A' ++ tvs →
      List.Forall₂ (Fits s C.toTypeCtx) pv tvs → AdminsOk s C L' ⟨A', it.inits, it.results⟩ := by
    intro C L it h
    refine AdminsOk.rec' (motive := fun C L it => ∀ pv rv, L = vals rv ++ [.plain i] →
      vs = pv ++ rv → ∀ A' tvs, it.params = A' ++ tvs →
      List.Forall₂ (Fits s C.toTypeCtx) pv tvs → AdminsOk s C L' ⟨A', it.inits, it.results⟩)
      ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro C pv rv e; exact absurd e vals_ne_nil
    · intro C a it ha pv rv e hv A' tvs hp hf
      rcases vals_cons_eq e with ⟨rfl, rfl, -⟩ | ⟨w, rv', rfl, rfl, e'⟩
      · simp only [List.append_nil] at hv; subst hv
        have hi := AdminOk.plain_inv ha hne
        have hr : ResultOk (C.initLocals it.inits).toTypeCtx it.results := by
          rw [Context.initLocals_toTypeCtx]; exact hreg C it hi
        have D := AdminsOk.frame (AdminsOk.nil (s := s) (C := C.initLocals it.inits)) hr
        simp only [List.append_nil] at D
        have := hbase C A' tvs it [] it.results hi hp hf D
        simpa using this
      · exact absurd e' vals_ne_nil
    · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ pv rv e hv A' tvs hp hf
      dsimp only at hp ⊢
      rcases split_redex e with ⟨rfl, e₁⟩ | ⟨r₁, r₂, rfl, rfl, e₂⟩
      · have := AdminsOk.seq (ih₁ pv rv e₁ hv A' tvs hp hf) hx h₂
        simpa using this
      · have hok := h₁.vals_params_ok r₁ rfl
        rw [hp] at hok
        have hfv : List.Forall₂ (FitsV s C.toTypeCtx) pv tvs :=
          forall₂_mono_mem' hf fun _ b hb h => .inl ⟨h, hok b (List.mem_append_right _ hb)⟩
        obtain ⟨A₁, T', h1, hf1, D⟩ := h₁.vals_fit r₁ rfl pv A' tvs hp hfv
        have hf1' : List.Forall₂ (Fits s (C.initLocals xs₁).toTypeCtx) (pv ++ r₁) T' := by
          rw [Context.initLocals_toTypeCtx]; exact hf1.imp fun _ _ h => h.fits
        have := ih₂ (pv ++ r₁) r₂ e₂ (by simp [hv]) A₁ T' h1 hf1'
        have := AdminsOk.seq D hx this
        simpa using this
    · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha _ hs ih pv rv e hv A' tvs hp hf
      rcases vals_cons_eq e with ⟨rfl, rfl, rfl⟩ | ⟨w, rv', rfl, rfl, rfl⟩
      · simp only [List.append_nil] at hv; subst hv
        exact hbase C A' tvs ⟨t₁, xs₁, t₂⟩ xs₂ t₃ (AdminOk.plain_inv ha hne) hp hf hs
      · obtain ⟨hp', hx', tv, hr, hv'⟩ := AdminOk.val_inv ha
        simp only at hp' hx' hr; subst hp' hx' hr
        simp only at hp
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hp.symm
        cases hf
        exact ih [w] rv' rfl (by simp [hv]) [] [tv] rfl (.cons (.of_valOk hv') .nil)
    · intro C as it it' _ hsub hok ih pv rv e hv A' tvs hp hf
      obtain ⟨hps, hrs, hin⟩ := hsub
      rw [hp] at hps
      have e1 : it.params = it.params.take A'.length ++ it.params.drop A'.length :=
        (List.take_append_drop _ _).symm
      have hA := List.forall₂_take A'.length hps
      have hT := List.forall₂_drop A'.length hps
      simp only [List.take_left', List.drop_left'] at hA hT
      have hokp : ResultOk C.toTypeCtx (A' ++ tvs) := hp ▸ hok.1
      have ih' := ih pv rv e hv _ _ e1 (forall₂_fits_step hf hT (ResultOk.right hokp))
      refine AdminsOk.sub ih' ⟨hA, hrs, hin⟩ ⟨ResultOk.left hokp, hok.2.1, hok.2.2⟩
    · intro C as ts t₁ t₂ xs hd hts ih pv rv e hv A' tvs hp hf
      have hl := AdminsOk.redex_len hlen hne hd pv rv e hv
      have hlt : pv.length = tvs.length := hf.length_eq
      dsimp only at hp hl ⊢
      rcases List.append_eq_append_iff.mp hp with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
      · subst h1; exact AdminsOk.frame (ih pv rv e hv a' tvs h2 hf) hts
      · have hc : c' = [] := by
          rw [h2] at hlt; simp only [List.length_append] at hlt
          apply List.eq_nil_of_length_eq_zero; omega
        subst hc
        simp only [List.append_nil, List.nil_append] at h1 h2
        subst h1 h2
        have := AdminsOk.frame (ih pv rv e hv [] _ rfl hf) hts
        simpa using this
  exact key h [] vs rfl rfl it.params [] (by simp) .nil

/-! ## Helpers for the family proofs -/

theorem params_split {P A' tvs : List CValType} (hp : P = A' ++ tvs)
    (hl : tvs.length = P.length) : A' = [] ∧ tvs = P := by
  subst hp
  simp only [List.length_append] at hl
  have : A' = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this; exact ⟨rfl, rfl⟩

theorem ResultOk.nil' (Δ : TypeCtx) : ResultOk Δ [] := fun _ h => by cases h

theorem ResultOk.num1 (Δ : TypeCtx) (nt : NumType) : ResultOk Δ [.num nt] := by
  intro t h; simp only [List.mem_singleton] at h; subst h; exact .num _

theorem ResultOk.vec1 (Δ : TypeCtx) (vt : VecType) : ResultOk Δ [.vec vt] := by
  intro t h; simp only [List.mem_singleton] at h; subst h; exact .vec _

/-- A step of a redex is a step of the redex under a value prefix. -/
theorem Step.under_vals {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {is is' : List Admin} (vs : List Val)
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    ∃ c', Step P host ⟨s, f, vals vs ++ is⟩ c' := by
  rcases vs with _ | ⟨v, vs⟩
  · exact ⟨_, h⟩
  · have := Step.ctxtInstrs (vs := v :: vs) (rest := []) h (.inl (List.cons_ne_nil _ _))
    simp only [List.append_nil] at this
    exact ⟨_, this⟩

end Silmaril.Wasm.Execution.Core
