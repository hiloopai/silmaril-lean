module

public import Silmaril.Wasm.Auto.EGraph.Defs
public import Silmaril.Wasm.Logic.Core.Thms

/-! # Soundness of the e-graph certificate checker

* values: `asInt_intVal`, the operator results are typed (`unV_typed` …), and
  `typeOf_sound`;
* patterns: `inst_eval`, `match_ext`, `match_inst`, `match_typed`;
* congruence: `set_ref` (refinement is preserved by plugging into any term context);
* steps: `fold?_eval`, `rewriteAt_spec`, `applyStep_sound`, `runSteps_sound`;
* the bridge to Core 3.0: `exec_compile`, `exec_compileL`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EGraph

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

theorem Ref.refl {α : Type} (o : Option α) : Ref o o := fun _ h => h

theorem Ref.trans {α : Type} {a b c : Option α} (h₁ : Ref a b) (h₂ : Ref b c) : Ref a c :=
  fun v h => h₂ v (h₁ v h)

theorem Ref.of_eq {α : Type} {a b : Option α} (h : a = b) : Ref a b := fun _ h' => h ▸ h'

theorem Ref.antisymm {α : Type} {a b : Option α} (h₁ : Ref a b) (h₂ : Ref b a) : a = b := by
  cases a with
  | some v => exact (h₁ v rfl).symm
  | none =>
    cases b with
    | none => rfl
    | some w => exact h₂ w rfl

/-- A refinement of a value that is defined is that value. -/
theorem Ref.eq_of_some {α : Type} {a b : Option α} {v : α} (h : Ref a b) (ha : a = some v) :
    b = a := by rw [ha]; exact h v ha

/-! ## Values -/

@[simp] theorem asInt_intVal (t : IntType) (x : BitVec t.width) :
    asInt t (intVal t x) = some x := by
  cases t <;> rfl

theorem asInt_eq_some {t : IntType} {v : Val} {x : BitVec t.width} (h : asInt t v = some x) :
    v = intVal t x := by
  cases t <;> rcases v with ⟨⟨(_ | _) | _⟩, b⟩ | _ | _ <;> cases h <;> rfl

@[simp] theorem i32_eq_intVal (x : BitVec 32) : Val.i32 x = intVal .i32 x := rfl

theorem unV_typed (t : IntType) (op : IntUnOp) (a : Option Val) : TypedV t (unV t op a) := by
  intro v h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨_, rfl⟩

theorem testV_typed (t : IntType) (a : Option Val) : TypedV .i32 (testV t a) := by
  intro v h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨_, rfl⟩

theorem binV_typed (t : IntType) (op : IntBinOp) (a b : Option Val) :
    TypedV t (binV t op a b) := by
  intro v h
  simp only [binV, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem relV_typed (t : IntType) (op : IntRelOp) (a b : Option Val) :
    TypedV .i32 (relV t op a b) := by
  intro v h
  simp only [relV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- **Typing is sound**: in a frame typed by `Γ`, a term of type `t` traps or has a
value of type `t`. -/
theorem typeOf_sound {Γ : List IntType} {f : Frame} (hf : FrameOk Γ f) :
    ∀ {e : Term} {t : IntType}, e.typeOf Γ = some t → TypedV t (e.eval f)
  | .const t' n, t, h => by
    cases h; intro v hv; cases hv; exact ⟨_, rfl⟩
  | .lget i, t, h => by
    intro v hv
    obtain ⟨x, hx⟩ := hf i t h
    exact ⟨x, Option.some.inj (hv.symm.trans hx)⟩
  | .un t' _ a, t, h => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    rw [← h.2]; exact unV_typed _ _ _
  | .test _ a, t, h => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    rw [← h.2]; exact testV_typed _ _
  | .bin t' _ a b, t, h => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    rw [← h.2]; exact binV_typed _ _ _ _
  | .rel _ _ a b, t, h => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    rw [← h.2]; exact relV_typed _ _ _ _

theorem noTrap_bin {t : IntType} {op : IntBinOp} {a b : Term}
    (h : (Term.bin t op a b).noTrap = true) :
    (∃ z : BitVec t.width → BitVec t.width → BitVec t.width, ∀ x y,
      intBinOp t op x y = .ok (z x y)) ∧ a.noTrap = true ∧ b.noTrap = true := by
  simp only [Term.noTrap, Bool.and_eq_true] at h
  refine ⟨?_, h.1.2, h.2⟩
  have hop := h.1.1
  rcases op with _ | _ | _ | sg | sg | _ | _ | _ | _ | sg | _ | _ <;> (try cases sg) <;>
    first | (exact ⟨_, fun x y => rfl⟩) | (simp at hop)

/-- **Terms without division cannot trap**: in a frame typed by `Γ`, a term of type `t`
without division or remainder has an integer value of type `t`. -/
theorem noTrap_total {Γ : List IntType} {f : Frame} (hf : FrameOk Γ f) :
    ∀ {e : Term} {t : IntType}, e.typeOf Γ = some t → e.noTrap = true → TotalV t (e.eval f)
  | .const t' n, t, h, _ => by cases h; exact ⟨_, rfl⟩
  | .lget i, t, h, _ => hf i t h
  | .un t' op a, t, h, hn => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨x, hx⟩ : TotalV t' (a.eval f) := noTrap_total hf h.1 hn
    rw [← h.2]
    exact ⟨intUnOp t' op x, by
      simp only [Term.eval, hx, unV, Option.bind_some, asInt_intVal, Option.map_some]⟩
  | .test t' a, t, h, hn => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨x, hx⟩ : TotalV t' (a.eval f) := noTrap_total hf h.1 hn
    rw [← h.2]
    exact ⟨intTestOp t' .eqz x, by
      simp only [Term.eval, hx, testV, Option.bind_some, asInt_intVal, Option.map_some]; rfl⟩
  | .bin t' op a b, t, h, hn => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨z, hz⟩, ha, hb⟩ := noTrap_bin hn
    obtain ⟨x, hx⟩ : TotalV t' (a.eval f) := noTrap_total hf h.1.1 ha
    obtain ⟨y, hy⟩ : TotalV t' (b.eval f) := noTrap_total hf h.1.2 hb
    rw [← h.2]
    exact ⟨z x y, by simp only [Term.eval, hx, hy, binV, Option.bind_some, asInt_intVal, hz]⟩
  | .rel t' op a b, t, h, hn => by
    simp only [Term.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    have hn' : a.noTrap = true ∧ b.noTrap = true := by simpa [Term.noTrap] using hn
    obtain ⟨x, hx⟩ : TotalV t' (a.eval f) := noTrap_total hf h.1.1 hn'.1
    obtain ⟨y, hy⟩ : TotalV t' (b.eval f) := noTrap_total hf h.1.2 hn'.2
    rw [← h.2]
    exact ⟨intRelOp t' op x y, by
      simp only [Term.eval, hx, hy, relV, Option.bind_some, asInt_intVal, Option.map_some]; rfl⟩

/-! ## Patterns -/

/-- Instantiation commutes with evaluation. -/
theorem inst_eval {σ : Subst} {f : Frame} :
    ∀ {p : Pat} {e : Term}, p.inst σ = some e → e.eval f = p.eval (σ.val f)
  | .var _ n, e, h | .tvar _ n, e, h => by
    have h' : σ.find? n = some e := h
    simp [Pat.eval, Subst.val, h']
  | .const _ _, e, h => by cases h; rfl
  | .un t op a, e, h => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Term.eval, Pat.eval, inst_eval ha]
  | .test t a, e, h => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Term.eval, Pat.eval, inst_eval ha]
  | .bin t op a b, e, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Term.eval, Pat.eval, inst_eval ha, inst_eval hb]
  | .rel t op a b, e, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Term.eval, Pat.eval, inst_eval ha, inst_eval hb]

theorem Subst.Ext.refl (σ : Subst) : σ.Ext σ := fun _ _ h => h

theorem Subst.Ext.trans {a b c : Subst} (h₁ : a.Ext b) (h₂ : b.Ext c) : a.Ext c :=
  fun n e h => h₂ n e (h₁ n e h)

theorem Subst.Ext.cons {σ : Subst} {n : Nat} {e : Term} (h : σ.find? n = none) :
    σ.Ext ((n, e) :: σ) := by
  intro m e' hm
  simp only [Subst.find?]
  split
  · subst_vars; rw [h] at hm; cases hm
  · exact hm

/-- Binding a pattern variable: the side condition holds, the substitution grows and binds
the variable to the matched term. -/
theorem bind_spec {c : Prop} [Decidable c] {σ σ' : Subst} {n : Nat} {e : Term}
    (h : (if c then (match σ.find? n with
      | some e' => if e' = e then some σ else none
      | none => some ((n, e) :: σ)) else none) = some σ') :
    c ∧ σ.Ext σ' ∧ σ'.find? n = some e := by
  split at h
  · rename_i hc
    split at h
    · rename_i e' hn
      split at h
      · rename_i he; cases h; exact ⟨hc, Subst.Ext.refl _, he ▸ hn⟩
      · cases h
    · rename_i hn; cases h; exact ⟨hc, Subst.Ext.cons hn, by simp [Subst.find?]⟩
  · cases h

/-- Matching extends the substitution. -/
theorem match_ext {Γ : List IntType} :
    ∀ {p : Pat} {a : Term} {σ σ' : Subst}, p.match Γ a σ = some σ' → σ.Ext σ'
  | .var _ _, _, _, _, h | .tvar _ _, _, _, _, h => (bind_spec h).2.1
  | .const _ _, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    cases h.2; exact Subst.Ext.refl _
  | .un _ _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    exact match_ext h.2
  | .test _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    exact match_ext h.2
  | .bin _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    exact Subst.Ext.trans (match_ext h₁) (match_ext h₂)
  | .rel _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    exact Subst.Ext.trans (match_ext h₁) (match_ext h₂)

/-- Instantiation is stable under extension. -/
theorem inst_ext {σ σ' : Subst} (hx : σ.Ext σ') :
    ∀ {p : Pat} {e : Term}, p.inst σ = some e → p.inst σ' = some e
  | .var _ n, e, h | .tvar _ n, e, h => hx n e h
  | .const _ _, e, h => h
  | .un t op a, e, h => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Pat.inst, inst_ext hx ha, Option.map_some]
  | .test t a, e, h => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Pat.inst, inst_ext hx ha, Option.map_some]
  | .bin t op a b, e, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Pat.inst, inst_ext hx ha, inst_ext hx hb, Option.bind_some, Option.map_some]
  | .rel t op a b, e, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Pat.inst, inst_ext hx ha, inst_ext hx hb, Option.bind_some, Option.map_some]

/-- A successful match instantiates back to the matched term. -/
theorem match_inst {Γ : List IntType} :
    ∀ {p : Pat} {a : Term} {σ σ' : Subst}, p.match Γ a σ = some σ' → p.inst σ' = some a
  | .var _ _, _, _, _, h | .tvar _ _, _, _, _, h => (bind_spec h).2.2
  | .const _ _, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h; rfl
  | .un _ _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    simp only [Pat.inst, match_inst h, Option.map_some]
  | .test _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Pat.inst, match_inst h, Option.map_some]
  | .bin _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hp : p.inst σ' = some _ := inst_ext (match_ext h₂) (match_inst h₁)
    simp only [Pat.inst, hp, match_inst h₂, Option.bind_some, Option.map_some]
  | .rel _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hp : p.inst σ' = some _ := inst_ext (match_ext h₂) (match_inst h₁)
    simp only [Pat.inst, hp, match_inst h₂, Option.bind_some, Option.map_some]

theorem Subst.Typed.ext {Γ : List IntType} {σ σ' : Subst} {vs : List (IntType × Nat)}
    (h : σ.Typed Γ vs) (hx : σ.Ext σ') : σ'.Typed Γ vs := by
  intro tn hm
  obtain ⟨e, he, ht⟩ := h tn hm
  exact ⟨e, hx _ _ he, ht⟩

theorem match_typed {Γ : List IntType} :
    ∀ {p : Pat} {a : Term} {σ σ' : Subst}, p.match Γ a σ = some σ' → σ'.Typed Γ p.vars
  | .var t n, a, σ, σ', h => by
    intro tn hm
    have hm' : tn = (t, n) := List.mem_singleton.mp hm
    rw [hm']
    exact ⟨a, (bind_spec h).2.2, (bind_spec h).1⟩
  | .tvar _ _, _, _, _, _ => by intro tn hm; simp [Pat.vars] at hm
  | .const _ _, a, σ, σ', h => by intro tn hm; simp [Pat.vars] at hm
  | .un _ _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    have k : σ'.Typed Γ p.vars := match_typed h.2
    exact k
  | .test _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    have k : σ'.Typed Γ p.vars := match_typed h.2
    exact k
  | .bin _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    intro tn hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Subst.Typed.ext (match_typed h₁) (match_ext h₂) tn hm
    · exact match_typed h₂ tn hm
  | .rel _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    intro tn hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Subst.Typed.ext (match_typed h₁) (match_ext h₂) tn hm
    · exact match_typed h₂ tn hm

theorem Subst.Total.ext {Γ : List IntType} {σ σ' : Subst} {vs : List (IntType × Nat)}
    (h : σ.Total Γ vs) (hx : σ.Ext σ') : σ'.Total Γ vs := by
  intro tn hm
  obtain ⟨e, he, ht⟩ := h tn hm
  exact ⟨e, hx _ _ he, ht⟩

theorem match_total {Γ : List IntType} :
    ∀ {p : Pat} {a : Term} {σ σ' : Subst}, p.match Γ a σ = some σ' → σ'.Total Γ p.tvars
  | .tvar t n, a, σ, σ', h => by
    intro tn hm
    have hm' : tn = (t, n) := List.mem_singleton.mp hm
    rw [hm']
    exact ⟨a, (bind_spec h).2.2, (bind_spec h).1.1, (bind_spec h).1.2⟩
  | .var _ _, _, _, _, _ => by intro tn hm; simp [Pat.tvars] at hm
  | .const _ _, a, σ, σ', h => by intro tn hm; simp [Pat.tvars] at hm
  | .un _ _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    have k : σ'.Total Γ p.tvars := match_total h.2
    exact k
  | .test _ p, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    have k : σ'.Total Γ p.tvars := match_total h.2
    exact k
  | .bin _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    intro tn hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Subst.Total.ext (match_total h₁) (match_ext h₂) tn hm
    · exact match_total h₂ tn hm
  | .rel _ _ p q, a, σ, σ', h => by
    cases a <;> simp only [Pat.match, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨σ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h.2
    intro tn hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Subst.Total.ext (match_total h₁) (match_ext h₂) tn hm
    · exact match_total h₂ tn hm

/-! ## Congruence -/

theorem unV_ref {t : IntType} {op : IntUnOp} {a a' : Option Val} (h : Ref a a') :
    Ref (unV t op a) (unV t op a') := by
  cases a with
  | none => intro v hv; cases hv
  | some x => rw [h x rfl]; exact Ref.refl _

theorem testV_ref {t : IntType} {a a' : Option Val} (h : Ref a a') :
    Ref (testV t a) (testV t a') := by
  cases a with
  | none => intro v hv; cases hv
  | some x => rw [h x rfl]; exact Ref.refl _

theorem binV_ref {t : IntType} {op : IntBinOp} {a a' b b' : Option Val} (ha : Ref a a')
    (hb : Ref b b') : Ref (binV t op a b) (binV t op a' b') := by
  cases a with
  | none => intro v hv; cases hv
  | some x =>
    cases b with
    | none => intro v hv; simp [binV] at hv
    | some y => rw [ha x rfl, hb y rfl]; exact Ref.refl _

theorem relV_ref {t : IntType} {op : IntRelOp} {a a' b b' : Option Val} (ha : Ref a a')
    (hb : Ref b b') : Ref (relV t op a b) (relV t op a' b') := by
  cases a with
  | none => intro v hv; cases hv
  | some x =>
    cases b with
    | none => intro v hv; simp [relV] at hv
    | some y => rw [ha x rfl, hb y rfl]; exact Ref.refl _

/-- **Congruence**: replacing a subterm by a refinement refines the whole term. -/
theorem set_ref {f : Frame} {a b : Term} (hab : Ref (a.eval f) (b.eval f)) :
    ∀ {e e' : Term} {p : List Nat}, e.get? p = some a → e.set? p b = some e' →
      Ref (e.eval f) (e'.eval f)
  | e, e', [], hg, hs => by
    have ha : e = a := by simpa [Term.get?] using hg
    have hb : e' = b := by simpa [Term.set?] using hs.symm
    rw [ha, hb]; exact hab
  | .un t op x, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.un t op x' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact unV_ref (set_ref hab (hg : x.get? p = some a) hx)
  | .test t x, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.test t x' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact testV_ref (set_ref hab (hg : x.get? p = some a) hx)
  | .bin t op x y, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.bin t op x' y = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact binV_ref (set_ref hab (hg : x.get? p = some a) hx) (Ref.refl _)
  | .rel t op x y, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.rel t op x' y = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact relV_ref (set_ref hab (hg : x.get? p = some a) hx) (Ref.refl _)
  | .bin t op x y, e', 1 :: p, hg, hs => by
    obtain ⟨y', hy, he⟩ : ∃ y', y.set? p b = some y' ∧ Term.bin t op x y' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact binV_ref (Ref.refl _) (set_ref hab (hg : y.get? p = some a) hy)
  | .rel t op x y, e', 1 :: p, hg, hs => by
    obtain ⟨y', hy, he⟩ : ∃ y', y.set? p b = some y' ∧ Term.rel t op x y' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    exact relV_ref (Ref.refl _) (set_ref hab (hg : y.get? p = some a) hy)
  | .const _ _, _, _ :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .lget _, _, _ :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .un _ _ _, _, (_ + 1) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .test _ _, _, (_ + 1) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .bin _ _ _ _, _, (_ + 2) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .rel _ _ _ _, _, (_ + 2) :: _, hg, _ => absurd hg (by simp [Term.get?])

/-- After a replacement, the path holds the new subterm, and replacing it back restores
the term. -/
theorem get_set {a b : Term} :
    ∀ {e e' : Term} {p : List Nat}, e.get? p = some a → e.set? p b = some e' →
      e'.get? p = some b ∧ e'.set? p a = some e
  | e, e', [], hg, hs => by
    have ha : e = a := by simpa [Term.get?] using hg
    have hb : e' = b := by simpa [Term.set?] using hs.symm
    rw [ha, hb]; simp [Term.get?, Term.set?]
  | .un t op x, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.un t op x' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : x'.get? p = some b ∧ x'.set? p a = some x :=
      get_set (e := x) hg hx
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .test t x, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.test t x' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : x'.get? p = some b ∧ x'.set? p a = some x :=
      get_set (e := x) hg hx
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .bin t op x y, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.bin t op x' y = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : x'.get? p = some b ∧ x'.set? p a = some x :=
      get_set (e := x) hg hx
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .rel t op x y, e', 0 :: p, hg, hs => by
    obtain ⟨x', hx, he⟩ : ∃ x', x.set? p b = some x' ∧ Term.rel t op x' y = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : x'.get? p = some b ∧ x'.set? p a = some x :=
      get_set (e := x) hg hx
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .bin t op x y, e', 1 :: p, hg, hs => by
    obtain ⟨y', hy, he⟩ : ∃ y', y.set? p b = some y' ∧ Term.bin t op x y' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : y'.get? p = some b ∧ y'.set? p a = some y :=
      get_set (e := y) hg hy
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .rel t op x y, e', 1 :: p, hg, hs => by
    obtain ⟨y', hy, he⟩ : ∃ y', y.set? p b = some y' ∧ Term.rel t op x y' = e' :=
      Option.map_eq_some_iff.mp hs
    rw [← he]
    have k : y'.get? p = some b ∧ y'.set? p a = some y :=
      get_set (e := y) hg hy
    exact ⟨k.1, by simp only [Term.set?, k.2, Option.map_some]⟩
  | .const _ _, _, _ :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .lget _, _, _ :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .un _ _ _, _, (_ + 1) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .test _ _, _, (_ + 1) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .bin _ _ _ _, _, (_ + 2) :: _, hg, _ => absurd hg (by simp [Term.get?])
  | .rel _ _ _ _, _, (_ + 2) :: _, hg, _ => absurd hg (by simp [Term.get?])

/-- Congruence for equal values. -/
theorem set_eq {f : Frame} {a b e e' : Term} {p : List Nat} (hab : a.eval f = b.eval f)
    (hg : e.get? p = some a) (hs : e.set? p b = some e') : e.eval f = e'.eval f :=
  have hback : e'.get? p = some b ∧ e'.set? p a = some e := get_set hg hs
  Ref.antisymm (set_ref (Ref.of_eq hab) hg hs) (set_ref (Ref.of_eq hab.symm) hback.1 hback.2)

end Silmaril.Proofs.Wasm.Auto.EGraph