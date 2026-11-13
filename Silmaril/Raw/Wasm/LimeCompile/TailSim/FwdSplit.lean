module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# The forward simulation of the tail-call rewrite: decomposition at the source's active head

`R.split`: in the forward relation, a source `val* a rest` (with `a` its first non-value) is
related to a target `val* V₀ y₀` where `V₀` is a prefix of the source's values and the rest is
described by one of the head shapes `SHead` (the constructor of `R` that relates `a`; for the
multi-instruction segments — a call redex, a bubbled pending tail call, a trap or a throw — the
remaining values `V₁` belong to the segment).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (vals_nil' vals_cons' vals_append_cons_inj)
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

/-- **The head shapes of the forward relation** at the source's first non-value `a`, with the
source values `V₁` of the segment it belongs to. -/
inductive SHead : Bool → List Val → Admin → List Admin → List Admin → Prop where
  | same {tl : Bool} {a : Admin} {rest y : List Admin} : ¬ a.IsCtx → R true tl rest y →
      SHead tl [] a rest (a :: y)
  | instr {i : Instr} {rest y : List Admin} : R true true rest y →
      SHead true [] (.plain i) rest ((tailI i).map .plain ++ y)
  | rcr {c c' : Admin} {rest y : List Admin} : RCRPair c c' → R true true rest y →
      SHead true [] c rest (c' :: .plain .return_ :: y)
  | label {tl : Bool} {n : Nat} {cont cont' : List Instr} {b b' rest y : List Admin} :
      (cont' = cont ∨ (tl = true ∧ cont' = tailL cont)) → R true tl b b' → R true tl rest y →
      SHead tl [] (.label n cont b) rest (.label n cont' b' :: y)
  | handler {tl : Bool} {n : Nat} {cs : List Catch} {b b' rest y : List Admin} :
      R true false b b' → R true tl rest y → SHead tl [] (.handler n cs b) rest (.handler n cs b' :: y)
  | frame {tl : Bool} {k n : Nat} {fc : Frame} {b ys rest y : List Admin} :
      CE true k [.frame n fc b] ys → R true tl rest y → SHead tl [] (.frame n fc b) rest (ys ++ y)
  | call {tl : Bool} {k : Nat} {vs : List Val} {a : Nat} {d : DefType} {ys rest y : List Admin} :
      CE true k (vals vs ++ [.ref (.func a), .callRefType d]) ys → R true tl rest y →
      SHead tl (vs ++ [.ref (.func a)]) (.callRefType d) rest (ys ++ y)
  | bub {ws : List Val} {c : Admin} {B : List Admin} (U : List Val) (X : List Admin) :
      PTL ws c B → SHead true (U ++ ws) c X B
  | trap {tl : Bool} (us : List Val) (x : List Admin) {y : List Admin} : TA y →
      SHead tl us .trap x y
  | throw {tl : Bool} {e : Nat} (us : List Val) (x : List Admin) {y : List Admin} : TT e y →
      SHead tl (us ++ [.ref (.exn e)]) (.plain .throwRef) x y

/-- The source side of a forward callee segment: a frame of the arity, or a call redex. -/
theorem CE.src_shape_aux : ∀ {fw : Bool} {k : Nat} {xs ys : List Admin}, CE fw k xs ys → fw = true →
    (∃ fc b, xs = [.frame k fc b]) ∨
      ∃ (vs : List Val) (a : Nat) (d : DefType), xs = vals vs ++ [.ref (.func a), .callRefType d]
  | _, _, _, _, .frame _, _ => .inl ⟨_, _, rfl⟩
  | _, _, _, _, .call _, _ => .inr ⟨_, _, _, rfl⟩
  | _, _, _, _, .pend _ _ _ _, _ => .inr ⟨_, _, _, rfl⟩
  | _, _, _, _, .wrap h _, hfw => CE.src_shape_aux h hfw
  | _, _, _, _, .vals _ _, hfw => by cases hfw

theorem CE.src_shape {k : Nat} {xs ys : List Admin} (h : CE true k xs ys) :
    (∃ fc b, xs = [.frame k fc b]) ∨
      ∃ (vs : List Val) (a : Nat) (d : DefType), xs = vals vs ++ [.ref (.func a), .callRefType d] :=
  CE.src_shape_aux h rfl

theorem RCRPair.val?_eq {c c' : Admin} (h : RCRPair c c') : c.val? = none := by
  cases c with
  | plain i => cases i <;> first | rfl | exact (h : False).elim
  | returnCallRefType d => rfl
  | _ => exact (h : False).elim

theorem RCRPair.isReturnCallRef {c c' : Admin} (h : RCRPair c c') : c.IsReturnCallRef := by
  cases c with
  | plain i => cases i <;> trivial
  | returnCallRefType d => trivial
  | _ => exact (h : False).elim

theorem RCRPair.isCallRef {c c' : Admin} (h : RCRPair c c') : c'.IsCallRef := by
  cases c with
  | plain i =>
    cases i <;> first | exact (h : False).elim | (subst h; trivial)
  | returnCallRefType d => subst h; trivial
  | _ => exact (h : False).elim

theorem tailI_of_val {i : Instr} {v : Val} (h : (Admin.plain i).val? = some v) :
    tailI i = [i] := by
  cases i <;> simp_all [Admin.val?, Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem call_redex_eq (vs : List Val) (a : Nat) (d : DefType) (x : List Admin) :
    vals vs ++ [.ref (.func a), .callRefType d] ++ x =
      vals (vs ++ [.ref (.func a)]) ++ .callRefType d :: x := by
  simp [vals, Val.toAdmin]

theorem throw_eq (us : List Val) (e : Nat) (x : List Admin) :
    vals us ++ throwing e ++ x = vals (us ++ [.ref (.exn e)]) ++ .plain .throwRef :: x := by
  simp [vals, Val.toAdmin, throwing]

theorem val?_crt (d : DefType) : (Admin.callRefType d).val? = none := rfl

theorem PTL.rcr {ws : List Val} {c : Admin} {B : List Admin} (h : PTL ws c B) :
    ∃ c', RCRPair c c' := by
  obtain ⟨_, _, _, _, _, c', _, hc, _⟩ := h
  exact ⟨c', hc⟩

/-- **Decomposition at the source's active head** (forward relation). -/
theorem R.split {tl : Bool} {a : Admin} {rest : List Admin} (ha : a.val? = none) :
    ∀ {V : List Val} {y : List Admin}, R true tl (vals V ++ a :: rest) y →
      ∃ (V₀ V₁ : List Val) (y₀ : List Admin), V = V₀ ++ V₁ ∧ y = vals V₀ ++ y₀ ∧
        SHead tl V₁ a rest y₀ := by
  intro V
  induction V with
  | nil =>
    intro y h
    generalize hx : vals [] ++ a :: rest = x at h
    cases h with
    | nil => simp at hx
    | same hc h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨[], [], _, rfl, by simp, .same hc h'⟩
    | instr h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨[], [], _, rfl, by simp, .instr h'⟩
    | rcr hc h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨[], [], _, rfl, by simp, .rcr hc h'⟩
    | label hc hb h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨[], [], _, rfl, by simp, .label hc hb h'⟩
    | handler hb h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨[], [], _, rfl, by simp, .handler hb h'⟩
    | callee hce h' =>
      rcases CE.src_shape hce with ⟨fc, b, rfl⟩ | ⟨vs, a', d, rfl⟩
      · simp only [Sim.vals_nil', List.nil_append, List.singleton_append, List.cons.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨[], [], _, rfl, by simp, .frame hce h'⟩
      · rw [call_redex_eq] at hx
        obtain ⟨h1, -, -⟩ := vals_append_cons_inj ha (val?_crt d) hx
        simp at h1
    | bub U X hp =>
      obtain ⟨c', hc⟩ := PTL.rcr hp
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha (RCRPair.val?_eq hc) hx
      exact ⟨[], U ++ _, y, by rw [List.nil_append, ← h1], by simp, .bub U _ hp⟩
    | trapC us x ht =>
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha rfl hx
      exact ⟨[], us, y, by rw [List.nil_append, ← h1], by simp, .trap us _ ht⟩
    | throwC us x ht =>
      rw [throw_eq] at hx
      obtain ⟨h1, -, -⟩ := vals_append_cons_inj ha rfl hx
      simp at h1
  | cons v V ih =>
    intro y h
    generalize hx : vals (v :: V) ++ a :: rest = x at h
    cases h with
    | nil => simp at hx
    | same hc h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := ih h'
      exact ⟨v :: V₀, V₁, y₀, rfl, by simp, hh⟩
    | @instr _ i x' y' h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
      obtain ⟨hv, rfl⟩ := hx
      have hti : tailI i = [i] := tailI_of_val (v := v) (by rw [← hv]; simp)
      obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := ih h'
      refine ⟨v :: V₀, V₁, y₀, rfl, ?_, hh⟩
      rw [hti, Sim.vals_cons', List.map_cons, List.map_nil, hv]
      simp
    | rcr hc h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
      have := RCRPair.val?_eq hc
      rw [← hx.1] at this
      simp at this
    | label hc hb h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
      have hn := Val.toAdmin_not_ctx v
      rw [hx.1] at hn
      exact absurd trivial hn
    | handler hb h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
      have hn := Val.toAdmin_not_ctx v
      rw [hx.1] at hn
      exact absurd trivial hn
    | callee hce h' =>
      rcases CE.src_shape hce with ⟨fc, b, rfl⟩ | ⟨vs, a', d, rfl⟩
      · simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hx
        have hn := Val.toAdmin_not_ctx v
        rw [hx.1] at hn
        exact absurd trivial hn
      · rw [call_redex_eq] at hx
        obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha (val?_crt d) hx
        exact ⟨[], _, _, by rw [List.nil_append, h1], by simp, .call hce h'⟩
    | bub U X hp =>
      obtain ⟨c', hc⟩ := PTL.rcr hp
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha (RCRPair.val?_eq hc) hx
      exact ⟨[], U ++ _, y, by rw [List.nil_append, h1], by simp, .bub U _ hp⟩
    | trapC us x ht =>
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha rfl hx
      exact ⟨[], us, y, by rw [List.nil_append, h1], by simp, .trap us _ ht⟩
    | throwC us x ht =>
      rw [throw_eq] at hx
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj ha rfl hx
      exact ⟨[], _, y, by rw [List.nil_append, h1], by simp, .throw us _ ht⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
