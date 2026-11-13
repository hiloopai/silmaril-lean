module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdBase
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame
public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv

/-!
# The backward simulation of the tail-call rewrite: decomposition at the target's active head

The backward simulation has the target on the left. This file decomposes the backward relation
(`R false`) at the target's first non-value:

* `THead`, `R.tsplit`: the head shapes, seen from the target;
* `R.vals_tinv`, `R.kernel_tinv`, `R.rcr_tinv`, `R.trap_tinv`, `R.throw_tinv`: a target of
  values, or values before `br`/`return`/`return_call_ref`, a trap or a throw, has a source of
  the same shape (or trap- / throw-active);
* `TA.step`, `TT.step`: trap- and throw-active code steps only to trap- and throw-active code,
  in the same store and frame, with smaller code;
* `PendR`: the pending shapes (a target `CALL_REF; RETURN` against the source's
  `RETURN_CALL_REF`, under labels), which the backward simulation handles at the enclosing frame.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The head shapes of the backward relation** at the target's first non-value `b`, with the
target values `V₁` of the segment it belongs to. -/
inductive THead : Bool → List Val → Admin → List Admin → List Admin → Prop where
  | same {tl : Bool} {b : Admin} {rest' x : List Admin} : ¬ b.IsCtx → R false tl x rest' →
      THead tl [] b rest' (b :: x)
  | instr {i : Instr} {b : Admin} {rest' x y : List Admin} : R false true x y →
      (tailI i).map .plain ++ y = b :: rest' → THead true [] b rest' (.plain i :: x)
  | rcr {c c' : Admin} {x y : List Admin} : RCRPair c c' → R false true x y →
      THead true [] c' (.plain .return_ :: y) (c :: x)
  | label {tl : Bool} {n : Nat} {cont cont' : List Instr} {b b' rest' x : List Admin} :
      (cont' = cont ∨ (tl = true ∧ cont' = tailL cont)) → R false tl b b' → R false tl x rest' →
      THead tl [] (.label n cont' b') rest' (.label n cont b :: x)
  | handler {tl : Bool} {n : Nat} {cs : List Catch} {b b' rest' x : List Admin} :
      R false false b b' → R false tl x rest' →
      THead tl [] (.handler n cs b') rest' (.handler n cs b :: x)
  | seg {tl : Bool} {k : Nat} {xs : List Admin} {b : Admin} {rest' x : List Admin} :
      CE false k xs [b] → R false tl x rest' → THead tl [] b rest' (xs ++ x)
  | call {tl : Bool} {k : Nat} {vs : List Val} {a : Nat} {d : DefType} {rest' x : List Admin} :
      Arity d k vs → R false tl x rest' →
      THead tl (vs ++ [.ref (.func a)]) (.callRefType d) rest'
        (vals vs ++ [.ref (.func a), .callRefType d] ++ x)
  | trap {tl : Bool} {ws : List Val} {b : Admin} {rest' : List Admin} (us : List Val)
      (x : List Admin) : TA (vals ws ++ b :: rest') → THead tl ws b rest' (vals us ++ .trap :: x)
  | throw {tl : Bool} {ws : List Val} {b : Admin} {rest' : List Admin} {e : Nat} (us : List Val)
      (x : List Admin) : TT e (vals ws ++ b :: rest') →
      THead tl ws b rest' (vals us ++ throwing e ++ x)

/-- The target side of a backward callee segment: a frame, or a call redex related to itself. -/
theorem CE.tgt_shape_aux : ∀ {fw : Bool} {k : Nat} {xs ys : List Admin}, CE fw k xs ys →
    (∃ fi B, ys = [.frame k fi B]) ∨
      ∃ (vs : List Val) (a : Nat) (d : DefType), xs = vals vs ++ [.ref (.func a), .callRefType d] ∧
        ys = xs ∧ Arity d k vs
  | _, _, _, _, .frame _ => .inl ⟨_, _, rfl⟩
  | _, _, _, _, .call har => .inr ⟨_, _, _, rfl, rfl, har⟩
  | _, _, _, _, .pend _ _ _ _ => .inl ⟨_, _, rfl⟩
  | _, _, _, _, .wrap _ _ => .inl ⟨_, _, rfl⟩
  | _, _, _, _, .vals _ _ => .inl ⟨_, _, rfl⟩

theorem tailI_head_val {i : Instr} {v : Val} {y : List Admin} {z : List Admin}
    (h : (tailI i).map Admin.plain ++ y = v.toAdmin :: z) : tailI i = [i] ∧ Admin.plain i = v.toAdmin ∧ z = y := by
  rcases tailI_cases' i with hti | hi
  · rw [hti] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨hti, h.1, h.2.symm⟩
  · exfalso
    rcases hi with ⟨x, rfl⟩ | ⟨x, y', rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ <;>
      simp only [Silmaril.Wasm.LimeCompile.Tail.tailI] at h <;>
      simp only [List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at h <;>
      rcases v with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at h
where
  tailI_cases' (i : Instr) :
      tailI i = [i] ∨ (∃ x, i = .returnCall x) ∨ (∃ x y, i = .returnCallIndirect x y) ∨
        (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨
          (∃ bt b₁ b₂, i = .if_ bt b₁ b₂) := by
    cases i <;> first
      | exact .inr (.inl ⟨_, rfl⟩)
      | exact .inr (.inr (.inl ⟨_, _, rfl⟩))
      | exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      | exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl⟩))))
      | exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
      | (left; simp [Silmaril.Wasm.LimeCompile.Tail.tailI])

/-- **Decomposition at the target's active head** (backward relation). -/
theorem R.tsplit {tl : Bool} {b : Admin} {rest' : List Admin} (hb : b.val? = none) :
    ∀ {V : List Val} {x : List Admin}, R false tl x (vals V ++ b :: rest') →
      ∃ (V₀ V₁ : List Val) (x₀ : List Admin), V = V₀ ++ V₁ ∧ x = vals V₀ ++ x₀ ∧
        THead tl V₁ b rest' x₀ := by
  intro V
  induction V with
  | nil =>
    intro x h
    generalize hy : vals [] ++ b :: rest' = y at h
    cases h with
    | nil => simp at hy
    | same hc h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨[], [], _, rfl, by simp, .same hc h'⟩
    | @instr _ i x' y' h' =>
      exact ⟨[], [], .plain i :: x', rfl, by simp,
        .instr h' (by simpa [Sim.vals_nil'] using hy.symm)⟩
    | rcr hc h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨[], [], _, rfl, by simp, .rcr hc h'⟩
    | label hc hb' h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨[], [], _, rfl, by simp, .label hc hb' h'⟩
    | handler hb' h' =>
      simp only [Sim.vals_nil', List.nil_append, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨[], [], _, rfl, by simp, .handler hb' h'⟩
    | callee hce h' =>
      rcases CE.tgt_shape_aux hce with ⟨fi, B, rfl⟩ | ⟨vs, a, d, rfl, rfl, har⟩
      · simp only [Sim.vals_nil', List.nil_append, List.singleton_append, List.cons.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨[], [], _, rfl, by simp, .seg hce h'⟩
      · rw [call_redex_eq] at hy
        obtain ⟨h1, -, -⟩ := vals_append_cons_inj hb (val?_crt d) hy
        simp at h1
    | trapC us x ht =>
      exact ⟨[], [], vals us ++ .trap :: x, rfl, by simp,
        .trap us x (by rw [hy]; exact ht)⟩
    | @throwC _ _ e us x _ ht =>
      exact ⟨[], [], vals us ++ throwing e ++ x, rfl, by simp,
        .throw us x (by rw [hy]; exact ht)⟩
  | cons v V ih =>
    intro x h
    generalize hy : vals (v :: V) ++ b :: rest' = y at h
    cases h with
    | nil => simp at hy
    | same hc h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      obtain ⟨V₀, V₁, x₀, rfl, rfl, hh⟩ := ih h'
      exact ⟨v :: V₀, V₁, x₀, rfl, by simp, hh⟩
    | @instr _ i x' y' h' =>
      simp only [Sim.vals_cons', List.cons_append] at hy
      obtain ⟨hti, hv, hz⟩ := tailI_head_val hy.symm
      obtain ⟨V₀, V₁, x₀, rfl, rfl, hh⟩ := ih (hz ▸ h')
      exact ⟨v :: V₀, V₁, x₀, rfl, by simp [hv], hh⟩
    | rcr hc h' =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hy
      have := Admin.val?_of_isCallRef (RCRPair.isCallRef hc)
      rw [← hy.1] at this; simp at this
    | label =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hy
      have hn := Val.toAdmin_not_ctx v
      rw [hy.1] at hn; exact absurd trivial hn
    | handler =>
      simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hy
      have hn := Val.toAdmin_not_ctx v
      rw [hy.1] at hn; exact absurd trivial hn
    | callee hce h' =>
      rcases CE.tgt_shape_aux hce with ⟨fi, B, rfl⟩ | ⟨vs, a, d, rfl, rfl, har⟩
      · simp only [Sim.vals_cons', List.cons_append, List.cons.injEq] at hy
        have hn := Val.toAdmin_not_ctx v
        rw [hy.1] at hn; exact absurd trivial hn
      · rw [call_redex_eq] at hy
        obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj hb (val?_crt d) hy
        exact ⟨[], _, _, by rw [List.nil_append, h1], by simp, .call har h'⟩
    | trapC us x ht =>
      exact ⟨[], _, vals us ++ .trap :: x, by rw [List.nil_append], by simp,
        .trap us x (by rw [hy]; exact ht)⟩
    | @throwC _ _ e us x _ ht =>
      exact ⟨[], _, vals us ++ throwing e ++ x, by rw [List.nil_append], by simp,
        .throw us x (by rw [hy]; exact ht)⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
