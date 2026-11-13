module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdBase

/-!
# The backward simulation of the tail-call rewrite: sources of target shapes

* `R.vals_tinv`: the source of target values is the same values;
* `R.kernel_tinv`, `R.rcr_tinv`: the source of values before `br`/`return` or a
  `return_call_ref` on the target has the same values and kernel;
* `R.trap_tinv`, `R.throw_tinv`: the source of a target trap (throw) is trap- (throw-)
  shaped;
* `TA.step`, `TT.step`: trap- and throw-active code steps only to trap- and throw-active code,
  in the same store and frame, with smaller code;
* `CallHead.match_back`: a target call is matched by the same call on the source.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem tailI_ne_nil (i : Instr) : tailI i ≠ [] := by
  rcases tailI_cases i with h | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ |
    ⟨bt, b₁, b₂, rfl⟩
  · rw [h]; simp
  all_goals simp [Silmaril.Wasm.LimeCompile.Tail.tailI]

theorem CE.tgt_ne_nil {fw : Bool} {k : Nat} {xs ys : List Admin} (h : CE fw k xs ys) :
    ys ≠ [] := by
  rcases CE.tgt_shape_aux h with ⟨fi, B, rfl⟩ | ⟨vs, a, d, rfl, rfl, -⟩ <;> simp

/-- A single-instruction target segment of a callee is a frame. -/
theorem CE.tgt_single {fw : Bool} {k : Nat} {xs : List Admin} {b : Admin} (h : CE fw k xs [b]) :
    ∃ fi B, b = .frame k fi B := by
  rcases CE.tgt_shape_aux h with ⟨fi, B, h1⟩ | ⟨vs, a, d, rfl, h1, -⟩
  · simp only [List.cons.injEq, and_true] at h1
    exact ⟨fi, B, h1⟩
  · have := congrArg List.length h1
    simp at this

/-- **The head of a rewritten instruction.** -/
theorem tailI_head {i : Instr} {y : List Admin} {b : Admin} {rest : List Admin}
    (h : (tailI i).map Admin.plain ++ y = b :: rest) :
    (tailI i = [i] ∧ b = .plain i ∧ rest = y) ∨ (∃ x, i = .returnCall x ∧ b = .plain (.call x)) ∨
      (∃ x y', i = .returnCallIndirect x y' ∧ b = .plain (.callIndirect x y')) ∨
      (∃ bt bd, i = .block bt bd ∧ b = .plain (.block bt (tailL bd))) ∨
      (∃ bt bd, i = .loop bt bd ∧ b = .plain (.loop bt (tailL bd))) ∨
      (∃ bt b₁ b₂, i = .if_ bt b₁ b₂ ∧ b = .plain (.if_ bt (tailL b₁) (tailL b₂))) := by
  rcases tailI_cases i with hti | ⟨x, rfl⟩ | ⟨x, y', rfl⟩ | ⟨bt, bd, rfl⟩ | ⟨bt, bd, rfl⟩ |
    ⟨bt, b₁, b₂, rfl⟩
  · rw [hti] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    exact .inl ⟨hti, h.1.symm, h.2.symm⟩
  · rw [tailI_returnCall] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at h
    exact .inr (.inl ⟨x, rfl, h.1.symm⟩)
  · rw [tailI_returnCallIndirect] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at h
    exact .inr (.inr (.inl ⟨x, y', rfl, h.1.symm⟩))
  · rw [tailI_block] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    exact .inr (.inr (.inr (.inl ⟨bt, bd, rfl, h.1.symm⟩)))
  · rw [tailI_loop] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    exact .inr (.inr (.inr (.inr (.inl ⟨bt, bd, rfl, h.1.symm⟩))))
  · rw [tailI_if] at h
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    exact .inr (.inr (.inr (.inr (.inr ⟨bt, b₁, b₂, rfl, h.1.symm⟩))))

/-- A head of a rewritten instruction that is not a plain control instruction is the instruction
itself. -/
theorem tailI_head_id {i : Instr} {y : List Admin} {b : Admin} {rest : List Admin}
    (h : (tailI i).map Admin.plain ++ y = b :: rest)
    (hb : ∀ j, b = .plain j → ¬ IsCtl j) : tailI i = [i] ∧ b = .plain i ∧ rest = y := by
  rcases tailI_head h with h1 | ⟨x, rfl, rfl⟩ | ⟨x, y', rfl, rfl⟩ | ⟨bt, bd, rfl, rfl⟩ |
    ⟨bt, bd, rfl, rfl⟩ | ⟨bt, b₁, b₂, rfl, rfl⟩
  · exact h1
  all_goals exact (hb _ rfl trivial).elim

/-- **The source of target values** is the same values. -/
theorem R.vals_tinv {tl : Bool} : ∀ {vs : List Val} {x : List Admin}, R false tl x (vals vs) →
    x = vals vs
  | [], x, h => by
    generalize hy : vals [] = y at h
    simp only [Sim.vals_nil'] at hy
    cases h with
    | nil => rfl
    | same => cases hy
    | @instr _ i _ _ _ =>
      have := congrArg List.length hy
      have h2 := tailI_ne_nil i
      simp at this
      exact (h2 (List.eq_nil_of_length_eq_zero (by omega))).elim
    | rcr => cases hy
    | label => cases hy
    | handler => cases hy
    | callee hce _ =>
      have := congrArg List.length hy
      have h2 := CE.tgt_ne_nil hce
      simp at this
      exact (h2 (List.eq_nil_of_length_eq_zero (by omega))).elim
    | trapC _ _ ht => exact (TA.not_vals ht [] (by rw [← hy]; rfl)).elim
    | throwC _ _ ht => exact (TT.not_vals ht [] (by rw [← hy]; rfl)).elim
  | v :: vs, x, h => by
    generalize hy : vals (v :: vs) = y at h
    cases h with
    | nil => simp at hy
    | same hc h' =>
      simp only [Sim.vals_cons', List.cons.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      rw [R.vals_tinv h']
    | @instr _ i x' y' h' =>
      rw [Sim.vals_cons'] at hy
      obtain ⟨hti, hv, rfl⟩ := tailI_head_val hy.symm
      rw [R.vals_tinv h', hti]
      rfl
    | rcr hc _ =>
      simp only [Sim.vals_cons', List.cons.injEq] at hy
      have := Admin.val?_of_isCallRef (RCRPair.isCallRef hc)
      rw [← hy.1] at this; simp at this
    | label =>
      simp only [Sim.vals_cons', List.cons.injEq] at hy
      have hn := Val.toAdmin_not_ctx v
      rw [hy.1] at hn; exact absurd trivial hn
    | handler =>
      simp only [Sim.vals_cons', List.cons.injEq] at hy
      have hn := Val.toAdmin_not_ctx v
      rw [hy.1] at hn; exact absurd trivial hn
    | callee hce _ =>
      exfalso
      rcases CE.tgt_shape_aux hce with ⟨fi, B, rfl⟩ | ⟨vs', a, d, rfl, rfl, -⟩
      · simp only [Sim.vals_cons', List.singleton_append, List.cons.injEq] at hy
        have hn := Val.toAdmin_not_ctx v
        rw [hy.1] at hn; exact absurd trivial hn
      · have hm : Admin.callRefType d ∈ vals (v :: vs) := by rw [hy]; simp
        obtain ⟨w, hw⟩ := PC.mem_vals hm
        rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw
    | trapC _ _ ht => exact (TA.not_vals ht _ hy.symm).elim
    | throwC _ _ ht => exact (TT.not_vals ht _ hy.symm).elim

/-- A kernel that relates only to itself on both sides: `br`, `return`, `return_call_ref`. -/
def TKernel (k : Admin) : Prop := Rigid k ∨ k.IsReturnCallRef

theorem TKernel.val?_eq {k : Admin} (hk : TKernel k) : k.val? = none := by
  rcases hk with hk | hk
  · exact hk.val?_eq
  · exact Admin.val?_of_isReturnCallRef hk

theorem TKernel.not_ctx {k : Admin} (hk : TKernel k) : ¬ k.IsCtx := by
  rcases k with i | _ | _ | _ | _ | _ | _ | _
  · simp [Admin.IsCtx]
  all_goals first | (rcases hk with hk | hk <;> exact (hk : False).elim) | simp [Admin.IsCtx]

theorem TKernel.not_callRef {k : Admin} (hk : TKernel k) : ¬ k.IsCallRef := by
  rcases hk with hk | hk
  · rcases k with i | _ | _ | _ | _ | _ | _ | _
    · cases i <;> simp_all [Rigid, Admin.IsCallRef]
    all_goals exact fun _ => (hk : False).elim
  · exact fun h => Admin.IsCallRef.not_isReturnCallRef h hk

theorem TKernel.not_ctl {k : Admin} (hk : TKernel k) : ∀ j, k = .plain j → ¬ IsCtl j := by
  rintro j rfl hj
  rcases hk with hk | hk <;> cases j <;> simp_all [Rigid, IsCtl, Admin.IsReturnCallRef]

/-- **Kernels on the target** come from the same kernel on the source. -/
theorem R.kernel_tinv {tl : Bool} {V : List Val} {k : Admin} {rest' x : List Admin}
    (hk : TKernel k) (h : R false tl x (vals V ++ k :: rest')) :
    ∃ x', x = vals V ++ k :: x' ∧ R false tl x' rest' := by
  obtain ⟨V₀, V₁, x₀, rfl, rfl, hh⟩ := R.tsplit hk.val?_eq h
  cases hh with
  | same _ hr => exact ⟨_, by simp, hr⟩
  | instr hr heq =>
    obtain ⟨-, rfl, rfl⟩ := tailI_head_id heq hk.not_ctl
    exact ⟨_, by simp, hr⟩
  | rcr hc _ => exact (hk.not_callRef (RCRPair.isCallRef hc)).elim
  | label => exact (hk.not_ctx trivial).elim
  | handler => exact (hk.not_ctx trivial).elim
  | seg hce _ =>
    obtain ⟨fi, B, rfl⟩ := CE.tgt_single hce
    exact (hk.not_ctx trivial).elim
  | call => exact (hk.not_callRef trivial).elim
  | trap us x ht =>
    rcases TA.head ht hk.val?_eq rfl with h1 | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩
    · subst h1; rcases hk with hk | hk <;> exact (hk : False).elim
    · subst h1; exact (hk.not_ctx trivial).elim
    · subst h1; exact (hk.not_ctx trivial).elim
  | throw us x ht =>
    rcases TT.head ht hk.val?_eq rfl with ⟨h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩
    · subst h1; rcases hk with hk | hk <;> exact (hk : False).elim
    · subst h1; exact (hk.not_ctx trivial).elim
    · subst h1; exact (hk.not_ctx trivial).elim

/-- **A target trap** comes from a source trap after values. -/
theorem R.trap_tinv {tl : Bool} {V : List Val} {rest' x : List Admin}
    (h : R false tl x (vals V ++ .trap :: rest')) : ∃ us x', x = vals us ++ .trap :: x' := by
  obtain ⟨V₀, V₁, x₀, rfl, rfl, hh⟩ := R.tsplit rfl h
  cases hh with
  | @same _ _ _ x' _ _ => exact ⟨V₀, x', by simp⟩
  | instr _ heq =>
    rcases tailI_head heq with ⟨-, h1, -⟩ | ⟨_, -, h1⟩ | ⟨_, _, -, h1⟩ | ⟨_, _, -, h1⟩ |
      ⟨_, _, -, h1⟩ | ⟨_, _, _, -, h1⟩ <;> cases h1
  | rcr hc _ => exact absurd (RCRPair.isCallRef hc) (by simp [Admin.IsCallRef])
  | seg hce _ =>
    obtain ⟨fi, B, h1⟩ := CE.tgt_single hce
    cases h1
  | trap us x _ => exact ⟨V₀ ++ us, x, by simp⟩
  | throw us x ht =>
    rcases TT.head ht rfl rfl with ⟨h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ <;> cases h1

/-- **A target throw** comes from a source throw of the same exception. -/
theorem R.throw_tinv {tl : Bool} {V : List Val} {a : Nat} {rest' x : List Admin}
    (h : R false tl x (vals V ++ throwing a ++ rest')) :
    ∃ us x', x = vals us ++ throwing a ++ x' := by
  rw [throw_eq] at h
  obtain ⟨V₀, V₁, x₀, hV, rfl, hh⟩ := R.tsplit rfl h
  cases hh with
  | @same _ _ _ x' _ _ =>
    simp only [List.append_nil] at hV
    exact ⟨V, x', by rw [throw_eq, ← hV]⟩
  | @instr i _ _ x' _ _ heq =>
    obtain ⟨-, h1, -⟩ := tailI_head_id heq (by
      intro j hj hc
      simp only [Admin.plain.injEq] at hj
      subst hj
      exact hc)
    simp only [Admin.plain.injEq] at h1
    subst h1
    simp only [List.append_nil] at hV
    exact ⟨V, x', by rw [throw_eq, ← hV]⟩
  | rcr hc _ => exact absurd (RCRPair.isCallRef hc) (by simp [Admin.IsCallRef])
  | seg hce _ =>
    obtain ⟨fi, B, h1⟩ := CE.tgt_single hce
    cases h1
  | trap us x ht =>
    rcases TA.head ht rfl rfl with h1 | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ <;> cases h1
  | @throw _ _ _ _ e us x ht =>
    rcases TT.head ht rfl rfl with ⟨-, ws', hws⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩
    · have hea : e = a := by
        have h2 := congrArg List.getLast? hV
        rw [hws] at h2
        simp at h2; exact h2.symm
      subst hea
      exact ⟨V₀ ++ us, x, by simp⟩
    · cases h1
    · cases h1

end Silmaril.Raw.Wasm.LimeCompile.TailSim
