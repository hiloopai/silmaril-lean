module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsDeferred

@[expose] public section

/-! # The real reverse base match for CoalesceLocals

The original side's first write is matched by target drop and overwrite steps.
The source's immediate overwrite is recorded as an actual forced completion,
after which the frames agree exactly. The suffix remains unrestricted.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics
open VacuumLite (constInstr constInstr_val)

variable {H : Type} {P : Profile} {F : FuncInst H → FuncInst H → Prop}

def reverseBI (a b : List Instr) : Prop := dsBI b a

def reverseB (a b : List Admin) : Prop :=
  ∃ (x : LocalIdx) (w : Val),
    a = [.plain (.localSet x), w.toAdmin, .plain (.localSet x)] ∧
    b = [.plain .drop, w.toAdmin, .plain (.localSet x)]

theorem reverseFacts : BaseFacts P closedHost F reverseBI reverseB aszs where
  src := by
    rintro a b ⟨x, k, hk, rfl, rfl⟩
    obtain ⟨w, hw⟩ := constInstr_val hk
    exact ⟨x, w, by simp [Execution.Core.expression, hw],
      by simp [Execution.Core.expression, hw]⟩
  exit := by
    intro s t f vs us a b k j hst hab hk he
    obtain ⟨x, w, rfl, rfl⟩ := hab
    exfalso
    obtain ⟨pre, e, hen, rfl⟩ := hk.eq_vals_append
    have hmem : e ∈ vals pre ++ [e] := by simp
    have h₁ : vals vs ++ Admin.plain (.localSet x) :: [w.toAdmin, .plain (.localSet x)] =
        vals (us ++ pre) ++ e :: j := by simpa using he
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h₁
    exact exit_not_set hk x _ hmem rfl
  values := by
    intro s t f vs us a b hst hab ha
    obtain ⟨x, w, rfl, rfl⟩ := hab
    exfalso
    have hmem : Admin.plain (.localSet x) ∈ vals us := by rw [← ha]; simp
    obtain ⟨v, -, hv⟩ := List.mem_map.mp hmem
    have := congrArg Admin.val? hv
    rw [Admin.val?_toAdmin] at this
    cases this

theorem run_drop_set {t : Store H} {f : Frame} {x : LocalIdx}
    (hx : x.toNat < f.locals.length) (u w : Val) (vs : List Val) (rest : List Admin) :
    Relation.TransGen (Step P closedHost)
      ⟨t, f, vals vs ++ [u.toAdmin, .plain .drop, w.toAdmin, .plain (.localSet x)] ++ rest⟩
      ⟨t, f.setLocal x w, vals vs ++ rest⟩ := by
  have hdrop := Step.append_right
    (Step.vals_left (Step.parametric (P := P) (host := closedHost) (s := t) (f := f)
      (ParametricStep.drop u)) vs) ([w.toAdmin, .plain (.localSet x)] ++ rest)
  have hset := (Completion.set t f vs w x rest hx).step (P := P) (host := closedHost)
  exact Closure.transGen_congr
    (Relation.TransGen.head' (by simpa using hdrop) (.single hset)) (by simp) rfl

/-- The reverse base step uses an actual forced completion, at every numerical profile. -/
theorem reverseBaseSim : DeferredBaseSim P F reverseBI reverseB where
  facts := reverseFacts
  step := by
    intro s t s' f f' vs a b rest rest' es' hst hab hrest hs
    obtain ⟨x, w, rfl, rfl⟩ := hab
    rw [show vals vs ++ [Admin.plain (.localSet x), w.toAdmin, .plain (.localSet x)] ++ rest =
      vals vs ++ Admin.plain (.localSet x) :: (w.toAdmin :: .plain (.localSet x) :: rest)
      by simp] at hs
    rcases Step.split_head rfl hs with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · obtain ⟨us₀, u, rfl, h1, h2, h3, hx⟩ := step_set_inv hs₁ us x rfl
      dsimp only at h1 h2 h3 hx
      subst s' f' is' vs
      have hx' : x.toNat < (f.setLocal x u).locals.length := by
        simpa [Frame.setLocal] using hx
      have hn := Completion.set s (f.setLocal x u) (ws ++ us₀) w x rest hx'
      rw [Frame.setLocal_setLocal] at hn
      refine ⟨⟨s, f.setLocal x w, vals (ws ++ us₀) ++ rest⟩,
        ⟨t, f.setLocal x w, vals (ws ++ us₀) ++ rest'⟩,
        .complete (by simpa using hn), Or.inl ?_, hst, rfl, ?_⟩
      · simpa [vals] using run_drop_set (P := P) hx u w (ws ++ us₀) rest'
      · exact (AdminsRel.vals _).append hrest
    · cases he
    · cases he

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
