module

public import Silmaril.Wasm.Binaryen.Inline
public import Silmaril.Wasm.Binaryen.Exe.InlineExe

@[expose] public section

/-! # The callee check of the executable inliner, on the proof side

`calleeOk_good`: a callee accepted by `Inl.calleeOk` is structured, free of tail calls and
satisfies `retGoodL 0`, the hypotheses of `inlineSite_valid_mt` and
`inlineSite_sound_of_good`. Without `return` this is `noRetL_good`; with `return` it is
`retGoodL_of`, from the depth bound the check tests on `Inl.depthL` (`depthL_eq`: the copy
is `BExpr.depthList`) and from `anyL_good` (a tree inside the profile is structured and
has no tail calls).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen

mutual
theorem depthE_eq : ∀ e : BExpr, Inl.depthE e = BExpr.depth e
  | .op _ args => by rw [Inl.depthE, BExpr.depth, depthL_eq args]
  | .block _ b => by rw [Inl.depthE, BExpr.depth, depthL_eq b]
  | .loop _ b => by rw [Inl.depthE, BExpr.depth, depthL_eq b]
  | .if_ _ c t e => by rw [Inl.depthE, BExpr.depth, depthL_eq c, depthL_eq t, depthL_eq e]
  | .tryTable _ _ b => by rw [Inl.depthE, BExpr.depth, depthL_eq b]
theorem depthL_eq : ∀ es : List BExpr, Inl.depthL es = BExpr.depthList es
  | [] => by rw [Inl.depthL, BExpr.depthList]
  | e :: es => by rw [Inl.depthL, BExpr.depthList, depthE_eq e, depthL_eq es]
end

mutual
/-- A tree inside the profile (`any = false`) is structured and has no tail calls. -/
theorem any_good : ∀ e : BExpr, (effects e).any = false →
    e.structured = true ∧ (∀ i ∈ e.lower, instrHasTailCall i = false)
  | .op i args, ha => by
    simp only [effects, Effects.merge, Bool.or_eq_false_iff] at ha
    obtain ⟨h1, h2⟩ := anyL_good args ha.1
    obtain ⟨hs, ht⟩ := instrEffects_flat ha.2
    refine ⟨by simp [BExpr.structured, hs, h1], ?_⟩
    intro j hj
    simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact h2 j hj
    · exact ht
  | .block bt b, ha => by
    simp only [effects, Effects.unbindLabel] at ha
    obtain ⟨h1, h2⟩ := anyL_good b ha
    refine ⟨h1, ?_⟩
    intro j hj
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrHasTailCall]
    exact tailCall_body_false h2
  | .loop bt b, ha => by
    simp only [effects, Effects.unbindLabel] at ha
    obtain ⟨h1, h2⟩ := anyL_good b ha
    refine ⟨h1, ?_⟩
    intro j hj
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrHasTailCall]
    exact tailCall_body_false h2
  | .if_ bt c t e, ha => by
    simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff] at ha
    obtain ⟨c1, c2⟩ := anyL_good c ha.1
    obtain ⟨t1, t2⟩ := anyL_good t ha.2.1
    obtain ⟨e1, e2⟩ := anyL_good e ha.2.2
    refine ⟨by simp [BExpr.structured, c1, t1, e1], ?_⟩
    intro j hj
    simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact c2 j hj
    · rw [instrHasTailCall, tailCall_body_false t2, tailCall_body_false e2]
      rfl
  | .tryTable _ _ _, ha => by simp [effects, Effects.top] at ha
/-- `any_good` on a list. -/
theorem anyL_good : ∀ es : List BExpr, (effectsList es).any = false →
    BExpr.structuredList es = true ∧ (∀ i ∈ BExpr.lowerList es, instrHasTailCall i = false)
  | [], _ => ⟨rfl, by simp⟩
  | e :: es, ha => by
    simp only [effectsList, Effects.merge, Bool.or_eq_false_iff] at ha
    obtain ⟨h1, h2⟩ := any_good e ha.1
    obtain ⟨k1, k2⟩ := anyL_good es ha.2
    refine ⟨by simp [BExpr.structuredList, h1, k1], ?_⟩
    intro j hj
    simp only [BExpr.lowerList_cons, List.mem_append] at hj
    rcases hj with hj | hj
    · exact h2 j hj
    · exact k2 j hj
end

/-- **A callee accepted by `calleeOk` can be inlined**: it is structured, has no tail calls
and its `return`s are rewritten exactly. -/
theorem calleeOk_good {budget : Nat} {m : BModule} {f : FuncIdx}
    (hc : Inl.calleeOk budget m f = true) {fn : BFunc} (hfn : m.defFunc? f.toNat = some fn) :
    (BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body) ∧
      InlineTy.retGoodL 0 (BExpr.lowerList fn.body) := by
  simp only [Inl.calleeOk, hfn, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨-, ha⟩, hr⟩, -⟩ := hc
  obtain ⟨hs, ht⟩ := anyL_good fn.body ha
  refine ⟨⟨hs, ht⟩, ?_⟩
  rcases hr with hb | hd
  · exact (noRetL_good 0 fn.body ha hb).2.2
  · rw [depthL_eq] at hd
    exact retGoodL_of 0 fn.body hs ht (by omega)

end Silmaril.Wasm.Binaryen.Exe
