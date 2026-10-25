module

public import Silmaril.Wasm.Binaryen.Pass.MergeBlocksAny

@[expose] public section

/-! Certificates for the nested-block search. -/

namespace Silmaril.Wasm.Binaryen.MergeBlocksAny

/-- A search result reconstructs its input and satisfies the unwrapping check. -/
def Good (es : List BExpr) (s : Site) : Prop :=
  es = s.ctx.plug [.block s.type s.body] ∧ UnusedBlocks.eligible s.body = true

/-- Context composition transports the search certificate. -/
theorem under_good {es : List BExpr} {ss : List Site} (k : BCtx)
    (h : ∀ s ∈ ss, Good es s) : ∀ s ∈ under k ss, Good (k.plug es) s := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  obtain ⟨he, hb⟩ := h t ht
  exact ⟨by simpa [BCtx.plug_comp] using congrArg k.plug he, hb⟩

/-- Descending under a node retains its complete source expression. -/
theorem children_good (search : List BExpr → Bool → List Site)
    (h : ∀ es b s, s ∈ search es b → Good es s) (e : BExpr) :
    ∀ s ∈ children search e, Good [e] s := by
  cases e with
  | op i args => simpa [children, BCtx.plug] using under_good (.op i [] .hole []) (h args false)
  | block bt body =>
    simpa [children, BCtx.plug] using under_good (.block bt [] .hole []) (h body true)
  | loop bt body =>
    simpa [children, BCtx.plug] using under_good (.loop bt [] .hole []) (h body false)
  | if_ bt c t f =>
    intro s hs
    simp only [children, List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · simpa [BCtx.plug] using under_good (.ifCond bt [] .hole [] t f) (h c false) s hs
    · simpa [BCtx.plug] using under_good (.ifThen bt c [] .hole [] f) (h t false) s hs
    · simpa [BCtx.plug] using under_good (.ifElse bt c t [] .hole []) (h f false) s hs
  | tryTable => simp [children]

/-- The check at the current node supplies its eligibility certificate. -/
theorem here_good (e : BExpr) (b : Bool) : ∀ s ∈ here e b, Good [e] s := by
  cases e <;> simp only [here]
  case block bt body =>
    split
    · next he =>
      intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      have he' : b = true ∧ UnusedBlocks.eligible body = true := by
        simpa only [Bool.and_eq_true] using he
      exact ⟨rfl, he'.2⟩
    · simp
  all_goals simp

/-- Every enumerated site is a checked one-hole decomposition of the input. -/
theorem sites_good (fuel : Nat) :
    ∀ es b s, s ∈ sites fuel es b → Good es s := by
  induction fuel with
  | zero => simp [sites]
  | succ fuel ih =>
    intro es b s hs
    cases es with
    | nil => simp [sites] at hs
    | cons e es =>
      simp only [sites, List.mem_append] at hs
      rcases hs with hs | hs
      · have h : ∀ t ∈ children (sites fuel) e ++ here e b, Good [e] t := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact children_good (sites fuel) ih e t ht
          · exact here_good e b t ht
        simpa [BCtx.plug] using under_good (.seq [] .hole es) h s hs
      · simpa [BCtx.plug] using under_good (.seq [e] .hole []) (ih es b) s hs

end Silmaril.Wasm.Binaryen.MergeBlocksAny
