module

public import Silmaril.Proofs.Wasm.Models.FXBind.Exact

/-!
# Partial application: the untyped `cont.bind` breaks the intended lowering

A concrete counterexample. The store `firstS` holds one function `first`,
`(func (param i32 i32) (result i32) (local.get 0))`, at address `0`. The source binds `y` and
resumes with `x`:

    x y ref.func 0 cont.new cont.bind resume          (vs₂ = [x], vs₁ = [y])

The intended target calls `first y x` and returns `[y]`. The untyped `cont.bind` may also bind
nothing, and `resume` then passes both values in stack order: `first x y` returns `[x]`. The
arity matches (`first` takes two parameters, `|vs₂ ++ vs₁| = 2`), so an arity check on the
call does not exclude it: only a typed `cont.bind` (binding exactly the parameters that `$ct`
has beyond `$ct'`) does.

* `first_runs`: `p q ref.func 0 call_ref` runs to `p` (any host);
* `nf_unique`: in a relation whose one-step successors join in at most one step each, two runs
  to normal forms end at the same configuration;
* `first_returns_only` (deterministic profile, no host calls): the call's only return is `[p]`;
* **`bind_ne_target`**: for `x ≠ y`, the source has the behaviour `returns [x]`, which the
  intended target does not have, so the two behaviour sets differ.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Wasm.SingleThreaded.Det (noHost Join not_step_vals)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- `(func (param i32 i32) (result i32))` as a closed defined type. -/
def firstD : DefType :=
  .defn (.group (.cons (.sub true .nil (Ty.funcOf [Ty.i32, Ty.i32] [Ty.i32])) .nil)) 0

theorem firstD_expand :
    Expand firstD (.func (Ty.ofList [Ty.i32, Ty.i32]) (Ty.ofList [Ty.i32])) := by
  decide

/-- The function `first`: return the first argument. -/
def firstFi : FuncInst H :=
  { type := firstD, module := {}, code := .wasm { type := ⟨0⟩, locals := [], body := [.localGet ⟨0⟩] } }

/-- The store with `first` at address `0`. -/
def firstS : Store H := { funcs := [firstFi] }

theorem firstS_func : (firstS (H := H)).funcs[0]? = some firstFi := rfl

/-- **`first p q` returns `p`** (any profile, any host). -/
theorem first_runs {P : Profile} {host : HostSemantics H} (f : Frame) (p q : Val) :
    Steps P host ⟨firstS, f, tgtCall 0 firstD [p, q]⟩ ⟨firstS, f, vals [p]⟩ := by
  let F : Frame := Frame.forCall {} [p, q] []
  have h1 : Step P host ⟨firstS, f, tgtCall 0 firstD [p, q]⟩
      ⟨firstS, f, [.frame 1 F [.label 1 [] [.plain (.localGet ⟨0⟩)]]]⟩ :=
    Step.callRefFunc (vs := [p, q]) (by simp [Admin.IsCallRef]) firstS_func firstD_expand rfl rfl
  have hl : F.local? ⟨0⟩ = some (some p) := rfl
  have h2 : Step P host ⟨firstS, f, [.frame 1 F [.label 1 [] [.plain (.localGet ⟨0⟩)]]]⟩
      ⟨firstS, f, [.frame 1 F [.label 1 [] (vals [p])]]⟩ :=
    Step.ctxtFrame (Step.ctxtLabel (Step.variable (VariableStep.localGet hl)))
  have h3 : Step P host ⟨firstS, f, [.frame 1 F [.label 1 [] (vals [p])]]⟩
      ⟨firstS, f, [.frame 1 F (vals [p])]⟩ :=
    Step.ctxtFrame Step.labelVals
  have h4 : Step P host ⟨firstS, f, [.frame 1 F (vals [p])]⟩ ⟨firstS, f, vals [p]⟩ :=
    Step.frameVals rfl
  exact (((Relation.ReflTransGen.single h1).tail h2).tail h3).tail h4

/-! ## Unique normal forms -/

section NF

variable {α : Type} {R : α → α → Prop}

/-- A step out of a configuration that runs to a normal form keeps the normal form reachable. -/
theorem step_to_nf (hj : ∀ x y z, R x y → R x z → Join R y z) {c r : α}
    (h : Relation.ReflTransGen R c r) (hn : ∀ z, ¬ R r z) :
    ∀ c₁, R c c₁ → Relation.ReflTransGen R c₁ r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun c₁ hc => absurd hc (hn c₁)
  | head hcc' hrest ih =>
    intro c₁ hc₁
    obtain ⟨z, h₁, h₂⟩ := hj _ _ _ hc₁ hcc'
    cases h₂ with
    | refl =>
      cases h₁ with
      | refl => exact hrest
      | single h => exact Relation.ReflTransGen.head h hrest
    | single h =>
      have hz := ih z h
      cases h₁ with
      | refl => exact hz
      | single h' => exact Relation.ReflTransGen.head h' hz

/-- **Unique normal forms** for a relation with the one-step diamond property. -/
theorem nf_unique (hj : ∀ x y z, R x y → R x z → Join R y z) {c r₁ r₂ : α}
    (h₁ : Relation.ReflTransGen R c r₁) (h₂ : Relation.ReflTransGen R c r₂)
    (n₁ : ∀ z, ¬ R r₁ z) (n₂ : ∀ z, ¬ R r₂ z) : r₁ = r₂ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨y, hy, -⟩
    · exact h
    · exact absurd hy (n₁ y)
  | head hcc' _ ih => exact ih (step_to_nf hj h₂ n₂ _ hcc')

end NF

/-- **The call `first p q` returns only `p`** (deterministic profile, no host calls). -/
theorem first_returns_only (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    (f : Frame) {p q : Val} {w : List Val}
    (hb : Behaviour.returns w ∈
      behavioursOf (Profile.deterministic o) noHost ⟨firstS (H := H), f, tgtCall 0 firstD [p, q]⟩) :
    w = [p] := by
  rcases hb with ⟨c', r, hrun, hcode, hbr⟩ | ⟨hd, -⟩
  · cases r with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hbr
      subst hbr
      have hj : ∀ x y z : Config H, Step (Profile.deterministic o) noHost x y →
          Step (Profile.deterministic o) noHost x z →
          Join (Step (Profile.deterministic o) noHost) y z :=
        fun _ _ _ h₁ h₂ => Silmaril.Wasm.SingleThreaded.Det.DStep.join' h₁ h₂
      have n₁ : ∀ z, ¬ Step (Profile.deterministic o) noHost c' z := by
        intro z hz
        obtain ⟨s', f', code⟩ := c'
        simp only [Result.toAdmin] at hcode
        subst hcode
        exact not_step_vals hz
      have n₂ : ∀ z, ¬ Step (Profile.deterministic o) noHost ⟨firstS (H := H), f, vals [p]⟩ z :=
        fun z hz => not_step_vals hz
      have he := nf_unique hj hrun (first_runs f p q) n₁ n₂
      have hc := congrArg Config.code he
      rw [hcode] at hc
      exact Silmaril.Wasm.SingleThreaded.Det.vals_inj.mp hc
    | throw a => simp [Result.toBehaviour] at hbr
    | trap => simp [Result.toBehaviour] at hbr
  · cases hd

/-- **The partial-application lowering is not correct for the untyped `cont.bind`**: binding
`y` and resuming with `x` has the behaviour `returns [x]`, which the intended call `first y x`
does not have. The arity matches, so `bind_eq_rot` applies: the extra behaviour is the rotation
in which `cont.bind` binds nothing. -/
theorem bind_ne_target (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {x y : Val} (hxy : x ≠ y) (K : List (Option ContFX)) (f : Frame) (ct ct' : TypeIdx) :
    behavioursFX (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, f, srcBind 0 ct ct' [] [x] [y]⟩ ≠
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), f, tgtCall 0 firstD ([y] ++ [x])⟩ := by
  intro heq
  have hsrc : Behaviour.returns [x] ∈ behavioursFX (Profile.deterministic o) noHost noFX
      ⟨firstS (H := H), K, f, srcBind 0 ct ct' [] [x] [y]⟩ := by
    have h := bind_rot_sound (P := Profile.deterministic o) (host := noHost) (fx := noFX) (K := K)
      (f := f) (ct := ct) (ct' := ct') (hs := []) (hs' := []) (vs₂ := [x]) (vs₁ := [y])
      (X₂ := [x, y]) (U₂ := [])
      (firstS_func (H := H)) rfl rfl
    rw [Silmaril.Wasm.Models.FX.blockFX_noFX] at h
    exact h (Or.inl ⟨_, .values [x], first_runs f x y, rfl, rfl⟩)
  rw [heq] at hsrc
  have := first_returns_only o f hsrc
  simp only [List.cons.injEq, and_true] at this
  exact hxy this

end Silmaril.Proofs.Wasm.Models.FXBind
