module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Step
public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Static linking, separation: Top

Original module documentation:

# Provider calls inside the consumer's context (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

In the shared world a call from the consumer into a provider function runs the provider's
code *inside* the consumer's evaluation context (the `Ctx` of the callout, `decompose?`); in
the split world the provider runs it as a separate thread whose configuration has the empty
frame of `$invoke`. This file provides the glue:

* `TopOK`: the code of a provider thread at top level (values, references, calls through
  `CALL_REF`, frames, traps and exception bubbles). Steps from such code do not read or write
  the outer frame (`step_reframe`), so they can be replayed under any frame and lifted into
  the consumer's context (`Ctx.step_fill`).
* `Ren.ctx`: renaming of callout contexts, with `Ren.code_fill`.
* `Own.CodeGood.fill`: goodness of a context does not depend on its hole.
* `reach_of_step`: host-free runs to a normal form are confluent (from the diamond
  `Internal.deterministic`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics

variable {H : Type}

/-! ### Top-level provider code -/

/-- Administrative instructions that may occur at the top level of a provider thread. -/
def TopAdmin : Admin → Prop
  | .plain (.intConst _ _) => True
  | .plain (.floatConst _ _) => True
  | .plain (.vecConst _) => True
  | .plain (.callRef _) => True
  | .plain .throwRef => True
  | .ref _ => True
  | .callRefType _ => True
  | .trap => True
  | .frame _ _ _ => True
  | _ => False

/-- Code that may occur at the top level of a provider thread. -/
def TopOK (l : List Admin) : Prop := ∀ a ∈ l, TopAdmin a

theorem TopOK.append {l₁ l₂ : List Admin} : TopOK (l₁ ++ l₂) ↔ TopOK l₁ ∧ TopOK l₂ := by
  simp only [TopOK, List.mem_append]
  exact ⟨fun h => ⟨fun a ha => h a (.inl ha), fun a ha => h a (.inr ha)⟩,
    fun h a ha => ha.elim (h.1 a) (h.2 a)⟩

theorem topAdmin_toAdmin (v : Val) : TopAdmin v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> trivial

theorem TopOK.vals (vs : List Val) : TopOK (vals vs) := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
  exact topAdmin_toAdmin v

theorem TopOK.nil : TopOK [] := by simp [TopOK]

theorem TopOK.cons {a : Admin} {l : List Admin} : TopOK (a :: l) ↔ TopAdmin a ∧ TopOK l := by
  simp [TopOK]

theorem TopOK.callRef {c : Admin} (hc : c.IsCallRef) : TopAdmin c := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef, TopAdmin]
  rename_i i
  cases i <;> simp_all [TopAdmin]

theorem TopOK.retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    TopAdmin (c.retToCallIn m) := by
  obtain ⟨y, rfl⟩ | ⟨d, rfl⟩ := Det.IsReturnCallRef.cases hc
  · simp only [Admin.retToCallIn]
    split <;> trivial
  · trivial

theorem TopOK.result_toAdmin (r : Result) : TopOK r.toAdmin := by
  cases r with
  | values vs => exact TopOK.vals vs
  | throw a =>
    intro x hx
    simp only [Result.toAdmin, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> trivial
  | trap =>
    intro x hx
    simp only [Result.toAdmin, List.mem_singleton] at hx
    subst hx; trivial

/-- A family step never starts from top-level code (its redex is an instruction that is not a
value, a call through `CALL_REF`, or a bubble). -/
theorem not_topOK_of_last {l : List Admin} {e : Admin} (he : ¬ TopAdmin e) (h : e ∈ l) :
    ¬ TopOK l := fun hl => he (hl e h)

theorem ParametricStep.not_top {is is' : List Admin} (h : ParametricStep is is') :
    ¬ TopOK is := by
  cases h <;> simp [TopOK, TopAdmin]

theorem NumericStep.not_top {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    ¬ TopOK is := by
  cases h <;> simp [TopOK, TopAdmin]

theorem VectorStep.not_top {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    ¬ TopOK is := by
  cases h <;> simp [TopOK, TopAdmin]

theorem VariableStep.not_top {c c' : Config H} (h : VariableStep c c') : ¬ TopOK c.code := by
  cases h <;> simp [TopOK, TopAdmin]

theorem TableStep.not_top {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    ¬ TopOK c.code := by
  cases h <;> simp [TopOK, TopAdmin]

theorem MemoryStep.not_top {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    ¬ TopOK c.code := by
  cases h <;> simp [TopOK, TopAdmin]

theorem RefStep.not_top {c c' : Config H} (h : RefStep c c') : ¬ TopOK c.code := by
  cases h <;> simp [TopOK, TopAdmin]

theorem AggregateStep.not_top {c c' : Config H} (h : AggregateStep c c') : ¬ TopOK c.code := by
  cases h <;> simp [TopOK, TopAdmin]

/-- **Frame independence at top level.** A step from top-level provider code keeps the frame,
stays at top level, and can be replayed under any frame. -/
theorem step_reframe {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Silmaril.Games.Step P host c c') (hc : TopOK c.code) :
    c'.frame = c.frame ∧ TopOK c'.code ∧
      ∀ g : Frame, Silmaril.Games.Step P host ⟨c.store, g, c.code⟩ ⟨c'.store, g, c'.code⟩ := by
  induction h with
  | parametric h => exact absurd hc (ParametricStep.not_top h)
  | numeric h => exact absurd hc (NumericStep.not_top h)
  | vector h => exact absurd hc (VectorStep.not_top h)
  | «variable» h => exact absurd hc (VariableStep.not_top h)
  | table h => exact absurd hc (TableStep.not_top h)
  | memory h => exact absurd hc (MemoryStep.not_top h)
  | reference h => exact absurd hc (RefStep.not_top h)
  | aggregate h => exact absurd hc (AggregateStep.not_top h)
  | ctxtInstrs _ hne ih =>
    obtain ⟨hvi, hr⟩ := TopOK.append.mp hc
    obtain ⟨hv, hi⟩ := TopOK.append.mp hvi
    obtain ⟨e1, e2, e3⟩ := ih hi
    exact ⟨e1, TopOK.append.mpr ⟨TopOK.append.mpr ⟨hv, e2⟩, hr⟩,
      fun g => Silmaril.Games.Step.ctxtInstrs (e3 g) hne⟩
  | ctxtLabel _ _ => exact absurd hc (by simp [TopOK, TopAdmin])
  | ctxtHandler _ _ => exact absurd hc (by simp [TopOK, TopAdmin])
  | ctxtFrame h _ =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.ctxtFrame h⟩
  | callRefNull hcr =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.callRefNull hcr⟩
  | callRefFunc hcr hf he hn hcode =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.callRefFunc hcr hf he hn hcode⟩
  | callRefHost hcr hf he hn hcode hhost =>
    exact ⟨rfl, TopOK.result_toAdmin _, fun g => Silmaril.Games.Step.callRefHost hcr hf he hn hcode hhost⟩
  | callRefHostDiv hcr hf he hn hcode hhost =>
    exact ⟨rfl, hc, fun g => Silmaril.Games.Step.callRefHostDiv hcr hf he hn hcode hhost⟩
  | returnCallRefFrameNull hcr =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.returnCallRefFrameNull hcr⟩
  | returnCallRefFrameAddr hcr hf he hn =>
    refine ⟨rfl, ?_, fun g => Silmaril.Games.Step.returnCallRefFrameAddr hcr hf he hn⟩
    exact TopOK.append.mpr ⟨TopOK.vals _, TopOK.cons.mpr ⟨trivial,
      TopOK.cons.mpr ⟨TopOK.retToCallIn hcr _, TopOK.nil⟩⟩⟩
  | frameVals hn => exact ⟨rfl, TopOK.vals _, fun g => Silmaril.Games.Step.frameVals hn⟩
  | returnFrame hn => exact ⟨rfl, TopOK.vals _, fun g => Silmaril.Games.Step.returnFrame hn⟩
  | throwRefNull => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.throwRefNull⟩
  | throwRefInstrs hne =>
    exact ⟨rfl, by simp [TopOK, TopAdmin, throwing], fun g => Silmaril.Games.Step.throwRefInstrs hne⟩
  | throwRefFrame => exact ⟨rfl, by simp [TopOK, TopAdmin, throwing], fun g => Silmaril.Games.Step.throwRefFrame⟩
  | trapInstrs hne => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.trapInstrs hne⟩
  | trapFrame => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Silmaril.Games.Step.trapFrame⟩
  | _ =>
    exfalso
    first
    | exact hc _ (List.mem_append_right _ (List.mem_singleton_self _))
    | exact hc _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    | exact hc _ (List.mem_singleton_self _)

theorem Ren.topOK_code (ρ : Ren) {l : List Admin} (h : TopOK l) : TopOK (ρ.code l) := by
  induction l with
  | nil => simp [TopOK]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := TopOK.cons.mp h
    have ih' := ih hl
    cases a with
    | plain i => simpa [TopOK.cons] using ⟨ha, ih'⟩
    | ref r => simpa [TopOK.cons, TopAdmin] using ih'
    | callRefType d => simpa [TopOK.cons, TopAdmin] using ih'
    | returnCallRefType d => simp [TopAdmin] at ha
    | label n c b => simp [TopAdmin] at ha
    | handler n cs b => simp [TopAdmin] at ha
    | frame n f b => simpa [TopOK.cons, TopAdmin] using ih'
    | trap => simpa [TopOK.cons, TopAdmin] using ih'

/-! ### Renaming of callout contexts -/

/-- Renaming of a callout context. -/
def Ren.ctx (ρ : Ren) : Ctx → Ctx
  | .top pre rest => .top (pre.map ρ.val) (ρ.code rest)
  | .label pre n cont E rest => .label (pre.map ρ.val) n cont (ρ.ctx E) (ρ.code rest)
  | .handler pre n cs E rest => .handler (pre.map ρ.val) n cs (ρ.ctx E) (ρ.code rest)
  | .frame pre n f E rest => .frame (pre.map ρ.val) n (ρ.frame f) (ρ.ctx E) (ρ.code rest)

theorem Ren.code_fill (ρ : Ren) (E : Ctx) (xs : List Admin) :
    ρ.code (E.fill xs) = (ρ.ctx E).fill (ρ.code xs) := by
  induction E with
  | top pre rest => simp [Ctx.fill, Ren.ctx]
  | label pre n cont E rest ih => simp [Ctx.fill, Ren.ctx, ih]
  | handler pre n cs E rest ih => simp [Ctx.fill, Ren.ctx, ih]
  | frame pre n f E rest ih => simp [Ctx.fill, Ren.ctx, ih]

/-- Goodness of `a ++ b ++ c` is preserved by replacing the middle part. -/
private theorem codeGood_mid {O : Own} {a b b' c : List Admin} (h : O.CodeGood (a ++ b ++ c))
    (hb : O.CodeGood b → O.CodeGood b') : O.CodeGood (a ++ b' ++ c) := by
  obtain ⟨h1, h2⟩ := O.codeGood_append.mp h
  obtain ⟨h3, h4⟩ := O.codeGood_append.mp h1
  exact O.codeGood_append.mpr ⟨O.codeGood_append.mpr ⟨h3, hb h4⟩, h2⟩

/-- Goodness of the context of a callout does not depend on the hole. -/
theorem Own.CodeGood.fill {O : Own} (E : Ctx) {xs ys : List Admin} (h : O.CodeGood (E.fill xs))
    (hy : O.CodeGood ys) : O.CodeGood (E.fill ys) := by
  induction E with
  | top pre rest => exact codeGood_mid (b := xs) h fun _ => hy
  | label pre n cont E rest ih =>
    exact codeGood_mid h fun h4 =>
      (O.codeGood_single_label ..).mpr (ih ((O.codeGood_single_label ..).mp h4))
  | handler pre n cs E rest ih =>
    exact codeGood_mid h fun h4 =>
      (O.codeGood_single_handler ..).mpr (ih ((O.codeGood_single_handler ..).mp h4))
  | frame pre n f E rest ih =>
    exact codeGood_mid h fun h4 =>
      have h56 := (O.codeGood_single_frame ..).mp h4
      (O.codeGood_single_frame ..).mpr ⟨h56.1, ih h56.2⟩

/-! ### Confluence of host-free runs -/

/-- Runs to a normal form are confluent: from any successor of the start, the same normal form
is reached (from the diamond `Internal.deterministic`). -/
theorem reach_of_step {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x y z}, R x y → R x z → Det.Join R y z) {x y z : α}
    (hxz : Relation.ReflTransGen R x z) (hz : ∀ w, ¬ R z w) (hxy : R x y) :
    Relation.ReflTransGen R y z := by
  induction hxz using Relation.ReflTransGen.head_induction_on generalizing y with
  | refl => exact absurd hxy (hz y)
  | head hxx₁ hx₁z ih =>
    obtain ⟨w, h1, h2⟩ := hj hxy hxx₁
    have hw : Relation.ReflTransGen R w z := by
      cases h2 with
      | refl => exact hx₁z
      | single h => exact ih h
    cases h1 with
    | refl => exact hw
    | single h => exact .head h hw

end Silmaril.Proofs.Wasm.Game.Linking.Split
