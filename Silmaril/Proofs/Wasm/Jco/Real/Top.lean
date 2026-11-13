module

public import Silmaril.Wasm.Execution.Core.Sim.Segments
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Frame independence of top-level code (copied)

Code at top level (values, references, calls through `CALL_REF`, frames, traps and exception
bubbles) does not read or write the outer frame: a run from it can be replayed under any frame.
This is what relates `$invoke` (the empty frame) to a `call` from inside an adaptor function.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- Administrative instructions that may occur at the top level of an invocation. -/
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

/-- Code that may occur at the top level of an invocation. -/
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

theorem TopOK.retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    TopAdmin (c.retToCallIn m) := by
  obtain ⟨y, rfl⟩ | ⟨d, rfl⟩ := Admin.isReturnCallRef_cases hc
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

/-- **Frame independence at top level** (copied). A step from top-level code keeps the frame,
stays at top level, and can be replayed under any frame. -/
theorem step_reframe {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : TopOK c.code) :
    c'.frame = c.frame ∧ TopOK c'.code ∧
      ∀ g : Frame, Step P host ⟨c.store, g, c.code⟩ ⟨c'.store, g, c'.code⟩ := by
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
      fun g => Step.ctxtInstrs (e3 g) hne⟩
  | ctxtLabel _ _ => exact absurd hc (by simp [TopOK, TopAdmin])
  | ctxtHandler _ _ => exact absurd hc (by simp [TopOK, TopAdmin])
  | ctxtFrame h _ =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.ctxtFrame h⟩
  | callRefNull hcr =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.callRefNull hcr⟩
  | callRefFunc hcr hf he hn hcode =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.callRefFunc hcr hf he hn hcode⟩
  | callRefHost hcr hf he hn hcode hhost =>
    exact ⟨rfl, TopOK.result_toAdmin _, fun g => Step.callRefHost hcr hf he hn hcode hhost⟩
  | callRefHostDiv hcr hf he hn hcode hhost =>
    exact ⟨rfl, hc, fun g => Step.callRefHostDiv hcr hf he hn hcode hhost⟩
  | returnCallRefFrameNull hcr =>
    exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.returnCallRefFrameNull hcr⟩
  | returnCallRefFrameAddr hcr hf he hn =>
    refine ⟨rfl, ?_, fun g => Step.returnCallRefFrameAddr hcr hf he hn⟩
    exact TopOK.append.mpr ⟨TopOK.vals _, TopOK.cons.mpr ⟨trivial,
      TopOK.cons.mpr ⟨TopOK.retToCallIn hcr _, TopOK.nil⟩⟩⟩
  | frameVals hn => exact ⟨rfl, TopOK.vals _, fun g => Step.frameVals hn⟩
  | returnFrame hn => exact ⟨rfl, TopOK.vals _, fun g => Step.returnFrame hn⟩
  | throwRefNull => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.throwRefNull⟩
  | throwRefInstrs hne =>
    exact ⟨rfl, by simp [TopOK, TopAdmin, throwing], fun g => Step.throwRefInstrs hne⟩
  | throwRefFrame => exact ⟨rfl, by simp [TopOK, TopAdmin, throwing], fun g => Step.throwRefFrame⟩
  | trapInstrs hne => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.trapInstrs hne⟩
  | trapFrame => exact ⟨rfl, by simp [TopOK, TopAdmin], fun g => Step.trapFrame⟩
  | _ =>
    exfalso
    first
    | exact hc _ (List.mem_append_right _ (List.mem_singleton_self _))
    | exact hc _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    | exact hc _ (List.mem_singleton_self _)

/-- **A run from top-level code can be replayed under any frame**, and keeps its frame. -/
theorem Steps.reframe {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hc : TopOK c.code) :
    c'.frame = c.frame ∧ TopOK c'.code ∧
      ∀ g : Frame, Steps P host ⟨c.store, g, c.code⟩ ⟨c'.store, g, c'.code⟩ := by
  induction h with
  | refl => exact ⟨rfl, hc, fun _ => .refl⟩
  | tail _ hs ih =>
    obtain ⟨hf, ht, hr⟩ := ih
    obtain ⟨hf', ht', hr'⟩ := step_reframe hs ht
    exact ⟨hf'.trans hf, ht', fun g => (hr g).tail (hr' g)⟩

/-- The code of `$invoke` is at top level. -/
theorem invoke_topOK (s : Store H) (a : Nat) (vs : List Val) : TopOK (invoke s a vs).code := by
  refine TopOK.append.mpr ⟨TopOK.vals vs, ?_⟩
  simp [TopOK, TopAdmin]

end Silmaril.Proofs.Wasm.Jco.Real
