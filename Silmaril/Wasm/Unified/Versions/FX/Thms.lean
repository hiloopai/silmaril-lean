module

public import Silmaril.Wasm.Unified.Versions.FX.Defs
public import Silmaril.Wasm.Unified.Versions.Run.Thms
public import Silmaril.Wasm.Models.FX.Thms

/-!
# WasmFX extends Core 3.0

* `sub30FX`: **the 3.0 signature is a sub-signature of WasmFX** (same typing on 3.0 opcodes);
  `fxResume_sep`: `resume` is in WasmFX and not in 3.0;
* `core_mem_evalCode`: evaluating 3.0 code in the reduct of the FX algebra contains the FX
  embedding of every Core meaning (mutual induction through blocks);
* `cfgFX_core`: running embedded Core code is running the Core configuration in CoreFX;
* `core_refines_fx`: **Core 3.0 refines the reduct of WasmFX without FX functions**, from
  conservativity of CoreFX (`Silmaril.Wasm.Models.FX.behavioursFX_conservative`). The direction is
  `sub`, not `eq`: the FX algebra also interprets `block`, `loop` and `if` by the FX structured
  forms, whose agreement with the Core forms on Core bodies is not proved here.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified.Core30 Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

/-- **3.0 is a sub-signature of WasmFX.** -/
theorem sub30FX : FSig.Sub sig30 sigFX := by
  refine ⟨fun _ ho => Or.inl ho, ?_⟩
  rintro _ ⟨i, rfl⟩
  cases i <;> simp [sigFX, sig30, arityFX, head]

/-- `resume`, as an opcode. -/
def nResume : Opcode := .named "resume" [1002]

/-- **`resume` is in WasmFX and not in 3.0.** -/
theorem fxResume_sep : nResume ∈ sigFX.ops ∧ nResume ∉ sig30.ops := by
  refine ⟨Or.inr ⟨.resume ⟨0⟩ [], rfl⟩, ?_⟩
  rintro ⟨i, hi⟩
  cases i <;> simp [head, nResume] at hi

section Eval

/-- The FX meaning of an instruction in the reduct along `σ`. -/
def evFXI (σ : sig30 ⟶ sigFX) (u : UInstr sig30.Op) : Set InstrFX :=
  (algFX.comap σ.f).evalInstr u

/-- The FX meaning of code in the reduct along `σ`. -/
def evFX (σ : sig30 ⟶ sigFX) (c : sig30.Code) : Set (List InstrFX) :=
  (algFX.comap σ.f).evalCode c

/-- The FX meanings of blocks in the reduct along `σ`. -/
def evFXB (σ : sig30 ⟶ sigFX) (bs : List sig30.Code) : List (Set (List InstrFX)) :=
  (algFX.comap σ.f).evalBlocks bs

/-- The 3.0 meanings of blocks. -/
def evB30 (bs : List sig30.Code) : List (Set (List Instr)) := alg30.evalBlocks bs

mutual
/-- Core meanings of an instruction embed in its FX meaning. -/
theorem core_mem_evalInstr (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (u : UInstr sig30.Op) → ∀ i ∈ evalI30 u, InstrFX.core i ∈ evFXI σ u
  | .op o imms bs hs => by
    intro i hi
    rw [evalI30, Alg.evalInstr] at hi
    rw [evFXI, Alg.evalInstr]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hi
    exact Or.inl ⟨i, rfl, h₁.trans (hσ o).symm, h₂, h₃,
      core_forall_evalBlocks σ hσ bs i.bodies h₄⟩
/-- **Core meanings of code embed in its FX meaning.** -/
theorem core_mem_evalCode (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (c : sig30.Code) → ∀ is ∈ evalC30 c, is.map InstrFX.core ∈ evFX σ c
  | [] => by
    intro is h
    rw [evalC30, Alg.evalCode] at h
    rw [evFX, Alg.evalCode]
    have h' : is = [] := h
    rw [h']
    rfl
  | u :: c => by
    intro is h
    rw [evalC30, Alg.evalCode] at h
    rw [evFX, Alg.evalCode]
    obtain ⟨i, t, rfl, hi, ht⟩ := h
    exact ⟨.core i, t.map InstrFX.core, rfl, core_mem_evalInstr σ hσ u i hi,
      core_mem_evalCode σ hσ c t ht⟩
/-- Core meanings of blocks embed in their FX meanings. -/
theorem core_forall_evalBlocks (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (bs : List sig30.Code) → ∀ bodies : List (List Instr),
      List.Forall₂ (· ∈ ·) bodies (evB30 bs) →
      List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) bodies (evFXB σ bs)
  | [] => by
    intro bodies h
    rw [evB30, Alg.evalBlocks] at h
    rw [evFXB, Alg.evalBlocks]
    cases h
    exact .nil
  | b :: bs => by
    intro bodies h
    rw [evB30, Alg.evalBlocks] at h
    rw [evFXB, Alg.evalBlocks]
    cases h with
    | cons h₁ h₂ =>
      exact .cons (core_mem_evalCode σ hσ b _ h₁) (core_forall_evalBlocks σ hσ bs _ h₂)
end

end Eval

variable {H : Type}

/-- Running embedded Core code is running the Core configuration in CoreFX. -/
theorem cfgFX_core (s : Store H) (f : Frame) (is : List Instr) (vs : UIn) :
    cfgFX s f (is.map InstrFX.core) vs = ofCore (cfgOf s f is vs) := by
  simp [cfgFX, ofCore, cfgOf, cvals, expression, List.map_map, Function.comp_def,
    InstrFX.toAdmin]

/-- **Core 3.0 refines the reduct of WasmFX without FX functions.** -/
theorem core_refines_fx (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okc is → okcFX (is.map InstrFX.core)) :
    Refines (model30 P host s f okc) ((fxModelN P host s noFX f okcFX).reduct (FSig.incl sub30FX)) := by
  rintro ⟨c, vs⟩ b ⟨⟨is, his, hok₁⟩, is', his', hok', hb⟩
  have hσ : ∀ o, ((FSig.incl sub30FX).f o).1 = o.1 := fun _ => rfl
  refine ⟨⟨is.map InstrFX.core, core_mem_evalCode _ hσ c is his, hok is hok₁⟩,
    is'.map InstrFX.core, core_mem_evalCode _ hσ c is' his', hok is' hok', ?_⟩
  show b ∈ behavioursFX P host noFX (cfgFX s f (is'.map InstrFX.core) vs)
  rw [cfgFX_core, behavioursFX_conservative]
  exact hb

end Silmaril.Wasm.Unified.Versions
