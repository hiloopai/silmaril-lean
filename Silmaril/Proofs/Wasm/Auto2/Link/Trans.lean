module

public import Silmaril.Wasm.Auto2.Link.Defs
public import Silmaril.Wasm.Auto2.Kernel.Thms

/-!
# Composing module equivalences

`modEquiv_trans`: two `Rel.eq` equivalences at export `j` compose when the middle module accepts
the arguments of the outer ones (`InvokeImp`); `invokeImp_of_sigOkK`: the same signature with
number or vector parameters (`sigOkK`, decided in the kernel over `instK?`) gives `InvokeImp` both
ways.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Link

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Front (addrOf ModEquiv ModRefines Rel)
open Silmaril.Wasm.Verify (instOf)
open Silmaril.Wasm.Auto2.Link
open Silmaril.Wasm.Numerics (Profile)

/-- **Composition of equivalences** at export `j`. -/
theorem modEquiv_trans {P : Profile} {m₁ m₂ m₃ : Module} {j : Nat}
    (h₁ : ModEquiv Rel.eq.toProp P m₁ m₂ j) (h₂ : ModEquiv Rel.eq.toProp P m₂ m₃ j)
    (i₁₂ : InvokeImp m₁ m₂ j) (i₃₂ : InvokeImp m₃ m₂ j) : ModEquiv Rel.eq.toProp P m₁ m₃ j := by
  refine ⟨fun vs hv b hb => ?_, fun vs hv b hb => ?_⟩
  · obtain ⟨b', hb', e⟩ := h₁.1 vs hv b hb
    obtain ⟨b'', hb'', e'⟩ := h₂.1 vs (i₁₂ vs hv) b' hb'
    exact ⟨b'', hb'', (show b = b' from e).trans e'⟩
  · obtain ⟨b', hb', e⟩ := h₂.2 vs hv b hb
    obtain ⟨b'', hb'', e'⟩ := h₁.2 vs (i₃₂ vs hv) b' hb'
    exact ⟨b'', hb'', (show b'' = b' from e').trans e⟩

/-- Values of number or vector types are typed independently of the store. -/
theorem valOk_transfer {s₁ s₂ : Store Nat} :
    ∀ {vs : List Val} {ts : List CValType}, List.Forall₂ (ValOk s₁) vs ts →
      (ts.all fun t => decide t.IsNumOrVec) = true → List.Forall₂ (ValOk s₂) vs ts
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hn
    refine .cons ?_ (valOk_transfer hs hn.2)
    cases h with
    | num v => exact .num v
    | vec b => exact .vec b
    | ref _ => simp [Ty.IsNumOrVec] at hn

/-- Arguments accepted by a function are accepted by another of the same type with number or
vector parameters. -/
theorem invokeOk_transfer {s₁ s₂ : Store Nat} {a₁ a₂ : Nat} {fi₁ fi₂ : FuncInst Nat}
    (h₁ : s₁.funcs[a₁]? = some fi₁) (h₂ : s₂.funcs[a₂]? = some fi₂) (ht : fi₁.type = fi₂.type)
    (hn : numParams fi₁.type = true) {vs : List Val} (hv : InvokeOk s₁ a₁ vs) :
    InvokeOk s₂ a₂ vs := by
  obtain ⟨fi, ps, rs, hf, he, hvs⟩ := hv
  rw [h₁] at hf
  cases hf
  have hx := Expand.iff.mp he
  have hp : (ps.toList.all fun t => decide t.IsNumOrVec) = true := by
    simpa [numParams, hx] using hn
  exact ⟨fi₂, ps, rs, h₂, ht ▸ he, valOk_transfer hvs hp⟩

/-- The instance of a valid module is the validation-free one. -/
theorem instOf_of_instK {m : Module} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hv : (validate? m).isSome = true) (h : Silmaril.Wasm.Auto2.Kernel.instK? m = some I) :
    instOf m = I := by
  have := Silmaril.Proofs.Wasm.Auto2.Kernel.instK?_eq hv
  rw [h] at this
  unfold instOf
  rw [← this]
  rfl

theorem sigK_spec {m : Module} {j : Nat} {d : DefType} (hv : (validate? m).isSome = true)
    (h : sigK m j = some d) :
    ∃ fi, (instOf m).store.funcs[addrOf m j]? = some fi ∧ fi.type = d := by
  unfold sigK at h
  cases hI : Silmaril.Wasm.Auto2.Kernel.instK? m with
  | none => simp [hI] at h
  | some I =>
    rw [hI] at h
    simp only [Option.map_some, Option.join_some, Option.map_eq_some_iff] at h
    obtain ⟨fi, hfi, rfl⟩ := h
    refine ⟨fi, ?_, rfl⟩
    simp only [addrOf, instOf_of_instK hv hI]
    exact hfi

/-- **The same signature gives `InvokeImp` both ways.** -/
theorem invokeImp_of_sigOkK {m₁ m₂ : Module} {j : Nat} (hv₁ : (validate? m₁).isSome = true)
    (hv₂ : (validate? m₂).isSome = true) (h : sigOkK m₁ m₂ j = true) :
    InvokeImp m₁ m₂ j ∧ InvokeImp m₂ m₁ j := by
  unfold sigOkK at h
  split at h
  · rename_i d₁ d₂ hs₁ hs₂
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hn⟩ := h
    obtain ⟨fi₁, hf₁, ht₁⟩ := sigK_spec hv₁ hs₁
    obtain ⟨fi₂, hf₂, ht₂⟩ := sigK_spec hv₂ hs₂
    refine ⟨fun vs hv => ?_, fun vs hv => ?_⟩
    · exact invokeOk_transfer hf₁ hf₂ (ht₁.trans ht₂.symm) (ht₁ ▸ hn) hv
    · exact invokeOk_transfer hf₂ hf₁ (ht₂.trans ht₁.symm) (ht₂ ▸ hn) hv
  · cases h

/-- `sigOkAll` at a listed export. -/
theorem sigOkK_of_all {m₁ m₂ : Module} {js : List Nat} {j : Nat} (h : sigOkAll m₁ m₂ js = true)
    (hj : j ∈ js) : sigOkK m₁ m₂ j = true :=
  List.all_eq_true.mp h j hj

/-- **Transfer of a certificate's equivalence through a link**: `m₁ ≈ m₂` (the link, e.g. a
binary's decoded module against Binaryen's reading of it) and `m₂ ≈ m₃` (the certificate) give
`m₁ ≈ m₃`, when `m₁`, `m₂` and `m₃` give export `j` the same signature. -/
theorem modEquiv_link {P : Profile} {m₁ m₂ m₃ : Module} {j : Nat}
    (hv₁ : (validate? m₁).isSome = true) (hv₂ : (validate? m₂).isSome = true)
    (hv₃ : (validate? m₃).isSome = true)
    (s₁₂ : sigOkK m₁ m₂ j = true) (s₂₃ : sigOkK m₂ m₃ j = true)
    (h₁ : ModEquiv Rel.eq.toProp P m₁ m₂ j) (h₂ : ModEquiv Rel.eq.toProp P m₂ m₃ j) :
    ModEquiv Rel.eq.toProp P m₁ m₃ j :=
  modEquiv_trans h₁ h₂ (invokeImp_of_sigOkK hv₁ hv₂ s₁₂).1 (invokeImp_of_sigOkK hv₂ hv₃ s₂₃).2

/-- Equivalence under `Rel.eq` is symmetric. -/
theorem modEquiv_symm {P : Profile} {m₁ m₂ : Module} {j : Nat}
    (h : ModEquiv Rel.eq.toProp P m₁ m₂ j) : ModEquiv Rel.eq.toProp P m₂ m₁ j := by
  refine ⟨fun vs hv b hb => ?_, fun vs hv b hb => ?_⟩
  · obtain ⟨b', hb', e⟩ := h.2 vs hv b hb
    exact ⟨b', hb', (show b' = b from e).symm⟩
  · obtain ⟨b', hb', e⟩ := h.1 vs hv b hb
    exact ⟨b', hb', (show b = b' from e).symm⟩

end Silmaril.Proofs.Wasm.Auto2.Link
