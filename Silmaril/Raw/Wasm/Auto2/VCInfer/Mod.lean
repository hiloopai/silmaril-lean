module

public import Silmaril.Wasm.Auto2.VCInfer.Defs

/-!
# Inferred contracts: soundness (unrefined)

* `derives_inferEntry`, `derives_libEntry`: inferred entries and library entries are derived
  from their `InferFun`;
* `InferFun.ext`: a functional contract with two more derived contracts (the precondition,
  the reference function and totality transfer from the base, since a derived contract has the
  base's functions, parameters, results, pre- and postcondition);
* **`modEquiv_of_infer`**: two derived contracts that check the two exports prove `ModEquiv`
  at every profile, for every reflexive relation.

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInfer

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Auto2.VCEquiv
open Silmaril.Wasm.Auto.Front (ModEquiv)

theorem derives_inferEntry (I : InferFun) (c : Option Cand) (code : Func)
    (h : AllValid I.base.F (genFunc (I.specOf c) code I.base.fuel)) :
    I.Derives (inferEntry I c code h) :=
  .inr ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem derives_libEntry (I : InferFun) (i : Nat) : I.Derives (libEntry I i) := by
  unfold libEntry
  left
  rw [List.getD_eq_getElem?_getD]
  cases hi : I.F.es[i]? with
  | none => exact I.mem
  | some e => exact List.mem_of_getElem? hi

theorem derives_pre {I : InferFun} {e : VcEntry} (h : I.Derives e) :
    ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ := by
  rcases h with h | ⟨hF, -, -, hpre, -⟩
  · exact I.F.pre e h
  · intro ρ hρ
    simp only [FnSpec.preF, hpre, hF]
    exact I.F.pre _ I.mem ρ hρ

theorem derives_ref {I : InferFun} {e : VcEntry} (h : I.Derives e) : RefOK e I.F.f := by
  rcases h with h | ⟨hF, hp, hr, -, hpost⟩
  · exact I.F.ref e h
  · intro vs res B htv hres hpost'
    rw [hp] at htv
    rw [hr] at hres
    rw [hpost, hF] at hpost'
    exact I.F.ref _ I.mem vs res B htv hres hpost'

theorem derives_tot {I : InferFun} {e : VcEntry} (h : I.Derives e) :
    ∀ vs, Silmaril.Wasm.Auto.Equiv.TypedVals e.S.params vs → ∃ res, I.F.f vs = some (.values res) := by
  rcases h with h | ⟨-, hp, -, -, -⟩
  · exact I.F.tot e h
  · intro vs htv
    rw [hp] at htv
    exact I.F.tot _ I.mem vs htv

/-- `I.F` with two more derived contracts. -/
def InferFun.ext (I : InferFun) (e₁ e₂ : VcEntry) (h₁ : I.Derives e₁) (h₂ : I.Derives e₂) :
    EqFun where
  name := I.F.name
  f := I.F.f
  es := [e₁, e₂]
  pre e he := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact derives_pre h₁
    · exact derives_pre h₂
  ref e he := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact derives_ref h₁
    · exact derives_ref h₂
  tot e he := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact derives_tot h₁
    · exact derives_tot h₂

/-- **Two derived contracts that check the two exports prove module equivalence**, every
profile, every reflexive relation. -/
theorem modEquiv_of_infer {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b) (I : InferFun) {e₁ e₂ : VcEntry} (h₁ : I.Derives e₁) (h₂ : I.Derives e₂)
    {m₁ m₂ : Module} {j : Nat} (h : vcEquivWith e₁ e₂ m₁ m₂ j = true) :
    ModEquiv R P m₁ m₂ j :=
  modEquiv_of_vcEquivWith (F := I.ext e₁ e₂ h₁ h₂) hR List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self) h

end Silmaril.Wasm.Auto2.VCInfer
