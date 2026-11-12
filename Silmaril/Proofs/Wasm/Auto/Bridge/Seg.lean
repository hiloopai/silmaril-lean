module

public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Proofs.Wasm.Auto.Bridge.All
public import Silmaril.Proofs.Wasm.Auto.Bridge.Partial
public import Silmaril.Wasm.Auto.ESeg.Thms

/-! # Function-entry certificates at the module level

`modEquiv_of_funcEquiv`: a certificate `FuncEquiv Γ da db a b` (bodies with the same
parameters and different declared locals, compared from function entry) on the bodies of two
summarised exports proves `ModEquiv` at every profile, for every reflexive relation, under the
decidable side conditions `egraphFuncOk`. The summaries' initial frames (`Bridge.fnInit`:
parameters, then zero declared locals) are entry frames with the same parameters.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Core (exec localVal?)
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Front (ModEquiv)

/-- What `egraphFuncOk` checks. -/
theorem egraphFuncOk_inv {m₁ m₂ : Module} {j : Nat} {Γ da db : List IntType} {a b : List Instr}
    (hok : egraphFuncOk m₁ m₂ j Γ da db = true) (ha : fnBody? m₁ j = some (Γ ++ da, a))
    (hb : fnBody? m₂ j = some (Γ ++ db, b)) :
    ∃ A B, fnSum? m₁ j = some A ∧ fnSum? m₂ j = some B ∧ A.params = Γ ∧ B.params = Γ ∧
      (∀ i ∈ a, plainI i = true) ∧ (∀ i ∈ b, plainI i = true) ∧ (Γ ++ da).length < 2 ^ 32 ∧
      (Γ ++ db).length < 2 ^ 32 := by
  unfold egraphFuncOk at hok
  rw [ha, hb] at hok
  split at hok
  · rename_i A B Γ₁ a' Γ₂ b' hA hB ha' hb'
    simp only [Option.some.injEq, Prod.mk.injEq] at ha' hb'
    obtain ⟨-, rfl⟩ := ha'
    obtain ⟨-, rfl⟩ := hb'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hok
    exact ⟨A, B, hA, hB, h1, h2, h5, h6, h7, h8⟩
  · cases hok

/-- Plain code has no `select`. -/
theorem noSelect_of_plain : ∀ {a : List Instr}, (∀ i ∈ a, plainI i = true) →
    XExec.noSelect a = true
  | [], _ => rfl
  | i :: is, h => by
    have hi : plainI i = true := h i List.mem_cons_self
    have ht := noSelect_of_plain (a := is) fun i' hi' => h i' (List.mem_cons_of_mem _ hi')
    cases i <;> simp_all [XExec.noSelect, plainI]

/-- The local `i` of the frame of `fnInit ps ls`. -/
theorem local_fnInit (ps ls : List IntType) (ρ : Env) (i : Nat) (hi : i < 2 ^ 32) :
    localVal? (frameAt {} ρ (fnInit ps ls)) (EGraph.lidx i) =
      ((fnInit ps ls).locals[i]?).map (den ρ) := by
  have hi32 : i < 4294967296 := hi
  have hidx : (EGraph.lidx i).toNat = i := by
    simp [EGraph.lidx, Idx.toNat, Fin.ofNat, hi32]
  simp only [localVal?, Frame.local?, hidx, frameAt, List.getElem?_map]
  cases (fnInit ps ls).locals[i]? <;> rfl

/-- The frame of `fnInit Γ ds` is an entry frame. -/
theorem entryFrame_fnInit {Γ ds : List IntType} (hn : (Γ ++ ds).length < 2 ^ 32) (ρ : Env) :
    ESeg.EntryFrame Γ ds (frameAt {} ρ (fnInit Γ ds)) := by
  refine ⟨frameOk_frameAt (fnInit_types Γ ds) hn {} ρ, fun j t hj => ?_⟩
  have hjl : j < ds.length := (List.getElem?_eq_some_iff.mp hj).1
  rw [local_fnInit _ _ _ _ (by simp at hn; omega)]
  have hloc : (fnInit Γ ds).locals[Γ.length + j]? = some (t, .const 0) := by
    simp only [fnInit, List.getElem?_append_right (by simp : (Γ.mapIdx _).length ≤ Γ.length + j),
      List.length_mapIdx, Nat.add_sub_cancel_left, List.getElem?_map, hj, Option.map_some]
  rw [hloc]
  rfl

/-- The frames of `fnInit Γ da` and `fnInit Γ db` hold the same parameters. -/
theorem sameParams_fnInit (Γ da db : List IntType) (hn : Γ.length < 2 ^ 32) (ρ : Env) :
    ESeg.SameParams Γ.length (frameAt {} ρ (fnInit Γ da)) (frameAt {} ρ (fnInit Γ db)) := by
  intro i hi
  rw [local_fnInit _ _ _ _ (by omega), local_fnInit _ _ _ _ (by omega)]
  have hp : ∀ ds : List IntType, (fnInit Γ ds).locals[i]? = some (Γ[i], .var i) := by
    intro ds
    have hlen : i < (Γ.mapIdx fun i t => (t, Term.var i)).length := by simpa using hi
    show (Γ.mapIdx (fun i t => (t, Term.var i)) ++ ds.map (fun t => (t, Term.const 0)))[i]? = _
    rw [List.getElem?_append_left hlen, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
    rfl
  rw [hp da, hp db]

/-- **A function-entry certificate on the bodies proves module equivalence**, at every
profile, for every reflexive relation, under the decidable side conditions `egraphFuncOk`. -/
theorem modEquiv_of_funcEquiv {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} {Γ da db : List IntType} {a b : List Instr}
    (hok : egraphFuncOk m₁ m₂ j Γ da db = true) (ha : fnBody? m₁ j = some (Γ ++ da, a))
    (hb : fnBody? m₂ j = some (Γ ++ db, b)) (h : ESeg.FuncEquiv Γ da db a b) :
    ModEquiv R P m₁ m₂ j := by
  obtain ⟨A, B, hA, hB, hpA, hpB, hpa, hpb, hna, hnb⟩ := egraphFuncOk_inv hok ha hb
  refine modEquiv_of_out hR hA hB (hpA.trans hpB.symm) fun vs _ => ?_
  obtain ⟨ls, F₁, hΓ₁, he₁⟩ := exec_of_fnSum hA ha hpa (H := Nat) {} {} (envOfVals vs)
  obtain ⟨ls', F₂, hΓ₂, he₂⟩ := exec_of_fnSum hB hb hpb (H := Nat) {} {} (envOfVals vs)
  have hls : ls = da := by
    rw [hpA] at hΓ₁; exact (List.append_cancel_left hΓ₁).symm
  have hls' : ls' = db := by
    rw [hpB] at hΓ₂; exact (List.append_cancel_left hΓ₂).symm
  rw [hpA, hls] at he₁
  rw [hpB, hls'] at he₂
  have hΓn : Γ.length < 2 ^ 32 := by simp at hna; omega
  have hout := h (H := Nat) {} _ _ [] (entryFrame_fnInit hna (envOfVals vs))
    (entryFrame_fnInit hnb (envOfVals vs)) (sameParams_fnInit Γ da db hΓn (envOfVals vs)) rfl
  rw [XExec.execS_eq_exec _ _ _ (noSelect_of_plain hpa),
    XExec.execS_eq_exec _ _ _ (noSelect_of_plain hpb), he₁, he₂] at hout
  have hst : stackAt (envOfVals vs) A.final = stackAt (envOfVals vs) B.final := hout.2.2
  simp only [fnOut, hst]

end Silmaril.Proofs.Wasm.Auto.Bridge
