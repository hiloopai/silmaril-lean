module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Thms

/-!
# Round 7, REH route 2: the erasure copy without `QInj`, basic facts (unrefined)

Every value is in the swap set `QT`; the scope invariant `NCalls` is monotone in the fuel and
survives term bindings; the list forms of the checks hold elementwise; and comparisons other
than `=` and `≠` commute with erasure with no hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn)

/-! ## The swap set of every value -/

mutual
theorem allIn_top : ∀ v : Value, AllIn QT v
  | .bool _ => trivial
  | .num _ => trivial
  | .text _ => trivial
  | .tuple vs => allIns_top vs
  | .case _ w => allIn_top w
  | .struct gs => ⟨fun _ => trivial, allInf_top gs⟩
  | .list vs => allIns_top vs
  | .opt none => trivial
  | .opt (some w) => allIn_top w

theorem allIns_top : ∀ vs : List Value, AllIns QT vs
  | [] => trivial
  | v :: vs => ⟨allIn_top v, allIns_top vs⟩

theorem allInf_top : ∀ gs : List (AtomS × Value), AllInf QT gs
  | [] => trivial
  | (_, v) :: gs => ⟨allIn_top v, allInf_top gs⟩
end

theorem sg_of_defs {gd : String → Bool} {ρ : VarEnv} (h : DefsG gd ρ) : SG QT gd ρ :=
  ⟨fun p _ => allIn_top p.2, h⟩

/-! ## The scope invariant -/

section
variable {gd : String → Bool} {S : Sig} {T : TSig} {tps : AuxCtx} {env : Env}

theorem CallE.congr {ρ ρ' : VarEnv} {k : Nat} (h : CallE gd S T tps env ρ k)
    (hs : SameCtx ρ ρ') : CallE gd S T tps env ρ' k := by
  intro m hm f xs ws d ha ht hg hd hw
  have hs' : SameCtx ρ' ρ := ⟨hs.1.symm, hs.2.symm⟩
  rw [← hs.findDef?] at hg hd
  exact h m hm f xs ws d (fun ps hp => ArgsR.congr hs' xs ws ps (ha ps hp)) ht hg hd hw

theorem CallE.mono {ρ : VarEnv} {k k' : Nat} (h : CallE gd S T tps env ρ k) (hk : k' ≤ k) :
    CallE gd S T tps env ρ k' :=
  fun m hm => h m (Nat.lt_of_lt_of_le hm hk)

theorem NCalls.mono {ρ : VarEnv} {k k' : Nat} (h : NCalls gd S T tps env ρ k) (hk : k' ≤ k) :
    NCalls gd S T tps env ρ k' :=
  ⟨h.callH.mono hk, h.callE.mono hk, h.defs⟩

theorem NCalls.bindVals {ρ : VarEnv} {k : Nat} (h : NCalls gd S T tps env ρ k)
    (r : List (IL.Id × Value)) : NCalls gd S T tps env (ρ.bindVals r) k :=
  ⟨h.callH.bindVals r, h.callE.congr ⟨rfl, rfl⟩, (sg_of_defs h.defs).bindVals
    (fun _ _ => allIn_top _) |>.2⟩

end

/-! ## Comparisons -/

theorem cmpValues_eraseV_ord {op : CmpOp} (h₁ : op ≠ .eqOp) (h₂ : op ≠ .neOp) (a b : Value) :
    cmpValues op (eraseV a) (eraseV b) = cmpValues op a b := by
  cases op with
  | eqOp => exact absurd rfl h₁
  | neOp => exact absurd rfl h₂
  | _ =>
    cases a with
    | num _ => cases b with
      | opt o => cases o <;> rfl
      | _ => rfl
    | opt o => cases o <;> rfl
    | _ => rfl

/-! ## The checks on lists, elementwise -/

section
variable {S : Sig} {T : TSig} {Γ : List (String × AT)} {tps : AuxCtx} {gr gd : String → Bool}

theorem tyOkL_mem : ∀ {es : List Exp}, tyOkL S T Γ es = true → ∀ e ∈ es, tyOk S T Γ e = true
  | [], _, _, he => by simp at he
  | e :: es, h, e', he => by
    simp only [tyOkL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact tyOkL_mem h.2 e' he

theorem auxL_mem : ∀ {es : List Exp}, auxL tps es = true → ∀ e ∈ es, auxE tps e = true
  | [], _, _, he => by simp at he
  | e :: es, h, e', he => by
    simp only [auxL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact auxL_mem h.2 e' he

theorem auxXL_mem : ∀ {es : List Exp}, auxXL tps es = true → ∀ e ∈ es, auxX tps e = true
  | [], _, _, he => by simp at he
  | e :: es, h, e', he => by
    simp only [auxXL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact auxXL_mem h.2 e' he

theorem badEs_mem : ∀ {es : List Exp}, badEs S Γ es = 0 → ∀ e ∈ es, badE S Γ e = 0
  | [], _, _, he => by simp at he
  | e :: es, h, e', he => by
    simp only [badEs, Nat.add_eq_zero_iff] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact badEs_mem h.2 e' he

/-- The checks on one record field. -/
theorem fields_mem : ∀ {fs : List ExpField}, tyOkF S T Γ fs = true → auxF tps fs = true →
    auxXF tps fs = true → badFs S Γ fs = 0 → ∀ a e, ExpField.mk a e ∈ fs →
      tyOk S T Γ e = true ∧ auxE tps e = true ∧ auxX tps e = true ∧ badE S Γ e = 0
  | [], _, _, _, _, _, _, he => by simp at he
  | .mk a₀ e₀ :: fs, h₁, h₂, h₃, h₄, a, e, he => by
    simp only [tyOkF, auxF, auxXF, badFs, Bool.and_eq_true, Nat.add_eq_zero_iff] at h₁ h₂ h₃ h₄
    rcases List.mem_cons.1 he with he | he
    · cases he
      exact ⟨h₁.1, h₂.1, h₃.1, h₄.1⟩
    · exact fields_mem h₁.2 h₂.2 h₃.2 h₄.2 a e he

/-- The checks on one domain. -/
theorem doms_mem : ∀ {ds : List Dom}, tyOkD S T Γ ds = true → auxD tps ds = true →
    auxXD tps ds = true → badDs S Γ ds = 0 → ∀ d ∈ ds,
      tyOk S T Γ (domSrc d) = true ∧ auxE tps (domSrc d) = true ∧
        auxX tps (domSrc d) = true ∧ badE S Γ (domSrc d) = 0
  | [], _, _, _, _, _, he => by simp at he
  | .mk x₀ e₀ :: ds, h₁, h₂, h₃, h₄, d, he => by
    simp only [tyOkD, auxD, auxXD, badDs, Bool.and_eq_true, Nat.add_eq_zero_iff] at h₁ h₂ h₃ h₄
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨h₁.1, h₂.1, h₃.1, h₄.1⟩
    · exact doms_mem h₁.2 h₂.2 h₃.2 h₄.2 d he

/-- The checks on one argument. -/
theorem args_mem : ∀ {xs : List Arg}, tyOkA S T Γ xs = true → auxA tps xs = true →
    auxXA tps xs = true → badAs S Γ xs = 0 → ∀ x ∈ xs,
      tyOkA S T Γ [x] = true ∧ auxA tps [x] = true ∧ auxXA tps [x] = true ∧ badAs S Γ [x] = 0
  | [], _, _, _, _, _, he => by simp at he
  | x₀ :: xs, h₁, h₂, h₃, h₄, x, he => by
    have e₁ : tyOkA S T Γ (x₀ :: xs) = (tyOkA S T Γ [x₀] && tyOkA S T Γ xs) := by
      cases x₀ <;> simp [tyOkA]
    have e₂ : auxA tps (x₀ :: xs) = (auxA tps [x₀] && auxA tps xs) := by
      cases x₀ <;> simp [auxA]
    have e₃ : auxXA tps (x₀ :: xs) = (auxXA tps [x₀] && auxXA tps xs) := by
      cases x₀ <;> simp [auxXA]
    have e₄ : badAs S Γ (x₀ :: xs) = badAs S Γ [x₀] + badAs S Γ xs := by
      cases x₀ <;> simp [badAs]
    rw [e₁, Bool.and_eq_true] at h₁
    rw [e₂, Bool.and_eq_true] at h₂
    rw [e₃, Bool.and_eq_true] at h₃
    rw [e₄, Nat.add_eq_zero_iff] at h₄
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨h₁.1, h₂.1, h₃.1, h₄.1⟩
    · exact args_mem h₁.2 h₂.2 h₃.2 h₄.2 x he

end

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
