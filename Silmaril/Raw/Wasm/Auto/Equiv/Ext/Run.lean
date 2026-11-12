module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Ext.Step

/-!
# Symbolic runs of the extended executor (unrefined)

* `wp_xstep`: one symbolic step, every instruction (from the cases of
  `Silmaril.Proofs.Wasm.Auto.Equiv.Ext.Step`);
* `wp_xsexec`: a symbolic run: the weakest precondition of the configuration of a state with
  all guards holding, followed by the segment, is `XOut` of the final state: the trap
  postcondition at the state of the first failing guard, or the weakest precondition of the
  final configuration.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem storeOf_guard (c : XCtx H) (mem : Bool) (S : XState) (g : Guard) (st : List (IntType × XT)) :
    c.storeOf mem { S.guard g with stack := st } = c.storeOf mem { S with stack := st } := rfl

theorem frameOf_guard (c : XCtx H) (S : XState) (g : Guard) (st : List (IntType × XT)) :
    c.frameOf { S.guard g with stack := st } = c.frameOf { S with stack := st } := rfl

/-- **One symbolic step.** -/
theorem wp_xstep {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) {S S' : XState}
    {i : Instr} (hl : S.globs.length = c.ga.length) (h : xstep mem S i = some S') (us : List Val)
    (rest : List Admin) (Q : Post H) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain i :: rest) Q ↔
      XStepOut m P host c mem S S' us rest Q := by
  cases i
  case convert op =>
    rcases op with _ | sx | _ | _ | _ | _ | _ | _ | _ <;> simp only [xstep] at h
    · split at h
      · rename_i a st hs
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_wrap hs
      · cases h
    · split at h
      · rename_i a st hs
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_extend hs
      · cases h
    all_goals cases h
  all_goals simp only [xstep] at h
  all_goals try cases h
  case nop =>
    refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
    exact case_nop
  case drop =>
    split at h
    · rename_i p st hs
      cases h
      refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
      exact case_drop hs
    · cases h
  case intConst t k =>
    refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
    exact case_const
  case localGet x =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
    exact case_localGet hp
  case localSet x =>
    split at h
    · rename_i p st hs
      split at h
      · rename_i hx
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_localSet hs hx
      · cases h
    · cases h
  case localTee x =>
    split at h
    · rename_i p st hs
      split at h
      · rename_i hx
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_localTee hs hx
      · cases h
    · cases h
  case globalGet x =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
    exact case_globalGet hc hl hp
  case globalSet x =>
    split at h
    · rename_i t v st t' w hs hg
      split at h
      · rename_i htt
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        have hx : x.toNat < S.globs.length := (List.getElem?_eq_some_iff.mp hg).1
        exact case_globalSet hc hl hs hx
      · cases h
    · cases h
  case intUnOp t op =>
    split at h
    · rename_i t₁ a st hs
      split at h
      · rename_i ht
        subst ht
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_unOp hs
      · cases h
    · cases h
  case intBinOp t op =>
    split at h
    · rename_i t₂ b t₁ a st hs
      split at h
      · rename_i ht
        rw [ht.1, ht.2] at hs
        cases h
        by_cases hsafe : safeBinX t op b = true
        · simp only [hsafe, ↓reduceIte]
          refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
          obtain ⟨z, hz⟩ := intBinOp_ok_of_safe (ρ := c.ρ) (B0 := c.mi.bytes) hsafe
            (evX c.ρ c.mi.bytes t a)
          exact case_binOk hs hz
        · simp only [hsafe, Bool.false_eq_true, ↓reduceIte]
          refine Iff.trans ?_ (xstepOut_guard (g := .binOk t op a b) (by simp [XState.guard])).symm
          cases hz : intBinOp t op (evX c.ρ c.mi.bytes t a) (evX c.ρ c.mi.bytes t b) with
          | ok z =>
            have hg : (Guard.binOk t op a b).holds c.ρ c.mi.bytes = true := by
              simp [Guard.holds, hz]
            rw [ite_eq_left hg, storeOf_guard, frameOf_guard]
            exact case_binOk hs hz
          | error e =>
            have hg : ¬ (Guard.binOk t op a b).holds c.ρ c.mi.bytes = true := by
              simp [Guard.holds, hz]
            rw [ite_eq_right hg]
            exact case_binTrap hs hz
      · cases h
    · cases h
  case intTestOp t op =>
    split at h
    · rename_i t₁ a st hs
      split at h
      · rename_i ht
        subst ht
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_testOp hs
      · cases h
    · cases h
  case intRelOp t op =>
    split at h
    · rename_i t₂ b t₁ a st hs
      split at h
      · rename_i ht
        obtain ⟨rfl, rfl⟩ := ht
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_relOp hs
      · cases h
    · cases h
  case select ts =>
    split at h
    · rename_i tc cnd t₂ b t₁ a st hs
      split at h
      · rename_i ht
        obtain ⟨rfl, rfl, -⟩ := ht
        cases h
        refine Iff.trans ?_ (xstepOut_noGuard (by rfl)).symm
        exact case_select hs
      · cases h
    · cases h
  case intLoad t p x arg =>
    split at h
    · rename_i a st hs
      split at h
      · rename_i hcond
        obtain ⟨hmem, hx, -⟩ := hcond
        subst hmem
        cases h
        refine Iff.trans ?_ (xstepOut_guard (g := .inb a arg (accBytes t (p.map Prod.fst))) (by simp [XState.guard])).symm
        by_cases hb : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t (p.map Prod.fst) ≤
            c.mi.bytes.size
        · rw [ite_eq_left ((holds_inb a arg _).mpr hb), storeOf_guard, frameOf_guard]
          exact case_load hc hx hs hb
        · rw [ite_eq_right (fun h' => hb ((holds_inb a arg _).mp h'))]
          exact case_load_oob hc hx hs hb
      · cases h
    · cases h
  case intStore t p x arg =>
    split at h
    · rename_i t₁ v a st hs
      split at h
      · rename_i hcond
        obtain ⟨hmem, hx, rfl, -⟩ := hcond
        subst hmem
        cases h
        refine Iff.trans ?_ (xstepOut_guard (g := .inb a arg (accBytes t₁ p)) (by simp [XState.guard])).symm
        by_cases hb : effAddr (evX c.ρ c.mi.bytes .i32 a).toNat arg + accBytes t₁ p ≤ c.mi.bytes.size
        · rw [ite_eq_left ((holds_inb a arg _).mpr hb)]
          exact case_store hc hx hs hb
        · rw [ite_eq_right (fun h' => hb ((holds_inb a arg _).mp h'))]
          exact case_store_oob hc hx hs hb
      · cases h
    · cases h

end Silmaril.Proofs.Wasm.Auto.Equiv