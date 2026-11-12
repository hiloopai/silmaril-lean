module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.StepExp

/-!
# Round 7, REH route 2: the other expression members, one step, and `ExpAt` at every fuel
(unrefined)

`expAt : (∀ m < k, DefsHyp) → ExpAt env k` is assembled from the step lemmas of the members by
induction on fuel. The calls are not unfolded here: `CallH` is a hypothesis of every member.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {n : Nat} {S : Sig} {T : TSig} {Γ : List (String × AT)}

/-! ## Static judgments on lists -/

theorem tyOkL_cons {e : Exp} {es : List Exp} :
    tyOkL S T Γ (e :: es) = (tyOk S T Γ e && tyOkL S T Γ es) := by rw [tyOkL]

theorem auxL_cons {tps : AuxCtx} {e : Exp} {es : List Exp} :
    auxL tps (e :: es) = (auxE tps e && auxL tps es) := by rw [auxL]

theorem tyOkD_cons {x : IL.Id} {e : Exp} {ds : List Dom} :
    tyOkD S T Γ (.mk x e :: ds) = (tyOk S T Γ e && tyOkD S T Γ ds) := by rw [tyOkD]

theorem auxD_cons {tps : AuxCtx} {x : IL.Id} {e : Exp} {ds : List Dom} :
    auxD tps (.mk x e :: ds) = (auxE tps e && auxD tps ds) := by rw [auxD]

theorem tyOkF_cons {a : AtomS} {e : Exp} {fs : List ExpField} :
    tyOkF S T Γ (.mk a e :: fs) = (tyOk S T Γ e && tyOkF S T Γ fs) := by rw [tyOkF]

theorem auxF_cons {tps : AuxCtx} {a : AtomS} {e : Exp} {fs : List ExpField} :
    auxF tps (.mk a e :: fs) = (auxE tps e && auxF tps fs) := by rw [auxF]

theorem tyOkA_cons (x : Arg) (xs : List Arg) :
    tyOkA S T Γ (x :: xs) = (tyOkA S T Γ [x] && tyOkA S T Γ xs) := by
  cases x <;> simp [tyOkA]

theorem auxA_cons (tps : AuxCtx) (x : Arg) (xs : List Arg) :
    auxA tps (x :: xs) = (auxA tps [x] && auxA tps xs) := by
  cases x <;> simp [auxA]

theorem ckArgs_cons (x : Arg) (xs : List Arg) (p : PT) (ps : List PT) :
    ckArgs S T Γ (x :: xs) (p :: ps) = (ckArgs S T Γ [x] [p] && ckArgs S T Γ xs ps) := by
  cases x <;> cases p <;> simp [ckArgs]

theorem ArgsR_cons {ρ : VarEnv} (x : Arg) (xs : List Arg) (w : ArgV) (ws : List ArgV) (p : PT)
    (ps : List PT) (h₁ : ArgsR S T ρ [x] [w] [p]) (h₂ : ArgsR S T ρ xs ws ps) :
    ArgsR S T ρ (x :: xs) (w :: ws) (p :: ps) := by
  cases x <;> cases w <;> cases p <;> simp_all [ArgsR]

/-! ## The lists of expressions -/

theorem step_exps (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (hρ : ScopeVT S Γ ρ)
    (hc : CallH S T tps env ρ (n + 1)) : ∀ (es : List Exp) (vs : List Value),
    tyOkL S T Γ es = true → auxL tps es = true → evalExps (n + 1) env ρ es = .ok vs →
    List.Forall₂ (EOk S T Γ) es vs := by
  intro es vs ht ha hv
  simp only [evalExps] at hv
  have h := mapM_forall₂ hv
  clear hv
  induction h with
  | nil => exact .nil
  | @cons e v es vs he _ ih' =>
    rw [tyOkL_cons, Bool.and_eq_true] at ht
    rw [auxL_cons, Bool.and_eq_true] at ha
    exact .cons (ih.exp S T Γ tps ρ e v hρ (hc.mono (Nat.le_succ n)) ht.1 ha.1 he) (ih' ht.2 ha.2)

theorem step_fields (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (hρ : ScopeVT S Γ ρ)
    (hc : CallH S T tps env ρ (n + 1)) : ∀ (fs : List ExpField) (gs : List (AtomS × Value)),
    tyOkF S T Γ fs = true → auxF tps fs = true → evalExpFields (n + 1) env ρ fs = .ok gs →
    List.Forall₂ (fun f g => match f with | .mk a e => g.1 = a ∧ EOk S T Γ e g.2) fs gs := by
  intro fs gs ht ha hv
  simp only [evalExpFields] at hv
  have h := mapM_forall₂ hv
  clear hv
  induction h with
  | nil => exact .nil
  | @cons f g fs gs hf _ ih' =>
    obtain ⟨a, e⟩ := f
    rw [tyOkF_cons, Bool.and_eq_true] at ht
    rw [auxF_cons, Bool.and_eq_true] at ha
    simp only [Res.map_eq_ok] at hf
    obtain ⟨w, hw, rfl⟩ := hf
    exact .cons ⟨rfl, ih.exp S T Γ tps ρ e w hρ (hc.mono (Nat.le_succ n)) ht.1 ha.1 hw⟩ (ih' ht.2 ha.2)

theorem step_doms (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (hρ : ScopeVT S Γ ρ)
    (hc : CallH S T tps env ρ (n + 1)) : ∀ (ds : List Dom) (xvs : List (IL.Id × Value)),
    tyOkD S T Γ ds = true → auxD tps ds = true → evalDoms (n + 1) env ρ ds = .ok xvs →
    List.Forall₂ (fun d p => p.1 = domVar d ∧ EOk S T Γ (domSrc d) p.2) ds xvs := by
  intro ds xvs ht ha hv
  simp only [evalDoms] at hv
  have h := mapM_forall₂ hv
  clear hv
  induction h with
  | nil => exact .nil
  | @cons d p ds xvs hd _ ih' =>
    obtain ⟨x, e⟩ := d
    rw [tyOkD_cons, Bool.and_eq_true] at ht
    rw [auxD_cons, Bool.and_eq_true] at ha
    simp only [Res.map_eq_ok] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    exact .cons ⟨rfl, ih.exp S T Γ tps ρ e w hρ (hc.mono (Nat.le_succ n)) ht.1 ha.1 hw⟩ (ih' ht.2 ha.2)

/-! ## Arguments -/

theorem step_arg (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv) (hρ : ScopeVT S Γ ρ)
    (hc : CallH S T tps env ρ (n + 1)) (x : Arg) (w : ArgV) (ht : tyOkA S T Γ [x] = true)
    (ha : auxA tps [x] = true) (hv : evalArg (n + 1) env ρ x = .ok w) (p : PT)
    (hp : ckArgs S T Γ [x] [p] = true) : ArgsR S T ρ [x] [w] [p] := by
  cases x with
  | expA e =>
    simp only [tyOkA, Bool.and_true] at ht
    simp only [auxA, Bool.and_true] at ha
    simp only [evalArg, Res.map_eq_ok] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    have h := ih.exp S T Γ tps ρ e v hρ (hc.mono (Nat.le_succ n)) ht ha hv
    cases p with
    | exp a =>
      simp only [ckArgs, Bool.and_true] at hp
      exact ⟨h.ck a hp, trivial⟩
    | _ => simp [ckArgs] at hp
  | typA t =>
    simp only [evalArg, Except.ok.injEq] at hv
    subst hv
    cases p with
    | other => exact ⟨rfl, trivial⟩
    | _ => simp [ckArgs] at hp
  | defA g =>
    simp only [evalArg, Except.ok.injEq] at hv
    subst hv
    cases p with
    | defn dps r =>
      simp only [ckArgs, Bool.and_true] at hp
      exact ⟨rfl, hp, trivial⟩
    | _ => simp [ckArgs] at hp
  | gramA g =>
    simp only [evalArg, Except.ok.injEq] at hv
    subst hv
    cases p with
    | other => exact trivial
    | _ => simp [ckArgs] at hp

theorem step_args (ih : ExpAt env n) (tps : AuxCtx) (ρ : VarEnv)
    (hρ : ScopeVT S Γ ρ) (hc : CallH S T tps env ρ (n + 1)) : ∀ (xs : List Arg) (ws : List ArgV),
    tyOkA S T Γ xs = true → auxA tps xs = true → evalArgs (n + 1) env ρ xs = .ok ws →
    ∀ ps, ckArgs S T Γ xs ps = true → ArgsR S T ρ xs ws ps := by
  intro xs ws ht ha hv
  simp only [evalArgs] at hv
  have h := mapM_forall₂ hv
  clear hv
  induction h with
  | nil =>
    intro ps hp
    cases ps with
    | nil => trivial
    | cons _ _ => simp [ckArgs] at hp
  | @cons x w xs ws hx _ ih' =>
    intro ps hp
    rw [tyOkA_cons, Bool.and_eq_true] at ht
    rw [auxA_cons, Bool.and_eq_true] at ha
    cases ps with
    | nil => cases x <;> simp [ckArgs] at hp
    | cons p ps =>
      rw [ckArgs_cons, Bool.and_eq_true] at hp
      exact ArgsR_cons x xs w ws p ps
        (ih.arg S T Γ tps ρ x w hρ (hc.mono (Nat.le_succ n)) ht.1 ha.1 hx p hp.1)
        (ih' ht.2 ha.2 ps hp.2)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
