module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Bridge3

/-!
# Round 7, REH route 2: entering a clause (unrefined)

`entry_go`: matching a clause's argument patterns against conforming arguments gives a
conforming scope, binds each definition parameter to a definition that may stand for it, and
binds the type parameter to the type argument (`EntryInv`). `typsOf_le`: a reachable definition
has at most one type argument, so the call's mode is that argument's export-freedom.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Type arguments -/

/-- The type arguments among evaluated arguments. -/
def typsOf (ws : List ArgV) : List Typ :=
  ws.filterMap fun w => match w with
    | .typ t => some t
    | _ => none

theorem mem_typsOf {ws : List ArgV} {t : Typ} (h : ArgV.typ t ∈ ws) : t ∈ typsOf ws := by
  simp only [typsOf, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

theorem tyArgsNxV_eq (S : Sig) : ∀ ws : List ArgV,
    tyArgsNxV S ws = (typsOf ws).all fun t => nxAT S.good (toAT t)
  | [] => rfl
  | w :: ws => by
    have ih := tyArgsNxV_eq S ws
    cases w <;> simp_all [tyArgsNxV, typsOf]

/-- No grammar parameter. -/
def noGram (ps : List Param) : Prop := ∀ p ∈ ps, (p matches .gramP ..) = false

theorem typsOf_le {S : Sig} {T : TSig} {tps : List String} {b : AT} :
    ∀ (ws : List ArgV) (ps : List Param), noGram ps →
      ArgsVT S T ws ((paramPTs ps).map (substPT tps b)) →
      (typsOf ws).length ≤ (typParams ps).length
  | [], [], _, _ => by simp [typsOf]
  | w :: ws, p :: ps, hg, h => by
    have hg' : noGram ps := fun q hq => hg q (List.mem_cons_of_mem _ hq)
    have hp := hg p (List.mem_cons_self ..)
    simp only [paramPTs, List.map_cons] at h
    cases p with
    | expP x t =>
      cases w <;> simp only [substPT, ArgsVT] at h
      simp only [typsOf, List.filterMap_cons, typParams] at ⊢
      exact typsOf_le ws ps hg' h.2
    | defP x dps t =>
      cases w <;> simp only [substPT, ArgsVT] at h
      simp only [typsOf, List.filterMap_cons, typParams] at ⊢
      exact typsOf_le ws ps hg' h.2
    | typP x =>
      cases w <;> simp only [substPT, ArgsVT] at h
      · simp only [typsOf, List.filterMap_cons, typParams, List.length_cons] at ⊢
        exact Nat.succ_le_succ (typsOf_le ws ps hg' h)
      · simp only [typsOf, List.filterMap_cons, typParams, List.length_cons] at ⊢
        exact Nat.le_succ_of_le (typsOf_le ws ps hg' h)
    | gramP x _ _ => simp at hp
  | [], _ :: _, _, h => by simp only [paramPTs, List.map_cons, ArgsVT] at h
  | _ :: _, [], _, h => by simp only [paramPTs, List.map_nil] at h; cases ‹ArgV› <;> exact h.elim

/-! ## Patterns align with parameters -/

theorem optATEq_iff : ∀ xs ys : List (Option AT), optATEq xs ys = true ↔ xs = ys
  | [], [] => by simp [optATEq]
  | some a :: xs, some b :: ys => by
    simp [optATEq, atEq_iff, optATEq_iff xs ys]
  | none :: xs, none :: ys => by simp [optATEq, optATEq_iff xs ys]
  | [], _ :: _ => by simp [optATEq]
  | _ :: _, [] => by cases ‹Option AT› <;> simp [optATEq]
  | some _ :: _, none :: _ => by simp [optATEq]
  | none :: _, some _ :: _ => by simp [optATEq]

theorem typA_of_align {qs : List Param} : ∀ (args : List Arg) (ps : List Param),
    argAlign qs args ps = true → ∀ y, Param.typP y ∈ ps → Arg.typA (.varT y []) ∈ args
  | [], [], _, y, hy => by simp at hy
  | a :: args, p :: ps, h, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · cases a with
      | typA t =>
        cases t with
        | varT x xs =>
          cases xs with
          | nil =>
            simp only [argAlign, Bool.and_eq_true, beq_iff_eq] at h
            rw [h.1]; exact List.mem_cons_self ..
          | cons _ _ => simp [argAlign] at h
        | _ => simp [argAlign] at h
      | _ => simp [argAlign] at h
    · have h' : argAlign qs args ps = true := by
        cases a with
        | typA t =>
          cases t with
          | varT x xs =>
            cases xs with
            | nil => cases p <;> simp_all [argAlign]
            | cons _ _ => simp [argAlign] at h
          | _ => simp [argAlign] at h
        | defA z => cases p <;> simp_all [argAlign]
        | _ => cases p <;> simp_all [argAlign]
      exact List.mem_cons_of_mem _ (typA_of_align args ps h' y hy)
  | [], _ :: _, h, _, _ => by simp [argAlign] at h
  | _ :: _, [], h, _, _ => by cases ‹Arg› <;> simp [argAlign] at h

/-! ## The invariant while matching the arguments -/

/-- **The invariant while matching a clause's argument patterns.** -/
structure EntryInv (S : Sig) (Γ : List (String × AT)) (qs : List Param) (tps : List String)
    (W : List ArgV) (ρ : VarEnv) : Prop where
  scope : ScopeVT S Γ ρ
  defs : ∀ y g', ρ.findDef? y = some g' → ∃ dps r, (defQuants qs).lookup y = some (dps, r) ∧
    defSub sigX tsigFixed g' dps r = true
  typs : ∀ x t, ρ.findTyp? x = some t → x ∈ tps ∧ ArgV.typ t ∈ W

theorem EntryInv.empty (S : Sig) (Γ : List (String × AT)) (qs : List Param) (tps : List String)
    (W : List ArgV) : EntryInv S Γ qs tps W VarEnv.empty where
  scope := ScopeVT.empty S Γ
  defs := fun y g' h => by simp [VarEnv.findDef?, VarEnv.empty, Map.empty] at h
  typs := fun x t h => by simp [VarEnv.findTyp?, VarEnv.empty, Map.empty] at h

theorem ScopeVT.congr_vals {S : Sig} {Γ : List (String × AT)} {ρ ρ' : VarEnv}
    (h : ScopeVT S Γ ρ) (hv : ρ'.vals = ρ.vals) : ScopeVT S Γ ρ' where
  val := fun x a v hx hv' => h.val x a v hx (by simpa [VarEnv.findVal?, hv] using hv')
  dom := fun x v hv' => h.dom x v (by simpa [VarEnv.findVal?, hv] using hv')
  wild := by simpa [VarEnv.findVal?, hv] using h.wild

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
