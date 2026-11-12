module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Entry

/-!
# Round 7, REH route 2: matching a clause's arguments (unrefined)
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

theorem findTyp?_bindTyp (ρ : VarEnv) (y x : IL.Id) (t : Typ) :
    (ρ.bindTyp y t).findTyp? x =
      if y = "_" then ρ.findTyp? x else if y = x then some t else ρ.findTyp? x :=
  find?_bind _ _ _ _

theorem findDef?_bindDef (ρ : VarEnv) (y x z : IL.Id) :
    (ρ.bindDef y z).findDef? x =
      if y = "_" then ρ.findDef? x else if y = x then some z else ρ.findDef? x :=
  find?_bind _ _ _ _

/-- The facts one step of argument matching establishes. -/
structure StepFacts (ρ ρ' : VarEnv) (a : Arg) : Prop where
  defsMono : ∀ y, (ρ.findDef? y).isSome = true → (ρ'.findDef? y).isSome = true
  defsHere : ∀ y, a = .defA y → y ≠ "_" → (ρ'.findDef? y).isSome = true
  typsMono : ∀ x, (ρ.findTyp? x).isSome = true → (ρ'.findTyp? x).isSome = true
  typsHere : ∀ x, a = .typA (.varT x []) → (ρ'.findTyp? x).isSome = true

variable {env : Env} {qs : List Param} {tps : List String} {b : AT} {Γ : List (String × AT)}
  {W : List ArgV}

set_option maxHeartbeats 800000 in
/-- **One argument pattern.** -/
theorem entry_step (hF : SigFacts) (hX : env.memTyp "X" = false) (htps : tps = [] ∨ tps = ["X"])
    (hbx : xFree b = true) (hdq : tps = [] ∨ defQuants qs = []) :
    ∀ (k : Nat) (a : Arg) (w : ArgV) (p : Param) (ρ ρ' : VarEnv),
    argAlign qs [a] [p] = true →
    patArgs (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs) Γ [a]
      ((paramPTs [p]).map (substPT tps b)) = true →
    ArgsVT sigX tsigFixed [w] ((paramPTs [p]).map (substPT tps b)) →
    w ∈ W → (p matches .gramP ..) = false → (∀ y, p = .typP y → y ∈ tps) →
    EntryInv (clauseSig sigX tps b qs) Γ qs tps W ρ → matchArg k env ρ a w = .ok ρ' →
    EntryInv (clauseSig sigX tps b qs) Γ qs tps W ρ' ∧ StepFacts ρ ρ' a := by
  intro k a w p ρ ρ' hal hpa hav hw hg hty hinv hm
  cases k with
  | zero => simp [matchArg] at hm
  | succ k =>
  cases a with
  | expA e =>
    cases p with
    | expP x t =>
      cases w with
      | val v =>
        simp only [matchArg] at hm
        split at hm
        · simp only [paramPTs, List.map_cons, List.map_nil, substPT, patArgs, Bool.and_true] at hpa
          simp only [paramPTs, List.map_cons, List.map_nil, substPT, ArgsVT, and_true] at hav
          have hv := vtB_clause_of hF htps b qs
            (by rcases htps with h | h
                · exact .inl h
                · exact .inr (xFree_substTP_X (by rw [h]; decide) hbx _)) hav
          have hmo := (matchAt env k).exp _ _ Γ ρ e _ v ρ' hinv.scope hpa hv hm
          have hd : ∀ y, ρ'.findDef? y = ρ.findDef? y := fun y => by
            simp only [VarEnv.findDef?, hmo.2.1]
          have ht : ∀ y, ρ'.findTyp? y = ρ.findTyp? y := fun y => by
            simp only [VarEnv.findTyp?, hmo.2.2]
          refine ⟨⟨hmo.1, fun y g' hy => hinv.defs y g' ((hd y).symm.trans hy),
            fun x t hx => hinv.typs x t ((ht x).symm.trans hx)⟩, ⟨?_, ?_, ?_, ?_⟩⟩
          · intro y hy; rw [hd]; exact hy
          · intro y h; cases h
          · intro x hx; rw [ht]; exact hx
          · intro x h; cases h
        · cases hm
      | _ => simp [paramPTs, substPT, ArgsVT] at hav
    | _ => simp [argAlign] at hal
  | typA t =>
    cases p with
    | typP y =>
      have hyt := hty y rfl
      cases t with
      | varT x xs =>
        cases xs with
        | nil =>
          simp only [argAlign, Bool.and_true, beq_iff_eq] at hal
          subst hal
          cases w with
          | typ t =>
            simp only [matchArg, matchTypV] at hm
            split at hm
            · split at hm
              · cases hm
                refine ⟨hinv, ⟨fun _ h => h, ?_, fun _ h => h, ?_⟩⟩
                · intro y h; cases h
                · intro x' h
                  cases h
                  simp_all
              · cases hm
            · rename_i hnone
              have hxX : x = "X" := by
                rcases htps with h | h
                · rw [h] at hyt; cases hyt
                · rw [h] at hyt; simpa using hyt
              subst hxX
              rw [hX] at hm
              simp only [Bool.false_eq_true, ite_false, Except.ok.injEq] at hm
              subst hm
              refine ⟨⟨hinv.scope.congr_vals rfl, fun y g' hy => hinv.defs y g' hy,
                fun x' t' hx' => ?_⟩, ⟨fun _ h => h, ?_, fun x' h => ?_,
                fun x' h => ?_⟩⟩
              · rw [findTyp?_bindTyp] at hx'
                simp only [show ("X" : String) ≠ "_" by decide, ite_false] at hx'
                split at hx'
                · cases hx'; rename_i h; subst h; exact ⟨hyt, hw⟩
                · exact hinv.typs x' t' hx'
              · intro y h; cases h
              · rw [findTyp?_bindTyp]
                simp only [show ("X" : String) ≠ "_" by decide, ite_false]
                split <;> simp_all
              · cases h
                rw [findTyp?_bindTyp]
                simp
          | _ => simp [paramPTs, substPT, ArgsVT, matchArg] at hav hm
        | cons _ _ => simp [argAlign] at hal
      | _ => simp [argAlign] at hal
    | _ => simp [argAlign] at hal
  | defA y =>
    cases p with
    | defP z dps t =>
      simp only [argAlign, Bool.and_true] at hal
      split at hal
      · rename_i dps' t' hl
        simp only [Bool.and_eq_true, optATEq_iff, atEq_iff] at hal
        obtain ⟨rfl, rfl⟩ := hal
        have htps0 : tps = [] := by
          rcases hdq with h | h
          · exact h
          · rw [h] at hl; simp [List.lookup] at hl
        subst htps0
        cases w with
        | defName g' =>
          simp only [paramPTs, List.map_cons, List.map_nil, substPT_nil, ArgsVT, and_true] at hav
          simp only [matchArg, Except.ok.injEq] at hm
          subst hm
          refine ⟨⟨hinv.scope.congr_vals rfl, fun y' g'' hy' => ?_, fun x t hx => hinv.typs x t hx⟩,
            ⟨fun y' h => ?_, fun y' h hy => ?_, fun _ h => h, fun _ h => by cases h⟩⟩
          · rw [findDef?_bindDef] at hy'
            split at hy'
            · exact hinv.defs y' g'' hy'
            · split at hy'
              · cases hy'; rename_i _ h; subst h; exact ⟨_, _, hl, hav⟩
              · exact hinv.defs y' g'' hy'
          · rw [findDef?_bindDef]
            split
            · exact h
            · split <;> simp_all
          · cases h
            rw [findDef?_bindDef]
            simp [hy]
        | _ => simp [paramPTs, substPT, ArgsVT] at hav
      · cases hal
    | _ => simp [argAlign] at hal
  | gramA g =>
    cases p with
    | gramP _ _ _ => simp at hg
    | _ => simp [argAlign] at hal

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

variable {env : Env} {qs : List Param} {tps : List String} {b : AT} {Γ : List (String × AT)}
  {W : List ArgV}

theorem argAlign_cons (a : Arg) (args : List Arg) (p : Param) (ps : List Param)
    (h : argAlign qs (a :: args) (p :: ps) = true) :
    argAlign qs [a] [p] = true ∧ argAlign qs args ps = true := by
  cases a with
  | typA t =>
    cases t with
    | varT x xs =>
      cases xs with
      | nil => cases p <;> simp_all [argAlign]
      | cons _ _ => simp [argAlign] at h
    | _ => simp [argAlign] at h
  | _ => cases p <;> simp_all [argAlign]

theorem patArgs_cons {S : Sig} {T : TSig} (a : Arg) (args : List Arg) (q : PT) (qs' : List PT)
    (h : patArgs S T Γ (a :: args) (q :: qs') = true) :
    patArgs S T Γ [a] [q] = true ∧ patArgs S T Γ args qs' = true := by
  cases a <;> cases q <;> simp_all [patArgs]

theorem argsVT_cons {S : Sig} {T : TSig} (w : ArgV) (ws : List ArgV) (q : PT) (qs' : List PT)
    (h : ArgsVT S T (w :: ws) (q :: qs')) : ArgsVT S T [w] [q] ∧ ArgsVT S T ws qs' := by
  cases w <;> cases q <;> simp_all [ArgsVT]

set_option maxHeartbeats 400000 in
/-- **Matching a clause's argument patterns.** -/
theorem entry_go (hF : SigFacts) (hX : env.memTyp "X" = false) (htps : tps = [] ∨ tps = ["X"])
    (hbx : xFree b = true) (hdq : tps = [] ∨ defQuants qs = []) :
    ∀ (k : Nat) (args : List Arg) (ws : List ArgV) (ps : List Param) (ρ ρ' : VarEnv),
    argAlign qs args ps = true →
    patArgs (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs) Γ args
      ((paramPTs ps).map (substPT tps b)) = true →
    ArgsVT sigX tsigFixed ws ((paramPTs ps).map (substPT tps b)) →
    (∀ w ∈ ws, w ∈ W) → noGram ps → (∀ y, Param.typP y ∈ ps → y ∈ tps) →
    EntryInv (clauseSig sigX tps b qs) Γ qs tps W ρ → matchArgs k env ρ args ws = .ok ρ' →
    EntryInv (clauseSig sigX tps b qs) Γ qs tps W ρ' ∧
      (∀ y, (ρ.findDef? y).isSome = true → (ρ'.findDef? y).isSome = true) ∧
      (∀ y, Arg.defA y ∈ args → y ≠ "_" → (ρ'.findDef? y).isSome = true) ∧
      (∀ x, (ρ.findTyp? x).isSome = true → (ρ'.findTyp? x).isSome = true) ∧
      (∀ x, Arg.typA (.varT x []) ∈ args → (ρ'.findTyp? x).isSome = true)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | k + 1, [], [], _, ρ, ρ', _, _, _, _, _, _, hinv, hm => by
    simp only [matchArgs, Except.ok.injEq] at hm
    subst hm
    exact ⟨hinv, fun _ h => h, fun _ h => by simp at h, fun _ h => h, fun _ h => by simp at h⟩
  | k + 1, a :: args, w :: ws, p :: ps, ρ, ρ', hal, hpa, hav, hW, hng, hty, hinv, hm => by
    simp only [matchArgs, Res.bind_eq_ok] at hm
    obtain ⟨ρ₁, h₁, h₂⟩ := hm
    have hal' := argAlign_cons a args p ps hal
    simp only [paramPTs, List.map_cons] at hpa hav
    have hpa' := patArgs_cons a args _ _ hpa
    have hav' := argsVT_cons w ws _ _ hav
    obtain ⟨hinv₁, hs⟩ := entry_step hF hX htps hbx hdq k a w p ρ ρ₁ hal'.1
      (by simpa [paramPTs] using hpa'.1) (by simpa [paramPTs] using hav'.1)
      (hW w (List.mem_cons_self ..)) (hng p (List.mem_cons_self ..))
      (fun y h => hty y (h ▸ List.mem_cons_self ..)) hinv h₁
    obtain ⟨hinv', hd, hda, ht, hta⟩ := entry_go hF hX htps hbx hdq k args ws ps ρ₁ ρ' hal'.2
      hpa'.2 hav'.2 (fun w' hw' => hW w' (List.mem_cons_of_mem _ hw'))
      (fun q hq => hng q (List.mem_cons_of_mem _ hq))
      (fun y hy => hty y (List.mem_cons_of_mem _ hy)) hinv₁ h₂
    refine ⟨hinv', fun y h => hd y (hs.defsMono y h), fun y hy hy' => ?_,
      fun x h => ht x (hs.typsMono x h), fun x hx => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hd y (hs.defsHere y rfl hy')
      · exact hda y hy hy'
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ht x (hs.typsHere x rfl)
      · exact hta x hx
  | k + 1, [], _ :: _, _, _, _, _, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | k + 1, _ :: _, [], _, _, _, _, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | k + 1, _ :: _, _ :: _, [], _, _, hal, _, _, _, _, _, _, _ => by
    cases ‹Arg› <;> simp [argAlign] at hal

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
