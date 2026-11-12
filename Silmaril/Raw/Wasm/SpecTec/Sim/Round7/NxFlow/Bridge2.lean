module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Bridge

/-!
# Round 7, REH route 2: `CallH` inside a clause (unrefined)
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

theorem defSub_go_congr {S₁ S₂ : Sig} (h : ∀ k a b, atLe S₁ k a b = atLe S₂ k a b) :
    ∀ dps gps, defSub.go S₁ dps gps = defSub.go S₂ dps gps
  | [], [] => rfl
  | some d :: ds, .exp p :: ps => by simp only [defSub.go, h, defSub_go_congr h ds ps]
  | none :: ds, .other :: ps => by simp only [defSub.go, defSub_go_congr h ds ps]
  | [], _ :: _ => rfl
  | _ :: _, [] => by cases ‹Option AT› <;> rfl
  | some _ :: _, .defn _ _ :: _ => rfl
  | some _ :: _, .other :: _ => rfl
  | none :: _, .exp _ :: _ => rfl
  | none :: _, .defn _ _ :: _ => rfl

theorem atLe_clause (b : AT) (qs : List Param) (k : Nat) (a c : AT) :
    atLe (clauseSig sigX [] b qs) k a c = atLe sigX k a c :=
  atLe_eq_good (sameShape_clauseSig sigX [] b qs).symm (clauseSig_good_nil sigX b qs) k a c

theorem lookup_map_none {β γ : Type} {G : String × β → γ} :
    ∀ {l : List (String × β)} {x : String}, l.lookup x = none →
      (l.map fun p => (p.1, G p)).lookup x = none
  | [], _, _ => rfl
  | (y, c) :: l, x, h => by
    simp only [List.lookup] at h
    simp only [List.map_cons, List.lookup]
    split at h
    · cases h
    · rename_i hy
      exact lookup_map_none h

theorem lookup_map_some {β γ : Type} {G : String × β → γ} :
    ∀ {l : List (String × β)} {x : String} {c : β}, l.lookup x = some c →
      (l.map fun p => (p.1, G p)).lookup x = some (G (x, c))
  | [], _, _, h => by cases h
  | (y, c') :: l, x, c, h => by
    simp only [List.lookup] at h
    simp only [List.map_cons, List.lookup]
    split at h
    · rename_i hy
      cases h
      have : x = y := beq_iff_eq.1 hy
      subst this
      simp
    · rename_i hy
      exact lookup_map_some h

theorem results_clause_none {tps : List String} {b : AT} {qs : List Param} {g : String}
    (hg : (defQuants qs).lookup g = none) :
    (clauseSig sigX tps b qs).results.lookup g = sigX.results.lookup g := by
  simp only [clauseSig]
  exact lookup_append_of_none (lookup_map_none hg)

theorem params_clause_none {tps : List String} {b : AT} {qs : List Param} {g : String}
    (hg : (defQuants qs).lookup g = none) :
    (clauseTSig tsigFixed tps b qs).params.lookup g = tsigFixed.params.lookup g := by
  simp only [clauseTSig]
  exact lookup_append_of_none (lookup_map_none hg)

theorem defSub_clause {b : AT} {qs : List Param} {g : String} (hg : (defQuants qs).lookup g = none)
    (dps : List (Option AT)) (r : AT) :
    defSub (clauseSig sigX [] b qs) (clauseTSig tsigFixed [] b qs) g dps r =
      defSub sigX tsigFixed g dps r := by
  simp only [defSub, results_clause_none hg, params_clause_none hg, atLe_clause]
  split <;> simp only [defSub_go_congr (atLe_clause b qs)]

/-- The conversion of `ArgsR` to `NxSound.ArgsVT` for a call through a definition parameter. -/
theorem argsVT_of_go {S' : Sig} {T' : TSig} {ρ : VarEnv}
    (hconv : ∀ a v, vtB S' a v = true → vtB sigX a v = true) :
    ∀ (xs : List Arg) (ws : List ArgV) (dps : List (Option AT)) (gps : List PT),
      ArgsR S' T' ρ xs ws (dps.map fun o => match o with
        | some a => PT.exp a
        | none => PT.other) →
      defSub.go sigX dps gps = true → ArgsVT sigX tsigFixed ws gps
  | [], [], [], [], _, _ => trivial
  | x :: xs, w :: ws, some d :: dps, .exp p :: gps, h, hg => by
    simp only [defSub.go, Bool.and_eq_true] at hg
    simp only [List.map_cons] at h
    cases x <;> cases w <;> simp only [ArgsR] at h
    exact ⟨vtB_of_atLe sigX _ _ _ hg.1 _ (hconv _ _ h.1), argsVT_of_go hconv xs ws dps gps h.2 hg.2⟩
  | x :: xs, w :: ws, none :: dps, .other :: gps, h, hg => by
    simp only [defSub.go] at hg
    simp only [List.map_cons] at h
    cases x <;> cases w <;> simp only [ArgsR] at h
    · exact argsVT_of_go hconv xs ws dps gps h.2 hg
    · exact argsVT_of_go hconv xs ws dps gps h hg
  | [], _ :: _, _, _, h, _ => by cases ‹List (Option AT)› <;> simp [ArgsR] at h
  | _ :: _, [], _, _, h, _ => by cases ‹List (Option AT)› <;> simp [ArgsR] at h
  | [], [], _ :: _, _, h, _ => by simp [ArgsR] at h
  | _ :: _, _ :: _, [], _, h, _ => by simp [ArgsR] at h
  | _, _, [], _ :: _, _, hg => by simp [defSub.go] at hg
  | _, _, some _ :: _, [], _, hg => by simp [defSub.go] at hg
  | _, _, none :: _, [], _, hg => by simp [defSub.go] at hg
  | _, _, some _ :: _, .defn _ _ :: _, _, hg => by simp [defSub.go] at hg
  | _, _, some _ :: _, .other :: _, _, hg => by simp [defSub.go] at hg
  | _, _, none :: _, .exp _ :: _, _, hg => by simp [defSub.go] at hg
  | _, _, none :: _, .defn _ _ :: _, _, hg => by simp [defSub.go] at hg

/-- The conversion of `ArgsR` to `NxSound.ArgsVT` for a call of a definition of the script. -/
theorem argsVT_of_argsR {qs : List Param} {tps : List String} {b : AT} {ρ : VarEnv}
    (hctx : ClauseCtx ρ qs tps b) {T' : TSig} (hT' : T' = clauseTSig tsigFixed tps b qs) :
    ∀ (xs : List Arg) (ws : List ArgV) (ps : List PT),
      ArgsR (clauseSig sigX tps b qs) T' ρ xs ws ps →
      typArgsOk (tps, (defQuants qs).map (·.1)) xs = true →
      (∀ a ∈ ps, ∀ c, a = PT.exp c → ∀ v,
        vtB (clauseSig sigX tps b qs) c v = true → vtB sigX c v = true) →
      ArgsVT sigX tsigFixed ws ps
  | [], [], [], _, _, _ => trivial
  | .expA _ :: xs, .val v :: ws, .exp c :: ps, ⟨h₁, h₂⟩, ht, hc => by
    simp only [typArgsOk, List.all_cons, Bool.true_and] at ht
    exact ⟨hc _ (List.mem_cons_self ..) c rfl v h₁,
      argsVT_of_argsR hctx hT' xs ws ps h₂ ht fun a ha => hc a (List.mem_cons_of_mem _ ha)⟩
  | .defA g :: xs, .defName g' :: ws, .defn dps r :: ps, ⟨h₀, h₁, h₂⟩, ht, hc => by
    simp only [typArgsOk, List.all_cons, Bool.and_eq_true, List.isEmpty_iff,
      Bool.not_eq_true'] at ht
    obtain ⟨⟨htps, hgq⟩, ht⟩ := ht
    subst htps hT'
    have hgl : (defQuants qs).lookup g = none := by
      cases hl : (defQuants qs).lookup g with
      | none => rfl
      | some c =>
        have := List.contains_iff_mem.2 (lookup_mem_names hl)
        rw [this] at hgq; cases hgq
    have hfd : ρ.findDef? g = none := by
      cases hf : ρ.findDef? g with
      | none => rfl
      | some g'' =>
        obtain ⟨_, _, hl, _⟩ := hctx.defs g g'' hf
        rw [hl] at hgl; cases hgl
    rw [hfd, Option.getD_none] at h₀
    subst h₀
    refine ⟨?_, argsVT_of_argsR hctx rfl xs ws ps h₂ ht fun a ha => hc a (List.mem_cons_of_mem _ ha)⟩
    rw [← defSub_clause hgl]
    exact h₁
  | .typA _ :: xs, .typ _ :: ws, .other :: ps, ⟨_, h₂⟩, ht, hc => by
    simp only [typArgsOk, List.all_cons, Bool.and_eq_true] at ht
    exact argsVT_of_argsR hctx hT' xs ws ps h₂ ht.2 fun a ha => hc a (List.mem_cons_of_mem _ ha)
  | .gramA _ :: xs, .gram _ :: ws, .other :: ps, h₂, ht, hc => by
    simp only [typArgsOk, List.all_cons, Bool.true_and] at ht
    exact argsVT_of_argsR hctx hT' xs ws ps h₂ ht fun a ha => hc a (List.mem_cons_of_mem _ ha)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
