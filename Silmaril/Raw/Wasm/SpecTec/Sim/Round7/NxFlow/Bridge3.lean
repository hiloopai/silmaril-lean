module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Bridge2

/-!
# Round 7, REH route 2: `CallH` inside a clause, assembled (unrefined)
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

theorem vtB_clause_of {tps : List String} (hF : SigFacts) (htps : tps = [] ∨ tps = ["X"])
    (b : AT) (qs : List Param) {a : AT} (ha : tps = [] ∨ xFree a = true) {v : Value}
    (h : vtB sigX a v = true) : vtB (clauseSig sigX tps b qs) a v = true := by
  rw [vtB_clauseSig hF.aliases hF.fields hF.cases htps b qs ha]; exact h

theorem vtB_of_clause {tps : List String} (hF : SigFacts) (htps : tps = [] ∨ tps = ["X"])
    (b : AT) (qs : List Param) {a : AT} (ha : tps = [] ∨ xFree a = true) {v : Value}
    (h : vtB (clauseSig sigX tps b qs) a v = true) : vtB sigX a v = true := by
  rw [vtB_clauseSig hF.aliases hF.fields hF.cases htps b qs ha] at h; exact h

theorem map_conv_nil (b : AT) (dps : List (Option AT)) :
    (dps.map fun o => match o with
      | some a => PT.exp (substTP [] b a)
      | none => PT.other) = dps.map fun o => match o with
      | some a => PT.exp a
      | none => PT.other := by
  congr 1
  funext o
  cases o <;> simp [substTP_nil]

set_option maxHeartbeats 1000000 in
/-- **Calls inside a clause conform**, given that definitions conform below the current fuel. -/
theorem callH_clause (hF : SigFacts) {env : Env} {k : Nat}
    (ih : ∀ m < k, DefsVT sigX tsigFixed env m) {qs : List Param} {tps : List String} {b : AT}
    (htps : tps = [] ∨ tps = ["X"]) (hb : tps = [] ∨ b = .unk ∨ b = .base)
    (hdq : tps = [] ∨ defQuants qs = [])
    (hgr : ∀ y c, (defQuants qs).lookup y = some c → tsigFixed.gres.lookup y = none)
    {ρ : VarEnv} (hctx : ClauseCtx ρ qs tps b) :
    CallH (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs)
      (tps, (defQuants qs).map (·.1)) env ρ k := by
  intro m hm f xs ws ps d v hp hargs hta hd hr
  have hmV := ih m hm
  cases hf : ρ.findDef? f with
  | some g' =>
    obtain ⟨dps, r, hl, hdef⟩ := hctx.defs f g' hf
    have h0 : tps = [] := by
      rcases hdq with h | h
      · exact h
      · rw [h] at hl; simp [List.lookup] at hl
    subst h0
    rw [hf, Option.getD_some] at hd hr
    have hpl : (clauseTSig tsigFixed [] b qs).params.lookup f =
        some ([], dps.map fun o => match o with
          | some a => PT.exp (substTP [] b a)
          | none => PT.other) := by
      simp only [clauseTSig]
      exact lookup_append_of_some (lookup_map_some hl)
    simp only [callPar, hpl, Option.map_some, Option.some.injEq] at hp
    rw [map_substPT_nil, map_conv_nil] at hp
    subst hp
    simp only [defSub, Bool.and_eq_true] at hdef
    obtain ⟨hres, hpar⟩ := hdef
    split at hpar
    · rename_i gps hgl
      have hargsVT := argsVT_of_go (fun a v h => vtB_of_clause hF (.inl rfl) b qs (.inl rfl) h)
        xs ws dps gps hargs hpar
      have hpv : parV sigX tsigFixed g' ws = some gps := by
        simp [parV, hgl, map_substPT_nil]
      have hv := hmV g' d gps ws v hd hpv hargsVT hr
      have hgn : tsigFixed.gres.lookup g' = none := by
        cases hg : tsigFixed.gres.lookup g' with
        | none => rfl
        | some p =>
          obtain ⟨tps', r'⟩ := p
          have := (hF.gres_lookup hg).2.2
          rw [hgl] at this
          simp at this
      simp only [resV, hgn] at hv
      have hvr : vtB sigX r v = true := vtB_of_atLe sigX _ _ _ hres v hv
      have hfr : tsigFixed.gres.lookup f = none := hgr f _ hl
      have hres' : (clauseSig sigX [] b qs).results.lookup f = some r := by
        simp only [clauseSig]
        rw [lookup_append_of_some (lookup_map_some hl), substTP_nil]
      have hv' := vtB_clause_of hF (.inl rfl) b qs (.inl rfl) hvr
      refine ⟨?_, by rw [hres']; exact hv'⟩
      simp only [callRes, clauseTSig, hfr, hres']
      exact hv'
    · cases hpar
  | none =>
    rw [hf, Option.getD_none] at hd hr
    have hfq : (defQuants qs).lookup f = none := by
      cases h : (defQuants qs).lookup f with
      | none => rfl
      | some c =>
        have := hctx.defsIn f (by simp [h])
        rw [hf] at this; cases this
    simp only [callPar, params_clause_none hfq] at hp
    obtain ⟨⟨tps_f, pts_f⟩, hpf, hp⟩ := Option.map_eq_some_iff.1 hp
    simp only at hp
    subst hp
    have hmode := tpFill_eq hF hctx htps hb hargs hta
    rw [hmode] at hargs
    have hxp : ∀ c, PT.exp c ∈ pts_f.map (substPT tps_f (fillV sigX ws)) →
        tps = [] ∨ xFree c = true := by
      intro c hc
      rcases htps with h | h
      · exact .inl h
      · refine .inr ?_
        obtain ⟨p, hpm, hpe⟩ := List.mem_map.1 hc
        rcases hF.params_xFree hpf with hX | hall
        · exact xFree_substPT (fill_xFree _ _) (.inr trivial) p (.inl hX) c hpe
        · exact xFree_substPT (fill_xFree _ _) (.inr trivial) p (.inr (hall p hpm)) c hpe
    have hargsVT := argsVT_of_argsR hctx rfl xs ws _ hargs hta fun a ha c hc v hv => by
      subst hc
      exact vtB_of_clause hF htps b qs (hxp c ha) hv
    have hpv : parV sigX tsigFixed f ws = some (pts_f.map (substPT tps_f (fillV sigX ws))) := by
      simp [parV, hpf]
    have hv := hmV f d _ ws v hd hpv hargsVT hr
    have hrs := results_clause_none (tps := tps) (b := b) hfq
    have hxr : tps = [] ∨ xFree (resV sigX tsigFixed f ws) = true := by
      rcases htps with h | h
      · exact .inl h
      · refine .inr ?_
        unfold resV
        split
        · rename_i tps' r' hg
          rw [(hF.gres_lookup hg).1]
          exact xFree_substTP_X (by decide) (fill_xFree _ _) r'
        · exact hF.results_xFree f
    have hv' := vtB_clause_of hF htps b qs hxr hv
    refine ⟨?_, ?_⟩
    · have : callRes (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs) f xs =
          resV sigX tsigFixed f ws := by
        simp only [callRes, resV, clauseTSig, hrs, hmode]
        generalize List.lookup f tsigFixed.gres = o
        rcases o with _ | ⟨_, _⟩ <;> rfl
      rw [this]; exact hv'
    · rw [hrs]
      cases hg : tsigFixed.gres.lookup f with
      | some p =>
        obtain ⟨tps', r'⟩ := p
        rw [(hF.gres_lookup hg).2.1]
        exact vtB_unk _ v
      | none =>
        have : resV sigX tsigFixed f ws = (sigX.results.lookup f).getD .unk := by
          simp [resV, hg]
        rw [this] at hv'
        exact hv'

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
