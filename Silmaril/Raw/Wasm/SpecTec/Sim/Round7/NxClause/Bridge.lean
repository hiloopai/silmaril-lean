module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Match

/-!
# Round 8, REH route 2: `CallE` inside a clause, from `DefsE` below the fuel (unrefined)

`callE_clause` is `NxFlow.callH_clause` with erasure in place of conformance: inside a clause, a
call the flow check passes resolves to a `gdE` definition whose evaluated arguments conform to
its parameter types (`NxSound.ArgsVT` at `NxSound.parV`), so `DefsE` below the fuel answers it.
The conversion from the clause's signature to `sigX` is round 7's (`argsVT_of_go`,
`argsVT_of_argsR`, `tpFill_eq`). It needs every `gdE` definition to have a parameter entry, which
the kernel check `yItems_fixed` gives.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (gdE)

set_option maxHeartbeats 1000000 in
/-- **Clause bodies commute with erasure at the calls inside a clause**, given `DefsE` below the
current fuel and parameter entries for the `gdE` definitions. -/
theorem callE_clause (hF : SigFacts) {env : Env}
    (hP : ∀ f d, gdE f = true → env.findDef? f = some d → (tsigFixed.params.lookup f).isSome = true)
    {k : Nat} (ih : ∀ m < k, DefsE env m) {qs : List Param} {tps : List String} {b : AT}
    (htps : tps = [] ∨ tps = ["X"]) (hb : tps = [] ∨ b = .unk ∨ b = .base)
    (hdq : tps = [] ∨ defQuants qs = [])
    {ρ : VarEnv} (hctx : ClauseCtx ρ qs tps b) :
    NxErase.CallE gdE (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs)
      (tps, (defQuants qs).map (·.1)) env ρ k := by
  intro m hm f xs ws d hA hta hg hd hw
  cases hf : ρ.findDef? f with
  | some g' =>
    obtain ⟨dps, r, hl, hdef⟩ := hctx.defs f g' hf
    have h0 : tps = [] := by
      rcases hdq with h | h
      · exact h
      · rw [h] at hl; simp [List.lookup] at hl
    subst h0
    rw [hf, Option.getD_some] at hg hd
    have hpl : (clauseTSig tsigFixed [] b qs).params.lookup f =
        some ([], dps.map fun o => match o with
          | some a => PT.exp (substTP [] b a)
          | none => PT.other) := by
      simp only [clauseTSig]
      exact lookup_append_of_some (lookup_map_some hl)
    have hp : callPar (clauseSig sigX [] b qs) (clauseTSig tsigFixed [] b qs) f xs =
        some (dps.map fun o => match o with
          | some a => PT.exp a
          | none => PT.other) := by
      simp only [callPar, hpl, Option.map_some]
      rw [map_substPT_nil]
      congr 2
      funext o
      cases o <;> simp [substTP_nil]
    have hargs := hA _ hp
    simp only [defSub, Bool.and_eq_true] at hdef
    obtain ⟨-, hpar⟩ := hdef
    split at hpar
    · rename_i gps hgl
      have hargsVT := argsVT_of_go (fun a v h => vtB_of_clause hF (.inl rfl) b qs (.inl rfl) h)
        xs ws dps gps hargs hpar
      have hpv : parV sigX tsigFixed g' ws = some gps := by
        simp [parV, hgl, map_substPT_nil]
      exact ih m hm g' d gps ws hg hd hpv hargsVT hw
    · cases hpar
  | none =>
    rw [hf, Option.getD_none] at hg hd
    have hfq : (defQuants qs).lookup f = none := by
      cases h : (defQuants qs).lookup f with
      | none => rfl
      | some c =>
        have := hctx.defsIn f (by simp [h])
        rw [hf] at this; cases this
    obtain ⟨⟨tps_f, pts_f⟩, hpf⟩ := Option.isSome_iff_exists.1 (hP f d hg hd)
    have hp : callPar (clauseSig sigX tps b qs) (clauseTSig tsigFixed tps b qs) f xs =
        some (pts_f.map (substPT tps_f (tpFill (clauseSig sigX tps b qs) xs))) := by
      simp only [callPar, params_clause_none hfq, hpf, Option.map_some]
    have hargs := hA _ hp
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
    exact ih m hm f d _ ws hg hd hpv hargsVT hw

/-- **The same in a scope without definition and type bindings**, the scope of a rule instance:
`NxErase.Task.clauseErase`'s conclusion. -/
theorem callE_nil (hF : SigFacts) {env : Env}
    (hP : ∀ f d, gdE f = true → env.findDef? f = some d → (tsigFixed.params.lookup f).isSome = true)
    {k : Nat} (ih : ∀ m < k, DefsE env m) {ρ : VarEnv} (hd : ρ.defs = []) (ht : ρ.typs = []) :
    NxErase.CallE gdE sigX tsigFixed ([], []) env ρ k := by
  have h := callE_clause hF hP ih (qs := []) (tps := []) (b := .unk) (.inl rfl) (.inl rfl)
    (.inl rfl) (NxRule.clauseCtx_nil hd ht)
  rw [NxRule.clauseSig_nil, NxRule.clauseTSig_nil] at h
  simpa [defQuants] using h

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
