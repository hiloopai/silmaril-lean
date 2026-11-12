module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Clause2

/-!
# Round 7, REH route 2: a clause, the clause list, and every fuel (unrefined)
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

theorem fillV_cases (S : Sig) (ws : List ArgV) : fillV S ws = .unk ∨ fillV S ws = .base := by
  unfold fillV; split
  · exact .inr rfl
  · exact .inl rfl

set_option maxHeartbeats 1000000 in
/-- **One clause returns a conforming value.** -/
theorem clause_ok (hF : SigFacts) {env : Env} (hX : env.memTyp "X" = false) {n : Nat}
    (ih : ∀ m < n, DefsVT sigX tsigFixed env m) {f : String} {ps : List Param} {t : Typ}
    {cls : List Clause} (hD : DefFacts f ps t cls) {qs : List Param} {args : List Arg}
    {e : Exp} {prems : List Prem} (hc : Clause.defD qs args e prems ∈ cls) {ws : List ArgV}
    (hargs : ArgsVT sigX tsigFixed ws
      ((paramPTs ps).map (substPT (typParams ps) (fillV sigX ws))))
    {ρ₀ ρ₁ : VarEnv} {v : Value}
    (hm : matchArgs n env VarEnv.empty args ws = .ok ρ₀)
    (hp : premsHold n env ρ₀ prems = .ok ρ₁) (he : evalExp n env ρ₁ e = .ok v) :
    vtB sigX (resV sigX tsigFixed f ws) v = true := by
  -- the static mode
  have htps := hD.tps
  let b : AT := if typParams ps = [] then .unk else fillV sigX ws
  have hbm : b ∈ modes (typParams ps) := by
    rcases htps with h | h
    · simp [b, h, modes]
    · rcases fillV_cases sigX ws with h' | h' <;> simp [b, h, h', modes]
  have hbx : xFree b = true := by
    simp only [b]; split
    · rfl
    · exact fill_xFree _ _
  have hb : typParams ps = [] ∨ b = .unk ∨ b = .base := by
    rcases htps with h | h
    · exact .inl h
    · simp only [b, h]
      exact .inr (fillV_cases sigX ws)
  have hpts : (paramPTs ps).map (substPT (typParams ps) b) =
      (paramPTs ps).map (substPT (typParams ps) (fillV sigX ws)) := by
    rcases htps with h | h
    · rw [h, map_substPT_nil, map_substPT_nil]
    · simp [b, h]
  obtain ⟨hdp, hpa, hpr, hty, hck⟩ := clauseFlow_zero (hD.flow b hbm _ hc)
  obtain ⟨hal, hae, hap, hdq, hgq⟩ := clauseAux_parts (hD.aux _ hc)
  have hdq' : typParams ps = [] ∨ defQuants qs = [] := by
    rcases hdq with h | h
    · exact .inl (List.isEmpty_iff.1 h)
    · exact .inr (List.isEmpty_iff.1 h)
  have hargs' : ArgsVT sigX tsigFixed ws ((paramPTs ps).map (substPT (typParams ps) b)) := by
    rw [hpts]; exact hargs
  -- entering the clause
  obtain ⟨hinv, -, hda, -, hta⟩ := entry_go (W := ws) hF hX htps hbx hdq'
    n args ws ps VarEnv.empty ρ₀ hal hpa hargs' (fun w hw => hw) hD.noGram
    (fun y hy => typParams_of_typP hy) (EntryInv.empty _ _ _ _ _) hm
  have hctx : ClauseCtx ρ₀ qs (typParams ps) b := {
    defs := hinv.defs
    defsIn := fun y hy => by
      obtain ⟨c, hl⟩ := Option.isSome_iff_exists.1 hy
      have hmem := mem_of_lookup hl
      simp only [defPatsOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hdp
      obtain ⟨a, ha, hya⟩ := hdp.2 _ hmem
      cases a with
      | defA y' =>
        simp only [beq_iff_eq] at hya
        subst hya
        exact hda y' ha (hgq _ hmem).2
      | _ => cases hya
    typs := fun x t hx => by
      obtain ⟨hxt, htw⟩ := hinv.typs x t hx
      refine ⟨hxt, ?_⟩
      rcases htps with h | h
      · rw [h] at hxt; cases hxt
      · have hle := typsOf_le ws ps hD.noGram hargs'
        rw [h] at hle
        have hmem := mem_typsOf htw
        have h1 : typsOf ws = [t] := by
          match hts : typsOf ws, hle with
          | [], _ => rw [hts] at hmem; cases hmem
          | [t'], _ => rw [hts] at hmem; simp at hmem; rw [hmem]
          | _ :: _ :: _, hl => simp at hl
        have hb' : b = fillV sigX ws := by simp [b, h]
        rw [hb']
        simp only [fillV, tyArgsNxV_eq, h1, List.all_cons, List.all_nil, Bool.and_true]
        split <;> simp_all
    typsIn := fun x hx => hta x (typA_of_align args ps hal x (typP_of_typParams hx)) }
  have hgr : ∀ y c, (defQuants qs).lookup y = some c → tsigFixed.gres.lookup y = none :=
    fun y c hl => (hgq _ (mem_of_lookup hl)).1
  have hC : ∀ ρ : VarEnv, ρ.defs = ρ₀.defs → ρ.typs = ρ₀.typs →
      CallH (clauseSig sigX (typParams ps) b qs) (clauseTSig tsigFixed (typParams ps) b qs)
        (typParams ps, (defQuants qs).map (·.1)) env ρ n :=
    fun ρ hd ht => callH_clause hF ih htps hb hdq' hgr (hctx.congr hd ht)
  -- premises and body
  have m₁ := prems_ok hC prems ρ₁ hinv.scope (fun pr h => ⟨hpr pr h, hap pr h⟩) hp
  have hE := (expAt env n).exp _ _ _ _ ρ₁ e v m₁.1 (hC ρ₁ m₁.2.1 m₁.2.2) hty hae he
  have hv := hE.ck _ hck
  -- the result type
  have hres : resV sigX tsigFixed f ws = substTP (typParams ps) b (resOf sigX tsigFixed f) := by
    cases hg : tsigFixed.gres.lookup f with
    | some p =>
      obtain ⟨tps', r⟩ := p
      simp only [resV, resOf, hg]
      have h1 := tsig_gres hD.tsig hg
      have h2 := (hF.gres_lookup hg).1
      rw [h1] at h2
      have hb' : b = fillV sigX ws := by simp [b, h2]
      rw [h1, hb']
    | none =>
      simp only [resV, resOf, hg]
      rcases htps with h | h
      · rw [h, substTP_nil]
      · rw [h, substTP_X_xFree (hF.results_xFree f)]
  have hxr : typParams ps = [] ∨ xFree (resV sigX tsigFixed f ws) = true := by
    rcases htps with h | h
    · exact .inl h
    · refine .inr ?_
      unfold resV
      split
      · rename_i tps' r' hg
        rw [(hF.gres_lookup hg).1]
        exact xFree_substTP_X (by decide) (fill_xFree _ _) r'
      · exact hF.results_xFree f
  rw [← hres] at hv
  exact vtB_of_clause hF htps b qs hxr hv

/-- **The clauses of a definition return conforming values.** -/
theorem tryClauses_ok (hF : SigFacts) {env : Env} (hX : env.memTyp "X" = false) {f : String}
    {ps : List Param} {t : Typ} {cls : List Clause} (hD : DefFacts f ps t cls) {ws : List ArgV}
    (hargs : ArgsVT sigX tsigFixed ws
      ((paramPTs ps).map (substPT (typParams ps) (fillV sigX ws)))) :
    ∀ (n : Nat) (cs : List Clause), (∀ c ∈ cs, c ∈ cls) →
      (∀ m < n, DefsVT sigX tsigFixed env m) → ∀ v,
      tryClauses n env cs ws = .ok v → vtB sigX (resV sigX tsigFixed f ws) v = true
  | 0, _, _, _, v, h => by simp [tryClauses] at h
  | n + 1, [], _, _, v, h => by simp [tryClauses] at h
  | n + 1, .defD qs args e prems :: cs, hcs, ih, v, h => by
    simp only [tryClauses] at h
    rcases elimUndef_eq_ok h with ⟨ρ₁, h₁, h₂⟩ | ⟨_, h₂⟩
    · simp only [Res.bind_eq_ok] at h₁
      obtain ⟨ρ₀, hm, hp⟩ := h₁
      exact clause_ok hF hX (fun m hm' => ih m (Nat.lt_succ_of_lt hm')) hD
        (hcs _ (List.mem_cons_self ..)) hargs hm hp h₂
    · exact tryClauses_ok hF hX hD hargs n cs (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
        (fun m hm' => ih m (Nat.lt_succ_of_lt hm')) v h₂

/-- **One step of the induction on fuel.** -/
theorem defsVT_of_lt (hF : SigFacts) {env : Env} (hE : EnvFacts env)
    (hB : BuiltinsVT sigX tsigFixed env) (n : Nat) (ih : ∀ m < n, DefsVT sigX tsigFixed env m) :
    DefsVT sigX tsigFixed env n := by
  intro f d pts ws v hd hp hargs hr
  rcases hr with hr | ⟨_, hb⟩
  · obtain ⟨⟨tps', pts'⟩, hl, hpe⟩ := Option.map_eq_some_iff.1 hp
    rcases hE.defs f d hd (by simp [hl]) with hnil | hD
    · rw [hnil] at hr
      cases n <;> simp [tryClauses] at hr
    · obtain ⟨h1, h2⟩ := tsig_params hD.tsig hl
      subst h1 h2
      simp only at hpe
      subst hpe
      exact tryClauses_ok hF hE.memX hD hargs n d.2.2 (fun c hc => hc) ih v hr
  · exact hB f pts ws v hp hargs hb

/-- **Definitions conform at every fuel**, in an environment with the static facts and conforming
primitives. -/
theorem defsVT_all (hF : SigFacts) {env : Env} (hE : EnvFacts env)
    (hB : BuiltinsVT sigX tsigFixed env) : ∀ n, DefsVT sigX tsigFixed env n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact defsVT_of_lt hF hE hB n ih

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
