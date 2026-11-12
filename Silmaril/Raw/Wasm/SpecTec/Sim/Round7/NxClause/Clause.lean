module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Prem
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxClause.Assemble

/-!
# Round 8, REH route 2: a clause, the clause list, every fuel, and `Task.clauseErase` (unrefined)

`clause_erase` follows `NxFlow.clause_ok`: matching the argument patterns (`matchArgs_erase`,
type-free), then the premises (`prems_erase`) and the body (`NxErase.nAt`) in the clause's scope,
which conforms by `NxFlow.entry_go` and whose calls are answered by `NxFlow.callH_clause` and
`callE_clause`. `defsE_all` is the induction on fuel; `clauseErase` instantiates it at
`utf8Env B`, from the kernel checks of rounds 6 and 7 and this round's `yItems_fixed`.
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
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT NCalls nAt clauseX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV nxB eraseA AllIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (ER ArgIn BIErase gdE grE xClause xPrems_mem)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

/-! ## Static facts -/

/-- **What the checks say about one `gdE` definition**: round 7's flow facts, the site check in
every mode (`NxErase.clauseX`), round 3's syntactic check, and this round's `clauseY`. -/
structure DefFactsE (f : String) (ps : List Param) (t : Typ) (cls : List Clause) : Prop where
  base : DefFacts f ps t cls
  x : ∀ b ∈ modes (typParams ps), ∀ c ∈ cls, clauseX (typParams ps) b c = true
  xc : ∀ c ∈ cls, xClause grE gdE c = true
  y : ∀ c ∈ cls, clauseY ps c = true

/-- **The facts about an environment** the erasure of clauses uses. -/
structure EnvFactsE (env : Env) : Prop where
  memX : env.memTyp "X" = false
  params : ∀ f d, gdE f = true → env.findDef? f = some d →
    (tsigFixed.params.lookup f).isSome = true
  defs : ∀ f d, gdE f = true → env.findDef? f = some d →
    d.2.2 = [] ∨ DefFactsE f d.1 d.2.1 d.2.2

theorem foldl_badPr_zero {S : Sig} {Γ : List (String × AT)} :
    ∀ (prems : List Prem) (a : Nat),
      prems.foldl (fun k pr => k + badPr S Γ pr) a = 0 → a = 0 ∧ ∀ pr ∈ prems, badPr S Γ pr = 0
  | [], a, h => ⟨h, fun _ h' => by cases h'⟩
  | pr :: prems, a, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h₁, h₂⟩ := foldl_badPr_zero prems _ h
    refine ⟨by omega, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · omega
    · exact h₂ q hq

/-- The arguments of export-free parameters are export-free. -/
theorem argsVT_get {S : Sig} {T : TSig} : ∀ (ws : List ArgV) (pts : List PT), ArgsVT S T ws pts →
    ∀ (i : Nat) (v : Value) (a : AT), ws[i]? = some (.val v) → pts[i]? = some (.exp a) →
      vtB S a v = true
  | [], [], _, _, _, _, h, _ => by simp at h
  | .val u :: ws, .exp b :: pts, h, i, v, a, hw, hp => by
    simp only [ArgsVT] at h
    cases i with
    | zero => simp at hw hp; subst hw hp; exact h.1
    | succ i => exact argsVT_get ws pts h.2 i v a (by simpa using hw) (by simpa using hp)
  | .defName _ :: ws, .defn _ _ :: pts, h, i, v, a, hw, hp => by
    simp only [ArgsVT] at h
    cases i with
    | zero => simp at hw
    | succ i => exact argsVT_get ws pts h.2 i v a (by simpa using hw) (by simpa using hp)
  | .typ _ :: ws, .other :: pts, h, i, v, a, hw, hp => by
    simp only [ArgsVT] at h
    cases i with
    | zero => simp at hw
    | succ i => exact argsVT_get ws pts h i v a (by simpa using hw) (by simpa using hp)
  | .gram _ :: ws, .other :: pts, h, i, v, a, hw, hp => by
    simp only [ArgsVT] at h
    cases i with
    | zero => simp at hw
    | succ i => exact argsVT_get ws pts h i v a (by simpa using hw) (by simpa using hp)
  | [], _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | _ :: _, [], h, _, _, _, _, _ => by cases ‹ArgV› <;> simp [ArgsVT] at h
  | .val _ :: _, .defn _ _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .val _ :: _, .other :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .defName _ :: _, .exp _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .defName _ :: _, .other :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .typ _ :: _, .exp _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .typ _ :: _, .defn _ _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .gram _ :: _, .exp _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h
  | .gram _ :: _, .defn _ _ :: _, h, _, _, _, _, _ => by simp [ArgsVT] at h

/-- **The export-free flags of the parameters hold of the arguments.** -/
theorem flags_ok {ps : List Param} {tps : List String} {b : AT}
    (htps : tps = [] ∨ tps = ["X"]) {ws : List ArgV}
    (h : ArgsVT sigX tsigFixed ws ((paramPTs ps).map (substPT tps b))) :
    ∀ (i : Nat) (v : Value), (ps.map nxP)[i]? = some true → ws[i]? = some (.val v) →
      nxB v = true := by
  intro i v hi hw
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨p, hp, hnx⟩ := hi
  cases p with
  | expP x t =>
    simp only [nxP, Bool.and_eq_true] at hnx
    have hpt : ((paramPTs ps).map (substPT tps b))[i]? = some (.exp (toAT t)) := by
      simp only [paramPTs, List.map_map, List.getElem?_map, hp, Option.map_some,
        Function.comp_apply, substPT]
      congr 2
      rcases htps with rfl | rfl
      · exact substTP_nil _ _
      · exact substTP_X_xFree hnx.2 b
    exact NxTyped.nxB_of_vtB hnx.1 (argsVT_get ws _ h i v _ hw hpt)
  | _ => simp [nxP] at hnx

/-! ## One clause -/

set_option maxHeartbeats 2000000 in
/-- **One clause commutes with erasure**, given what comes after it. -/
theorem clause_erase (hF : SigFacts) {env : Env} (hE : EnvFactsE env)
    (hBI : BIErase QT gdE env) (hDV : ∀ m, DefsVT sigX tsigFixed env m) {n : Nat}
    (ih : ∀ m < n, DefsE env m) {f : String} {ps : List Param} {t : Typ} {cls : List Clause}
    (hD : DefFactsE f ps t cls) {qs : List Param} {args : List Arg} {e : Exp}
    {prems : List Prem} (hc : Clause.defD qs args e prems ∈ cls) {ws : List ArgV}
    (hargs : ArgsVT sigX tsigFixed ws
      ((paramPTs ps).map (substPT (typParams ps) (fillV sigX ws))))
    (hw : ∀ w ∈ ws, ArgIn QT gdE w) {R R' : Res Value} (hR : ER eraseV (AllIn QT) R R') :
    ER eraseV (AllIn QT)
      (Res.elimUndef (matchArgs n env VarEnv.empty args ws >>= fun ρ₀ => premsHold n env ρ₀ prems)
        (fun ρ₁ => evalExp n env ρ₁ e) (fun _ => R))
      (Res.elimUndef
        (matchArgs n env VarEnv.empty args (ws.map eraseA) >>= fun ρ₀ => premsHold n env ρ₀ prems)
        (fun ρ₁ => evalExp n env ρ₁ e) (fun _ => R')) := by
  -- the static mode, as in `NxFlow.clause_ok`
  have htps := hD.base.tps
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
  obtain ⟨hdp, hpa, hpr, hty, -⟩ := clauseFlow_zero (hD.base.flow b hbm _ hc)
  obtain ⟨hal, hae, -, hdq, hgq⟩ := clauseAux_parts (hD.base.aux _ hc)
  have hdq' : typParams ps = [] ∨ defQuants qs = [] := by
    rcases hdq with h | h
    · exact .inl (List.isEmpty_iff.1 h)
    · exact .inr (List.isEmpty_iff.1 h)
  have hargs' : ArgsVT sigX tsigFixed ws ((paramPTs ps).map (substPT (typParams ps) b)) := by
    rw [hpts]; exact hargs
  have hgr : ∀ y c, (defQuants qs).lookup y = some c → tsigFixed.gres.lookup y = none :=
    fun y c hl => (hgq _ (mem_of_lookup hl)).1
  -- the site check, round 3's check and this round's check on the clause
  have hcx := hD.x b hbm _ hc
  simp only [clauseX, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcx
  obtain ⟨⟨⟨hsite, -⟩, hXe⟩, hXp⟩ := hcx
  rw [Nat.add_eq_zero_iff, Nat.add_eq_zero_iff] at hsite
  obtain ⟨⟨-, hbe⟩, hbp⟩ := hsite
  have hbp' := (foldl_badPr_zero prems 0 hbp).2
  have hxc := hD.xc _ hc
  simp only [xClause, Bool.and_eq_true] at hxc
  obtain ⟨⟨-, hxe⟩, hxp⟩ := hxc
  have hyc := hD.y _ hc
  simp only [clauseY, Bool.and_eq_true, List.all_eq_true] at hyc
  obtain ⟨hlin, hpy⟩ := hyc
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.1 hlin
  -- matching, type-free
  have hM := matchArgs_erase (gd := gdE) env n VarEnv.empty args ws (ps.map nxP) ([], []) st'
    inv_empty (flags_ok htps hargs') hw hst'
  rw [EraseAll.eraseScope_empty] at hM
  -- the predicate after the premises
  let S' := clauseSig sigX (typParams ps) b qs
  let T' := clauseTSig tsigFixed (typParams ps) b qs
  let Γ' := (quantsΓ qs).map fun p => (p.1, substTP (typParams ps) b p.2)
  let c' : AuxCtx := (typParams ps, (defQuants qs).map (·.1))
  let P' : VarEnv → Prop := fun ρ => ScopeVT S' Γ' ρ ∧ NCalls gdE S' T' c' env ρ n
  have hin : ER eraseScope P'
      (matchArgs n env VarEnv.empty args ws >>= fun ρ₀ => premsHold n env ρ₀ prems)
      (matchArgs n env VarEnv.empty args (ws.map eraseA) >>= fun ρ₀ => premsHold n env ρ₀ prems) := by
    refine ER.bind hM fun ρ₀ hm hinv => ?_
    -- entering the clause, as in `NxFlow.clause_ok`
    obtain ⟨hent, -, hda, -, hta⟩ := entry_go (W := ws) hF hE.memX htps hbx hdq'
      n args ws ps VarEnv.empty ρ₀ hal hpa hargs' (fun w hw => hw) hD.base.noGram
      (fun y hy => typParams_of_typP hy) (EntryInv.empty _ _ _ _ _) hm
    have hctx : ClauseCtx ρ₀ qs (typParams ps) b := {
      defs := hent.defs
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
        obtain ⟨hxt, htw⟩ := hent.typs x t hx
        refine ⟨hxt, ?_⟩
        rcases htps with h | h
        · rw [h] at hxt; cases hxt
        · have hle := typsOf_le ws ps hD.base.noGram hargs'
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
    have hNC : NCalls gdE S' T' c' env ρ₀ n :=
      ⟨callH_clause hF (fun m _ => hDV m) htps hb hdq' hgr hctx,
        callE_clause hF hE.params ih htps hb hdq' hctx, hinv.defs⟩
    refine ER.weaken (prems_erase (gr := grE) hBI hent.scope hNC prems fun pr hm =>
      ⟨hpy pr hm, hpr pr hm, hbp' pr hm, hXp pr hm, xPrems_mem hxp pr hm⟩)
      fun ρ₁ h => ?_
    subst h
    exact ⟨hent.scope, hNC⟩
  refine ER.elimUndef hin (fun ρ₁ _ hP => ?_) fun _ => hR
  exact (nAt (gr := grE) hBI n).exp S' T' Γ' c' ρ₁ e hP.1 hP.2 hty hae hXe hbe hxe

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
