module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.XFree
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSound.Defs

/-!
# Round 7, REH route 2: calls inside a clause conform (unrefined)

`callH_clause`: inside a clause whose scope satisfies `ClauseCtx` (definition parameters bound to
definitions that may stand for them, the type parameter bound to a type that is export-free
exactly in the export-free mode), every call the flow check passes returns a conforming value,
given `NxSound.DefsVT` below the current fuel. The call's mode, read on the evaluated type
arguments, is the mode the flow check read on the syntactic ones (`tpFill_eq`).
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

/-- **The runtime invariant of a clause's scope.** -/
structure ClauseCtx (ρ : VarEnv) (qs : List Param) (tps : List String) (b : AT) : Prop where
  defs : ∀ y g', ρ.findDef? y = some g' → ∃ dps r, (defQuants qs).lookup y = some (dps, r) ∧
    defSub sigX tsigFixed g' dps r = true
  defsIn : ∀ y, ((defQuants qs).lookup y).isSome = true → (ρ.findDef? y).isSome = true
  typs : ∀ x t, ρ.findTyp? x = some t → x ∈ tps ∧
    nxAT sigX.good (toAT t) = (match b with | .base => true | _ => false)
  typsIn : ∀ x ∈ tps, (ρ.findTyp? x).isSome = true

theorem ClauseCtx.congr {ρ ρ' : VarEnv} {qs : List Param} {tps : List String} {b : AT}
    (h : ClauseCtx ρ qs tps b) (hd : ρ'.defs = ρ.defs) (ht : ρ'.typs = ρ.typs) :
    ClauseCtx ρ' qs tps b where
  defs := fun y g' hy => h.defs y g' (by simpa [VarEnv.findDef?, hd] using hy)
  defsIn := fun y hy => by simpa [VarEnv.findDef?, hd] using h.defsIn y hy
  typs := fun x t hx => h.typs x t (by simpa [VarEnv.findTyp?, ht] using hx)
  typsIn := fun x hx => by simpa [VarEnv.findTyp?, ht] using h.typsIn x hx

/-! ## Lookups -/

theorem lookup_map {β γ : Type} (F : String × β → γ) : ∀ (l : List (String × β)) (x : String),
    (l.map fun p => (p.1, F p)).lookup x = (l.lookup x).map fun c => F (x, c)
  | [], _ => rfl
  | (y, c) :: l, x => by
    simp only [List.map_cons, List.lookup]
    split
    · rename_i h
      have : x = y := beq_iff_eq.1 h
      subst this
      rfl
    · exact lookup_map F l x

theorem lookup_mem_names {β : Type} {l : List (String × β)} {x : String} {c : β}
    (h : l.lookup x = some c) : x ∈ l.map (·.1) := by
  have := mem_of_lookup h
  exact List.mem_map.2 ⟨_, this, rfl⟩

theorem lookup_none_of_not_mem {β : Type} {l : List (String × β)} {x : String}
    (h : x ∉ l.map (·.1)) : l.lookup x = none := by
  cases hl : l.lookup x with
  | none => rfl
  | some c => exact absurd (lookup_mem_names hl) h

/-! ## Facts from `sigsAux` -/

structure SigFacts : Prop where
  goodX : sigX.good.contains "X" = true
  aliases : (sigX.aliases.all fun p => xFree p.2) = true
  fields : (sigX.fields.all fun p => xFree p.2.2) = true
  cases : (sigX.cases.all fun p => xFree p.2.2) = true
  results : (sigX.results.all fun p => xFree p.2) = true
  params : (tsigFixed.params.all fun p => reach 1 p.1 &&
    (p.2.1.contains "X" || p.2.2.all xFreePT)) = true
  gres : (tsigFixed.gres.all fun p => p.2.1 == ["X"] && (sigX.results.lookup p.1).isNone &&
    (tsigFixed.params.lookup p.1).map (·.1) == some p.2.1) = true

theorem sigFacts (h : sigsAux sigX tsigFixed = true) : SigFacts := by
  simp only [sigsAux, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hX, ha⟩, hf⟩, hc⟩, hr⟩, hp⟩, hg⟩ := h
  exact ⟨hX, ha, hf, hc, hr, hp, hg⟩

theorem SigFacts.gres_lookup (h : SigFacts) {f : String} {tps : List String} {r : AT}
    (hg : tsigFixed.gres.lookup f = some (tps, r)) :
    tps = ["X"] ∧ sigX.results.lookup f = none ∧
      (tsigFixed.params.lookup f).map (·.1) = some ["X"] := by
  have hm := mem_of_lookup hg
  have := (List.all_eq_true.1 h.gres) _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  subst h1
  exact ⟨rfl, h2, h3⟩

theorem SigFacts.results_xFree (h : SigFacts) (f : String) :
    xFree ((sigX.results.lookup f).getD .unk) = true := by
  cases hl : sigX.results.lookup f with
  | none => rfl
  | some a => exact (List.all_eq_true.1 h.results) _ (mem_of_lookup hl)

theorem SigFacts.params_xFree (h : SigFacts) {f : String} {tps : List String} {ps : List PT}
    (hl : tsigFixed.params.lookup f = some (tps, ps)) :
    tps.contains "X" = true ∨ ∀ p ∈ ps, xFreePT p = true := by
  have := (List.all_eq_true.1 h.params) _ (mem_of_lookup hl)
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at this
  exact this.2

theorem fill_xFree (S : Sig) (ws : List ArgV) : xFree (fillV S ws) = true := by
  unfold fillV; split <;> rfl

theorem tpFill_xFree (S : Sig) (xs : List Arg) : xFree (tpFill S xs) = true := by
  unfold tpFill; split <;> rfl

theorem xFree_substPT {tps : List String} {b : AT} (hb : xFree b = true)
    (_hX : tps.contains "X" = true ∨ True) : ∀ p : PT, (tps.contains "X" = true ∨ xFreePT p = true) →
    ∀ a, substPT tps b p = .exp a → xFree a = true := by
  intro p hp a ha
  cases p with
  | exp c =>
    simp only [substPT, PT.exp.injEq] at ha
    subst ha
    rcases hp with hp | hp
    · exact xFree_substTP_X hp hb c
    · exact xFree_substTP hb hp
  | defn _ _ => simp [substPT] at ha
  | other => simp [substPT] at ha

/-! ## The mode of a call -/

theorem resolveTyp_of_ne {ρ : VarEnv} {t : Typ} (h : ∀ x, t ≠ .varT x []) :
    resolveTyp ρ t = t := by
  unfold Silmaril.SpecTec.Sem.resolveTyp
  split
  · rename_i x; exact absurd rfl (h x)
  · rfl

theorem clauseSig_contains {tps : List String} {b : AT} {qs : List Param} {n : String}
    (hn : n ∉ tps) : (clauseSig sigX tps b qs).good.contains n = sigX.good.contains n := by
  simp only [clauseSig]
  split
  · simp [List.mem_filter, hn]
  · rfl

/-- One type argument has the same export-freedom statically and at runtime. -/
theorem nx_typArg (hF : SigFacts) {ρ : VarEnv} {qs : List Param} {tps : List String} {b : AT}
    (hctx : ClauseCtx ρ qs tps b) (htps : tps = [] ∨ tps = ["X"])
    (hb : tps = [] ∨ b = .unk ∨ b = .base) {t : Typ} (ht : typArgOk tps t = true) :
    nxAT (clauseSig sigX tps b qs).good (toAT t) = nxAT sigX.good (toAT (resolveTyp ρ t)) := by
  by_cases hv : ∃ x, t = .varT x []
  · obtain ⟨x, rfl⟩ := hv
    simp only [Silmaril.SpecTec.Sem.resolveTyp]
    cases hx : ρ.findTyp? x with
    | some t₀ =>
      obtain ⟨hxt, hnx⟩ := hctx.typs x t₀ hx
      simp only [Option.getD_some, hnx]
      rcases htps with rfl | rfl
      · cases hxt
      · simp only [List.mem_singleton] at hxt
        subst hxt
        simp only [toAT, toATArgs, nxAT, nxATs, Bool.and_true]
        rcases hb with h | h | h
        · cases h
        · subst h; simp [clauseSig]
        · subst h; simpa [clauseSig, List.contains_iff_mem] using hF.goodX
    | none =>
      simp only [Option.getD_none]
      have hxn : x ∉ tps := fun hm => by
        have := hctx.typsIn x hm
        rw [hx] at this; cases this
      simp only [toAT, toATArgs, nxAT, nxATs, Bool.and_true]
      exact clauseSig_contains hxn
  · have hne : ∀ x, t ≠ .varT x [] := fun x h => hv ⟨x, h⟩
    rw [resolveTyp_of_ne hne]
    refine nxAT_agree _ fun n hn => ?_
    have hnt : n ∉ tps := by
      have : typArgOk tps t = (atNames (toAT t)).all fun n => !tps.contains n := by
        unfold typArgOk
        split
        · rename_i x; exact absurd rfl (hne x)
        · rfl
      rw [this, List.all_eq_true] at ht
      have := ht n hn
      simpa [List.contains_iff_mem] using this
    exact clauseSig_contains hnt

/-- **The mode of a call is the same statically and at runtime.** -/
theorem tyArgsNx_eq (hF : SigFacts) {ρ : VarEnv} {qs : List Param} {tps : List String} {b : AT}
    (hctx : ClauseCtx ρ qs tps b) (htps : tps = [] ∨ tps = ["X"])
    (hb : tps = [] ∨ b = .unk ∨ b = .base) {S' : Sig} (hS' : S' = clauseSig sigX tps b qs)
    {T' : TSig} {dq : List String} :
    ∀ (xs : List Arg) (ws : List ArgV) (ps : List PT), ArgsR S' T' ρ xs ws ps →
      typArgsOk (tps, dq) xs = true → tyArgsNx S' xs = tyArgsNxV sigX ws
  | [], [], [], _, _ => rfl
  | .expA _ :: xs, .val _ :: ws, .exp _ :: ps, ⟨_, h⟩, ht => by
    simp only [typArgsOk, List.all_cons, Bool.true_and] at ht
    simp only [tyArgsNx, tyArgsNxV, List.all_cons, Bool.true_and]
    exact tyArgsNx_eq hF hctx htps hb hS' xs ws ps h ht
  | .defA _ :: xs, .defName _ :: ws, .defn _ _ :: ps, ⟨_, _, h⟩, ht => by
    simp only [typArgsOk, List.all_cons, Bool.and_eq_true] at ht
    simp only [tyArgsNx, tyArgsNxV, List.all_cons, Bool.true_and]
    exact tyArgsNx_eq hF hctx htps hb hS' xs ws ps h ht.2
  | .typA t :: xs, .typ t' :: ws, .other :: ps, ⟨ht', h⟩, ht => by
    simp only [typArgsOk, List.all_cons, Bool.and_eq_true] at ht
    simp only [tyArgsNx, tyArgsNxV, List.all_cons]
    subst ht' hS'
    rw [nx_typArg hF hctx htps hb ht.1]
    exact congrArg _ (tyArgsNx_eq hF hctx htps hb rfl xs ws ps h ht.2)
  | .gramA _ :: xs, .gram _ :: ws, .other :: ps, h, ht => by
    simp only [typArgsOk, List.all_cons, Bool.true_and] at ht
    simp only [tyArgsNx, tyArgsNxV, List.all_cons, Bool.true_and]
    exact tyArgsNx_eq hF hctx htps hb hS' xs ws ps h ht

theorem tpFill_eq (hF : SigFacts) {ρ : VarEnv} {qs : List Param} {tps : List String} {b : AT}
    (hctx : ClauseCtx ρ qs tps b) (htps : tps = [] ∨ tps = ["X"])
    (hb : tps = [] ∨ b = .unk ∨ b = .base) {T' : TSig} {dq : List String} {xs : List Arg}
    {ws : List ArgV} {ps : List PT} (h : ArgsR (clauseSig sigX tps b qs) T' ρ xs ws ps)
    (ht : typArgsOk (tps, dq) xs = true) :
    tpFill (clauseSig sigX tps b qs) xs = fillV sigX ws := by
  simp only [tpFill, fillV, tyArgsNx_eq hF hctx htps hb rfl xs ws ps h ht]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
