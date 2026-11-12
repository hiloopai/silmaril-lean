module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxQuant.Typ3

/-!
# Round 7, REH route 2: values of a checked type conform, assembled (unrefined)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {m : Nat}

/-- **The environment's types pass `typVt`.** -/
def TypsVt (env : Env) : Prop :=
  ∀ x td, env.findTyp? x = some td → typVt sigX x td.1 td.2 = true

theorem noEntry {x : String} (h : hasEntry sigX x = false) :
    sigX.aliases.lookup x = none ∧ (∀ p ∈ sigX.fields, p.1 ≠ x) ∧ (∀ p ∈ sigX.cases, p.1 ≠ x) := by
  simp only [hasEntry, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at h
  obtain ⟨⟨ha, hf⟩, hc⟩ := h
  refine ⟨?_, hf, hc⟩
  cases hl : sigX.aliases.lookup x with
  | none => rfl
  | some a =>
    obtain ⟨p, hp, h1, _⟩ := lookup_entry hl
    exact absurd h1 (ha p hp)

set_option maxHeartbeats 800000 in
theorem vt_typ_succ (hE : EnvNx sigX.good env) (hT : TypsVt env) (ih : VtTyp env m)
    (ρ : VarEnv) (t : Typ) (v : Value) (hρ : TypsNx sigX.good ρ)
    (h : hasTyp (m + 1) env ρ t v = .ok true) : vtB sigX (toAT t) v = true := by
  cases hn : nxAT sigX.good (toAT t)
  · cases t with
    | boolT => simp [toAT, nxAT] at hn
    | numT _ => simp [toAT, nxAT] at hn
    | textT => simp [toAT, nxAT] at hn
    | tupT bs =>
      cases v <;> simp only [hasTyp, Value.asTuple?, Except.ok.injEq, Bool.false_eq_true] at h
      rename_i vs
      simp only [toAT] at hn ⊢
      rw [vtB_tup hn (unf_tup' bs)]
      exact ih.tup ρ bs vs hρ h
    | iterT t it =>
      simp only [toAT] at hn ⊢
      have hu : unf sigX (.iter (toAT t)) = .iter (toAT t) := by simp [unf, unalias]
      rw [vtB_iter hn hu]
      cases it with
      | opt =>
        cases v <;> simp only [hasTyp, Value.asOpt?, Except.ok.injEq, Bool.false_eq_true] at h
        rename_i o
        cases o with
        | none => rfl
        | some w => exact ih.typ ρ t w hρ h
      | list =>
        cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
        exact (vtL_iff _ _).2 (ih.list ρ t _ hρ h)
      | list1 =>
        cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true] at h
        split at h
        · cases h
        · exact (vtL_iff _ _).2 (ih.list ρ t _ hρ h)
      | listN e x =>
        cases v <;> simp only [hasTyp, Value.asList?, Except.ok.injEq, Bool.false_eq_true,
          Res.bind_eq_ok] at h
        obtain ⟨_, _, _, _, h⟩ := h
        split at h
        · exact (vtL_iff _ _).2 (ih.list ρ t _ hρ h)
        · cases h
    | varT x args =>
      simp only [hasTyp] at h
      split at h
      · rename_i t' hl
        have hf : ρ.findTyp? x = some t' := by
          cases args with
          | nil => simpa only [localTyp?] using hl
          | cons _ _ => simp [localTyp?] at hl
        have hnx := hρ (x, t') (Script.mem_of_find? hf)
        exact vtB_of_nxB' (nxB_of_HasTyp hE hρ hnx ⟨m, h⟩)
      · obtain ⟨td, htd, ws, hws, h'⟩ : ∃ td, env.findTyp? x = some td ∧ ∃ ws,
            evalArgs m env ρ args = .ok ws ∧ hasTypInsts m env td.2 ws v = .ok true := by
          simpa only [Res.bind_eq_ok, Res.ofOption_eq_ok] using h
        have hv := hT x td htd
        simp only [toAT] at hn ⊢
        cases he : hasEntry sigX x
        · obtain ⟨ha, hf, hc⟩ := noEntry he
          exact vtB_name_plain hn ha hf hc v
        · exact ih.insts x td.2 ws v _ (if_of_typVt hv he) h'
  · exact vtB_of_nxB' (nxB_of_HasTyp hE hρ hn ⟨m + 1, h⟩)
where
  unf_tup' (bs : List TypBind) : unf sigX (.tup (toATBinds bs)) = .tup (toATBinds bs) := by
    simp [unf, unalias]

theorem vtTyp_succ (hE : EnvNx sigX.good env) (hT : TypsVt env) (ih : VtTyp env m) :
    VtTyp env (m + 1) where
  typ := vt_typ_succ hE hT ih
  tup := vt_tup_succ ih
  list := fun ρ t vs hρ h => vt_list_succ ih ρ t vs hρ h
  defT := vt_defT_succ hE ih
  fields := fun x ρ fs gs hF hρ h => vt_fields_succ ih x ρ hρ fs gs hF h
  case := fun x ρ cs op w hC hρ h => vt_case_succ ih x ρ hρ cs op w hC h
  insts := vt_insts_succ ih

theorem vtTyp (hE : EnvNx sigX.good env) (hT : TypsVt env) : ∀ n, VtTyp env n
  | 0 => vtTyp_zero env
  | n + 1 => vtTyp_succ hE hT (vtTyp hE hT n)

/-- **A value of a checked type conforms to the type.** -/
theorem vtB_of_HasTyp (hE : EnvNx sigX.good env) (hT : TypsVt env) {ρ : VarEnv} {t : Typ}
    {v : Value} (hρ : TypsNx sigX.good ρ) (h : HasTyp env ρ t v) : vtB sigX (toAT t) v = true := by
  obtain ⟨n, hn⟩ := h
  exact (vtTyp hE hT n).typ ρ t v hρ hn

/-! ## The round-7 environment -/

mutual
theorem typVt_def : ∀ d : Def, typVtItem sigX d = true →
    ∀ p ∈ typsOfDef d, typVt sigX p.1 p.2.1 p.2.2 = true
  | .typD x ps insts, h, p, hp => by
    simp only [typVtItem] at h
    simp only [typsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact h
  | .recD ds, h, p, hp => by
    simp only [typVtItem] at h
    simp only [typsOfDef] at hp
    exact typVt_defs ds h p hp
  | .decD _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp
  | .relD _ _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, p, hp => by simp [typsOfDef, Map.empty] at hp

theorem typVt_defs : ∀ ds : List Def, typVtItems sigX ds = true →
    ∀ p ∈ typsOfDefs ds, typVt sigX p.1 p.2.1 p.2.2 = true
  | [], _, p, hp => by simp [typsOfDefs, Map.empty] at hp
  | d :: ds, h, p, hp => by
    simp only [typVtItems, Bool.and_eq_true] at h
    simp only [typsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact typVt_defs ds h.2 p hp
    · exact typVt_def d h.1 p hp
end

theorem typsVt_utf8Env (B : Builtins) : TypsVt (utf8Env B) := by
  intro x td h
  have he : (utf8Env B).findTyp? x = (simEnv B).findTyp? x := by
    simp only [utf8Env, utf8BaseEnv, simEnv, Env.findTyp?, Env.withBuiltins, Env.bindDef]
  have hm := TypAgree.mem_typs_of_findTyp (B := B) (he ▸ h)
  exact typVt_defs _ typVtItems_fixed (x, td) hm

/-- **A value of a checked type conforms, in the round-7 environment.** -/
theorem vtB_of_HasTyp_utf8Env {B : Builtins} {ρ : VarEnv} {t : Typ} {v : Value}
    (hρ : TypsNx sigX.good ρ) (h : HasTyp (utf8Env B) ρ t v) : vtB sigX (toAT t) v = true :=
  vtB_of_HasTyp (envNx_utf8Env B) (typsVt_utf8Env B) hρ h

/-- **Rule quantifiers conform**: under `Sim.QuantsOk` in `utf8Env B`, in a scope whose type
variables are export-free, every expression quantifier holds a value conforming to its declared
type. -/
theorem vtB_of_quantsOk {B : Builtins} {ρ : VarEnv} {qs : List Param}
    (hρ : TypsNx sigX.good ρ) (hq : Sim.QuantsOk (utf8Env B) ρ qs) {x : IL.Id} {t : Typ}
    (hx : Param.expP x t ∈ qs) : ∃ w, ρ.findVal? x = some w ∧ vtB sigX (toAT t) w = true := by
  obtain ⟨w, hw, hty⟩ := hq x t hx
  exact ⟨w, hw, vtB_of_HasTyp_utf8Env hρ hty⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
