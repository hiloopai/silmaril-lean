module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessExp10

/-!
# In the 1.0 script, the only `name` is the empty one

Round 6 observed that the kernel typing check of an invocation image fails at fuel
2000 when the instantiated module exports a function under `"a"` or `"add"`, with an error
result rather than `false`, and used the empty export name to avoid it. This file proves the
cause, which is the 1.0 form 's 2.0 `$utf8` gap (`Sim20.Utf8Mono.typedV_name20_iff`).

* The 1.0 `$utf8` (`utf8Clauses10`) has the parameters, result type and last clause of the 2.0
  one; its four one-character clauses also bind a byte variable only in their premise
  (`utf8Clauses10_bad`, checked by evaluation). So round 6's generic lemmas apply: on a
  non-empty list the clauses are out of fuel **at every fuel** (`tryClauses_utf8_ne10`).
* `name`'s premise `|$utf8(char*)| < 2^32` then has no value (`not_evalExp_namePrem_ne10`), so
  **a non-empty string is not a `name`** (`not_hasTyp_name_ne10`). `typedV_name10_iff`: in
  `simEnv10 B` and `simEnv10T B`, a string is a `name` exactly when it is empty.
* Up the store: a module instance exporting a non-empty name is not a `moduleinst`
  (`not_typedV_moduleInst10_ne`), a defined function instance whose module does so is not a
  `funcinst` (`not_typed_funcInst10_ne`), and **no configuration over a store holding one is
  `Typed10`** (`not_typed10_export_ne`, `not_typed10T_export_ne`).
* The observed failure: `addModule` (export `"add"`) instantiated into the empty store, and the
  invocation of its function, is not typed (`not_typed10_add`). The checker's answer at fuel
  2000 is an out-of-fuel error because the evaluation of `$utf8` never terminates on a
  non-empty list; it is not a gap of the fuel bound.

The repair is an erratum on `$utf8`, as in 2.0 (`Sim20.StoreBulk.utf8Env20`): bind it to the
primitive. It is not stated here for 1.0.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Name10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef)
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics prepare? Instantiation)
open Silmaril.Wasm.Execution.Runtime (ModuleInst ExportInst FuncInst Frame)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT)
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (utf8Clause1)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res clausePats)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (badClause BadShape badClause_spec tryClauses_badL
  utf8_small20 utf8_step20)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (ChPat tryClauses_peelCh tryClauses_last_cons)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

set_option maxRecDepth 100000

/-! ## `$utf8` in the 1.0 script -/

/-- The clauses of `$utf8` in the 1.0 script. -/
noncomputable def utf8Clauses10 : List Clause :=
  ((baseEnv10.findDef? "utf8").map (·.2.2)).getD []

set_option maxRecDepth 8000000 in
theorem findDef_utf8_10 (B : Builtins) :
    (simEnv10 B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10) := rfl

set_option maxRecDepth 8000000 in
theorem findDef_utf8_10T (B : Builtins) :
    (simEnv10T B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10) := rfl

set_option maxRecDepth 8000000 in
/-- The last clause is round 5's `utf8Clause1`, as in 2.0. -/
theorem utf8Clauses10_split : utf8Clauses10 = utf8Clauses10.take 4 ++ [utf8Clause1] := rfl

set_option maxRecDepth 8000000 in
/-- The first four never apply on a one-element list (checked by evaluation of `badClause`). -/
theorem utf8Clauses10_bad : (utf8Clauses10.take 4).all badClause = true := rfl

theorem utf8Clauses10_badShape : ∀ c ∈ utf8Clauses10.take 4, BadShape c := fun c hc =>
  badClause_spec c (List.all_eq_true.1 utf8Clauses10_bad c hc)

set_option maxRecDepth 8000000 in
theorem chPat_take4_10 : ∀ c ∈ utf8Clauses10.take 4, ChPat c := by
  have h : (utf8Clauses10.take 4).map clausePats =
      List.replicate 4 [.expA (.listE [.varE "ch"])] := rfl
  intro c hc
  exact List.eq_of_mem_replicate (h ▸ List.mem_map_of_mem hc)

variable {env : Env}

/-- **`$utf8` on a one-element list never returns**, in every environment with the 1.0 clauses. -/
theorem tryClauses_utf8_single10
    (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10)) (u : Value) :
    ∀ n, tryClauses n env utf8Clauses10 [.val (.list [u])] = .error .outOfFuel := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [utf8Clauses10_split]
    rcases tryClauses_badL (env := env) u [utf8Clause1] _ utf8Clauses10_badShape n
      with h | ⟨m, hm, h⟩
    · exact h
    · rw [h]
      have hl : (utf8Clauses10.take 4).length = 4 := rfl
      by_cases hs : m < 12
      · exact utf8_small20 m hs u [] hd
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 12 := ⟨m - 12, by omega⟩
        exact utf8_step20 j u [] hd (ih (j + 1) (by omega))

/-- On a list of two or more characters the 1.0 clauses are out of fuel. -/
theorem tryClauses_utf8_long10
    (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10))
    (u u' : Value) (us : List Value) (n : Nat) :
    tryClauses n env utf8Clauses10 [.val (.list (u :: u' :: us))] = .error .outOfFuel := by
  rw [utf8Clauses10_split]
  rcases tryClauses_peelCh (env := env) (u :: u' :: us) (by simp) [utf8Clause1] _ chPat_take4_10 n
    with h' | ⟨m, -, h'⟩
  · exact h'
  · rw [h']
    exact tryClauses_last_cons u (u' :: us) hd (tryClauses_utf8_single10 hd u) m

/-- **`$utf8`'s 1.0 clauses are out of fuel on every non-empty list, at every fuel.** -/
theorem tryClauses_utf8_ne10
    (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10)) {L : List Value}
    (hL : L ≠ []) (n : Nat) :
    tryClauses n env utf8Clauses10 [.val (.list L)] = .error .outOfFuel := by
  rcases L with _ | ⟨u, _ | ⟨u', us⟩⟩
  · exact absurd rfl hL
  · exact tryClauses_utf8_single10 hd u n
  · exact tryClauses_utf8_long10 hd u u' us n

/-! ## `name` -/

/-- An environment with the 1.0 `$utf8` and the 1.0 `name`. -/
structure NameEnv10 (env : Env) : Prop where
  utf8 : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10)
  name : env.findTyp? "name" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "char*" (.iterT (.varT "char" []) .list)]) []
      [.ifPr Sim.Round5.Pos.namePrem]])])

set_option maxRecDepth 8000000 in
theorem nameEnv10 (B : Builtins) : NameEnv10 (simEnv10 B) := ⟨findDef_utf8_10 B, rfl⟩

set_option maxRecDepth 8000000 in
theorem nameEnv10T (B : Builtins) : NameEnv10 (simEnv10T B) := ⟨findDef_utf8_10T B, rfl⟩

/-- **`name`'s premise has no value on a non-empty list.** -/
theorem not_evalExp_namePrem_ne10 (hE : NameEnv10 env) {L : List Value} (hL : L ≠ [])
    (v : Value) :
    ¬ EvalExp env (VarEnv.empty.bindVal "char*" (.list L)) Sim.Round5.Pos.namePrem v := by
  intro h
  obtain ⟨v₁, -, h₁, -, -⟩ := evalExp_cmpE_iff.1 h
  obtain ⟨vs, h₂, -⟩ := evalExp_lenE_iff.1 h₁
  have ha : EvalArgs env (VarEnv.empty.bindVal "char*" (.list L))
      [.expA (.iterE (.varE "char") Sim.Round5.Pos.charDom)] [.val (.list L)] :=
    evalArgs_cons (Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide)
      (by simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, Map.bind])) evalArgs_nil
  have hA := (applies_iff_callDef (by rfl) ha).2 (evalExp_callE_iff.1 h₂)
  obtain ⟨ps, t, cs, hf, hT⟩ := hA
  have hcs : cs = utf8Clauses10 := by
    have h' := hf.symm.trans hE.utf8
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    exact h'.2.2
  subst hcs
  rcases hT with ⟨n, hn⟩ | ⟨⟨n, hn⟩, -⟩ <;> simp [tryClauses_utf8_ne10 hE.utf8 hL n] at hn

/-- **A non-empty string is not a `name`**, in any term-only scope. -/
theorem not_hasTyp_name_ne10 (hE : NameEnv10 env) {ρ : VarEnv} (hρ : ValsOnly ρ)
    {L : List Value} (hL : L ≠ []) :
    ¬ HasTyp env ρ (.varT "name" []) (.case "%" (.tuple [.list L])) := by
  intro h
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [hE.name] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    obtain ⟨-, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    exact not_evalExp_namePrem_ne10 hE hL _ (Sim.ConfigOk.evalExp_of_premsOk_if hp)
  · exact absurd hrest not_hasTypInsts_nil

/-- A non-empty string's image is not a `name`. -/
theorem not_hasTyp_nameV_ne10 (hE : NameEnv10 env) {s : String} (hs : s ≠ "") :
    ¬ HasTyp env VarEnv.empty (.varT "name" []) (Sim20.nameV s) := by
  have hL : s.toList.map (fun c => Silmaril.SpecTec.Equiv.Execution.pctV c.toNat) ≠ [] := by
    simpa using hs
  simpa [Sim20.nameV] using not_hasTyp_name_ne10 hE (ρ := VarEnv.empty) ⟨rfl, rfl, rfl⟩ hL

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
theorem typedV_name_nil10 (B : Builtins) : TypedV (simEnv10 B) (.varT "name" []) (Sim20.nameV "") :=
  Sim20.Whole.typedV_of_empty20 ⟨100, by with_unfolding_all rfl⟩

/-- **In `simEnv10 B`, a string is a `name` exactly when it is empty.** -/
theorem typedV_name10_iff (B : Builtins) (s : String) :
    TypedV (simEnv10 B) (.varT "name" []) (Sim20.nameV s) ↔ s = "" := by
  constructor
  · intro h
    by_contra hs
    exact not_hasTyp_nameV_ne10 (nameEnv10 B) hs (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  · rintro rfl
    exact typedV_name_nil10 B

end Silmaril.Wasm.SpecTec.Sim10.Name10
