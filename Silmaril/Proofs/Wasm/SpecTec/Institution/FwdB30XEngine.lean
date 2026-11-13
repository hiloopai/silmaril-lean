module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XTables
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms

/-!
# Inverting `Step` at a short flat redex, at every evaluator

Whatever the primitives, a `Step` fact from `z; l`, where `l` is `k` values followed by one
instruction named `t` (`FlatK k t l`), comes from `Step/pure` at the whole of `l` when
`pureOk k t` holds, and from `Step/read` at the whole of `l` when `readOk k t` holds.

The argument reads left-hand sides only. `Step` rules 0–2 (`pure`, `read`, `ctxt-instrs`) are
inverted (`Bwd.inv_*`); every other rule of `Step`, `Step_pure` and `Step_read` is refuted by its
row of `pureInfoT`, `readInfoT`, `stepInfoT`: it forces a constructor the code avoids
(`RefsGC.not_ruleBody_of_tags`) or a code of another length (`ruleLen_sound`). `ctxt-instrs`
moves to a proper infix, on which nothing fires (`not_sstep`, by recursion on the length).

* `ruleLen_sound`, `not_fires_of_blk`: the length half of the refutation, and the two halves
  against a table.
* `Tables env`, `tables_simEnv`: the relations and their tables, in every `simEnv B`.
* `not_sstep`, `spure_of_sstep`, `sread_of_sstep`: the inversion, from inertness of the infixes.
* `spure_of_sstep_flat`, `sread_of_sstep_flat`: the same from the checks `pureOk`, `readOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn LhsIn relRules not_ruleBody_of_tags code_of_cfg)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read inv_ctxtInstrs cfgV_inj findRel_of_ruleAt)

variable {env : Env}

/-! ## Forced lengths are sound -/

/-- A list of expressions denotes a list of the same length. -/
theorem evalExps_length {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → vs.length = es.length
  | [], _, h => by rw [evalExps_nil_iff.1 h]; rfl
  | _ :: _, _, h => by
      obtain ⟨w, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 h
      simp [evalExps_length hws]

/-- A list literal of forced length `m` denotes a list of length `m`. -/
theorem lenOf_eval {ρ : VarEnv} {e : Exp} {v : Value} {m : Nat} (hm : lenOf e = some m)
    (he : EvalExp env ρ e v) : ∃ k, v = .list k ∧ k.length = m := by
  cases e with
  | listE es =>
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 he
    simp only [lenOf, Option.some.injEq] at hm
    exact ⟨vs, rfl, by rw [evalExps_length hvs, hm]⟩
  | _ => simp [lenOf] at hm

/-- A left-hand side whose code has its constructors in `S` and length `n`: `instr*` (for
`Step_pure`) or `z; instr*` (for `Step_read` and `Step`). -/
def LhsIs (S : List MixopS) (n : Nat) (a : Value) : Prop :=
  (∃ l, a = .list l ∧ TagsIn S l ∧ l.length = n) ∨
    (∃ z l, a = cfgV z l ∧ TagsIn S l ∧ l.length = n)

theorem LhsIs.lhsIn {S : List MixopS} {n : Nat} {a : Value} (h : LhsIs S n a) : LhsIn S a :=
  h.imp (fun ⟨l, ha, hl, _⟩ => ⟨l, ha, hl⟩) fun ⟨z, l, ha, hl, _⟩ => ⟨z, l, ha, hl⟩

/-- The code of a left-hand side with forced length `m` has length `m`. -/
theorem codeLen_sound {ρ : VarEnv} {l : Exp} {a : Value} {S : List MixopS} {n m : Nat}
    (ha : LhsIs S n a) (hm : codeLen l = some m) (he : EvalExp env ρ l a) : m = n := by
  unfold codeLen at hm
  split at hm
  · obtain ⟨u, w, hc, rfl⟩ := code_of_cfg he
    obtain ⟨k', rfl, hlen'⟩ := lenOf_eval hm hc
    rcases ha with ⟨k, hk, -⟩ | ⟨z', k, hk, -, hlen⟩
    · cases hk
    · have hw : Value.list k' = .list k := by
        simp only [cfgV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at hk
        exact hk.2.2.1
      rw [← hlen', Value.list.inj hw, hlen]
  · obtain ⟨k', rfl, hlen'⟩ := lenOf_eval hm he
    rcases ha with ⟨k, hk, -, hlen⟩ | ⟨z', k, hk, -, -⟩
    · rw [← hlen', Value.list.inj hk, hlen]
    · simp [cfgV] at hk

/-- **Forced lengths are sound**: a rule whose left-hand side forces a code of length `m` fires
only on code of length `m`. -/
theorem ruleLen_sound {D : Interp} {els : Prop} {ps : List Param} {args : List ArgV}
    {opx : MixopS} {r : Rule} {S : List MixopS} {n m : Nat} {a c : Value} (ha : LhsIs S n a)
    (hm : ruleLen r = some m) (hb : RuleBody env D els ps args opx r (.tuple [a, c])) : m = n := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  simp only [ruleLen] at hm
  unfold concLen at hm
  split at hm
  · obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 he
    obtain ⟨u₁, ws, hl, -, rfl⟩ := evalExps_cons_iff.1 hvs
    simp only [Value.tuple.injEq, List.cons.injEq] at hv
    rw [← hv.1] at hl
    exact codeLen_sound ha hm hl
  · simp at hm

/-! ## Refuting a rule by its row -/

/-- A row refutes a left-hand side with constructors in `S` and code length `n`: it forces a
constructor outside `S`, or another length. -/
def Blk (S : List MixopS) (n : Nat) (row : List MixopS × Option Nat) : Prop :=
  (∃ op ∈ row.1, op ∉ S) ∨ ∃ m, row.2 = some m ∧ m ≠ n

/-- A rule whose row refutes the left-hand side does not fire there. -/
theorem not_ruleBody_of_blk {D : Interp} {els : Prop} {ps : List Param} {args : List ArgV}
    {opx : MixopS} {r : Rule} {S : List MixopS} {n : Nat} {a c : Value} (ha : LhsIs S n a)
    (hb : Blk S n (ruleInfo r)) : ¬ RuleBody env D els ps args opx r (.tuple [a, c]) := by
  intro hr
  rcases hb with ⟨op, hop, hS⟩ | ⟨m, hm, hne⟩
  · exact not_ruleBody_of_tags ha.lhsIn hop hS hr
  · exact hne (ruleLen_sound ha hm hr)

/-- **A rule `i ≥ d` of `x` does not fire** at a left-hand side that every row of the table from
`d` on refutes. -/
theorem not_fires_of_blk {x : IL.Id} {T : List (List MixopS × Option Nat)}
    (hT : (relRules env x).map ruleInfo = T) {d i : Nat} (hi : d ≤ i) {a c : Value}
    (hb : ∀ row ∈ T.drop d, ∃ S n, LhsIs S n a ∧ Blk S n row) :
    ¬ Fires env x i (.tuple [a, c]) := by
  rintro ⟨t, rules, r, hrel, hr, hbody⟩
  have hrr : relRules env x = rules := by simp only [relRules, hrel]
  have hget : (T.drop d)[i - d]? = some (ruleInfo r) := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hi, ← hT, hrr, List.getElem?_map, hr]
    rfl
  obtain ⟨S, n, ha, hblk⟩ := hb _ (List.mem_of_getElem? hget)
  exact not_ruleBody_of_blk ha hblk hbody

/-! ## The relations and their tables -/

/-- The three relations of the wasm-3.0 script and their `ruleInfo` tables, with the structural
rules of `Step`. -/
structure Tables (env : Env) : Prop where
  rules : HasStepRules env
  pure : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules)
  read : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)
  step : ∃ t rules, env.findRel? "Step" = some ([], "%~>%", t, rules)
  pureT : (relRules env "Step_pure").map ruleInfo = pureInfoT
  readT : (relRules env "Step_read").map ruleInfo = readInfoT
  stepT : (relRules env "Step").map ruleInfo = stepInfoT

/-- **The tables hold in every `simEnv B`.** -/
theorem tables_simEnv (B : Builtins) : Tables (simEnv B) where
  rules := hasStepRules_simEnv B
  pure := findRel_of_ruleAt
    (hasRuleAt_simEnv B Equiv.ExecPureArrayNew.hasArrayNew_wasm30)
  read := Round6.Reading.findRel_read B
  step := findRel_of_ruleAt (hasStepRules_simEnv B).pure
  pureT := (infoT_simEnv B).1
  readT := (infoT_simEnv B).2.1
  stepT := (infoT_simEnv B).2.2

/-! ## The inversion -/

/-- Nothing fires on `M`: no rule of `Step_pure` at `M`, no rule of `Step_read` at `z; M`, and
no rule of `Step` beyond the first three at `z; M`. -/
def Inert (env : Env) (M : List Value) : Prop :=
  (∀ i v, ¬ Fires env "Step_pure" i (.tuple [.list M, v])) ∧
    (∀ i z v, ¬ Fires env "Step_read" i (.tuple [cfgV z M, v])) ∧
    ∀ i z v, 3 ≤ i → ¬ Fires env "Step" i (.tuple [cfgV z M, v])

/-- **No step from inert code**: if nothing fires on any infix of `l`, then `z; l` takes no
`Step`. The recursion is on the length of `l`: `ctxt-instrs` steps a proper infix. -/
theorem not_sstep (Tb : Tables env) :
    ∀ (n : Nat) (l : List Value), l.length < n → (∀ A M C, A ++ M ++ C = l → Inert env M) →
      ∀ z w, ¬ SStep env (cfgV z l) w
  | 0, _, hlt, _, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, l, hlt, hin, z, w, hs => by
    obtain ⟨t, rules, hrel⟩ := Tb.step
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    have hl : Inert env l := hin [] l [] (by simp)
    match i, hf with
    | 0, hf =>
      obtain ⟨z', is, js, h₁, -, hp⟩ := inv_pure Tb.rules.pure hf
      obtain ⟨tp, rp, hrelp⟩ := Tb.pure
      obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hp
      rw [← (cfgV_inj h₁).2] at hj
      exact hl.1 j _ hj
    | 1, hf =>
      obtain ⟨z', is, js, h₁, -, hp⟩ := inv_read Tb.rules.read hf
      obtain ⟨tr, rr, hrelr⟩ := Tb.read
      obtain ⟨j, hj⟩ := (dderives_iff_fires hrelr).1 hp
      rw [← (cfgV_inj h₁).2] at hj
      exact hl.2.1 j z' _ hj
    | 2, hf =>
      obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, -, hs'⟩ :=
        inv_ctxtInstrs Tb.rules.ctxtInstrs hf
      have e : l = vs ++ is ++ rest := (cfgV_inj h₁).2
      have hlen : is.length < n := by
        have : l.length = vs.length + is.length + rest.length := by
          rw [e]; simp only [List.length_append]
        rcases hne with h | h
        · have := List.length_pos_iff.2 h; omega
        · have := List.length_pos_iff.2 h; omega
      refine not_sstep Tb n is hlen (fun A M C h => hin (vs ++ A) M (C ++ rest) ?_) z₁ _ hs'
      rw [e, ← h]
      simp
    | k + 3, hf => exact hl.2.2 (k + 3) z w (by omega) hf

/-- The step of a proper infix is impossible, so `ctxt-instrs` does not fire at `z; l`. -/
theorem not_ctxt (Tb : Tables env) {l : List Value}
    (hprop : ∀ A M C, A ++ M ++ C = l → (A ≠ [] ∨ C ≠ []) → Inert env M) {z w : Value}
    (hf : Fires env "Step" 2 (.tuple [cfgV z l, w])) : False := by
  obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, -, hs'⟩ := inv_ctxtInstrs Tb.rules.ctxtInstrs hf
  have e : l = vs ++ is ++ rest := (cfgV_inj h₁).2
  refine not_sstep Tb (is.length + 1) is (Nat.lt_succ_self _)
    (fun A M C h => hprop (vs ++ A) M (C ++ rest) ?_ ?_) z₁ _ hs'
  · rw [e, ← h]
    simp
  · exact hne.imp (fun h => by simp [h]) (fun h => by simp [h])

/-- **Inversion at a `Step_pure` redex**: if nothing fires on a proper infix of `l`, and no
`Step_read` rule and no `Step` rule beyond the first three fires at `z; l`, then every `Step`
fact from `z; l` is `Step/pure` at the whole of `l`. -/
theorem spure_of_sstep (Tb : Tables env) {l : List Value}
    (hprop : ∀ A M C, A ++ M ++ C = l → (A ≠ [] ∨ C ≠ []) → Inert env M)
    (hread : ∀ i z v, ¬ Fires env "Step_read" i (.tuple [cfgV z l, v]))
    (hstep : ∀ i z v, 3 ≤ i → ¬ Fires env "Step" i (.tuple [cfgV z l, v])) {z w : Value}
    (hs : SStep env (cfgV z l) w) : ∃ js, w = cfgV z js ∧ SPure env l js := by
  obtain ⟨t, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf =>
    obtain ⟨z', is, js, h₁, h₂, hp⟩ := inv_pure Tb.rules.pure hf
    obtain ⟨ez, el⟩ := cfgV_inj h₁
    subst ez el
    exact ⟨js, h₂, hp⟩
  | 1, hf =>
    obtain ⟨z', is, js, h₁, -, hp⟩ := inv_read Tb.rules.read hf
    obtain ⟨tr, rr, hrelr⟩ := Tb.read
    obtain ⟨j, hj⟩ := (dderives_iff_fires hrelr).1 hp
    rw [← (cfgV_inj h₁).2] at hj
    exact absurd hj (hread j z' _)
  | 2, hf => exact (not_ctxt Tb hprop hf).elim
  | k + 3, hf => exact absurd hf (hstep (k + 3) z w (by omega))

/-- **Inversion at a `Step_read` redex**: as `spure_of_sstep`, with `Step_pure` refuted at the
whole of `l` instead. -/
theorem sread_of_sstep (Tb : Tables env) {l : List Value}
    (hprop : ∀ A M C, A ++ M ++ C = l → (A ≠ [] ∨ C ≠ []) → Inert env M)
    (hpure : ∀ i v, ¬ Fires env "Step_pure" i (.tuple [.list l, v]))
    (hstep : ∀ i z v, 3 ≤ i → ¬ Fires env "Step" i (.tuple [cfgV z l, v])) {z w : Value}
    (hs : SStep env (cfgV z l) w) : ∃ js, w = cfgV z js ∧ SRead env (cfgV z l) js := by
  obtain ⟨t, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf =>
    obtain ⟨z', is, js, h₁, -, hp⟩ := inv_pure Tb.rules.pure hf
    obtain ⟨tp, rp, hrelp⟩ := Tb.pure
    obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hp
    rw [← (cfgV_inj h₁).2] at hj
    exact absurd hj (hpure j _)
  | 1, hf =>
    obtain ⟨z', is, js, h₁, h₂, hp⟩ := inv_read Tb.rules.read hf
    obtain ⟨ez, el⟩ := cfgV_inj h₁
    subst ez el
    exact ⟨js, h₂, hp⟩
  | 2, hf => exact (not_ctxt Tb hprop hf).elim
  | k + 3, hf => exact absurd hf (hstep (k + 3) z w (by omega))

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
