module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.Env

/-!
# Round 7: `$utf8` in `simEnv B` is below the erratum's primitive

The one non-congruence case of environment monotonicity from `simEnv B` to `utf8Env B`
(`Round7.Utf8.Mono`) is a call of `$utf8`. In `simEnv B` its clauses are tried; in `utf8Env B`
there are none and the primitive `utf8Call` answers. This file proves that, at every fuel and on
every argument list, the first answer is below the second in `Res.Le` (`utf8_le`), provided `B`
does not itself interpret `$utf8`:

* on `[[]]` the first clause returns `[]` once it has fuel (`utf8_nil`, then fuel monotonicity),
  which is what the primitive answers;
* on a non-empty list the first clause calls itself on a singleton, which never returns
  (`Round5.Pos.tryClauses_utf8`), so the clauses are out of fuel at every fuel
  (`tryClauses_utf8_cons`);
* on any other argument list no clause pattern matches (`tryClauses_bad`), and both sides are a
  definite failure.

The shape of the four later clauses is read off the script (`utf8_rest`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round5.Pos (utf8Clause1 chsDom utf8Body)
open Round6.MemSimd (utf8Call)
open scoped Silmaril.SpecTec.Sem.Res

def concatClause1 : Clause := Clause.defD [(Param.typP "X")]
  [(Arg.typA (Typ.varT "X" [])), (Arg.expA (Exp.listE []))] (Exp.listE []) []

set_option maxRecDepth 100000 in
theorem findDef_concat (B : Builtins) :
    ∃ ps t rest, (simEnv B).findDef? "concat_" = some (ps, t, concatClause1 :: rest) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem memTyp_X (B : Builtins) : (simEnv B).memTyp "X" = false := rfl

set_option maxRecDepth 100000 in
theorem utf8_nil (B : Builtins) (rest : List Clause) :
    tryClauses 12 (simEnv B) (utf8Clause1 :: rest) [.val (.list [])] = .ok (.list []) := by
  obtain ⟨ps, t, crest, hc⟩ := findDef_concat B
  simp [tryClauses, utf8Clause1, matchArgs, matchArg, argSubOk, matchExp, chsDom,
    matchIterE, matchIterList, matchRounds, matchExps, premsHold, utf8Body, evalExp, callDef,
    evalArgs, evalArg, evalIterE, evalDoms, evalIterList, evalRounds, Res.ofOption, domVar, domSrc,
    iterCols, iterRows, Res.assert, hc, VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals,
    VarEnv.empty, Map.bind, Map.find?, iterCol, VarEnv.findVal?,
    Map.empty, Res.elimUndef, concatClause1, matchTypV, Map.binds, resolveTyp,
    VarEnv.findTyp?, VarEnv.bindTyp, memTyp_X, evalExps]
  rfl

theorem matchRounds_ch (env : Env) (ρ : VarEnv) (hρ : ρ.findVal? "ch" = none) :
    ∀ (vs : List Value) (n i : Nat),
      matchRounds n env ρ (.varE "ch") ["ch"] none i vs = .error .outOfFuel ∨
        matchRounds n env ρ (.varE "ch") ["ch"] none i vs = .ok (vs.map fun v => [v])
  | vs, 0, i => by simp [matchRounds]
  | [], n + 1, i => by simp [matchRounds]
  | v :: vs, n + 1, i => by
      rcases n with _ | n
      · simp [matchRounds, matchExp]
      · have hρ' : Map.find? ρ.vals "ch" = none := hρ
        rcases matchRounds_ch env ρ hρ vs (n + 1) (i + 1) with h | h <;>
        simp [matchRounds, matchExp, h, Res.ofOption, VarEnv.findVals?, VarEnv.bindVal,
          VarEnv.findVal?, Map.bind, Map.find?, hρ']


theorem iterRows_cons (u : Value) (us : List Value) :
    ∃ t, iterRows [("ch", u :: us)] none (us.length + 1) = [("ch", u)] :: t :=
  ⟨_, by simp [iterRows, List.range_succ_eq_map, iterRow]; rfl⟩

set_option maxRecDepth 100000 in
theorem body_oof (B : Builtins) (u : Value) (us : List Value) (rest : List Clause)
    (hd : (simEnv B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest)) :
    ∀ m, evalExp m (simEnv B) (VarEnv.empty.bindVal "ch*" (.list (u :: us))) utf8Body =
      .error .outOfFuel := by
  have hT := fun m => Round5.Pos.tryClauses_utf8 B u utf8Params utf8Res rest hd m
  obtain ⟨t, hR⟩ := iterRows_cons u us
  intro m
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;>
  simp [utf8Body, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms, chsDom,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, Res.assert, hd, VarEnv.findDef?,
    VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, VarEnv.findVal?,
    Map.empty, Res.elimUndef, hT, Map.binds, hR, evalExps, List.mapM_cons]

theorem iterCol_singletons (L : List Value) : iterCol (L.map fun v => [v]) 0 = L := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [iterCol]

theorem matchArgs_clause1 (env : Env) (L : List Value) :
    ∀ m, matchArgs m env VarEnv.empty [.expA (.iterE (.varE "ch") chsDom)] [.val (.list L)] =
        .error .outOfFuel ∨
      matchArgs m env VarEnv.empty [.expA (.iterE (.varE "ch") chsDom)] [.val (.list L)] =
        .ok (VarEnv.empty.bindVal "ch*" (.list L)) := by
  have hR := fun n => matchRounds_ch env VarEnv.empty rfl L n 0
  have he : VarEnv.empty.findVal? "ch*" = none := rfl
  intro m
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | m
  iterate 5 · simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList]
  · rcases hR 0 with h | h <;>
      simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, domVar,
        domSrc, h, matchExps]
  · rcases hR 1 with h | h <;>
      simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, domVar,
        domSrc, h, iterCols, matchExps]
  · rcases hR 2 with h | h <;>
      simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, domVar,
        domSrc, h, iterCols, iterCol_singletons, matchExps, he]
  · rcases hR (m + 3) with h | h <;>
      simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, domVar,
        domSrc, h, iterCols, iterCol_singletons, matchExps, he]

theorem tryClauses_utf8_cons (B : Builtins) (u : Value) (us : List Value) (rest : List Clause)
    (hd : (simEnv B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest)) :
    ∀ n, tryClauses n (simEnv B) (utf8Clause1 :: rest) [.val (.list (u :: us))] =
      .error .outOfFuel
  | 0 => by simp [tryClauses]
  | n + 1 => by
      have hb := body_oof B u us rest hd n
      rcases matchArgs_clause1 (simEnv B) (u :: us) n with h | h
      · simp [tryClauses, utf8Clause1, h, Res.elimUndef]
      · rcases n with _ | n
        · simp [tryClauses, utf8Clause1, h, Res.elimUndef, premsHold]
        · simp [tryClauses, utf8Clause1, h, Res.elimUndef, premsHold, hb]

def clausePats : Clause → List Arg
  | .defD _ pats _ _ => pats

set_option maxRecDepth 100000 in
theorem utf8_rest :
    ∃ rest, baseEnv.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest) ∧
      rest.map clausePats = List.replicate 4 [.expA (.listE [.varE "ch"])] :=
  ⟨_, rfl, rfl⟩


/-- A result that is out of fuel or a definite failure. -/
def OofOrUndef {α : Type} (r : Res α) : Prop := r = .error .outOfFuel ∨ r = .error .undef

/-- The argument lists `$utf8`'s clauses do not match: anything but one list value. -/
def BadArgs (ws : List ArgV) : Prop := ∀ L, ws ≠ [.val (.list L)]

theorem matchArgs_bad (env : Env) (pat : Exp)
    (hpat : pat = .iterE (.varE "ch") chsDom ∨ pat = .listE [.varE "ch"]) :
    ∀ (ws : List ArgV), BadArgs ws → ∀ k, OofOrUndef (matchArgs k env VarEnv.empty [.expA pat] ws)
  | ws, _, 0 => by simp [OofOrUndef, matchArgs]
  | [], _, k + 1 => by simp [OofOrUndef, matchArgs]
  | [.val v], hb, k + 1 => by
      have hv : v.asList? = none := by
        cases v <;> simp_all [BadArgs, Value.asList?]
      rcases k with _ | _ | _ | k
      · simp [OofOrUndef, matchArgs, matchArg]
      · rcases hpat with rfl | rfl <;> simp [OofOrUndef, matchArgs, matchArg, argSubOk, matchExp]
      · rcases hpat with rfl | rfl <;>
          simp [OofOrUndef, matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, hv,
            Res.ofOption]
      · rcases hpat with rfl | rfl <;>
          simp [OofOrUndef, matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, hv,
            Res.ofOption]
  | [.typ _], _, k + 1 => by rcases k with _ | k <;> simp [OofOrUndef, matchArgs, matchArg]
  | [.defName _], _, k + 1 => by rcases k with _ | k <;> simp [OofOrUndef, matchArgs, matchArg]
  | [.gram _], _, k + 1 => by rcases k with _ | k <;> simp [OofOrUndef, matchArgs, matchArg]
  | w :: w' :: ws, _, k + 1 => by
      simp only [matchArgs]
      cases hm : matchArg k env VarEnv.empty (.expA pat) w with
      | error e => cases e <;> simp [OofOrUndef]
      | ok ρ => rcases k with _ | k <;> simp [OofOrUndef, matchArgs]


theorem tryClauses_bad (env : Env) (ws : List ArgV) (hb : BadArgs ws) :
    ∀ (cs : List Clause), (∀ c ∈ cs, clausePats c = [.expA (.iterE (.varE "ch") chsDom)] ∨
        clausePats c = [.expA (.listE [.varE "ch"])]) →
      ∀ n, OofOrUndef (tryClauses n env cs ws)
  | _, _, 0 => by simp [OofOrUndef, tryClauses]
  | [], _, n + 1 => by simp [OofOrUndef, tryClauses]
  | .defD q pats e prems :: cs, hcs, n + 1 => by
      have hp : pats = [.expA (.iterE (.varE "ch") chsDom)] ∨ pats = [.expA (.listE [.varE "ch"])] :=
        hcs _ (List.mem_cons_self ..)
      have ih := tryClauses_bad env ws hb cs (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) n
      have hm : OofOrUndef (matchArgs n env VarEnv.empty pats ws) := by
        rcases hp with rfl | rfl
        · exact matchArgs_bad env _ (Or.inl rfl) ws hb n
        · exact matchArgs_bad env _ (Or.inr rfl) ws hb n
      simp only [tryClauses]
      rcases hm with h | h <;> simp [h, Res.elimUndef, OofOrUndef]; exact ih

theorem utf8Call_bad {ws : List ArgV} (hb : BadArgs ws) : utf8Call ws = none := by
  unfold utf8Call
  split
  · rename_i cs; exact absurd rfl (hb cs)
  · rfl


/-- On `[[]]` the clauses answer `[]` or are out of fuel, at every fuel (`utf8_nil` and fuel
monotonicity). -/
theorem tryClauses_utf8_nil (B : Builtins) (rest : List Clause) (n : Nat) :
    tryClauses n (simEnv B) (utf8Clause1 :: rest) [.val (.list [])] = .error .outOfFuel ∨
      tryClauses n (simEnv B) (utf8Clause1 :: rest) [.val (.list [])] = .ok (.list []) := by
  have h12 : tryClauses 12 (simEnv B) (utf8Clause1 :: rest) [.val (.list [])] = .ok (.list []) :=
    utf8_nil B rest
  rcases Nat.le_total n 12 with h | h
  · rcases (monoAt_of_le h).tryClauses (simEnv B) (utf8Clause1 :: rest) [.val (.list [])]
      with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.symm.trans h12)
  · rcases (monoAt_of_le h).tryClauses (simEnv B) (utf8Clause1 :: rest) [.val (.list [])]
      with h' | h'
    · exact absurd (h12.symm.trans h') (by simp)
    · exact Or.inr (h12 ▸ h')

/-- Every clause of `$utf8` has one of the two argument patterns. -/
theorem utf8_clausePats (rest : List Clause)
    (hrest : rest.map clausePats = List.replicate 4 [.expA (.listE [.varE "ch"])]) :
    ∀ c ∈ utf8Clause1 :: rest, clausePats c = [.expA (.iterE (.varE "ch") chsDom)] ∨
      clausePats c = [.expA (.listE [.varE "ch"])] := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · exact Or.inl (h ▸ rfl)
  · have hm : clausePats c ∈ List.replicate 4 [.expA (.listE [.varE "ch"])] :=
      hrest ▸ List.mem_map_of_mem h
    exact Or.inr (List.eq_of_mem_replicate hm)

/-- The answer of `$utf8` in `simEnv B`: the clauses, then `B`. -/
noncomputable abbrev utf8Lhs (B : Builtins) (rest : List Clause) (n : Nat) (ws : List ArgV) :
    Res Value :=
  Res.elimUndef (tryClauses n (simEnv B) (utf8Clause1 :: rest) ws) .ok
    (fun _ => Res.ofOption (B.call "utf8" ws))

theorem utf8Lhs_nil (B : Builtins) (rest : List Clause) (n : Nat) :
    utf8Lhs B rest n [.val (.list [])] ⊑ Res.ofOption (utf8Call [.val (.list [])]) := by
  have hc := tryClauses_utf8_nil B rest n
  rcases hc with h | h <;> simp only [utf8Lhs, h, Res.elimUndef]
  · exact Res.oof_le _
  · exact Res.Le.refl _

theorem utf8Lhs_cons (B : Builtins) (rest : List Clause)
    (hd : (simEnv B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest))
    (n : Nat) (u : Value) (us : List Value) (r : Res Value) :
    utf8Lhs B rest n [.val (.list (u :: us))] ⊑ r := by
  have h : tryClauses n (simEnv B) (utf8Clause1 :: rest) [.val (.list (u :: us))] =
      .error .outOfFuel := tryClauses_utf8_cons B u us rest hd n
  simp only [utf8Lhs, h, Res.elimUndef]
  exact Res.oof_le _

theorem utf8Lhs_bad (B : Builtins) (hB : ∀ ws, B.call "utf8" ws = none) (rest : List Clause)
    (hrest : rest.map clausePats = List.replicate 4 [.expA (.listE [.varE "ch"])]) (n : Nat)
    {ws : List ArgV} (hb : BadArgs ws) : utf8Lhs B rest n ws ⊑ Res.ofOption (utf8Call ws) := by
  have hc := tryClauses_bad (simEnv B) ws hb _ (utf8_clausePats rest hrest) n
  rcases hc with h | h <;> simp only [utf8Lhs, h, Res.elimUndef, hB, utf8Call_bad hb]
  · exact Res.oof_le _
  · exact Res.Le.refl _

/-- **`$utf8` in `simEnv B` is below the primitive of `utf8Env B`**, at every fuel and on every
argument list, when `B` leaves `$utf8` uninterpreted. -/
theorem utf8_le (B : Builtins) (hB : ∀ ws, B.call "utf8" ws = none) (rest : List Clause)
    (hd : (simEnv B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest))
    (hrest : rest.map clausePats = List.replicate 4 [.expA (.listE [.varE "ch"])])
    (n : Nat) (ws : List ArgV) :
    Res.elimUndef (tryClauses n (simEnv B) (utf8Clause1 :: rest) ws) .ok
        (fun _ => Res.ofOption (B.call "utf8" ws)) ⊑
      Res.elimUndef (tryClauses n (utf8Env B) [] ws) .ok
        (fun _ => Res.ofOption (utf8Call ws)) := by
  rcases n with _ | n
  · simp only [tryClauses, Res.elimUndef]; exact Res.oof_le _
  have hR : Res.elimUndef (tryClauses (n + 1) (utf8Env B) [] ws) .ok
      (fun _ => Res.ofOption (utf8Call ws)) = Res.ofOption (utf8Call ws) := by
    simp [tryClauses, Res.elimUndef]
  show utf8Lhs B rest (n + 1) ws ⊑ _
  rw [hR]
  by_cases hw : ∃ L, ws = [.val (.list L)]
  · obtain ⟨L, hL⟩ := hw
    rcases L with _ | ⟨u, us⟩
    · exact hL ▸ utf8Lhs_nil B rest (n + 1)
    · exact hL ▸ utf8Lhs_cons B rest hd (n + 1) u us _
  · exact utf8Lhs_bad B hB rest hrest (n + 1) fun L h => hw ⟨L, h⟩

/-- The clauses of `$utf8` after the first, in the fixed script. -/
noncomputable def utf8Rest : List Clause :=
  match baseEnv.findDef? "utf8" with
  | some (_, _, _ :: r) => r
  | _ => []

theorem utf8Rest_eq {rest : List Clause}
    (h : baseEnv.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: rest)) :
    utf8Rest = rest := by
  unfold utf8Rest
  rw [h]

theorem findDef?_utf8_simEnv (B : Builtins) :
    (simEnv B).findDef? "utf8" = some (utf8Params, utf8Res, utf8Clause1 :: utf8Rest) := by
  obtain ⟨rest, h, _⟩ := utf8_rest
  rw [simEnv, Env.findDef?_withBuiltins, h, utf8Rest_eq h]

theorem utf8Rest_pats :
    utf8Rest.map clausePats = List.replicate 4 [.expA (.listE [.varE "ch"])] := by
  obtain ⟨rest, h, h'⟩ := utf8_rest
  rw [utf8Rest_eq h]
  exact h'

end Silmaril.Wasm.SpecTec.Sim.Round7
