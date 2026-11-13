module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumLk

/-!
# Clause lists that bind in an `if` premise definitely fail

The IL evaluator's `if` premise only tests (`Sem.premHolds`): it evaluates its expression in the
current scope. A premise `x* = rhs` written to *bind* the list variable `x*` therefore reads an
unbound variable and fails definitely (`.error .undef`), and so does its clause, provided the
clause's argument patterns cannot have bound `x*` themselves.

This module states that syntactically and proves it once for every environment:

* `pureP e`: `e` is a *pure pattern*, built from variables, `caseE`, `tupE` and `subE` only, so
  matching it never evaluates anything. `pvs e` are its variables.
* `unbHead prems = some x`: the first premise is an `if` test whose left operand iterates over the
  variable `x`.
* `clauseUnb cl`: `cl`'s first premise is such a test over `x`, and its argument patterns are pure
  and do not mention `x`.
* **`tryClausesUndef_of_all`**: if every clause of `cs` passes `clauseUnb`, then `cs` definitely
  fails at every argument list, in every environment (`TryClausesUndef`).

The matching half is `matchExp_good`/`matchArgs_good`: a pure pattern either definitely fails or
binds only its own variables, once the fuel exceeds its depth (`pdep`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (TryClausesUndef)

/-! ## The syntactic check -/

mutual
/-- **A pure pattern**: variables, `caseE`, `tupE` and `subE` only. -/
def pureP : Exp → Bool
  | .varE _ => true
  | .caseE _ e => pureP e
  | .tupE es => purePs es
  | .subE e _ _ => pureP e
  | _ => false

/-- `pureP` on a list. -/
def purePs : List Exp → Bool
  | [] => true
  | e :: es => pureP e && purePs es
end

mutual
/-- The variables of a pattern. -/
def pvs : Exp → List IL.Id
  | .varE x => [x]
  | .caseE _ e => pvs e
  | .tupE es => pvss es
  | .subE e _ _ => pvs e
  | _ => []

/-- `pvs` on a list. -/
def pvss : List Exp → List IL.Id
  | [] => []
  | e :: es => pvs e ++ pvss es
end

mutual
/-- The fuel a pure pattern needs. -/
def pdep : Exp → Nat
  | .caseE _ e => pdep e + 1
  | .tupE es => pdeps es + 1
  | .subE e _ _ => pdep e + 1
  | _ => 1

/-- `pdep` on a list. -/
def pdeps : List Exp → Nat
  | [] => 1
  | e :: es => max (pdep e) (pdeps es) + 1
end

/-- The fuel a list of argument patterns needs. -/
def adeps : List Arg → Nat
  | [] => 1
  | .expA e :: xs => max (pdep e + 1) (adeps xs) + 1
  | _ :: xs => adeps xs + 1

/-- The list variable the first premise iterates over, when it is an `if` test whose left operand
is an iteration over one domain. -/
def unbHead : List Prem → Option IL.Id
  | .ifPr (.cmpE _ _ (.iterE _ (.mk .list [.mk _ (.varE x)])) _) :: _ => some x
  | _ => none

/-- An argument pattern that is a pure expression pattern not mentioning `x`. -/
def patOk (x : IL.Id) : Arg → Bool
  | .expA e => pureP e && !(pvs e).contains x
  | _ => false

/-- **A clause that binds in an `if` premise**: its first premise tests over a variable `x` that
its pure argument patterns do not mention. -/
def clauseUnb : Clause → Bool
  | .defD _ pats _ prems =>
    match unbHead prems with
    | some x => pats.all (patOk x)
    | none => false

/-! ## Matching pure patterns -/

/-- The outcome of matching: a definite failure, or a scope that agrees with `ρ` at `y`. -/
def Good (y : IL.Id) (ρ : VarEnv) (r : Res VarEnv) : Prop :=
  r = .error .undef ∨ ∃ ρ', r = .ok ρ' ∧ ρ'.findVal? y = ρ.findVal? y

theorem good_undef {y : IL.Id} {ρ : VarEnv} : Good y ρ (.error .undef) := Or.inl rfl

theorem good_ok {y : IL.Id} {ρ : VarEnv} : Good y ρ (.ok ρ) := Or.inr ⟨ρ, rfl, rfl⟩

/-- `Good` composes along a bind. -/
theorem good_bind {y : IL.Id} {ρ : VarEnv} {r : Res VarEnv} {f : VarEnv → Res VarEnv}
    (hr : Good y ρ r) (hf : ∀ ρ', ρ'.findVal? y = ρ.findVal? y → Good y ρ (f ρ')) :
    Good y ρ (r >>= f) := by
  rcases hr with h | ⟨ρ', h, hy⟩
  · subst h; exact good_undef
  · subst h; exact hf ρ' hy

theorem findVal?_bindVal_ne {ρ : VarEnv} {x y : IL.Id} {v : Value} (h : x ≠ y) :
    (ρ.bindVal x v).findVal? y = ρ.findVal? y := by
  simp only [VarEnv.findVal?, VarEnv.bindVal]
  exact Map.find?_bind_of_ne _ h _

theorem good_assert {y : IL.Id} {ρ : VarEnv} {c : Prop} [Decidable c] {r : Res VarEnv}
    (h : Good y ρ r) : Good y ρ (Res.assert c r) := by
  unfold Res.assert
  split
  · exact h
  · exact good_undef

theorem good_ofOption_bind {α : Type} {y : IL.Id} {ρ : VarEnv} {o : Option α}
    {f : α → Res VarEnv} (hf : ∀ a, Good y ρ (f a)) : Good y ρ (Res.ofOption o >>= f) := by
  cases o with
  | none => exact good_undef
  | some a => exact hf a

/-- A fuel bound `k ≤ n` with `0 < k` gives `n = m + 1`. -/
theorem succ_of_le {k n : Nat} (hk : 0 < k) (h : k ≤ n) : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

mutual
/-- **A pure pattern either definitely fails or binds only its own variables.** -/
theorem matchExp_good (env : Env) (y : IL.Id) :
    ∀ (e : Exp), pureP e = true → y ∉ pvs e → ∀ n, pdep e ≤ n → ∀ ρ v,
      Good y ρ (matchExp n env ρ e v)
  | .varE x, _, hy, n, hn, ρ, v => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdep]) hn
    have hxy : x ≠ y := fun h => hy (by simp [pvs, h])
    simp only [matchExp]
    split
    · split
      · exact good_ok
      · exact good_undef
    · exact Or.inr ⟨_, rfl, findVal?_bindVal_ne hxy⟩
  | .caseE op e, hp, hy, n, hn, ρ, v => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdep]) hn
    simp only [matchExp]
    refine good_ofOption_bind fun p => ?_
    exact good_assert (matchExp_good env y e hp (by simpa [pvs] using hy) n
      (by simp [pdep] at hn; omega) ρ p.2)
  | .tupE es, hp, hy, n, hn, ρ, v => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdep]) hn
    simp only [matchExp]
    exact good_ofOption_bind fun vs => matchExps_good env y es (by simpa [pureP] using hp)
      (by simpa [pvs] using hy) n (by simp [pdep] at hn; omega) ρ vs
  | .subE e _ _, hp, hy, n, hn, ρ, v => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdep]) hn
    simp only [matchExp]
    exact matchExp_good env y e hp (by simpa [pvs] using hy) n (by simp [pdep] at hn; omega) ρ v
  | .boolE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .numE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .textE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .unE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .binE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .cmpE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .projE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .uncaseE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .optE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .theE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .strE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .dotE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .compE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .listE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .liftE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .memE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .lenE _, hp, _, _, _, _, _ => by simp [pureP] at hp
  | .catE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .idxE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .sliceE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .updE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .extE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .callE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .iterE .., hp, _, _, _, _, _ => by simp [pureP] at hp
  | .cvtE .., hp, _, _, _, _, _ => by simp [pureP] at hp

/-- `matchExp_good` on a list. -/
theorem matchExps_good (env : Env) (y : IL.Id) :
    ∀ (es : List Exp), purePs es = true → y ∉ pvss es → ∀ n, pdeps es ≤ n → ∀ ρ vs,
      Good y ρ (matchExps n env ρ es vs)
  | [], _, _, n, hn, ρ, vs => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdeps]) hn
    cases vs with
    | nil => simp only [matchExps]; exact good_ok
    | cons _ _ => simp only [matchExps]; exact good_undef
  | e :: es, hp, hy, n, hn, ρ, vs => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [pdeps]) hn
    simp only [purePs, Bool.and_eq_true] at hp
    simp only [pvss, List.mem_append, not_or] at hy
    simp only [pdeps] at hn
    cases vs with
    | nil => simp only [matchExps]; exact good_undef
    | cons v vs =>
      simp only [matchExps]
      refine good_bind (matchExp_good env y e hp.1 hy.1 n (by omega) ρ v) fun ρ' h' => ?_
      rcases matchExps_good env y es hp.2 hy.2 n (by omega) ρ' vs with h | ⟨ρ'', h, hy'⟩
      · rw [h]; exact good_undef
      · rw [h]; exact Or.inr ⟨ρ'', rfl, hy'.trans h'⟩
end

/-- One argument pattern that passes `patOk`. -/
theorem matchArg_good (env : Env) (y : IL.Id) {e : Exp} (he : pureP e = true) (hy : y ∉ pvs e)
    (n : Nat) (hn : pdep e + 1 ≤ n) (ρ : VarEnv) (w : ArgV) :
    Good y ρ (matchArg n env ρ (.expA e) w) := by
  obtain ⟨n, rfl⟩ := succ_of_le (by omega) hn
  cases w with
  | val v =>
    simp only [matchArg]
    split
    · exact matchExp_good env y e he hy n (by omega) ρ v
    · exact good_undef
  | _ => simp only [matchArg]; exact good_undef

/-- **Argument patterns that pass `patOk` either definitely fail or keep `y` as it was.** -/
theorem matchArgs_good (env : Env) (y : IL.Id) :
    ∀ (xs : List Arg), xs.all (patOk y) = true → ∀ n, adeps xs ≤ n → ∀ ρ ws,
      Good y ρ (matchArgs n env ρ xs ws)
  | [], _, n, hn, ρ, ws => by
    obtain ⟨n, rfl⟩ := succ_of_le (by simp [adeps]) hn
    cases ws with
    | nil => simp only [matchArgs]; exact good_ok
    | cons _ _ => simp only [matchArgs]; exact good_undef
  | .expA e :: xs, ha, n, hn, ρ, ws => by
    simp only [List.all_cons, Bool.and_eq_true, patOk, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at ha
    obtain ⟨⟨he, hy⟩, has⟩ := ha
    simp only [adeps] at hn
    obtain ⟨n, rfl⟩ := succ_of_le (by omega) hn
    cases ws with
    | nil => simp only [matchArgs]; exact good_undef
    | cons w ws =>
      simp only [matchArgs]
      refine good_bind (matchArg_good env y he hy n (by omega) ρ w) fun ρ' h' => ?_
      rcases matchArgs_good env y xs has n (by omega) ρ' ws with h | ⟨ρ'', h, hy'⟩
      · rw [h]; exact good_undef
      · rw [h]; exact Or.inr ⟨ρ'', rfl, hy'.trans h'⟩
  | .typA _ :: _, ha, _, _, _, _ => by simp [patOk] at ha
  | .defA _ :: _, ha, _, _, _, _ => by simp [patOk] at ha
  | .gramA _ :: _, ha, _, _, _, _ => by simp [patOk] at ha

/-! ## Premises and clauses -/

/-- **An `if` test over an unbound list variable definitely fails**, and so do the premises it
heads. -/
theorem premsUndef_of_unbHead {env : Env} {ρ : VarEnv} {prems : List Prem} {x : IL.Id}
    (h : unbHead prems = some x) (hx : ρ.findVal? x = none) :
    premsHold 8 env ρ prems = .error .undef := by
  unfold unbHead at h
  split at h
  · cases h
    simp [premsHold, premHolds, evalExp, evalIterE, evalDoms, domVar, domSrc, hx, Bind.bind,
      Except.bind, Res.ofOption, List.foldlM]
  · cases h

/-- The empty clause list definitely fails. -/
theorem tryClausesUndef_nil {env : Env} {ws : List ArgV} : TryClausesUndef env [] ws :=
  ⟨1, by simp [tryClauses]⟩

/-- One clause that passes `clauseUnb`, in front of a list that definitely fails. -/
theorem tryClausesUndef_cons {env : Env} {ws : List ArgV} {q : List Param} {pats : List Arg}
    {e : Exp} {prems : List Prem} {cs : List Clause}
    (hc : clauseUnb (.defD q pats e prems) = true) (hcs : TryClausesUndef env cs ws) :
    TryClausesUndef env (.defD q pats e prems :: cs) ws := by
  obtain ⟨k, hk⟩ := hcs
  simp only [clauseUnb] at hc
  split at hc
  · rename_i x hx
    refine ⟨max (max (adeps pats) 8) k + 1, ?_⟩
    have hk' := tryClauses_undef_of_le (n := max (max (adeps pats) 8) k) (by omega) hk
    rcases matchArgs_good env x pats hc (max (max (adeps pats) 8) k) (by omega) VarEnv.empty ws
      with hm | ⟨ρ₀, hm, hy⟩
    · simp only [tryClauses, hm, Bind.bind, Except.bind, Res.elimUndef_undef, hk']
    · have hp : premsHold (max (max (adeps pats) 8) k) env ρ₀ prems = .error .undef :=
        premsHold_undef_of_le (m := 8) (by omega)
          (premsUndef_of_unbHead hx (by rw [hy]; rfl))
      simp only [tryClauses, hm, Bind.bind, Except.bind, hp, Res.elimUndef_undef, hk']
  · cases hc

/-- **A clause list every clause of which passes `clauseUnb` definitely fails**, at every argument
list and in every environment. -/
theorem tryClausesUndef_of_all (env : Env) (ws : List ArgV) :
    ∀ cs : List Clause, cs.all clauseUnb = true → TryClausesUndef env cs ws
  | [], _ => tryClausesUndef_nil
  | .defD _ _ _ _ :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact tryClausesUndef_cons h.1 (tryClausesUndef_of_all env ws cs h.2)

end Silmaril.Wasm.SpecTec.Sim20.VecNum
