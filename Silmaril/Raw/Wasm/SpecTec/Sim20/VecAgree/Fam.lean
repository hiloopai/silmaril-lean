module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecAgree.Typ

/-!
# The prepended float instances, evaluated (unrefined)

`VecFix.fixFamily` puts `floatInst "F32" cs` and `floatInst "F64" cs` in front of a family's two
instances. Their argument patterns `F32 X M` and `F64 X M` (`floatPat`) are matched without any
environment lookup, so the two facts `VecAgree.FamRel.fam` asks for hold in every environment:

* `hasTypInsts_skip`: at a value that is not a float shape (`FloatSh`), both patterns fail
  definitely (`matchArgs_floatPat_miss`), and the list answers as its tail two units of fuel
  earlier;
* `hasTypInsts_float`: at a float shape, when the float instance's cases are the nullary cases
  `nullCases names` (`names` of length at most `8`), every nullary case named in `names` is
  accepted, from fuel `16` on.

Kept unrefined: the proofs are case analyses on the value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (floatInst)

/-- The argument pattern `C X M` of a prepended float instance. -/
def floatPat (c : String) : List Arg :=
  [.expA (.caseE "%X%" (.tupE [.caseE c (.tupE []), .varE "M"]))]

/-- Nullary cases without premises. -/
def nullCases (names : List String) : List TypCase :=
  names.map fun o => .mk o (.tupT []) [] []

theorem floatInst_eq (c : String) (cs : List TypCase) :
    floatInst c cs = .instD [.expP "M" (.varT "M" [])] (floatPat c) (.variantT cs) := rfl

theorem matchArgs_floatPat_miss {env : Env} {c : String} {a : Value} (n : Nat)
    (h : ∀ M, a ≠ .case "%X%" (.tuple [.case c (.tuple []), M])) :
    matchArgs (n + 8) env VarEnv.empty (floatPat c) [.val a] = .error .undef := by
  simp only [floatPat, matchArgs, matchArg, argSubOk, ↓reduceIte]
  rcases a with _ | _ | _ | _ | ⟨op, w⟩ | _ | _ | _ <;> try simp [matchExp, Value.asCase?]
  by_cases ho : op = "%X%"
  · subst ho
    rcases w with _ | _ | _ | vs | _ | _ | _ | _ <;> try simp [Value.asTuple?]
    rcases vs with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;>
      try simp [matchExp, matchExps, Value.asCase?, Value.asTuple?]
    all_goals
      rcases x with _ | _ | _ | _ | ⟨c', w'⟩ | _ | _ | _ <;> try simp
      by_cases hc : c' = c <;> simp [hc]
      rcases w' with _ | _ | _ | vs' | _ | _ | _ | _ <;> try simp
      cases vs' <;> simp [matchExps]
    subst hc
    cases rest with
    | nil => exact absurd rfl (h y)
    | cons z rest => simp [matchExps]
  · simp [ho]

theorem matchArgs_floatPat_hit {env : Env} {c : String} {M : Value} (n : Nat) :
    matchArgs (n + 8) env VarEnv.empty (floatPat c)
      [.val (.case "%X%" (.tuple [.case c (.tuple []), M]))] =
      .ok (VarEnv.empty.bindVal "M" M) := by
  simp [floatPat, matchArgs, matchArg, argSubOk, matchExp, matchExps, Value.asCase?,
    Value.asTuple?, VarEnv.findVal?, VarEnv.empty, Map.empty, Map.find?]

theorem hasTypCase_null {env : Env} {ρ : VarEnv} :
    ∀ (names : List String) (o : String) (j : Nat), o ∈ names →
      hasTypCase (j + names.length + 3) env ρ (nullCases names) o (.tuple []) = .ok true
  | [], _, _, h => by simp at h
  | o' :: names, o, j, h => by
    have hj : j + (o' :: names).length + 3 = (j + names.length + 3) + 1 := by simp; omega
    rw [hj]
    simp only [nullCases, List.map_cons, hasTypCase]
    by_cases ho : o' = o
    · subst ho
      rw [ite_eq_left rfl]
      have h₁ : hasTyp (j + names.length + 3) env ρ (.tupT []) (.tuple []) = .ok true := by
        rw [show j + names.length + 3 = (j + names.length + 1) + 1 + 1 by omega]
        simp [hasTyp, hasTypTup, Value.asTuple?]
      rw [h₁]
      have h₂ : premsOk (j + names.length + 3) env (caseScope ρ (.tupT []) (.tuple [])) [] =
          .ok true := by
        rw [show j + names.length + 3 = (j + names.length + 2) + 1 by omega]
        simp [premsOk, premsHold, Res.elimUndef, pure, Except.pure]
      simp [quantDefs, bindQuants, Res.elimUndef, h₂]
    · rw [ite_eq_right ho]
      have h' : o ∈ names := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ho
        · exact h
      exact hasTypCase_null names o j h'

/-- **At a value that is not a float shape, the two float instances are skipped.** -/
theorem hasTypInsts_skip {env : Env} {cs : List TypCase} {rest : List Inst} {a v : Value}
    (k : Nat) (h : ¬ FloatSh a) :
    hasTypInsts (k + 16 + 2) env (floatInst "F32" cs :: floatInst "F64" cs :: rest) [.val a] v =
      hasTypInsts (k + 16) env rest [.val a] v := by
  have hm : ∀ c, c = "F32" ∨ c = "F64" → ∀ n, matchArgs (n + 8) env VarEnv.empty (floatPat c)
      [.val a] = .error .undef := fun c hc n =>
    matchArgs_floatPat_miss n fun M he => h ⟨c, M, hc, he⟩
  rw [show k + 16 + 2 = (k + 16 + 1) + 1 by omega]
  simp only [floatInst_eq, hasTypInsts]
  rw [show k + 16 + 1 = (k + 9) + 8 by omega, hm "F32" (Or.inl rfl)]
  simp only [Res.elimUndef]
  have h₂ := hm "F64" (Or.inr rfl) (k + 8)
  rw [show k + 8 + 8 = k + 16 by omega] at h₂
  rw [h₂]

/-- **At a float shape, every nullary case of the float instance is accepted.** -/
theorem hasTypInsts_float {env : Env} {names : List String} {rest : List Inst} {a : Value}
    {o : String} (k : Nat) (hl : names.length ≤ 8) (ha : FloatSh a) (ho : o ∈ names) :
    hasTypInsts (k + 16) env (floatInst "F32" (nullCases names) ::
      floatInst "F64" (nullCases names) :: rest) [.val a] (.case o (.tuple [])) = .ok true := by
  obtain ⟨c, M, hc, rfl⟩ := ha
  have hd : ∀ ρ m, 11 ≤ m → hasTypDef (m + 1) env ρ (.variantT (nullCases names))
      (.case o (.tuple [])) = .ok true := by
    intro ρ m hm
    simp only [hasTypDef, Value.asCase?]
    exact hasTypCase_ok_of_le (by omega) (hasTypCase_null names o 0 ho)
  rw [show k + 16 = (k + 15) + 1 by omega]
  simp only [floatInst_eq, hasTypInsts]
  rcases hc with rfl | rfl
  · rw [show k + 15 = (k + 7) + 8 by omega, matchArgs_floatPat_hit]
    simp only [Res.elimUndef]
    exact hd _ _ (by omega)
  · rw [show k + 15 = (k + 7) + 8 by omega, matchArgs_floatPat_miss (c := "F32") (k + 7)
      (fun M' he => by simp at he)]
    simp only [Res.elimUndef]
    have h₂ := matchArgs_floatPat_hit (env := env) (c := "F64") (M := M) (k + 6)
    rw [show k + 6 + 8 = k + 14 by omega] at h₂
    rw [h₂]
    rw [show k + 14 = (k + 13) + 1 by omega]
    exact hd _ _ (by omega)

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
