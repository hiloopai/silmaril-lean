module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Basic

/-!
# Round 7, memory SIMD: the last instruction of a left-hand side, on values

The semantic half of the `otherwise` argument of `Round7.VElse`. `VElse.ruleAtom r` reads the mixop
of the last instruction of the code expression of a conclusion `(z; instr*) ~> _` when that code
is a list, or a concatenation ending in a list, whose last element is a `case` expression.
`lhsAtom v` reads the same on a value `v = ((z; instr*), rhs)`.

* `lhsAtom_of_eval`: if a conclusion `e` has the atom `a` and `e` evaluates to `v` (in any
  environment and scope), then `lhsAtom v = some a`. Evaluation keeps the shape: a tuple of two,
  a `case` of a pair, a list whose last element is evaluated from the last expression, and a
  concatenation of two lists is a list ending in the second.
* `lhsAtom_sameLhs`: `lhsAtom` reads only the left-hand side, so two values with the same
  left-hand side (`SameLhs`) have the same atom.

So a value that a rule with atom `b` derives is not derived by a rule with atom `a ≠ b`, at any
builtins. For `Step_read`, rule 43 has atom `VLOAD` and every later `otherwise` rule another one
(`VElse.read_elseOk`, and `VDecl.read_elseAltsOk` for the conclusion alternatives).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- A list of values whose last element is a `case` of `a`. -/
def LastCase (a : MixopS) (cs : List Value) : Prop := ∃ w, cs.getLast? = some (.case a w)

theorem mapM_cons_ok {f : Exp → Res Value} {e₀ : Exp} {rest : List Exp} {vs : List Value}
    (hm : (e₀ :: rest).mapM f = .ok vs) :
    ∃ v, f e₀ = .ok v ∧ ∃ vs', rest.mapM f = .ok vs' ∧ v :: vs' = vs := by
  rw [List.mapM_cons] at hm
  simpa only [Res.bind_eq_ok, pure, Except.pure, Except.ok.injEq] using hm

theorem mapM_getLast {f : Exp → Res Value} :
    ∀ {es : List Exp} {vs : List Value} {e : Exp},
      es.mapM f = .ok vs → es.getLast? = some e → ∃ v, f e = .ok v ∧ vs.getLast? = some v
  | [], _, _, _, h => by simp at h
  | e₀ :: rest, vs, e, hm, hl => by
    obtain ⟨v, hv, vs', hvs', hcons⟩ := mapM_cons_ok hm
    by_cases hr : rest = []
    · have he : e₀ = e := by simpa [hr] using hl
      have hvs : vs' = [] := by
        rw [hr, List.mapM_nil] at hvs'
        exact (Except.ok.inj hvs').symm
      exact ⟨v, he ▸ hv, by rw [← hcons, hvs]; rfl⟩
    · have hl' : rest.getLast? = some e := by
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
        simpa [List.getLast?_cons_cons] using hl
      obtain ⟨u, hu, hlast⟩ := mapM_getLast hvs' hl'
      have hne : vs' ≠ [] := by rintro rfl; simp at hlast
      refine ⟨u, hu, ?_⟩
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [← hcons]
      simpa [List.getLast?_cons_cons] using hlast

theorem evalExp_caseE_shape {n : Nat} {env : Env} {ρ : VarEnv} {a : MixopS} {e : Exp} {v : Value}
    (h : evalExp n env ρ (.caseE a e) = .ok v) : ∃ w, v = .case a w := by
  rcases n with _ | n
  · simp [evalExp] at h
  · have h' : ∃ w, evalExp n env ρ e = .ok w ∧ Value.case a w = v := by
      simpa only [evalExp, Res.map_eq_ok] using h
    obtain ⟨w, -, hw⟩ := h'
    exact ⟨w, hw.symm⟩

theorem lastAtom_listE {es : List Exp} {a : MixopS} (ha : VElse.lastAtom (.listE es) = some a) :
    ∃ e₀, es.getLast? = some (.caseE a e₀) := by
  simp only [VElse.lastAtom] at ha
  split at ha
  · rename_i op e₀ hl
    have hop : op = a := Option.some.inj ha
    exact ⟨e₀, hop ▸ hl⟩
  · cases ha

/-- A list expression with last atom `a` evaluates to a list ending in a `case` of `a`. -/
theorem evalExp_listE_last {n : Nat} {env : Env} {ρ : VarEnv} {es : List Exp} {a : MixopS}
    {v : Value} (ha : VElse.lastAtom (.listE es) = some a)
    (h : evalExp (n + 2) env ρ (.listE es) = .ok v) : ∃ cs, v = .list cs ∧ LastCase a cs := by
  have h' : ∃ vs, es.mapM (evalExp n env ρ) = .ok vs ∧ Value.list vs = v := by
    simpa only [evalExp, evalExps, Res.map_eq_ok] using h
  obtain ⟨vs, hvs, hv⟩ := h'
  obtain ⟨e₀, hl⟩ := lastAtom_listE ha
  obtain ⟨u, hu, hlast⟩ := mapM_getLast hvs hl
  obtain ⟨w, hw⟩ := evalExp_caseE_shape hu
  exact ⟨vs, hv.symm, w, hw ▸ hlast⟩

/-- Concatenating any value with a list ending in a `case` of `a` gives such a list. -/
theorem cat_lastCase {v₁ v : Value} {cs₂ : List Value} {a : MixopS} (hw : LastCase a cs₂)
    (hc : Value.cat? v₁ (.list cs₂) = some v) : ∃ cs, v = .list cs ∧ LastCase a cs := by
  obtain ⟨w, hw⟩ := hw
  have hne : cs₂ ≠ [] := by rintro rfl; simp at hw
  cases v₁ <;> simp only [Value.cat?, Option.some.injEq, reduceCtorEq] at hc
  case list cs₁ =>
    refine ⟨cs₁ ++ cs₂, hc.symm, w, ?_⟩
    rw [List.getLast?_append_of_ne_nil _ hne]
    exact hw

/-- **A code expression with last atom `a` evaluates to a list ending in a `case` of `a`.** -/
theorem evalExp_lastAtom {env : Env} {ρ : VarEnv} (n : Nat) :
    ∀ {e : Exp} {a : MixopS} {v : Value}, VElse.lastAtom e = some a →
      evalExp n env ρ e = .ok v → ∃ cs, v = .list cs ∧ LastCase a cs := by
  induction n with
  | zero => intro e a v _ h; simp [evalExp] at h
  | succ n ih =>
    intro e a v ha h
    cases e
    case listE es =>
      rcases n with _ | n
      · simp [evalExp, evalExps] at h
      · exact evalExp_listE_last ha h
    case catE e₁ e₂ =>
      have ha₂ : VElse.lastAtom e₂ = some a := by simpa only [VElse.lastAtom] using ha
      have h' : ∃ v₁, evalExp n env ρ e₁ = .ok v₁ ∧ ∃ v₂, evalExp n env ρ e₂ = .ok v₂ ∧
          Value.cat? v₁ v₂ = some v := by
        simpa only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] using h
      obtain ⟨v₁, -, v₂, h₂, hc⟩ := h'
      obtain ⟨cs₂, hv₂, hw⟩ := ih ha₂ h₂
      exact cat_lastCase hw (hv₂ ▸ hc)
    all_goals simp [VElse.lastAtom] at ha

theorem evalExp_tupE2 {n : Nat} {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : evalExp n env ρ (.tupE [e₁, e₂]) = .ok v) :
    ∃ m v₁ v₂, evalExp m env ρ e₁ = .ok v₁ ∧ evalExp m env ρ e₂ = .ok v₂ ∧ v = .tuple [v₁, v₂] := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps] at h
  have h' : ∃ vs, [e₁, e₂].mapM (evalExp k env ρ) = .ok vs ∧ Value.tuple vs = v := by
    simpa only [evalExp, evalExps, Res.map_eq_ok] using h
  obtain ⟨vs, hvs, hv⟩ := h'
  obtain ⟨v₁, h₁, vs', hvs', hc⟩ := mapM_cons_ok hvs
  obtain ⟨v₂, h₂, vs'', hvs'', hc'⟩ := mapM_cons_ok hvs'
  have hnil : vs'' = [] := (Except.ok.inj (by simpa only [List.mapM_nil, pure, Except.pure] using hvs'')).symm
  refine ⟨k, v₁, v₂, h₁, h₂, ?_⟩
  rw [← hv, ← hc, ← hc', hnil]

theorem evalExp_caseE {n : Nat} {env : Env} {ρ : VarEnv} {c : MixopS} {e : Exp} {v : Value}
    (h : evalExp n env ρ (.caseE c e) = .ok v) : ∃ m w, evalExp m env ρ e = .ok w ∧ v = .case c w := by
  rcases n with _ | n
  · simp [evalExp] at h
  · have h' : ∃ w, evalExp n env ρ e = .ok w ∧ Value.case c w = v := by
      simpa only [evalExp, Res.map_eq_ok] using h
    obtain ⟨w, hw, hv⟩ := h'
    exact ⟨n, w, hw, hv.symm⟩

theorem readCode_some {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    {code : Exp} (h : VElse.readCode (.ruleD nm qs op e prems) = some code) :
    ∃ c z rhs, e = .tupE [.caseE c (.tupE [z, code]), rhs] := by
  unfold VElse.readCode at h
  split at h
  · rename_i c z code' rhs _ heq
    have hc : code' = code := Option.some.inj h
    injection heq with _ _ _ he _
    exact ⟨c, z, rhs, by rw [he, hc]⟩
  · cases h

/-- **A conclusion with atom `a` evaluates to a value whose left-hand side ends in `a`.** -/
theorem lhsAtom_of_eval {env : Env} {ρ : VarEnv} {nm : IL.Id} {qs : List Param} {op : MixopS}
    {e : Exp} {prems : List Prem} {a : MixopS} {v : Value}
    (ha : VElse.ruleAtom (.ruleD nm qs op e prems) = some a) (he : EvalExp env ρ e v) :
    lhsAtom v = some a := by
  obtain ⟨code, hcode, hlast⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨c, z, rhs, rfl⟩ := readCode_some hcode
  obtain ⟨n, hn⟩ := he
  obtain ⟨m, v₁, vr, h₁, -, rfl⟩ := evalExp_tupE2 hn
  obtain ⟨m', w, hw, rfl⟩ := evalExp_caseE h₁
  obtain ⟨k, zv, cv, -, hcv, rfl⟩ := evalExp_tupE2 hw
  obtain ⟨cs, rfl, u, hu⟩ := evalExp_lastAtom k hlast hcv
  simp only [lhsAtom, codeAtom, hu]

/-- `lhsAtom` reads only the left-hand side. -/
theorem lhsAtom_sameLhs {v w : Value} (h : SameLhs v w) : lhsAtom v = lhsAtom w := by
  obtain ⟨a, b, c, rfl, rfl⟩ := h
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
