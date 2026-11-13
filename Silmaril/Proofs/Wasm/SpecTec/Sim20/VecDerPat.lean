module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerTask
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms

/-!
# `VOk` of quantifiers read off a `VOk` conclusion

The transfer `VecDer.dderivesBS_toV'` needs `QuantsV` at every rule instance: each quantifier whose
type reaches `vbad20` is bound to a `VOk` value at a type `hasTyp_vec` moves. This file gives a
syntactic sufficient condition for one rule instance.

* `patB n e y`: `y` sits at a pattern position of `e`: under variables, subtype coercions,
  constructors, tuples, lists, concatenations and iterations `x*`/`x^m` over the domain `y` whose
  body reads `x` back.
* **`vOk_of_patB`**: if `e` evaluates to a `VOk` value, a variable at a pattern position of `e` is
  bound to a `VOk` value. By induction on the fuel, with the evaluator's inversion lemmas.
* `quantPatB e q`: the quantifier `q` has a type off `vbad20`, or a type naming no family whose
  variable sits at a pattern position of `e`.
* **`quantsV_of_pat`**: a rule instance whose quantifiers pass `quantPatB` at the conclusion
  alternative it evaluates, at a `VOk` value, in a scope without type variables, satisfies
  `QuantsV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (VOk fams vOk_tuple vOk_list vOk_case)

/-! ## Pattern positions -/

/-- The body of an iteration reads the iteration variable `x` back. -/
def bodyX (x : IL.Id) : Exp → Bool
  | .varE y => y == x
  | .subE (.varE y) _ _ => y == x
  | _ => false

/-- An unbounded or counted iteration. -/
def iterX : Iter → Bool
  | .list => true
  | .listN (.varE _) none => true
  | _ => false

/-- **`y` sits at a pattern position of `e`** (fuel `n`). -/
def patB : Nat → Exp → IL.Id → Bool
  | 0, _, _ => false
  | _ + 1, .varE x, y => x == y
  | n + 1, .subE e _ _, y => patB n e y
  | n + 1, .caseE _ e, y => patB n e y
  | n + 1, .tupE es, y => es.any fun e => patB n e y
  | n + 1, .listE es, y => es.any fun e => patB n e y
  | n + 1, .catE a b, y => patB n a y || patB n b y
  | _ + 1, .iterE b (.mk it [.mk x (.varE z)]), y =>
      iterX it && bodyX x b && x != "_" && z == y
  | _ + 1, _, _ => false

/-! ## Inversions -/

theorem bodyX_sound {env : Env} {x : IL.Id} {b : Exp} (hb : bodyX x b = true) :
    ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w := by
  intro σ w u hw hu
  unfold bodyX at hb
  split at hb
  · obtain rfl := beq_iff_eq.1 hb
    rw [evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · obtain rfl := beq_iff_eq.1 hb
    rw [evalExp_subE_iff, evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · cases hb

/-- `x*` over one domain `y`, inverted: `y` is bound to the result. -/
theorem evalExp_iterL_inv {env : Env} {ρ : VarEnv} {b : Exp} {x y : IL.Id} {v : Value}
    (hb : ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w)
    (hx : x ≠ "_") (h : EvalExp env ρ (.iterE b (.mk .list [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ v = .list vs := by
  obtain ⟨n, hn⟩ := evalExp_iterE_iff.1 h
  cases n with
  | zero => simp [evalIterE] at hn
  | succ n =>
      rw [evalIterE] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at hn
      obtain ⟨xvs, hdoms, -, k, -, hlist⟩ := hn
      obtain ⟨yv, fy, rfl⟩ := Sim.Exn.evalDoms_one hdoms
      obtain ⟨l, rfl, -, rfl⟩ := Sim.Exn.evalIterList_one_inv hb hx hlist
      exact ⟨l, fy, rfl⟩

/-- An iteration that reads its variable back evaluates to its domain's value. -/
theorem evalExp_iterX_inv {env : Env} {ρ : VarEnv} {b : Exp} {it : Iter} {x y : IL.Id}
    {v : Value} (hit : iterX it = true) (hb : bodyX x b = true) (hx : x ≠ "_")
    (h : EvalExp env ρ (.iterE b (.mk it [.mk x (.varE y)])) v) : ρ.findVal? y = some v := by
  unfold iterX at hit
  split at hit
  · obtain ⟨vs, hy, rfl⟩ := evalExp_iterL_inv (bodyX_sound hb) hx h
    exact hy
  · obtain ⟨vs, hy, -, rfl⟩ := Sim.Exn.evalExp_iterN_inv (bodyX_sound hb) hx h
    exact hy
  · cases hit

/-- Every expression of a list evaluates to a member of the list's value. -/
theorem evalExps_mem' {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → ∀ e ∈ es,
      ∃ u ∈ vs, EvalExp env ρ e u
  | [], _, _, e, he => absurd he List.not_mem_nil
  | e₀ :: es, vs, h, e, he => by
    obtain ⟨w, ws, rfl, h₁, h₂⟩ := Equiv.Validation.evalExps_cons_iff.1 h
    rcases List.mem_cons.1 he with rfl | he'
    · exact ⟨w, List.mem_cons_self .., h₁⟩
    · obtain ⟨u, hu, hue⟩ := evalExps_mem' h₂ e he'
      exact ⟨u, List.mem_cons_of_mem _ hu, hue⟩

/-- The two halves of a concatenation of `VOk` values are `VOk`. -/
theorem vOk_of_cat {v₁ v₂ v : Value} (hc : Value.cat? v₁ v₂ = some v) (hv : VOk v) :
    VOk v₁ ∧ VOk v₂ := by
  unfold Value.cat? at hc
  split at hc
  · rename_i a b
    obtain rfl := (Option.some.inj hc).symm
    have h := vOk_list hv
    exact ⟨.list fun w hw => h w (List.mem_append_left _ hw),
      .list fun w hw => h w (List.mem_append_right _ hw)⟩
  · obtain rfl := (Option.some.inj hc).symm
    exact ⟨.opt (by simp), hv⟩
  · obtain rfl := (Option.some.inj hc).symm
    exact ⟨hv, .opt (by simp)⟩
  · cases hc

/-! ## The lemma -/

/-- The statement of `vOk_of_patB` at fuel `n`. -/
def PatIH (env : Env) (n : Nat) : Prop :=
  ∀ {ρ : VarEnv} {e : Exp} {v : Value} {y : IL.Id} {w : Value},
    patB n e y = true → EvalExp env ρ e v → VOk v → ρ.findVal? y = some w → VOk w

section Cases

variable {env : Env} {n : Nat} {ρ : VarEnv} {v : Value} {y : IL.Id} {w : Value}

theorem pat_var {x : IL.Id} (hp : patB (n + 1) (.varE x) y = true)
    (he : EvalExp env ρ (.varE x) v) (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  have hxy : x = y := by simpa [patB] using hp
  have hxv : ρ.findVal? x = some v := evalExp_varE_iff.1 he
  rw [hxy, hw] at hxv
  exact (Option.some.inj hxv) ▸ hv

theorem pat_sub (ih : PatIH env n) {e : Exp} {t₁ t₂ : Typ}
    (hp : patB (n + 1) (.subE e t₁ t₂) y = true) (he : EvalExp env ρ (.subE e t₁ t₂) v)
    (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w :=
  ih (by simpa [patB] using hp) (evalExp_subE_iff.1 he) hv hw

theorem pat_case (ih : PatIH env n) {op : MixopS} {e : Exp}
    (hp : patB (n + 1) (.caseE op e) y = true) (he : EvalExp env ρ (.caseE op e) v)
    (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 he
  exact ih (by simpa [patB] using hp) hu (vOk_case hv).1 hw

theorem pat_tup (ih : PatIH env n) {es : List Exp} (hp : patB (n + 1) (.tupE es) y = true)
    (he : EvalExp env ρ (.tupE es) v) (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 he
  obtain ⟨e, hm, hpe⟩ := List.any_eq_true.1 (by simpa [patB] using hp)
  obtain ⟨u, hu, hue⟩ := evalExps_mem' hvs e hm
  exact ih hpe hue (vOk_tuple hv u hu) hw

theorem pat_list (ih : PatIH env n) {es : List Exp} (hp : patB (n + 1) (.listE es) y = true)
    (he : EvalExp env ρ (.listE es) v) (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 he
  obtain ⟨e, hm, hpe⟩ := List.any_eq_true.1 (by simpa [patB] using hp)
  obtain ⟨u, hu, hue⟩ := evalExps_mem' hvs e hm
  exact ih hpe hue (vOk_list hv u hu) hw

theorem pat_cat (ih : PatIH env n) {a b : Exp} (hp : patB (n + 1) (.catE a b) y = true)
    (he : EvalExp env ρ (.catE a b) v) (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 he
  obtain ⟨hv₁, hv₂⟩ := vOk_of_cat hc hv
  rcases Bool.or_eq_true_iff.1 (by simpa only [patB] using hp) with hpa | hpb
  · exact ih hpa h₁ hv₁ hw
  · exact ih hpb h₂ hv₂ hw

theorem pat_iter {b : Exp} {ie : IterExp} (hp : patB (n + 1) (.iterE b ie) y = true)
    (he : EvalExp env ρ (.iterE b ie) v) (hv : VOk v) (hw : ρ.findVal? y = some w) : VOk w := by
  rcases ie with ⟨it, ds⟩
  rcases ds with _ | ⟨⟨x, ze⟩, _ | ⟨d, ds⟩⟩
  · simp [patB] at hp
  · by_cases hz : ∃ z, ze = .varE z
    · obtain ⟨z, rfl⟩ := hz
      have hp' : ((iterX it = true ∧ bodyX x b = true) ∧ x ≠ "_") ∧ z = y := by
        simpa [patB] using hp
      obtain ⟨⟨⟨hit, hb⟩, hx⟩, rfl⟩ := hp'
      have hy : ρ.findVal? z = some v := evalExp_iterX_inv hit hb hx he
      rw [hy] at hw
      exact (Option.some.inj hw) ▸ hv
    · cases ze <;> simp_all [patB]
  · simp [patB] at hp

end Cases

/-- `vOk_of_patB`, at every fuel. -/
theorem patIH {env : Env} : ∀ n, PatIH env n
  | 0 => by
    intro hp
    simp [patB] at hp
  | n + 1 => by
    intro hp he hv hw
    rename_i ρ e v y w
    have ih : PatIH env n := patIH n
    cases e with
    | varE x => exact pat_var hp he hv hw
    | subE e t₁ t₂ => exact pat_sub ih hp he hv hw
    | caseE op e => exact pat_case ih hp he hv hw
    | tupE es => exact pat_tup ih hp he hv hw
    | listE es => exact pat_list ih hp he hv hw
    | catE a b => exact pat_cat ih hp he hv hw
    | iterE b ie => exact pat_iter hp he hv hw
    | _ => simp [patB] at hp

/-- **A variable at a pattern position of an expression that evaluates to a `VOk` value is bound
to a `VOk` value.** -/
theorem vOk_of_patB {env : Env} (n : Nat) {ρ : VarEnv} {e : Exp} {v : Value} {y : IL.Id}
    {w : Value} (hp : patB n e y = true) (he : EvalExp env ρ e v) (hv : VOk v)
    (hw : ρ.findVal? y = some w) : VOk w :=
  patIH n hp he hv hw

/-! ## Rule instances -/

/-- **A quantifier read off the conclusion `e`**: its type is off `vbad20`, or it names no family
and its variable sits at a pattern position of `e`. -/
def quantPatB (e : Exp) : Param → Bool
  | .expP y t => (evTyp t).all (tyEvB vbad20) || ((evTyp t).all (tyEvB fams) && patB 64 e y)
  | _ => true

/-- **A rule instance whose quantifiers are read off a `VOk` conclusion satisfies `QuantsV`.** -/
theorem quantsV_of_pat {env : Env} {ρ : VarEnv} {qs : List Param} {e : Exp} {v : Value}
    (hρ : ρ.typs = []) (h : qs.all (quantPatB e) = true) (he : EvalExp env ρ e v) (hv : VOk v) :
    QuantsV ρ qs := by
  refine ⟨hρ, fun y t w hy hw => ?_⟩
  have hq := List.all_eq_true.1 h _ hy
  simp only [quantPatB, Bool.or_eq_true, Bool.and_eq_true] at hq
  rcases hq with hoff | ⟨hff, hpat⟩
  · exact Or.inl (goodT_of_all hoff)
  · exact Or.inr ⟨vOk_of_patB 64 hpat he hv hw, Or.inl (goodT_of_all hff)⟩

end Silmaril.Wasm.SpecTec.Sim20.VecDer
