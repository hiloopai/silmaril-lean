module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Basic

/-!
# Round 6: the two readings agree away from empty-domain options

* `premW_imp`, `ruleBody_imp`: a premise (a rule body) holds under a second interpretation when
  the two agree on the relations it consults.
* `dderivesB_iff_of_closed`: on a set of relations `S` closed under plainness (`Closed`), the two
  readings derive the same facts, for readings of `otherwise` that agree on `S`.
* `otherwiseAtB_iff_of_closed`, `firesB_iff_of_closed`, `dderivesB_otherwise_iff_of_closed`: on
  such a set, the two readings of `otherwise`, the per-rule `Fires` and the whole relation agree.
* `otherwiseAtB_iff_at`, `firesB_iff_at`: the same for one relation `x` at one left-hand side
  `a`, when every rule of `x` is plain for a closed `S` or cannot fire at `a` (`DeadAt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Interpretations that agree on the consulted relations -/

/-- A relation a premise of a list consults is consulted by the list. -/
theorem mem_premsRels {prems : List Prem} {pr : Prem} (hpr : pr ∈ prems) {y : IL.Id}
    (hy : y ∈ premRels pr) : y ∈ premsRels prems := by
  induction prems with
  | nil => cases hpr
  | cons p ps ih =>
    rcases List.mem_cons.1 hpr with rfl | h
    · exact List.mem_append_left _ hy
    · exact List.mem_append_right _ (ih h)

/-- A premise holds under `D'` and `els'` when it holds under `D` and `els`, and `D` implies `D'`
on the relations it consults. -/
theorem premW_imp {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (hD : ∀ y ∈ premRels pr, ∀ op a w, D y op a w → D' y op a w) (hel : els → els')
    (h : PremW env D els ρ pr) : PremW env D' els' ρ pr := by
  induction h with
  | ifPr h => exact .ifPr h
  | elsePr h => exact .elsePr (hel h)
  | letPr h₁ h₂ => exact .letPr h₁ h₂
  | rulePr ha he hd => exact .rulePr ha he (hD _ (List.mem_singleton_self _) _ _ _ hd)
  | iterOptNone hd hn hs => exact .iterOptNone hd hn hs
  | iterOptSome hd hn hs _ ih => exact .iterOptSome hd hn hs (ih hD)
  | iterList hit hd hn hl hk _ ih => exact .iterList hit hd hn hl hk fun r hr => ih r hr hD
  | iterListN hd he hk hl hlen _ ih =>
    exact .iterListN hd he hk hl hlen fun r hr => ih r hr hD

/-- `premW_imp` for interpretations that agree. -/
theorem premW_iff {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (hD : ∀ y ∈ premRels pr, ∀ op a w, D y op a w ↔ D' y op a w) (hel : els ↔ els') :
    PremW env D els ρ pr ↔ PremW env D' els' ρ pr :=
  ⟨premW_imp (fun y hy op a w => (hD y hy op a w).1) hel.1,
    premW_imp (fun y hy op a w => (hD y hy op a w).2) hel.2⟩

/-- A rule body under interpretations that agree on the relations its premises consult. -/
theorem ruleBody_iff {env : Env} {D D' : Interp} {els els' : Prop} {ps : List Param}
    {args : List ArgV} {op : MixopS} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
    {prems : List Prem} {v : Value}
    (hD : ∀ y ∈ premsRels prems, ∀ op a w, D y op a w ↔ D' y op a w) (hel : els ↔ els') :
    RuleBody env D els ps args op (.ruleD nm qs op' e prems) v ↔
      RuleBody env D' els' ps args op (.ruleD nm qs op' e prems) v := by
  have hp : ∀ ρ, (∀ pr ∈ prems, PremW env D els ρ pr) ↔ ∀ pr ∈ prems, PremW env D' els' ρ pr :=
    fun ρ => forall₂_congr fun pr hpr =>
      premW_iff (fun y hy => hD y (mem_premsRels hpr hy)) hel
  simp only [RuleBody, hp]

/-- A premise without `otherwise` does not read its `otherwise`. -/
theorem premW_imp_noElse {env : Env} {D D' : Interp} {els els' : Prop} {ρ : VarEnv} {pr : Prem}
    (hD : ∀ y ∈ premRels pr, ∀ op a w, D y op a w → D' y op a w) (hne : noElsePr pr = true)
    (h : PremW env D els ρ pr) : PremW env D' els' ρ pr := by
  induction h with
  | ifPr h => exact .ifPr h
  | elsePr _ => exact absurd hne (by simp [noElsePr])
  | letPr h₁ h₂ => exact .letPr h₁ h₂
  | rulePr ha he hd => exact .rulePr ha he (hD _ (List.mem_singleton_self _) _ _ _ hd)
  | iterOptNone hd hn hs => exact .iterOptNone hd hn hs
  | iterOptSome hd hn hs _ ih => exact .iterOptSome hd hn hs (ih hD hne)
  | iterList hit hd hn hl hk _ ih => exact .iterList hit hd hn hl hk fun r hr => ih r hr hD hne
  | iterListN hd he hk hl hlen _ ih =>
    exact .iterListN hd he hk hl hlen fun r hr => ih r hr hD hne

/-- A rule body without `otherwise` premises, under interpretations that agree on the relations
its premises consult, whatever the two readings of `otherwise`. -/
theorem ruleBody_iff_noElse {env : Env} {D D' : Interp} {els els' : Prop} {ps : List Param}
    {args : List ArgV} {op : MixopS} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
    {prems : List Prem} {v : Value}
    (hD : ∀ y ∈ premsRels prems, ∀ op a w, D y op a w ↔ D' y op a w)
    (hne : ∀ pr ∈ prems, noElsePr pr = true) :
    RuleBody env D els ps args op (.ruleD nm qs op' e prems) v ↔
      RuleBody env D' els' ps args op (.ruleD nm qs op' e prems) v := by
  have hp : ∀ ρ, (∀ pr ∈ prems, PremW env D els ρ pr) ↔ ∀ pr ∈ prems, PremW env D' els' ρ pr :=
    fun ρ => forall₂_congr fun pr hpr =>
      ⟨premW_imp_noElse (fun y hy op a w => (hD y (mem_premsRels hpr hy) op a w).1) (hne pr hpr),
        premW_imp_noElse (fun y hy op a w => (hD y (mem_premsRels hpr hy) op a w).2) (hne pr hpr)⟩
  simp only [RuleBody, hp]

/-! ## Closed sets of relations -/

/-- A rule of a relation in a closed set is plain for it. -/
theorem plain_of_closed {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id} (hx : S x)
    {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some (ps, op, t, rules)) {i : Nat} {r : Rule}
    (hr : rules[i]? = some r) : PlainRule S r :=
  C x hx ps op t rules hrel r (List.mem_of_getElem? hr)

/-- The only alternative of a plain rule's conclusion is the conclusion. -/
theorem eq_of_plain {S : IL.Id → Prop} {nm : IL.Id} {qs : List Param} {op : MixopS} {e e' : Exp}
    {prems : List Prem} (hp : PlainRule S (.ruleD nm qs op e prems)) (h : e' ∈ conclAlts e) :
    e' = e := by
  rw [conclAlts_of_not hp.1] at h
  exact List.mem_singleton.1 h

mutual
/-- On a closed set, a `DDerivesB` derivation is a `DDerives` derivation, for readings of
`otherwise` with `O'` implying `O` on the set. -/
theorem dderives_of_dderivesB_closed {env : Env} {S : IL.Id → Prop} {O O' : ElseI}
    (C : Closed env S) (hO : ∀ y, S y → ∀ args i v, O' y args i v → O y args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, S x →
      DDerivesB env O' x op args v → DDerives env O x op args v
  | _, _, _, _, hx, .rule hrel hrule halt hps hq he hp => by
    have hpl := plain_of_closed C hx hrel hrule
    rw [eq_of_plain hpl halt] at he
    exact .rule hrel hrule hps hq he fun pr hpr =>
      dprem_of_dpremB_closed C hO (fun y hy => hpl.2 y (mem_premsRels hpr hy)) (hO _ hx _ _ _)
        (hp pr hpr)

/-- `dderives_of_dderivesB_closed`, on premises. -/
theorem dprem_of_dpremB_closed {env : Env} {S : IL.Id → Prop} {O O' : ElseI}
    (C : Closed env S) (hO : ∀ y, S y → ∀ args i v, O' y args i v → O y args i v) :
    ∀ {els els' : Prop} {ρ : VarEnv} {pr : Prem}, (∀ y ∈ premRels pr, S y) → (els → els') →
      DPremB env O' els ρ pr → DPrem env O els' ρ pr
  | _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, hel, .elsePr h => .elsePr (hel h)
  | _, _, _, _, _, _, .letPr h₁ h₂ => .letPr h₁ h₂
  | _, _, _, _, hS, _, .rulePr ha he hd =>
      .rulePr ha he (dderives_of_dderivesB_closed C hO (hS _ (List.mem_singleton_self _)) hd)
  | _, _, _, _, _, _, .iterOptNone hd hn hs => .iterOptNone hd hn hs
  | _, _, _, _, hS, hel, .iterOptSome hd hn hs h =>
      .iterOptSome hd hn hs (dprem_of_dpremB_closed C hO hS hel h)
  | _, _, _, _, hS, hel, .iterList hit hd hn hl hk h =>
      .iterList hit hd hn hl hk fun r hr => dprem_of_dpremB_closed C hO hS hel (h r hr)
  | _, _, _, _, hS, hel, .iterListN hd he hk hl hlen h =>
      .iterListN hd he hk hl hlen fun r hr => dprem_of_dpremB_closed C hO hS hel (h r hr)
end

mutual
/-- On a closed set, a `DDerives` derivation is a `DDerivesB` derivation, for readings of
`otherwise` with `O` implying `O'` on the set. -/
theorem dderivesB_of_dderives_closed {env : Env} {S : IL.Id → Prop} {O O' : ElseI}
    (C : Closed env S) (hO : ∀ y, S y → ∀ args i v, O y args i v → O' y args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, S x →
      DDerives env O x op args v → DDerivesB env O' x op args v
  | _, _, _, _, hx, .rule hrel hrule hps hq he hp =>
    have hpl := plain_of_closed C hx hrel hrule
    .rule hrel hrule (self_mem_conclAlts _) hps hq he fun pr hpr =>
      dpremB_of_dprem_closed C hO (fun y hy => hpl.2 y (mem_premsRels hpr hy)) (hO _ hx _ _ _)
        (hp pr hpr)

/-- `dderivesB_of_dderives_closed`, on premises. -/
theorem dpremB_of_dprem_closed {env : Env} {S : IL.Id → Prop} {O O' : ElseI}
    (C : Closed env S) (hO : ∀ y, S y → ∀ args i v, O y args i v → O' y args i v) :
    ∀ {els els' : Prop} {ρ : VarEnv} {pr : Prem}, (∀ y ∈ premRels pr, S y) → (els → els') →
      DPrem env O els ρ pr → DPremB env O' els' ρ pr
  | _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, hel, .elsePr h => .elsePr (hel h)
  | _, _, _, _, _, _, .letPr h₁ h₂ => .letPr h₁ h₂
  | _, _, _, _, hS, _, .rulePr ha he hd =>
      .rulePr ha he (dderivesB_of_dderives_closed C hO (hS _ (List.mem_singleton_self _)) hd)
  | _, _, _, _, _, _, .iterOptNone hd hn hs => .iterOptNone hd hn hs
  | _, _, _, _, hS, hel, .iterOptSome hd hn hs h =>
      .iterOptSome hd hn hs (dpremB_of_dprem_closed C hO hS hel h)
  | _, _, _, _, hS, hel, .iterList hit hd hn hl hk h =>
      .iterList hit hd hn hl hk fun r hr => dpremB_of_dprem_closed C hO hS hel (h r hr)
  | _, _, _, _, hS, hel, .iterListN hd he hk hl hlen h =>
      .iterListN hd he hk hl hlen fun r hr => dpremB_of_dprem_closed C hO hS hel (h r hr)
end

/-- **On a closed set the two readings agree**, for readings of `otherwise` that agree on it. -/
theorem dderivesB_iff_of_closed {env : Env} {S : IL.Id → Prop} {O O' : ElseI}
    (C : Closed env S) (hO : ∀ y, S y → ∀ args i v, O y args i v ↔ O' y args i v)
    {x : IL.Id} (hx : S x) {op : MixopS} {args : List ArgV} {v : Value} :
    DDerivesB env O' x op args v ↔ DDerives env O x op args v :=
  ⟨dderives_of_dderivesB_closed C (fun y hy a i w => (hO y hy a i w).2) hx,
    dderivesB_of_dderives_closed C (fun y hy a i w => (hO y hy a i w).1) hx⟩

/-- `dderivesB_iff_of_closed`, at the relations a list of premises of a plain rule consults. -/
theorem consulted_iff {env : Env} {S : IL.Id → Prop} {O O' : ElseI} (C : Closed env S)
    (hO : ∀ y, S y → ∀ args i v, O y args i v ↔ O' y args i v) {prems : List Prem}
    (hS : ∀ y ∈ premsRels prems, S y) :
    ∀ y ∈ premsRels prems, ∀ op a w, DDerivesB env O' y op a w ↔ DDerives env O y op a w :=
  fun y hy _ _ _ => dderivesB_iff_of_closed C hO (hS y hy)

/-- A plain rule's body reads the same under both readings, when the readings of its premises
and of its `otherwise` agree. -/
theorem ruleBodyB_iff_of_plain {env : Env} {S : IL.Id → Prop} {O O' : ElseI} (C : Closed env S)
    (hO : ∀ y, S y → ∀ args i v, O y args i v ↔ O' y args i v) {els els' : Prop}
    (hel : els' ↔ els) {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value}
    (hp : PlainRule S r) :
    RuleBodyB env (DDerivesB env O') els' ps args op r v ↔
      RuleBody env (DDerives env O) els ps args op r v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  rw [ruleBodyB_iff_of_not hp.1]
  exact ruleBody_iff (consulted_iff C hO hp.2) hel

/-! ## `otherwise` and `Fires` on a closed set -/

/-- **On a closed set, the two readings of `otherwise` agree.** -/
theorem otherwiseAtB_iff_of_closed {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    (hx : S x) (args : List ArgV) :
    ∀ i v, otherwiseAtB env x args i v ↔ otherwiseAt env x args i v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v
    have hn : ∀ y, S y → ∀ (a : List ArgV) (k : Nat) (w : Value), noElse y a k w ↔ noElse y a k w :=
      fun _ _ _ _ _ => Iff.rfl
    rw [otherwiseAtB, otherwiseAt]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    refine forall_congr' fun ps => forall_congr' fun op => forall_congr' fun t => ?_
    refine forall_congr' fun rules => forall_congr' fun r => forall_congr' fun hrel => ?_
    refine forall_congr' fun hr => forall_congr' fun w => forall_congr' fun _ => ?_
    exact not_congr (ruleBodyB_iff_of_plain C hn (ih j hj w) (plain_of_closed C hx hrel hr))

/-- On a closed set, `otherwise` and `otherwiseB` agree. -/
theorem otherwise_iff_of_closed {env : Env} {S : IL.Id → Prop} (C : Closed env S) :
    ∀ y, S y → ∀ args i v, otherwise env y args i v ↔ otherwiseB env y args i v :=
  fun _ hy args i v => (otherwiseAtB_iff_of_closed C hy args i v).symm

/-- **On a closed set, a rule fires the same under both readings.** -/
theorem firesB_iff_of_closed {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    (hx : S x) {i : Nat} {v : Value} : FiresB env x i v ↔ Fires env x i v := by
  constructor
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    exact ⟨t, rules, r, hrel, hr, (ruleBodyB_iff_of_plain C (otherwise_iff_of_closed C)
      (otherwiseAtB_iff_of_closed C hx [] i v) (plain_of_closed C hx hrel hr)).1 hb⟩
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    exact ⟨t, rules, r, hrel, hr, (ruleBodyB_iff_of_plain C (otherwise_iff_of_closed C)
      (otherwiseAtB_iff_of_closed C hx [] i v) (plain_of_closed C hx hrel hr)).2 hb⟩

/-- **On a closed set, the whole relation, with `otherwise`, is the same under both
readings.** -/
theorem dderivesB_otherwise_iff_of_closed {env : Env} {S : IL.Id → Prop} (C : Closed env S)
    {x : IL.Id} (hx : S x) {op : MixopS} {args : List ArgV} {v : Value} :
    DDerivesB env (otherwiseB env) x op args v ↔ DDerives env (otherwise env) x op args v :=
  dderivesB_iff_of_closed C (otherwise_iff_of_closed C) hx

/-! ## One relation at one left-hand side -/

/-- Rule `r` (of a relation `config ~> _` or `instr* ~> _` without parameters) cannot fire at the
left-hand side `a`, under any interpretation and either reading. -/
def DeadAt (env : Env) (r : Rule) (a : Value) : Prop :=
  ∀ (D : Interp) (els : Prop) (b : Value), ¬ RuleBodyB env D els [] [] "%~>%" r (.tuple [a, b])

/-- **Plain or dead at `a`**: every rule of `x` is plain for `S` or cannot fire at `a`. -/
def ClosedAt (env : Env) (S : IL.Id → Prop) (x : IL.Id) (a : Value) : Prop :=
  ∀ ps op t rules, env.findRel? x = some (ps, op, t, rules) →
    ∀ r ∈ rules, PlainRule S r ∨ DeadAt env r a

/-- A dead rule does not fire under the old reading either. -/
theorem not_ruleBody_of_dead {env : Env} {r : Rule} {a : Value} (h : DeadAt env r a)
    {D : Interp} {els : Prop} {b : Value} : ¬ RuleBody env D els [] [] "%~>%" r (.tuple [a, b]) :=
  fun hb => h D els b (ruleBodyB_of_ruleBody hb)

/-- A rule body at the left-hand side `a` reads the same under both readings when the rule is
plain or dead at `a`. -/
theorem ruleBodyB_iff_at {env : Env} {S : IL.Id → Prop} (C : Closed env S) {O O' : ElseI}
    (hO : ∀ y, S y → ∀ args i v, O y args i v ↔ O' y args i v) {els els' : Prop}
    (hel : els' ↔ els) {r : Rule} {a b : Value} (hr : PlainRule S r ∨ DeadAt env r a) :
    RuleBodyB env (DDerivesB env O') els' [] [] "%~>%" r (.tuple [a, b]) ↔
      RuleBody env (DDerives env O) els [] [] "%~>%" r (.tuple [a, b]) := by
  rcases hr with hp | hd
  · exact ruleBodyB_iff_of_plain C hO hel hp
  · exact ⟨fun h => (hd _ _ _ h).elim, fun h => (not_ruleBody_of_dead hd h).elim⟩

/-- `SameLhs` keeps the left-hand side. -/
theorem sameLhs_tuple {a b w : Value} (h : SameLhs (.tuple [a, b]) w) : ∃ c, w = .tuple [a, c] := by
  obtain ⟨a', b', c, h₁, rfl⟩ := h
  simp only [Value.tuple.injEq, List.cons.injEq] at h₁
  exact ⟨c, by rw [h₁.1]⟩

/-- One earlier rule, in `otherwiseAtB_iff_at`: at the shared left-hand side, it fires under
the new reading exactly when it fires under the old one. -/
theorem ruleBodyB_iff_sameLhs {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    {t₀ : Typ} {rules₀ : List Rule} (hx : env.findRel? x = some ([], "%~>%", t₀, rules₀))
    {a b : Value} (hA : ClosedAt env S x a) {j : Nat}
    (ih : ∀ c, otherwiseAtB env x [] j (.tuple [a, c]) ↔ otherwiseAt env x [] j (.tuple [a, c]))
    {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some (ps, op, t, rules)) {r : Rule} (hr : rules[j]? = some r)
    {w : Value} (hw : SameLhs (.tuple [a, b]) w) :
    RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x [] j w) ps [] op r w ↔
      RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) ps [] op r w := by
  have hn : ∀ y, S y → ∀ (a : List ArgV) (k : Nat) (w : Value), noElse y a k w ↔ noElse y a k w :=
    fun _ _ _ _ _ => Iff.rfl
  have he : ([], "%~>%", t₀, rules₀) = (ps, op, t, rules) := Option.some.inj (hx.symm.trans hrel)
  obtain ⟨rfl, rfl, rfl, rfl⟩ : [] = ps ∧ "%~>%" = op ∧ t₀ = t ∧ rules₀ = rules := by
    simpa only [Prod.mk.injEq] using he
  obtain ⟨c, rfl⟩ := sameLhs_tuple hw
  exact ruleBodyB_iff_at C hn (ih c) (hA _ _ _ _ hrel r (List.mem_of_getElem? hr))

/-- **At a left-hand side where every rule is plain or dead, the two readings of `otherwise`
agree.** -/
theorem otherwiseAtB_iff_at {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    {t₀ : Typ} {rules₀ : List Rule} (hx : env.findRel? x = some ([], "%~>%", t₀, rules₀))
    {a : Value} (hA : ClosedAt env S x a) :
    ∀ i b, otherwiseAtB env x [] i (.tuple [a, b]) ↔ otherwiseAt env x [] i (.tuple [a, b]) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro b
    rw [otherwiseAtB, otherwiseAt]
    exact forall₂_congr fun j hj => forall_congr' fun ps => forall_congr' fun op =>
      forall_congr' fun t => forall_congr' fun rules => forall_congr' fun r =>
        forall_congr' fun hrel => forall_congr' fun hr => forall_congr' fun w =>
          forall_congr' fun hw =>
            not_congr (ruleBodyB_iff_sameLhs C hx hA (ih j hj) hrel hr hw)

/-- **At a left-hand side where every rule is plain or dead, a rule fires the same under both
readings**, given a closed `S` containing the relations the plain rules consult. -/
theorem firesB_iff_at {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    {t₀ : Typ} {rules₀ : List Rule} (hx : env.findRel? x = some ([], "%~>%", t₀, rules₀))
    {a : Value} (hA : ClosedAt env S x a) {i : Nat} {b : Value} :
    FiresB env x i (.tuple [a, b]) ↔ Fires env x i (.tuple [a, b]) := by
  have hel := otherwiseAtB_iff_at C hx hA i b
  constructor
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    exact ⟨t, rules, r, hrel, hr, (ruleBodyB_iff_at C (otherwise_iff_of_closed C) hel
      (hA _ _ _ _ hrel r (List.mem_of_getElem? hr))).1 hb⟩
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    exact ⟨t, rules, r, hrel, hr, (ruleBodyB_iff_at C (otherwise_iff_of_closed C) hel
      (hA _ _ _ _ hrel r (List.mem_of_getElem? hr))).2 hb⟩

/-- `FiresB`, unfolded: `DDerivesB` with `otherwiseB`, for a relation without parameters. -/
theorem dderivesB_iff_firesB {env : Env} {x : IL.Id} {v : Value} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some ([], "%~>%", t, rules)) :
    DDerivesB env (otherwiseB env) x "%~>%" [] v ↔ ∃ i, FiresB env x i v := by
  rw [dderivesB_iff]
  constructor
  · rintro ⟨ps, t', rules', i, r, hrel', hrule, hb⟩
    rw [hrel] at hrel'
    obtain ⟨rfl, rfl, rfl⟩ : [] = ps ∧ t = t' ∧ rules = rules' := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
      exact ⟨hrel'.1, hrel'.2.2.1, hrel'.2.2.2⟩
    exact ⟨i, t, rules, r, hrel, hrule, hb⟩
  · rintro ⟨i, t', rules', r, hrel', hrule, hb⟩
    exact ⟨[], t', rules', i, r, hrel', hrule, hb⟩

/-- **At a left-hand side where every rule is plain or dead, the whole relation, with
`otherwise`, is the same under both readings.** -/
theorem dderivesB_iff_at {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    {t₀ : Typ} {rules₀ : List Rule} (hx : env.findRel? x = some ([], "%~>%", t₀, rules₀))
    {a : Value} (hA : ClosedAt env S x a) {b : Value} :
    DDerivesB env (otherwiseB env) x "%~>%" [] (.tuple [a, b]) ↔
      DDerives env (otherwise env) x "%~>%" [] (.tuple [a, b]) := by
  rw [dderivesB_iff_firesB hx, dderives_iff_fires hx]
  exact exists_congr fun _ => firesB_iff_at C hx hA

/-! ## One rule, outside the closed set -/

/-- **A rule that is plain for a closed `S` and has no `otherwise` premise fires the same under
both readings**, even when its relation is not in `S`. -/
theorem firesB_iff_of_plain {env : Env} {S : IL.Id → Prop} (C : Closed env S) {x : IL.Id}
    {t : Typ} {rules : List Rule} (hrel : env.findRel? x = some ([], "%~>%", t, rules)) {i : Nat}
    {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (hr : rules[i]? = some (.ruleD nm qs op e prems))
    (hp : PlainRule S (.ruleD nm qs op e prems)) (hne : ∀ pr ∈ prems, noElsePr pr = true)
    {v : Value} : FiresB env x i v ↔ Fires env x i v := by
  have hb : ∀ els els', RuleBodyB env (DDerivesB env (otherwiseB env)) els' [] [] "%~>%"
      (.ruleD nm qs op e prems) v ↔
      RuleBody env (DDerives env (otherwise env)) els [] [] "%~>%" (.ruleD nm qs op e prems) v :=
    fun _ _ => (ruleBodyB_iff_of_not hp.1).trans
      (ruleBody_iff_noElse (consulted_iff C (otherwise_iff_of_closed C) hp.2) hne)
  constructor
  · rintro ⟨t', rules', r, hrel', hr', hb'⟩
    obtain ⟨rfl, rfl⟩ : t = t' ∧ rules = rules' := by
      simpa only [Option.some.injEq, Prod.mk.injEq, true_and] using hrel.symm.trans hrel'
    obtain rfl : r = _ := Option.some.inj (hr'.symm.trans hr)
    exact ⟨t, rules, _, hrel, hr, (hb _ _).1 hb'⟩
  · rintro ⟨t', rules', r, hrel', hr', hb'⟩
    obtain ⟨rfl, rfl⟩ : t = t' ∧ rules = rules' := by
      simpa only [Option.some.injEq, Prod.mk.injEq, true_and] using hrel.symm.trans hrel'
    obtain rfl : r = _ := Option.some.inj (hr'.symm.trans hr)
    exact ⟨t, rules, _, hrel, hr, (hb _ _).2 hb'⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
