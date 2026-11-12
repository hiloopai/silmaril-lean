module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Fires

/-!
# Round 7, memory SIMD: the backend reading (`DDerivesB`, `otherwiseB`, `FiresB`) across `withVBytes`

Round 6's backend reading reads conclusions through `conclAlts`. The transfer of `Fires`
(`VDecl.Fires`) carries over: every step reads one conclusion alternative instead of the
conclusion, and the kernel facts already cover every alternative (`alt_rg`, and `altAtomOk` in
`read_elseAltsOk`).

* `otherwiseAtB_agree`, `otherwiseAtB_goodRel`, `otherwiseAtB_read`: `otherwiseAtB` moves from
  `B₁` to `B₂` as `otherwiseAt` does;
* `dderivesB_otherwise`: a `DDerivesB env (otherwiseB env)` derivation of a `GoodRel` relation moves;
* `firesB_pure_iff`, `firesB_read_iff` (not 43), `firesB_step_iff` (not 1–5, 23), and their
  `withVBytes` forms.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evRule stepReach)
open Round7.VAgree (GoodEvs GoodRel GoodRule ArgOk AgreeOff agreeOff_symm agreeOff_withVBytes
  findRel?_simEnv)
open Round6.Reading (DDerivesB RuleBodyB otherwiseAtB otherwiseB FiresB conclAlts)

variable {B₁ B₂ : Builtins}

/-- `DDerivesB _ noElse` of a `GoodRel` relation moves from `B₁` to `B₂`. -/
theorem dderivesB_noElse (hB : AgreeOff B₁ B₂) {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} (hx : GoodRel x) (h : DDerivesB (simEnv B₁) noElse x op args v) :
    DDerivesB (simEnv B₂) noElse x op args v :=
  dderivesB_agree hB (fun _ _ _ _ _ h => h) hx h

/-- **One `GoodRule` body, read through `conclAlts`, moves from `B₁` to `B₂`.** -/
theorem ruleBodyB_rel (hB : AgreeOff B₁ B₂) {x : IL.Id} (hx : (0, x) ∈ stepReach) {j : Nat}
    (hg : GoodRule x j) {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule}
    (hrel : (simEnv B₁).findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    {D₁ D₂ : Interp}
    (hD : ∀ x op args v, GoodRel x → (∀ w ∈ args, ArgOk w) → D₁ x op args v → D₂ x op args v)
    {els₁ els₂ : Prop} (hels : els₁ → els₂) {args : List ArgV} {op' : MixopS} {w : Value}
    (h : RuleBodyB (simEnv B₁) D₁ els₁ ps args op' r w) :
    RuleBodyB (simEnv B₂) D₂ els₂ ps args op' r w := by
  have hF := relFacts_of_find hrel hx
  have hps : ps = [] := hF.1
  have hRF : ruleFactsB r = true := hF.2 r (List.mem_of_getElem? hr)
  have hG : GoodEvs (evRule r) := hg B₁ _ r hrel hr
  rw [hps] at h ⊢
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  exact ruleBodyB_agree hB hD (quant_rg hRF) (alt_rg hRF) (goodEvs_prems_of_rule hG)
    (fun _ => hels) h

/-- The rules of `x` that are not `GoodRule` never fire, under the backend reading, where `P`
holds. -/
def BadSilentB (x : IL.Id) (args : List ArgV) (P : Nat → Value → Prop) : Prop :=
  ∀ i v j w, P i v → j < i → SameLhs v w → ¬ GoodRule x j →
    ∀ (B : Builtins) (D : Interp) (els : Prop) ps op t rules r,
      (simEnv B).findRel? x = some (ps, op, t, rules) → rules[j]? = some r →
      ¬ RuleBodyB (simEnv B) D els ps args op r w

/-- **`otherwiseB` moves from `B₁` to `B₂` where `P` holds.** -/
theorem otherwiseAtB_agree {x : IL.Id} (hx : (0, x) ∈ stepReach) {args : List ArgV}
    {P : Nat → Value → Prop} (hP : Inherits P) (hbad : BadSilentB x args P) (i : Nat) :
    ∀ (B₁ B₂ : Builtins), AgreeOff B₁ B₂ → ∀ v, P i v →
      otherwiseAtB (simEnv B₁) x args i v → otherwiseAtB (simEnv B₂) x args i v := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro B₁ B₂ hB v hPv h
    rw [otherwiseAtB] at h ⊢
    intro j hj ps op t rules r hrel hr w hw hbody
    by_cases hg : GoodRule x j
    · have hB' := agreeOff_symm hB
      have hels : otherwiseAtB (simEnv B₂) x args j w → otherwiseAtB (simEnv B₁) x args j w :=
        ih j hj B₂ B₁ hB' w (hP i v j w hPv hj hw)
      exact h j hj ps op t rules r ((findRel?_simEnv B₁ B₂ x).trans hrel) hr w hw
        (ruleBodyB_rel hB' hx hg hrel hr (fun _ _ _ _ hy _ hd => dderivesB_noElse hB' hy hd) hels
          hbody)
    · exact hbad i v j w hPv hj hw hg B₂ _ _ ps op t rules r hrel hr hbody

/-- **The backend `otherwise` reading of a `GoodRel` relation moves from `B₁` to `B₂`.** -/
theorem otherwiseAtB_goodRel (hB : AgreeOff B₁ B₂) {x : IL.Id} (hx : GoodRel x)
    (args : List ArgV) (i : Nat) (v : Value) :
    otherwiseAtB (simEnv B₁) x args i v → otherwiseAtB (simEnv B₂) x args i v :=
  otherwiseAtB_agree (P := fun _ _ => True) hx.1 (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ j _ _ _ _ hg => absurd (goodRule_of_goodRel hx j) hg) i B₁ B₂ hB v trivial

/-- **A `DDerivesB env (otherwiseB env)` derivation of a `GoodRel` relation moves.** -/
theorem dderivesB_otherwise (hB : AgreeOff B₁ B₂) {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} (hx : GoodRel x) (h : DDerivesB (simEnv B₁) (otherwiseB (simEnv B₁)) x op args v) :
    DDerivesB (simEnv B₂) (otherwiseB (simEnv B₂)) x op args v :=
  dderivesB_agree hB (fun _ args i w hy => otherwiseAtB_goodRel hB hy args i w) hx h

/-! ## `Step_read` and rule 43, alternative by alternative -/

theorem elseAltsOk_read {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (h : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) :
    elseAltsOk rules = true := by
  have h₁ := onRel_of_find elseAltsOk h
  rw [read_elseAltsOk] at h₁
  exact (Option.some.inj h₁).symm

/-- An alternative of a rule passing `altAtomOk r a` has the atom `a`. -/
theorem altAtom {nm : IL.Id} {qs : List Param} {op : MixopS} {e e' : Exp} {prems : List Prem}
    {a : MixopS} (h : altAtomOk (.ruleD nm qs op e prems) a = true) (he' : e' ∈ conclAlts e) :
    VElse.ruleAtom (.ruleD nm qs op e' prems) = some a := by
  have := List.all_eq_true.1 h e' he'
  simpa only [beq_iff_eq] using this

/-- **Rule 43 of `Step_read` fires, under the backend reading, only on left-hand sides ending in
`VLOAD`.** -/
theorem lhsAtom_of_read43B {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[43]? = some r) (hb : RuleBodyB (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "VLOAD" := by
  have hok := elseAltsOk_read h
  simp only [elseAltsOk, hr, Bool.and_eq_true] at hok
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨e', he', -, ρ₀, σ, -, -, hev, -⟩ := hb
  exact lhsAtom_of_eval (altAtom hok.1 he') hev

theorem readP_badSilentB (args : List ArgV) : BadSilentB "Step_read" args ReadP := by
  intro i v j w h hj hw hg B D els ps op t rules r hrel hr hb
  have h43 : j = 43 := by
    by_contra hne
    exact hg (VAgree.goodRule_read hne)
  rw [h43] at hr hj
  have hw' : lhsAtom w = some "VLOAD" := lhsAtom_of_read43B hrel hr hb
  rcases h with h | h
  · omega
  · exact h (by rw [lhsAtom_sameLhs hw]; exact hw')

/-- **The backend `otherwise` premises of `Step_read` move from `B₁` to `B₂`** where `ReadP`
holds. -/
theorem otherwiseAtB_read (hB : AgreeOff B₁ B₂) (args : List ArgV) {i : Nat} {v : Value}
    (h : ReadP i v) :
    otherwiseAtB (simEnv B₁) "Step_read" args i v → otherwiseAtB (simEnv B₂) "Step_read" args i v :=
  otherwiseAtB_agree read_mem_stepReach readP_inherits (readP_badSilentB args) i B₁ B₂ hB v h

/-! ## `FiresB` -/

/-- The hypothesis of `firesB_agree`: where rule `i` of `x` has an `otherwise` premise and one of
its conclusion alternatives evaluates to `v`, the backend `otherwise` reading moves. -/
def ElseMovesB (B₁ B₂ : Builtins) (x : IL.Id) (i : Nat) (v : Value) : Prop :=
  ∀ nm qs op e e' prems t rules,
    (simEnv B₁).findRel? x = some ([], "%~>%", t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ conclAlts e → (∃ ρ, EvalExp (simEnv B₁) ρ e' v) → prems.all elseFree = false →
    otherwiseB (simEnv B₁) x [] i v → otherwiseB (simEnv B₂) x [] i v

/-- **A `GoodRule` fires alike under the backend reading**, when its `otherwise` premise moves. -/
theorem firesB_agree (hB : AgreeOff B₁ B₂) {x : IL.Id} {i : Nat} {v : Value}
    (hx : (0, x) ∈ stepReach) (hg : GoodRule x i) (hels : ElseMovesB B₁ B₂ x i v)
    (h : FiresB (simEnv B₁) x i v) : FiresB (simEnv B₂) x i v := by
  obtain ⟨t, rules, r, hrel, hr, hb⟩ := h
  have hRF : ruleFactsB r = true := (relFacts_of_find hrel hx).2 r (List.mem_of_getElem? hr)
  have hG : GoodEvs (evRule r) := hg B₁ _ r hrel hr
  obtain ⟨nm, qs, op, e, prems⟩ := r
  obtain ⟨e', he', hb'⟩ := hb
  have hE : ∃ ρ, EvalExp (simEnv B₁) ρ e' v := by
    obtain ⟨-, ρ₀, σ, -, -, hev, -⟩ := hb'
    exact ⟨_, hev⟩
  refine ⟨t, rules, _, (findRel?_simEnv B₂ B₁ x).trans hrel, hr, e', he', ?_⟩
  exact ruleBody_agree hB (fun _ _ _ _ hy _ hd => dderivesB_otherwise hB hy hd) (quant_rg hRF)
    (alt_rg hRF e' he') (goodEvs_prems_of_rule hG)
    (fun hf => hels nm qs op e e' prems t rules hrel hr he' hE hf) hb'

theorem firesB_pure (hB : AgreeOff B₁ B₂) (i : Nat) (v : Value)
    (h : FiresB (simEnv B₁) "Step_pure" i v) : FiresB (simEnv B₂) "Step_pure" i v :=
  firesB_agree hB pure_goodRel.1 (VAgree.goodRule_pure i)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => otherwiseAtB_goodRel hB pure_goodRel [] i v) h

theorem firesB_step (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23]) (v : Value)
    (h : FiresB (simEnv B₁) "Step" i v) : FiresB (simEnv B₂) "Step" i v := by
  refine firesB_agree hB Round7.Script.step_mem_stepReach (VAgree.goodRule_step hi) ?_ h
  intro nm qs op e e' prems t rules hrel hr _ _ hf
  have hmem : i ∈ elseFreeIdx rules := mem_elseFreeIdx hr hf
  have hnil : elseFreeIdx rules = [] := by
    have h₁ := onRel_of_find elseFreeIdx hrel
    rw [step_elseDeep] at h₁
    exact (Option.some.inj h₁).symm
  rw [hnil] at hmem
  exact absurd hmem List.not_mem_nil

/-- After 43, a rule of `Step_read` with an `otherwise` premise has, on every conclusion
alternative, an atom other than `VLOAD`. -/
theorem read_else_altAtom {B : Builtins} {t : Typ} {rules : List Rule} {i : Nat} {nm : IL.Id}
    {qs : List Param} {op : MixopS} {e e' : Exp} {prems : List Prem}
    (hrel : (simEnv B).findRel? "Step_read" = some ([], "%~>%", t, rules))
    (hr : rules[i]? = some (.ruleD nm qs op e prems)) (hmem : i ∈ elseFreeIdx rules) (hi : 43 < i)
    (he' : e' ∈ conclAlts e) :
    ∃ b, VElse.ruleAtom (.ruleD nm qs op e' prems) = some b ∧ b ≠ "VLOAD" := by
  have hok := elseAltsOk_read hrel
  simp only [elseAltsOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hj := hok.2 i hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, hr] at hj
  rcases hj with hj | hj
  · omega
  · split at hj
    · rename_i b _
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
      exact ⟨b, altAtom hj.2 he', hj.1⟩
    · cases hj

theorem firesB_read (hB : AgreeOff B₁ B₂) {i : Nat} (hi : i ≠ 43) (v : Value)
    (h : FiresB (simEnv B₁) "Step_read" i v) : FiresB (simEnv B₂) "Step_read" i v := by
  refine firesB_agree hB read_mem_stepReach (VAgree.goodRule_read hi) ?_ h
  intro nm qs op e e' prems t rules hrel hr he' hE hf
  refine otherwiseAtB_read hB [] ?_
  by_cases hle : i ≤ 43
  · exact .inl hle
  · obtain ⟨b, hb, hne⟩ := read_else_altAtom hrel hr (mem_elseFreeIdx hr hf) (by omega) he'
    obtain ⟨ρ, hev⟩ := hE
    exact .inr (by rw [lhsAtom_of_eval hb hev]; exact fun h => hne (Option.some.inj h))

/-- **Every rule of `Step_pure` fires alike at `withVBytes B` and at `B`, backend reading.** -/
theorem firesB_pure_withVBytes_iff (B : Builtins) (i : Nat) (v : Value) :
    FiresB (simEnv (MemSimd.withVBytes B)) "Step_pure" i v ↔ FiresB (simEnv B) "Step_pure" i v :=
  ⟨firesB_pure (agreeOff_withVBytes B) i v,
    firesB_pure (agreeOff_symm (agreeOff_withVBytes B)) i v⟩

/-- **Every rule of `Step_read` other than 43 fires alike at `withVBytes B` and at `B`, backend
reading.** -/
theorem firesB_read_withVBytes_iff (B : Builtins) {i : Nat} (hi : i ≠ 43) (v : Value) :
    FiresB (simEnv (MemSimd.withVBytes B)) "Step_read" i v ↔ FiresB (simEnv B) "Step_read" i v :=
  ⟨firesB_read (agreeOff_withVBytes B) hi v,
    firesB_read (agreeOff_symm (agreeOff_withVBytes B)) hi v⟩

/-- **Every rule of `Step` other than 1–5 and 23 fires alike at `withVBytes B` and at `B`, backend
reading.** -/
theorem firesB_step_withVBytes_iff (B : Builtins) {i : Nat} (hi : i ∉ [1, 2, 3, 4, 5, 23])
    (v : Value) :
    FiresB (simEnv (MemSimd.withVBytes B)) "Step" i v ↔ FiresB (simEnv B) "Step" i v :=
  ⟨firesB_step (agreeOff_withVBytes B) hi v,
    firesB_step (agreeOff_symm (agreeOff_withVBytes B)) hi v⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
