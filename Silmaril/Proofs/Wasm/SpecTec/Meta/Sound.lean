module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Lits

/-!
# Soundness: their reduction computes what our evaluator computes

`stepF_sound`: in `fixed`, a step `S |- e ~> x` from an encoded fragment expression goes to an
encoded fragment expression `e'`, and every value of `e'` is a value of `e`. With `reduce_rec`
this gives `reduceF_sound`: a reduction to the encoding of a value `v` means `e.strict = some v`.
The proof dispatches on the rule (`stepF_rule`: only the rules with the right head can apply)
and uses the inversion lemmas of `Inv` and the primitive specifications of `Numbin`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives RuleBody otherwise)

set_option maxRecDepth 100000

/-- A step from a constructor value uses a rule with that head. -/
theorem stepF_rule {S w x : Value} {c : MixopS} (h : MStep envF S (.case c w) x) :
    ∃ i r, (rulesOf envF "Step_exp")[i]? = some r ∧ i ∈ headIdx (rulesOf envF "Step_exp") c ∧
      RuleBody envF (DDerives envF (otherwise envF))
        (otherwise envF "Step_exp" [] i (.tuple [S, .case c w, x])) [] [] "%|-%~>%" r
        (.tuple [S, .case c w, x]) := by
  obtain ⟨ps, t, rules, i, r, hrel, hr, hb⟩ := Sim.dderives_iff.1 h
  rw [findRel_stepF] at hrel
  have e : [] = ps ∧ sxxT = t ∧ rulesOf envF "Step_exp" = rules := by simpa using hrel
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (headsF_all i r hr)
  have hc : c' = c := head_of_body hb hc'
  subst hc
  exact ⟨i, r, hr, mem_headIdx hr hc', hb⟩

/-- No step from a literal: no rule has head `BOOL`, `NAT` or `INT`. -/
theorem stepF_lit {S w x : Value} {c : MixopS} (hc : headIdx (rulesOf envF "Step_exp") c = [])
    (h : MStep envF S (.case c w) x) : False := by
  obtain ⟨i, r, -, hi, -⟩ := stepF_rule h
  rw [hc] at hi
  cases hi

/-! ## Values propagate backwards through congruence steps -/

theorem strict_un {op : UnOp} {t : OpTyp} {a a' : FExp}
    (h : ∀ v, a'.strict = some v → a.strict = some v) :
    ∀ v, (FExp.un op t a').strict = some v → (FExp.un op t a).strict = some v := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 hv
  exact Option.bind_eq_some_iff.2 ⟨u, h u hu, hv⟩

theorem strict_bin_l {op : BinOp} {t : OpTyp} {a a' b : FExp}
    (h : ∀ v, a'.strict = some v → a.strict = some v) :
    ∀ v, (FExp.bin op t a' b).strict = some v → (FExp.bin op t a b).strict = some v := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 hv
  exact Option.bind_eq_some_iff.2 ⟨u, h u hu, hv⟩

theorem strict_bin_r {op : BinOp} {t : OpTyp} {a b b' : FExp}
    (h : ∀ v, b'.strict = some v → b.strict = some v) :
    ∀ v, (FExp.bin op t a b').strict = some v → (FExp.bin op t a b).strict = some v := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨u', hu', hv⟩ := Option.bind_eq_some_iff.1 hv
  exact Option.bind_eq_some_iff.2 ⟨u, hu, Option.bind_eq_some_iff.2 ⟨u', h u' hu', hv⟩⟩

theorem strict_cmp_l {op : CmpOp} {t : OpTyp} {a a' b : FExp}
    (h : ∀ v, a'.strict = some v → a.strict = some v) :
    ∀ v, (FExp.cmp op t a' b).strict = some v → (FExp.cmp op t a b).strict = some v := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 hv
  exact Option.bind_eq_some_iff.2 ⟨u, h u hu, hv⟩

theorem strict_cmp_r {op : CmpOp} {t : OpTyp} {a b b' : FExp}
    (h : ∀ v, b'.strict = some v → b.strict = some v) :
    ∀ v, (FExp.cmp op t a b').strict = some v → (FExp.cmp op t a b).strict = some v := by
  intro v hv
  obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨u', hu', hv⟩ := Option.bind_eq_some_iff.1 hv
  exact Option.bind_eq_some_iff.2 ⟨u, hu, Option.bind_eq_some_iff.2 ⟨u', h u' hu', hv⟩⟩

/-! ## Each constructor -/

/-- The soundness property of one step from `e`. -/
def SoundAt (e : FExp) : Prop := ∀ {S x : Value}, MStep envF S e.enc x →
  ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → e.strict = some v

theorem enc_eq_bool {a : FExp} {b : Bool} (h : a.enc = con "BOOL" [.bool b]) : a = .bool b := by
  cases a <;> simp_all [FExp.enc, con]

theorem unValue_bool {op : UnOp} {b : Bool} {w : Value}
    (h : FExp.resVal (unValue op (.bool b)) = some w) : w = .bool (!b) := by
  cases op <;> simp_all [unValue, FExp.resVal]

theorem binValues_bool {op : BinOp} {b₁ b₂ : Bool} {w : Value}
    (h : FExp.resVal (binValues op (.bool b₁) (.bool b₂)) = some w) : ∃ b, w = .bool b := by
  cases op <;> cases b₁ <;> cases b₂ <;> simp_all [binValues, boolBin, FExp.resVal, Res.ofOption]

theorem sound_un_bool {op : UnOp} {t : OpTyp} {b : Bool} {w : Value}
    (h : FExp.resVal (unValue op (.bool b)) = some w) :
    ∃ e' : FExp, con "BOOL" [w] = e'.enc ∧
      ∀ v, e'.strict = some v → (FExp.un op t (.bool b)).strict = some v := by
  obtain rfl := unValue_bool h
  exact close_lit (w := .bool (!b)) rfl trivial h

theorem sound_un_num {op : UnOp} {t : OpTyp} {a : FExp} {x : Value}
    (ha : TypedIn envF (.varT "num" []) a.enc)
    (hx : TryClauses envF (fdef "numun").2.2 (args2 (encUnOp op) a.enc) x) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.un op t a).strict = some v := by
  obtain ⟨m, hm, he, hs⟩ := num_of_typed ha
  rw [he] at hx
  obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.1 ((numun_spec op hm).iff.1 hx)
  refine close_lit rfl (isLitV_num (un_natInt hm hm')) ?_
  simp [FExp.strict, hs, unValue, hm', FExp.resVal, Res.ofOption]

theorem sound_un (op : UnOp) (t : OpTyp) (a : FExp) (ih : SoundAt a) :
    SoundAt (.un op t a) := by
  intro S x h
  obtain ⟨i, r, hr, hi, hb⟩ := stepF_rule (c := "UN") (w := .tuple [encUnOp op, a.enc]) h
  rw [headsF_un] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · obtain rfl := Option.some.inj (stepF_0.symm.trans hr)
    obtain ⟨w, rfl, hd⟩ := unCtx_inv hb
    obtain ⟨a', rfl, hp⟩ := ih hd
    exact ⟨.un op t a', rfl, strict_un hp⟩
  · obtain rfl := Option.some.inj (stepF_1.symm.trans hr)
    obtain ⟨bv, w, ha, rfl, htc⟩ := unBool_inv (findDef_fdef rfl) (builtins_envF _) hb
    obtain rfl := enc_eq_bool ha
    exact sound_un_bool ((boolun_spec op bv).iff.1 htc)
  · obtain rfl := Option.some.inj (stepF_2.symm.trans hr)
    obtain ⟨ha, htc⟩ := unNum_inv (findDef_fdef rfl) (builtins_envF _) hb
    exact sound_un_num ha htc

theorem sound_bin_bool {op : BinOp} {t : OpTyp} {b₁ b₂ : Bool} {w : Value}
    (h : FExp.resVal (binValues op (.bool b₁) (.bool b₂)) = some w) :
    ∃ e' : FExp, con "BOOL" [w] = e'.enc ∧
      ∀ v, e'.strict = some v → (FExp.bin op t (.bool b₁) (.bool b₂)).strict = some v := by
  obtain ⟨b, rfl⟩ := binValues_bool h
  exact close_lit (w := .bool b) rfl trivial h

theorem sound_bin_num {op : BinOp} {t : OpTyp} {a b : FExp} {x : Value}
    (ha : TypedIn envF (.varT "num" []) a.enc) (hb : TypedIn envF (.varT "num" []) b.enc)
    (hx : TryClauses envF Rules.F.numbinF (args3 (encBinOp op) a.enc b.enc) x) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.bin op t a b).strict = some v := by
  obtain ⟨m₁, hm₁, he₁, hs₁⟩ := num_of_typed ha
  obtain ⟨m₂, hm₂, he₂, hs₂⟩ := num_of_typed hb
  rw [he₁, he₂] at hx
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 (numbin_le op hm₁ hm₂ hx)
  refine close_lit rfl (isLitV_num (bin_natInt hm₁ hm₂ hm)) ?_
  simp [FExp.strict, hs₁, hs₂, binValues, hm, FExp.resVal, Res.ofOption]

/-- The rule at a looked-up index is the literal. -/
theorem rule_at {rs : List Rule} {i : Nat} {r r₀ : Rule} (h : rs[i]? = some r)
    (h₀ : rs[i]? = some r₀) : r = r₀ :=
  Option.some.inj (h.symm.trans h₀)

theorem sound_bin_ctx1 {op : BinOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop} (iha : SoundAt a) (hD : D = DDerives envF (otherwise envF))
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.binCtx1
      (.tuple [S, con "BIN" [encBinOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.bin op t a b).strict = some v := by
  subst hD
  obtain ⟨w, rfl, hd⟩ := ctx1_inv hb
  obtain ⟨a', rfl, hp⟩ := iha hd
  exact ⟨.bin op t a' b, rfl, strict_bin_l hp⟩

theorem sound_bin_ctx2 {op : BinOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop} (ihb : SoundAt b) (hD : D = DDerives envF (otherwise envF))
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.binCtx2
      (.tuple [S, con "BIN" [encBinOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.bin op t a b).strict = some v := by
  subst hD
  obtain ⟨w, rfl, hd⟩ := ctx2_inv hb
  obtain ⟨b', rfl, hp⟩ := ihb hd
  exact ⟨.bin op t a b', rfl, strict_bin_r hp⟩

theorem sound_bin_bool' {op : BinOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop}
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.binBool
      (.tuple [S, con "BIN" [encBinOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.bin op t a b).strict = some v := by
  obtain ⟨b₁, b₂, w, ha, hb', rfl, htc⟩ := binBool_inv (findDef_fdef rfl) (builtins_envF _) hb
  obtain rfl := enc_eq_bool ha
  obtain rfl := enc_eq_bool hb'
  exact sound_bin_bool ((boolbin_spec op b₁ b₂).iff.1 htc)

theorem sound_bin_num' {op : BinOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop}
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.binNum
      (.tuple [S, con "BIN" [encBinOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.bin op t a b).strict = some v := by
  obtain ⟨ha, hb', htc⟩ := binNum_inv findDef_numbin (builtins_envF _) hb
  exact sound_bin_num ha hb' htc

theorem sound_bin (op : BinOp) (t : OpTyp) (a b : FExp) (iha : SoundAt a) (ihb : SoundAt b) :
    SoundAt (.bin op t a b) := by
  intro S x h
  obtain ⟨i, r, hr, hi, hb⟩ := stepF_rule (c := "BIN") (w := .tuple [encBinOp op, a.enc, b.enc]) h
  rw [headsF_bin] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact sound_bin_ctx1 iha rfl (rule_at hr stepF_3 ▸ hb)
  · exact sound_bin_ctx2 ihb rfl (rule_at hr stepF_4 ▸ hb)
  · exact sound_bin_bool' (rule_at hr stepF_5 ▸ hb)
  · exact sound_bin_num' (rule_at hr stepF_6 ▸ hb)

theorem sound_cmp_num {op : CmpOp} {t : OpTyp} {a b : FExp} {w : Value}
    (ha : TypedIn envF (.varT "num" []) a.enc) (hb : TypedIn envF (.varT "num" []) b.enc)
    (hx : TryClauses envF (fdef "numcmp").2.2 (args3 (encCmpOp op) a.enc b.enc) w) :
    ∃ e' : FExp, con "BOOL" [w] = e'.enc ∧
      ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  obtain ⟨m₁, hm₁, he₁, hs₁⟩ := num_of_typed ha
  obtain ⟨m₂, hm₂, he₂, hs₂⟩ := num_of_typed hb
  rw [he₁, he₂] at hx
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ((numcmp_spec op hm₁ hm₂).iff.1 hx)
  refine close_lit (w := .bool c) rfl trivial ?_
  cases op <;> simp_all [FExp.strict, cmpValues, FExp.resVal, Res.ofOption, Num.cmp]

/-- The four comparison rules on values, given what their test says about values. -/
theorem sound_cmp_val {op : CmpOp} {t : OpTyp} {a b : FExp} {k : CmpOp} {r : Bool}
    (ha : TypedIn envF (.varT "val" []) a.enc) (hb : TypedIn envF (.varT "val" []) b.enc)
    (hc : cmpValues k a.enc b.enc = .ok (.bool true))
    (hk : ∀ u v, IsLitV u → IsLitV v → cmpValues k (encVal u) (encVal v) = .ok (.bool true) →
      cmpValues op u v = .ok (.bool r)) :
    ∃ e' : FExp, con "BOOL" [.bool r] = e'.enc ∧
      ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  obtain ⟨u, hu, he₁, hs₁⟩ := lit_of_typed_val ha
  obtain ⟨v, hv, he₂, hs₂⟩ := lit_of_typed_val hb
  rw [he₁, he₂] at hc
  refine close_lit (w := .bool r) rfl trivial ?_
  simp [FExp.strict, hs₁, hs₂, hk u v hu hv hc, FExp.resVal]

theorem cmp_eq_true {u v : Value} (hu : IsLitV u) (hv : IsLitV v)
    (h : cmpValues .eqOp (encVal u) (encVal v) = .ok (.bool true)) :
    cmpValues .eqOp u v = .ok (.bool true) := by
  have e : encVal u = encVal v := by simpa [cmpValues] using h
  simp [cmpValues, encVal_inj hu hv e]

theorem cmp_eq_false {u v : Value}
    (h : cmpValues .neOp (encVal u) (encVal v) = .ok (.bool true)) :
    cmpValues .eqOp u v = .ok (.bool false) := by
  have e : encVal u ≠ encVal v := by simpa [cmpValues] using h
  have e' : u ≠ v := fun h' => e (congrArg encVal h')
  simp [cmpValues, e']

theorem cmp_ne_false {u v : Value} (hu : IsLitV u) (hv : IsLitV v)
    (h : cmpValues .eqOp (encVal u) (encVal v) = .ok (.bool true)) :
    cmpValues .neOp u v = .ok (.bool false) := by
  have e : encVal u = encVal v := by simpa [cmpValues] using h
  simp [cmpValues, encVal_inj hu hv e]

theorem cmp_ne_true {u v : Value}
    (h : cmpValues .neOp (encVal u) (encVal v) = .ok (.bool true)) :
    cmpValues .neOp u v = .ok (.bool true) := by
  have e : encVal u ≠ encVal v := by simpa [cmpValues] using h
  have e' : u ≠ v := fun h' => e (congrArg encVal h')
  simp [cmpValues, e']

theorem cmpOp_of_EQ {op : CmpOp} (h : encCmpOp op = con "EQ" []) : op = .eqOp := by
  cases op <;> simp_all [encCmpOp, con]

theorem cmpOp_of_NE {op : CmpOp} (h : encCmpOp op = con "NE" []) : op = .neOp := by
  cases op <;> simp_all [encCmpOp, con]

theorem sound_cmp_ctx1 {op : CmpOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop} (iha : SoundAt a) (hD : D = DDerives envF (otherwise envF))
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.cmpCtx1
      (.tuple [S, con "CMP" [encCmpOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  subst hD
  obtain ⟨w, rfl, hd⟩ := ctx1_inv hb
  obtain ⟨a', rfl, hp⟩ := iha hd
  exact ⟨.cmp op t a' b, rfl, strict_cmp_l hp⟩

theorem sound_cmp_ctx2 {op : CmpOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop} (ihb : SoundAt b) (hD : D = DDerives envF (otherwise envF))
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.cmpCtx2
      (.tuple [S, con "CMP" [encCmpOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  subst hD
  obtain ⟨w, rfl, hd⟩ := ctx2_inv hb
  obtain ⟨b', rfl, hp⟩ := ihb hd
  exact ⟨.cmp op t a b', rfl, strict_cmp_r hp⟩

/-- The four comparison rules on values, with the operator the rule's head and test fix. -/
theorem sound_cmp_rule {op : CmpOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop} {nm : IL.Id} {C : MixopS} {r : Bool} {k op₀ : CmpOp}
    (hC : encCmpOp op = con C [] → op = op₀)
    (hk : ∀ u v, IsLitV u → IsLitV v → cmpValues k (encVal u) (encVal v) = .ok (.bool true) →
      cmpValues op₀ u v = .ok (.bool r))
    (hb : RuleBody envF D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []),
      .expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" [])] "%|-%~>%"
      (.tupE [.varE "S", .caseE "CMP" (.tupE [.caseE C (.tupE []),
        .subE (.varE "val_1") (.varT "val" []) (.varT "exp" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "exp" [])]),
        .caseE "BOOL" (.tupE [.boolE r])])
      [.ifPr (.cmpE k .boolT (.varE "val_1") (.varE "val_2"))])
      (.tuple [S, con "CMP" [encCmpOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  obtain ⟨ho, rfl, ha, hb', hc⟩ := cmpVal_inv hb
  obtain rfl := hC ho
  exact sound_cmp_val ha hb' hc hk

theorem sound_cmp_num' {op : CmpOp} {t : OpTyp} {a b : FExp} {S x : Value} {D : Sim.Interp}
    {els : Prop}
    (hb : RuleBody envF D els [] [] "%|-%~>%" Rules.F.cmpNum
      (.tuple [S, con "CMP" [encCmpOp op, a.enc, b.enc], x])) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → (FExp.cmp op t a b).strict = some v := by
  obtain ⟨ha, hb', w, rfl, htc⟩ := cmpNum_inv (findDef_fdef rfl) (builtins_envF _) hb
  exact sound_cmp_num ha hb' htc

theorem sound_cmp (op : CmpOp) (t : OpTyp) (a b : FExp) (iha : SoundAt a) (ihb : SoundAt b) :
    SoundAt (.cmp op t a b) := by
  intro S x h
  obtain ⟨i, r, hr, hi, hb⟩ := stepF_rule (c := "CMP") (w := .tuple [encCmpOp op, a.enc, b.enc]) h
  rw [headsF_cmp] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sound_cmp_ctx1 iha rfl (rule_at hr stepF_7 ▸ hb)
  · exact sound_cmp_ctx2 ihb rfl (rule_at hr stepF_8 ▸ hb)
  · exact sound_cmp_rule cmpOp_of_EQ (fun _ _ hu hv => cmp_eq_true hu hv) (rule_at hr stepF_9 ▸ hb)
  · exact sound_cmp_rule cmpOp_of_EQ (fun _ _ _ _ => cmp_eq_false) (rule_at hr stepF_10 ▸ hb)
  · exact sound_cmp_rule cmpOp_of_NE (fun _ _ hu hv => cmp_ne_false hu hv) (rule_at hr stepF_11 ▸ hb)
  · exact sound_cmp_rule cmpOp_of_NE (fun _ _ _ _ => cmp_ne_true) (rule_at hr stepF_12 ▸ hb)
  · exact sound_cmp_num' (rule_at hr stepF_13 ▸ hb)

/-- **One step is sound.** -/
theorem stepF_sound : ∀ e : FExp, SoundAt e
  | .bool _ => fun h => (stepF_lit headsF_bool h).elim
  | .nat _ => fun h => (stepF_lit headsF_nat h).elim
  | .int _ => fun h => (stepF_lit headsF_int h).elim
  | .un op t a => sound_un op t a (stepF_sound a)
  | .bin op t a b => sound_bin op t a b (stepF_sound a) (stepF_sound b)
  | .cmp op t a b => sound_cmp op t a b (stepF_sound a) (stepF_sound b)

/-- An encoded fragment expression is the encoding of a value only when it is a literal. -/
theorem lit_of_enc_eq {e : FExp} {v : Value} (h : e.enc = encVal v) : e.strict = some v := by
  cases e <;> cases v <;> simp_all [FExp.enc, encVal, encNum, con, FExp.strict] <;>
    rename_i n <;> cases n <;> simp_all

/-- **Their reduction is sound for ours** (fixed script): a reduction from an encoded fragment
expression to the encoding of a value `v` means the expression evaluates, strictly, to `v`. -/
theorem reduceF_sound {S : Value} {e : FExp} {v : Value}
    (h : MReduce envF S e.enc (encVal v)) : e.strict = some v := by
  have key := reduce_rec findRel_reduceF rfl rfl
    (fun _ a c => ∀ e : FExp, a = e.enc → ∀ v, c = encVal v → e.strict = some v)
    (fun _ a e ha v hc => lit_of_enc_eq (ha.symm.trans hc))
    (fun S a b c hab hbc e ha v hc => by
      subst ha
      obtain ⟨e', rfl, hp⟩ := stepF_sound e hab
      exact hp v (hbc e' rfl v hc))
    h
  exact key e rfl v rfl

end Silmaril.Wasm.SpecTec.Meta
