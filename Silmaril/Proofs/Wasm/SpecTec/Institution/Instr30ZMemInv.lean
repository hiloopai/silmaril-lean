module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZMem

/-!
# Module typing of the wasm-3.0 script, `Mem_ok` is exact

`Limits_ok`, `Memtype_ok` and `Mem_ok` have one rule each, with no optional atoms in its
conclusion. Inverting a `DDerivesB` fact of such a relation (`dd_oneRule_inv`) gives a scope in
which the conclusion evaluates to the fact and every premise holds. Reading the scope back from the
conclusion (`EvalExp.unique`):

* `limitsOk_inv`: a `Limits_ok(C, l, k)` fact at the image of Core limits `l` gives Core's
  `l.Valid k`;
* `memtypeOk_inv`: a `Memtype_ok(C, mt)` fact gives `mt.Valid`, the bound `2 ^ ($size(at) - 16)`
  being evaluated by `evalExp_memBound`;
* `memOk_inv`: a `Mem_ok(C, MEMORY mt, v)` fact gives `v = mt` and `mt.Valid`;
* `memOk_iff`: so, in every typed context and every evaluator `simEnv B`, under every reading of
  `otherwise`, `Mem_ok(C, MEMORY mt, v)` holds **exactly** when `v` is `mt` and Core validates `mt`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT ctxP)

variable {B : Builtins}

/-! ## One-rule relations -/

/-- **Inversion of a fact of a one-rule relation without optional atoms in its conclusion.** -/
theorem dd_oneRule_inv {env : Env} {O : ElseI} {x : IL.Id} {op : MixopS} {t : Typ} {nm : IL.Id}
    {qs : List Param} {e : Exp} {prems : List Prem} {v : Value}
    (hrel : env.findRel? x = some ([], op, t, [.ruleD nm qs op e prems]))
    (hc : conclAlts e = [e]) (h : DDerivesB env O x op [] v) :
    ∃ σ : List (IL.Id × Value), EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, DPremB env O (O x [] 0 v) (VarEnv.empty.bindVals σ) pr := by
  cases h with
  | @rule _ _ _ _ _ _ _ i _ _ _ e' _ ρ₀ σ hrel' hrule halt hps _ he hp =>
    rw [hrel] at hrel'
    cases hrel'
    obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
    cases i with
    | zero =>
      obtain ⟨-, -, -, rfl, rfl⟩ := Rule.ruleD.inj (Option.some.inj hrule)
      rw [hc, List.mem_singleton] at halt
      subst halt
      exact ⟨σ, he, hp⟩
    | succ i => simp at hrule

set_option maxRecDepth 100000 in
/-- `Limits_ok` is the one rule `limitsOkRule`. -/
theorem rel_limitsOk : ∃ t, (simEnv B).findRel? "Limits_ok" = some ([], "%|-%:%", t, [limitsOkRule]) :=
  ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- `Memtype_ok` is the one rule `memtypeOkRule`. -/
theorem rel_memtypeOk :
    ∃ t, (simEnv B).findRel? "Memtype_ok" = some ([], "%|-%:OK", t, [memtypeOkRule]) := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- `Mem_ok` is the one rule `memOkRule`. -/
theorem rel_memOk : ∃ t, (simEnv B).findRel? "Mem_ok" = some ([], "%|-%:%", t, [memOkRule]) :=
  ⟨_, rfl⟩

/-! ## Reading values back -/

/-- A three-component tuple expression, inverted. -/
theorem evalExp_tup3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [v₁, v₂, v₃])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h
  obtain rfl := Value.tuple.inj he
  obtain ⟨a, ws, h₁, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ws', h₂, hb, hws'⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain ⟨c, ws'', h₃, hc, hws''⟩ := Equiv.Validation.evalExps_cons_iff.1 hws'
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hws''
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₂
  obtain ⟨rfl, -⟩ := List.cons.inj h₃
  exact ⟨ha, hb, hc⟩

/-- A two-component tuple expression, inverted. -/
theorem evalExp_tup2_inv' {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h
  obtain rfl := Value.tuple.inj he
  obtain ⟨a, ws, h₁, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, ws', h₂, hb, hws'⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hws'
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨rfl, -⟩ := List.cons.inj h₂
  exact ⟨ha, hb⟩

/-- A case expression, inverted at a case value. -/
theorem evalExp_case_inv {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE op e) (.case op w)) : EvalExp env ρ e w := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  obtain ⟨-, rfl⟩ := Value.case.inj he
  exact hu

/-- `%(x)` evaluated to `%(w)` reads `x` as `w`. -/
theorem pctVar_inv {env : Env} {ρ : VarEnv} {x : IL.Id} {w : Value}
    (h : EvalExp env ρ (.caseE "%" (.tupE [.varE x])) (.case "%" (.tuple [w]))) :
    ρ.findVal? x = some w := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 (evalExp_case_inv h)
  obtain rfl := Value.tuple.inj he
  obtain ⟨a, ws, h₁, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hws
  obtain ⟨rfl, -⟩ := List.cons.inj h₁
  exact evalExp_varE_iff.1 ha

/-- `a ≤ b` over two naturals, read back. -/
theorem cmpLe_inv {env : Env} {ρ : VarEnv} {a b : IL.Id} {p q : Nat}
    (ha : ρ.findVal? a = some (natV p)) (hb : ρ.findVal? b = some (natV q))
    (h : EvalExp env ρ (.cmpE .leOp (.numT .natT) (.varE a) (.varE b)) (.bool true)) : p ≤ q := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  obtain rfl : v₁ = natV p := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans ha)
  obtain rfl : v₂ = natV q := Option.some.inj ((evalExp_varE_iff.1 h₂).symm.trans hb)
  simpa [cmpValues, Num.cmp, natV] using hc

/-- One domain `x <- y`, inverted (as `Round7.MemSimd.evalDoms_one_inv`). -/
theorem evalDoms_one_inv' {env : Env} {ρ : VarEnv} {x y : IL.Id} {xvs : List (IL.Id × Value)}
    (h : EvalDoms env ρ [.mk x (.varE y)] xvs) : ∃ w, ρ.findVal? y = some w ∧ xvs = [(x, w)] := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [evalDoms] at hn
  | succ n =>
    simp only [evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc] at hn
    cases h₁ : evalExp n env ρ (.varE y) with
    | error e => simp [h₁] at hn
    | ok v =>
      simp [h₁] at hn
      exact ⟨v, evalExp_varE_iff.1 ⟨n, h₁⟩, hn.symm⟩

/-- The newest binding of `x` is found. -/
theorem findVal_bindVals_one' (ρ : VarEnv) {x : IL.Id} (hx : x ≠ "_") (w : Value) :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, hx]

/-- An older binding of `y ≠ x` is found under a binding of `x`. -/
theorem findVal_bindVals_other (ρ : VarEnv) {x y : IL.Id} (hxy : y ≠ x) (w : Value) :
    (ρ.bindVals [(x, w)]).findVal? y = ρ.findVal? y := by
  by_cases hx : x = "_"
  · simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, hx]
  · simp only [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, hx, ite_false, List.foldl]
    simp [hxy.symm]

/-- `Limits_ok`'s conclusion iteration `(%(m))?`, where `m?` is bound to `o`. -/
theorem evalExp_maxIter {env : Env} {ρ : VarEnv} {o : Option Value}
    (h : ρ.findVal? "m?" = some (.opt o)) :
    EvalExp env ρ (.iterE (.caseE "%" (.tupE [.varE "m"])) (.mk .opt [.mk "m" (.varE "m?")]))
      (.opt (o.map fun w => .case "%" (.tuple [w]))) :=
  IntNumeric.evalExp_iterOpt h
    (fun w hw => ⟨_, by simp [hw], evalExp_case (evalExp_tupE_iff.2 ⟨_,
      evalExps_cons (Sim.evalExp_var (findVal_bindVals_one' _ (by decide) w)) evalExps_nil, rfl⟩)⟩)
    (fun hn => by simp [hn])

/-- `n ≤ m ∧ m ≤ k`, read back. -/
theorem andLe_inv {env : Env} {ρ : VarEnv} {p q r : Nat}
    (hn : ρ.findVal? "n" = some (natV p)) (hm : ρ.findVal? "m" = some (natV q))
    (hk : ρ.findVal? "k" = some (natV r))
    (h : EvalExp env ρ (.binE .andOp .boolT (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "m"))
      (.cmpE .leOp (.numT .natT) (.varE "m") (.varE "k"))) (.bool true)) : p ≤ q ∧ q ≤ r := by
  obtain ⟨v₁, h₁, hs⟩ := evalExp_binE_iff.1 h
  obtain ⟨u₁, u₂, e₁, e₂, c₁⟩ := evalExp_cmpE_iff.1 h₁
  obtain rfl : u₁ = natV p := Option.some.inj ((evalExp_varE_iff.1 e₁).symm.trans hn)
  obtain rfl : u₂ = natV q := Option.some.inj ((evalExp_varE_iff.1 e₂).symm.trans hm)
  have hv₁ : v₁ = .bool (decide (p ≤ q)) := by
    simpa [cmpValues, Num.cmp, natV] using c₁.symm
  subst hv₁
  by_cases hpq : p ≤ q
  · show p ≤ q ∧ q ≤ r
    rcases hs with hs | ⟨-, v₂, h₂, hb⟩
    · simp [boolShort, hpq] at hs
    · obtain ⟨w₁, w₂, f₁, f₂, c₂⟩ := evalExp_cmpE_iff.1 h₂
      obtain rfl : w₁ = natV q := Option.some.inj ((evalExp_varE_iff.1 f₁).symm.trans hm)
      obtain rfl : w₂ = natV r := Option.some.inj ((evalExp_varE_iff.1 f₂).symm.trans hk)
      have hv₂ : v₂ = .bool (decide (q ≤ r)) := by
        simpa [cmpValues, Num.cmp, natV] using c₂.symm
      subst hv₂
      exact ⟨hpq, by simpa [binValues, boolBin, hpq, Res.ofOption] using hb⟩
  · rcases hs with hs | ⟨hs, -⟩
    · simp [boolShort, hpq] at hs
    · simp [boolShort, hpq] at hs

/-- `domSomes` at one domain, inverted. -/
theorem domSomes_one_inv {x : IL.Id} {w : Value} {row : List (IL.Id × Value)}
    (hs : domSomes [(x, w)] = some row) : ∃ u, w = .opt (some u) ∧ row = [(x, u)] := by
  cases w with
  | opt o =>
    cases o with
    | some u => exact ⟨u, rfl, by simpa [domSomes] using hs.symm⟩
    | none => simp [domSomes] at hs
  | _ => simp [domSomes] at hs

/-- `Limits_ok`'s iterated premise with the maximum `M` read back: `n ≤ M ≤ k`. -/
theorem limMaxSome_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {n M k : Nat} {u : Value}
    (fn : ρ.findVal? "n" = some (natV n)) (fk : ρ.findVal? "k" = some (natV k))
    (hu : u = natV M) (h : DPremB (simEnv B) O els (ρ.bindVals [("m", u)])
      (.ifPr (.binE .andOp .boolT (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "m"))
        (.cmpE .leOp (.numT .natT) (.varE "m") (.varE "k"))))) : n ≤ M ∧ M ≤ k := by
  subst hu
  cases h with
  | ifPr hc =>
    exact andLe_inv (by rw [findVal_bindVals_other _ (by decide)]; exact fn)
      (findVal_bindVals_one' _ (by decide) _)
      (by rw [findVal_bindVals_other _ (by decide)]; exact fk) hc

/-- **`Limits_ok`'s iterated premise, inverted**: at a maximum `M`, `n ≤ M ≤ k`. -/
theorem limMax_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {l : Silmaril.Wasm.Limits} {k : Nat}
    (hm : EvalExp (simEnv B) ρ (.iterE (.caseE "%" (.tupE [.varE "m"]))
      (.mk .opt [.mk "m" (.varE "m?")])) (.opt (l.max.map fun m => .case "%" (.tuple [natV m.val]))))
    (fn : ρ.findVal? "n" = some (natV l.min.val)) (fk : ρ.findVal? "k" = some (natV k))
    (h : DPremB (simEnv B) O els ρ limMaxPr) :
    ∀ M, l.max = some M → l.min.val ≤ M.val ∧ M.val ≤ k := by
  intro M hM
  cases h with
  | iterOptNone hd _ hall =>
    obtain ⟨w, hw, rfl⟩ := evalDoms_one_inv' hd
    obtain rfl : w = .opt none := hall _ List.mem_cons_self
    have hu := EvalExp.unique hm (evalExp_maxIter hw)
    simp [hM] at hu
  | @iterOptSome _ _ _ _ _ row hd _ hs hpr =>
    obtain ⟨w, hw, rfl⟩ := evalDoms_one_inv' hd
    obtain ⟨u, rfl, rfl⟩ := domSomes_one_inv hs
    have hu := EvalExp.unique hm (evalExp_maxIter hw)
    exact limMaxSome_inv fn fk (by simpa [hM] using hu.symm) hpr
  | iterList hit => simp at hit

/-- **A `Limits_ok(C, l, k)` fact at the image of Core limits gives `l.Valid k`.** -/
theorem limitsOk_inv {O : ElseI} {c : Value} {l : Silmaril.Wasm.Limits} {k : Nat}
    (h : DDerivesB (simEnv B) O "Limits_ok" "%|-%:%" [] (.tuple [c, Encode.toValue l, natV k])) :
    l.Valid k := by
  obtain ⟨t, hrel⟩ := rel_limitsOk (B := B)
  obtain ⟨σ, he, hp⟩ := dd_oneRule_inv hrel rfl h
  obtain ⟨-, hl, hk⟩ := evalExp_tup3_inv he
  rw [toValue_limits] at hl
  obtain ⟨hn, hm⟩ := evalExp_tup2_inv' (evalExp_case_inv hl)
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (natV l.min.val) := pctVar_inv hn
  have fk : (VarEnv.empty.bindVals σ).findVal? "k" = some (natV k) := evalExp_varE_iff.1 hk
  have hle : l.min.val ≤ k := by
    have h₁ := hp _ List.mem_cons_self
    cases h₁ with
    | ifPr h₁ => exact cmpLe_inv fn fk h₁
  have hmax : ∀ M, l.max = some M → l.min.val ≤ M.val ∧ M.val ≤ k :=
    limMax_inv hm fn fk (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine ⟨hle, ?_⟩
  cases hmx : l.max with
  | none => trivial
  | some M => exact hmax M hmx

/-- **A `Memtype_ok(C, mt)` fact at the image of a Core memory type gives `mt.Valid`.** -/
theorem memtypeOk_inv {O : ElseI} {c : Value} {mt : Silmaril.Wasm.MemoryType}
    (h : DDerivesB (simEnv B) O "Memtype_ok" "%|-%:OK" [] (.tuple [c, Encode.toValue mt])) :
    mt.Valid := by
  obtain ⟨t, hrel⟩ := rel_memtypeOk (B := B)
  obtain ⟨σ, he, hp⟩ := dd_oneRule_inv hrel rfl h
  obtain ⟨hC, hm⟩ := evalExp_tup2_inv' he
  rw [toValue_memtype] at hm
  obtain ⟨ha, hl⟩ := evalExp_tup2_inv' (evalExp_case_inv hm)
  have hlim : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.varE "C", .varE "limits", memBoundE])
      (.tuple [c, Encode.toValue mt.limits, natV (2 ^ (mt.address.width - 16))]) :=
    evalExp_tup3 hC hl (evalExp_memBound (Memory.findDef_bindVals_empty _ _) mt.address
      (evalExp_varE_iff.1 ha))
  have hpr := hp _ List.mem_cons_self
  cases hpr with
  | rulePr hargs hw hd =>
    obtain rfl := evalArgs_nil_iff.1 hargs
    obtain rfl := EvalExp.unique hw hlim
    exact limitsOk_inv hd

/-- **A `Mem_ok(C, MEMORY mt, v)` fact at the image of a Core memory type gives `v = mt` and
`mt.Valid`.** -/
theorem memOk_inv {O : ElseI} {c v : Value} {mt : Silmaril.Wasm.MemoryType}
    (h : DDerivesB (simEnv B) O "Mem_ok" "%|-%:%" []
      (.tuple [c, .case "MEMORY" (Encode.toValue mt), v])) :
    v = Encode.toValue mt ∧ mt.Valid := by
  obtain ⟨t, hrel⟩ := rel_memOk (B := B)
  obtain ⟨σ, he, hp⟩ := dd_oneRule_inv hrel rfl h
  obtain ⟨hC, hm, hv⟩ := evalExp_tup3_inv he
  have fm := evalExp_varE_iff.1 (evalExp_case_inv hm)
  obtain rfl : v = Encode.toValue mt := Option.some.inj ((evalExp_varE_iff.1 hv).symm.trans fm)
  refine ⟨rfl, ?_⟩
  have hpr := hp _ List.mem_cons_self
  cases hpr with
  | rulePr hargs hw hd =>
    obtain rfl := evalArgs_nil_iff.1 hargs
    obtain rfl := EvalExp.unique hw (evalExp_tup2 hC (Sim.evalExp_var fm))
    exact memtypeOk_inv hd

/-- **`Mem_ok` is exact at Core's memory types**: in every typed context, every evaluator
`simEnv B` and under every reading of `otherwise`, `Mem_ok(C, MEMORY mt, v)` holds exactly when
`v` is `mt` and Core validates `mt`. -/
theorem memOk_iff (O : ElseI) {c : Value} (hc : CtxT B c) (mt : Silmaril.Wasm.MemoryType)
    (v : Value) :
    DDerivesB (simEnv B) O "Mem_ok" "%|-%:%" [] (.tuple [c, .case "MEMORY" (Encode.toValue mt), v]) ↔
      v = Encode.toValue mt ∧ mt.Valid :=
  ⟨memOk_inv, fun ⟨hv, hval⟩ => hv ▸ dd_memOk O hc hval⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
