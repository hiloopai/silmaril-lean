module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Table
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# The out-of-bounds stores, backward (`Step` 18, 20)

`store-num-oob` (integer and float stores) and `store-pack-oob`. The premise reads
`$mem(z, x).BYTES`, which evaluates only when the module lists `x` and the store holds the
memory (`mem_inv`, Core's `s.mem? f x`). The access end `i + ao.OFFSET + width / 8` is evaluated
forward with the memory track's lemmas and compared by `EvalExp.unique`. The `STORE` image is
decoded by `head_store` and the injectivity of the number-type encoding (`numType_inj`). Needs `B`
not to interpret `$mem` (true of `Prims.builtins`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

theorem head_store {a : Admin} (h : Typing.adminHead a = "STORE") :
    (∃ t p m arg, a = .plain (.intStore t p m arg)) ∨ (∃ t m arg, a = .plain (.floatStore t m arg)) := by
  revert h
  admin_head_inv

/-- The number-type encoding is injective. -/
theorem numType_inj {t t' : NumType} (h : Encode.toValue t = Encode.toValue t') : t = t' := by
  rw [Typing.toValue_numType, Typing.toValue_numType] at h
  rcases t with t | t <;> rcases t' with t' | t' <;> cases t <;> cases t' <;>
    simp_all [Vec.numTypeV, caseNilV]

/-- A `CONST nt c` element of a left-hand side: a numeric constant whose type `nt` is bound to. -/
theorem const_of_lhs {env : Env} {ρ : VarEnv} {ent ec : Exp} {a : Admin} {NT : Value}
    (hnt : EvalExp env ρ ent NT) (h : EvalExp env ρ (.caseE "CONST" (.tupE [ent, ec])) (adminToV a)) :
    (∃ t c, a = .plain (.intConst t c) ∧ NT = Encode.toValue (NumType.int t)) ∨
      (∃ t c, a = .plain (.floatConst t c) ∧ NT = Encode.toValue (NumType.float t)) := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  obtain ⟨u₁, u₂, hu₁, -, rfl⟩ := State.evalExp_tup2_inv hu
  have e₁ : u₁ = NT := EvalExp.unique hu₁ hnt
  rcases Typing.head_const (Typing.adminToV_case he).symm with ⟨t, c, rfl⟩ | ⟨t, c, rfl⟩
  · have he' : Value.case "CONST" (.tuple [Encode.toValue (NumType.int t), pctV c.toNat]) =
        .case "CONST" (.tuple [u₁, u₂]) := he
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
    exact .inl ⟨t, c, rfl, e₁ ▸ he'.1.symm⟩
  · have he' : Value.case "CONST" (.tuple [Encode.toValue (NumType.float t), Sim.floatV t c]) =
        .case "CONST" (.tuple [u₁, u₂]) := he
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
    exact .inr ⟨t, c, rfl, e₁ ▸ he'.1.symm⟩

/-- The payload of a `STORE` element of a left-hand side `STORE (nt, p, x, ao)`. -/
theorem storePayload {env : Env} {ρ : VarEnv} {ent ep : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE "STORE" (.tupE [ent, ep, .varE "x", .varE "ao"])) (adminToV a)) :
    ∃ NT P X AO, EvalExp env ρ ent NT ∧ EvalExp env ρ ep P ∧ ρ.findVal? "x" = some X ∧
      ρ.findVal? "ao" = some AO ∧ adminToV a = .case "STORE" (.tuple [NT, P, X, AO]) := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨NT, vs₁, h₁, hvs₁, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs
  obtain ⟨P, vs₂, h₂, hvs₂, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs₁
  obtain ⟨X, vs₃, h₃, hvs₃, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs₂
  obtain ⟨AO, vs₄, h₄, hvs₄, rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hvs₃
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hvs₄
  exact ⟨NT, P, X, AO, h₁, h₂, evalExp_varE_iff.1 h₃, evalExp_varE_iff.1 h₄, he⟩

variable (B)
variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **`$mem(z, x)`, inverted**: the module lists `x` and the store holds the memory. -/
theorem mem_inv (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat} {M : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (h : EvalExp (simEnv B) ρ (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) M) :
    ∃ ma mi, f.module.mems[k]? = some ma ∧ s.mems[ma]? = some mi ∧ M = memInstToValue mi := by
  have D := State.stateDefs_simEnv B
  have hbody := evalExp_call1_inv D.mem (Prims.findDef_none_of_valsOnly hρ _) (hb _ _)
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx) evalArgs_nil))
    State.matchArgs_zxPat h
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hbody
  have eL : L = .list (s.mems.map memInstToValue) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, State.evalExp_sof D rfl (evalExp_var rfl),
      State.storeV_MEMS hn s⟩)
  obtain ⟨ma, hma, hj'⟩ := moduleIdx_inv D rfl rfl rfl (State.moduleV_MEMS _) hj
  have hj'' : j = ma := by simpa using hj'
  have hLt : (s.mems.map memInstToValue)[ma]? = some M := by
    rw [eL, hj''] at hLj
    exact hLj
  rw [List.getElem?_map] at hLt
  obtain ⟨mi, hmi, he⟩ := Option.map_eq_some_iff.1 hLt
  exact ⟨ma, mi, hma, hmi, he.symm⟩

/-- The premise `N > |$mem(z, x).BYTES|`, read back, given the access end `N`. -/
theorem memPrem_inv (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k N : Nat} {eN : Exp}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (hN : EvalExp (simEnv B) ρ eN (.num (.natN N)))
    (h : EvalExp (simEnv B) ρ (.cmpE .gtOp (.numT .natT) eN
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true)) :
    ∃ ma mi, f.module.mems[k]? = some ma ∧ s.mems[ma]? = some mi ∧ mi.bytes.size < N := by
  obtain ⟨v₁, v₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 h
  have ev₁ : v₁ = .num (.natN N) := EvalExp.unique e₁ hN
  obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.1 e₂
  obtain ⟨M, hM, hMf⟩ := evalExp_dotE_iff.1 hvs
  obtain ⟨ma, mi, hma, hmi, rfl⟩ := mem_inv B hb hρ fz fx hM
  have evs : vs = Memory.bytesL mi.bytes := by
    simpa [Memory.memInstV_BYTES] using hMf.symm
  have hlt : mi.bytes.size < N := by
    simpa [ev₁, evs, cmpValues, Num.cmp, Res.ofOption] using hc
  exact ⟨ma, mi, hma, hmi, hlt⟩

/-- An integer `STORE` image, read off. -/
theorem intStore_image {t : IntType} {p : Option PackSize} {m : MemIdx} {arg : MemArg}
    {NT Pv X AO : Value}
    (he : adminToV (.plain (.intStore t p m arg)) = .case "STORE" (.tuple [NT, Pv, X, AO])) :
    NT = Encode.toValue (NumType.int t) ∧ Pv = .opt (p.map fun q => .case "%" (.tuple [szV q])) ∧
      X = .case "%" (.tuple [.num (.natN m.toNat)]) ∧ AO = memargV arg := by
  have he' : Value.case "STORE" (.tuple [Encode.toValue (NumType.int t),
      .opt (p.map fun q => .case "%" (.tuple [szV q])), Encode.toValue m, memargV arg]) =
      .case "STORE" (.tuple [NT, Pv, X, AO]) := he
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
  exact ⟨he'.1.symm, he'.2.1.symm, he'.2.2.1.symm, he'.2.2.2.symm⟩

/-- A float `STORE` image, read off. -/
theorem floatStore_image {t : FloatType} {m : MemIdx} {arg : MemArg} {NT Pv X AO : Value}
    (he : adminToV (.plain (.floatStore t m arg)) = .case "STORE" (.tuple [NT, Pv, X, AO])) :
    NT = Encode.toValue (NumType.float t) ∧ Pv = .opt none ∧
      X = .case "%" (.tuple [.num (.natN m.toNat)]) ∧ AO = memargV arg := by
  have he' : Value.case "STORE" (.tuple [Encode.toValue (NumType.float t), .opt none,
      Encode.toValue m, memargV arg]) = .case "STORE" (.tuple [NT, Pv, X, AO]) := he
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
  exact ⟨he'.1.symm, he'.2.1.symm, he'.2.2.1.symm, he'.2.2.2.symm⟩

/-- The constant stored by a `STORE` of number type `NT`: of that type. -/
theorem const_int_of {env : Env} {ρ : VarEnv} {ent ec : Exp} {a : Admin} {t : IntType}
    (hnt : EvalExp env ρ ent (Encode.toValue (NumType.int t)))
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [ent, ec])) (adminToV a)) :
    ∃ c : BitVec t.width, a = .plain (.intConst t c) := by
  rcases const_of_lhs hnt h with ⟨t', c, rfl, he⟩ | ⟨t', c, rfl, he⟩
  · obtain rfl : t = t' := by simpa using numType_inj he
    exact ⟨c, rfl⟩
  · exact absurd (numType_inj he) (by simp)

/-- The constant stored by a float `STORE`. -/
theorem const_float_of {env : Env} {ρ : VarEnv} {ent ec : Exp} {a : Admin} {t : FloatType}
    (hnt : EvalExp env ρ ent (Encode.toValue (NumType.float t)))
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [ent, ec])) (adminToV a)) :
    ∃ c : BitVec t.width, a = .plain (.floatConst t c) := by
  rcases const_of_lhs hnt h with ⟨t', c, rfl, he⟩ | ⟨t', c, rfl, he⟩
  · exact absurd (numType_inj he) (by simp)
  · obtain rfl : t = t' := by simpa using numType_inj he
    exact ⟨c, rfl⟩

/-- `Backward.step 18` at an integer store. -/
theorem bwd_storeNumOob_int (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {at_ : AddrType}
    {i : BitVec at_.intType.width} {t : IntType} {m : MemIdx} {arg : MemArg} {a₂ : Admin}
    {w : Value} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Encode.toValue (NumType.int t)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (.case "%" (.tuple [.num (.natN m.toNat)])))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (h₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.varE "nt", .varE "c"])) (adminToV a₂))
    (hw : w = configV hn ⟨s, f, [.trap]⟩)
    (hp : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"))) (.bool true)) :
    BwdP hn P host ⟨s, f, [aconst at_ i, a₂, .plain (.intStore t none m arg)]⟩ w := by
  obtain ⟨c, rfl⟩ := const_int_of (evalExp_var fnt) h₂
  have hN := RefsGC.evalExp_addNat (t := .numT .natT) (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
    (Memory.evalExp_widthInt (State.growDefs_simEnv B) t (evalExp_var fnt))
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_inv B hb (valsOnly_bindVals σ) fz fx hN hp
  have hm : s.mem? f m = some (ma, mi) := by simp [Store.mem?, hma, hmi]
  exact ⟨_, hw, .memory (.storeIntOob hm (by simpa [effAddr] using hlt))⟩

/-- `Backward.step 18` at a float store. -/
theorem bwd_storeNumOob_float (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {at_ : AddrType}
    {i : BitVec at_.intType.width} {t : FloatType} {m : MemIdx} {arg : MemArg} {a₂ : Admin}
    {w : Value} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fnt : (VarEnv.empty.bindVals σ).findVal? "nt" = some (Encode.toValue (NumType.float t)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (.case "%" (.tuple [.num (.natN m.toNat)])))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (h₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.varE "nt", .varE "c"])) (adminToV a₂))
    (hw : w = configV hn ⟨s, f, [.trap]⟩)
    (hp : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"))) (.bool true)) :
    BwdP hn P host ⟨s, f, [aconst at_ i, a₂, .plain (.floatStore t m arg)]⟩ w := by
  obtain ⟨c, rfl⟩ := const_float_of (evalExp_var fnt) h₂
  have hN := RefsGC.evalExp_addNat (t := .numT .natT) (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
    (Memory.evalExp_div8 (by cases t <;> simp [FloatType.width])
      (Memory.evalExp_sizeFloat (Memory.sizeDefs_simEnv B)
        (Prims.findDef_none_of_valsOnly (valsOnly_bindVals σ) _) t (evalExp_var fnt)))
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_inv B hb (valsOnly_bindVals σ) fz fx hN hp
  have hm : s.mem? f m = some (ma, mi) := by simp [Store.mem?, hma, hmi]
  exact ⟨_, hw, .memory (.storeFloatOob hm (by simpa [effAddr] using hlt))⟩

/-- `Backward.step 18` (`store-num-oob`). -/
theorem bwd_storeNumOob (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {c : Config H} {w : Value} (hf : Fires (simEnv B) "Step" 18 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv B).storeNumOob hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨NT, Pv, X, AO, hNT, hP, fx, fao, he⟩ := storePayload h₃
  have hw : w = configV hn ⟨s, f, [.trap]⟩ := EvalExp.unique hr (by beval)
  have hif := RefsGC.premW_if (hp _ (List.mem_singleton_self _))
  have ePv : Pv = .opt none := EvalExp.unique hP (evalExp_optE_none_iff.2 rfl)
  rcases head_store (Typing.adminToV_case he).symm with ⟨t, p, m, arg, rfl⟩ | ⟨t, m, arg, rfl⟩
  · obtain ⟨rfl, hp', rfl, rfl⟩ := intStore_image he
    obtain rfl : p = none := by cases p <;> simp_all
    exact bwd_storeNumOob_int B hb fz fi (evalExp_varE_iff.1 hNT) fx fao h₂ hw hif
  · obtain ⟨rfl, -, rfl, rfl⟩ := floatStore_image he
    exact bwd_storeNumOob_float B hb fz fi (evalExp_varE_iff.1 hNT) fx fao h₂ hw hif

/-- The pack-width payload `?(% (% n))` of a `STORE`, read back at a Core pack size. -/
theorem packWidth_of {env : Env} {ρ : VarEnv} {p : Option PackSize}
    (h : EvalExp env ρ (.optE (some (.caseE "%" (.tupE [.caseE "%" (.tupE [.varE "n"])]))))
      (.opt (p.map fun q => .case "%" (.tuple [szV q])))) :
    ∃ q, p = some q ∧ ρ.findVal? "n" = some (.num (.natN q.width)) := by
  obtain ⟨u, hu, he⟩ := evalExp_optE_some_iff.1 h
  cases p with
  | none => simp at he
  | some q =>
      have eu : u = .case "%" (.tuple [pctV q.width]) := by simpa [szV] using he.symm
      have h₁ := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv (eu ▸ hu)))).1
      have h₂ := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv h₁))).1
      exact ⟨q, rfl, evalExp_varE_iff.1 h₂⟩

/-- `Backward.step 20` at a Core pack store. -/
theorem bwd_storePackOob_int (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {at_ : AddrType}
    {i : BitVec at_.intType.width} {t : IntType} {q : PackSize} {m : MemIdx} {arg : MemArg}
    {a₂ : Admin} {ent : Exp} {w : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (hnt : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ent (Encode.toValue (NumType.int t)))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN q.width)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (.case "%" (.tuple [.num (.natN m.toNat)])))
    (fao : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV arg))
    (h₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [ent, .varE "c"])) (adminToV a₂))
    (hw : w = configV hn ⟨s, f, [.trap]⟩)
    (hp : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "n") .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"))) (.bool true)) :
    BwdP hn P host ⟨s, f, [aconst at_ i, a₂, .plain (.intStore t (some q) m arg)]⟩ w := by
  obtain ⟨c, rfl⟩ := const_int_of hnt h₂
  have hN := RefsGC.evalExp_addNat (env := simEnv B) (t := .numT .natT)
    (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
    (Memory.evalExp_div8 (by cases q <;> simp [PackSize.width]) (evalExp_var fn))
  obtain ⟨ma, mi, hma, hmi, hlt⟩ := memPrem_inv B hb (valsOnly_bindVals σ) fz fx hN hp
  have hm : s.mem? f m = some (ma, mi) := by simp [Store.mem?, hma, hmi]
  exact ⟨_, hw, .memory (.storePackOob hm (by simpa [effAddr] using hlt))⟩

/-- `Backward.step 20` (`store-pack-oob`). -/
theorem bwd_storePackOob (hb : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none)
    {c : Config H} {w : Value} (hf : Fires (simEnv B) "Step" 20 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv B).storePackOob hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨NT, Pv, X, AO, hNT, hP, fx, fao, he⟩ := storePayload h₃
  have hw : w = configV hn ⟨s, f, [.trap]⟩ := EvalExp.unique hr (by beval)
  have hif := RefsGC.premW_if (hp _ (List.mem_singleton_self _))
  rcases head_store (Typing.adminToV_case he).symm with ⟨t, p, m, arg, rfl⟩ | ⟨t, m, arg, rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := intStore_image he
    obtain ⟨q, rfl, fn⟩ := packWidth_of hP
    exact bwd_storePackOob_int B hb fz fi hNT fn fx fao h₂ hw hif
  · obtain ⟨-, rfl, -, -⟩ := floatStore_image he
    obtain ⟨u, -, hu⟩ := evalExp_optE_some_iff.1 hP
    simp at hu

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
