module

public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Defs

/-!
# Round 5: the aggregate out-of-bounds traps, backward

`Step_read` 78 (`array.get-oob`), 88, 89 (`array.copy-oob1`/`-oob2`), 94 (`array.init_elem-oob1`)
and 99 (`array.init_data-oob1`). Each premise evaluates `|$arrayinst(z)[a].FIELDS|` for the one
array Core's trap rule reads, so that array exists (`arrayLen_inv`); Core's trap rules need
nothing else. No validity is used.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (ReadValid decode_refArray decode_aconst_at)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_arrayCopy {a : Admin} (h : Typing.adminHead a = "ARRAY.COPY") :
    ∃ x y, a = .plain (.arrayCopy x y) := by
  revert h
  admin_head_inv

/-- The image of a six-instruction sequence. -/
theorem adminsToV_eq_six {is : List Admin} {v₁ v₂ v₃ v₄ v₅ v₆ : Value}
    (h : adminsToV is = [v₁, v₂, v₃, v₄, v₅, v₆]) :
    ∃ a₁ a₂ a₃ a₄ a₅ a₆, is = [a₁, a₂, a₃, a₄, a₅, a₆] ∧ adminToV a₁ = v₁ ∧ adminToV a₂ = v₂ ∧
      adminToV a₃ = v₃ ∧ adminToV a₄ = v₄ ∧ adminToV a₅ = v₅ ∧ adminToV a₆ = v₆ := by
  obtain ⟨a₁, is₁, rfl, h₁, hc₁⟩ := BwdRead.adminsToV_eq_cons h
  obtain ⟨a₂, a₃, a₄, a₅, a₆, rfl, h₂, h₃, h₄, h₅, h₆⟩ := BwdRead.adminsToV_eq_quint hc₁
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩

variable (B : Builtins)

/-- **`|$arrayinst(z)[a].FIELDS|` on an encoded state, read back**, at any name of the address
variable: the array exists. -/
theorem arrayLen_inv {σ : List (IL.Id × Value)} {xa : IL.Id} {s : Store H} {f : Frame} {k : Nat}
    {v : Value} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fa : (VarEnv.empty.bindVals σ).findVal? xa = some (.num (.natN k)))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE xa)) "FIELDS")) v) :
    ∃ ai, s.arrays[k]? = some ai ∧ v = .num (.natN ai.fields.length) := by
  obtain ⟨fs, hfs, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨R, hR, hRF⟩ := evalExp_dotE_iff.1 hfs
  obtain ⟨Ls, j, hLs, hj, hidx⟩ := evalExp_idxE_iff.1 hR
  have eLs : Ls = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hLs (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B) rfl
      (evalExp_var fz))
  have ej : j = k := by
    have := EvalExp.unique hj (evalExp_var fa)
    simpa using this
  subst eLs ej
  have hmap : (s.arrays[j]?).map arrayInstV = some R := by simpa [Value.idx?] using hidx
  obtain ⟨ai, ha, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have efs : fs = ai.fields.map fieldValV := by simpa [arrayInstV] using hRF.symm
  subst efs
  exact ⟨ai, ha, by simp⟩

/-- **`Step_read` 78 (`array.get-oob`), backward.** -/
theorem bwdV_arrayGetOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 78 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayGetOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  have hc : ∃ G, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]), .case "ARRAY.GET" G]]) ∧
      w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨G, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨sx, x, rfl⟩ := BwdRead.head_arrayGet (Typing.adminToV_case h₃).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa e₂
  have ev₁ : v₁ = .num (.natN i.toNat) := EvalExp.unique e₁ (RefsGC.evalExp_unpct (evalExp_var fi))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hw, ?_⟩
  exact .aggregate (.arrayGetOob ha (BwdRead.ge_nat_inv hcmp))

/-- **`Step_read` 88 (`array.copy-oob1`), backward.** -/
theorem bwdV_arrayCopyOob₁ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 88 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayCopyOob1 hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A₁, fa₁, -⟩ := hq "a_1" (.varT "addr" []) (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" State.num32T (by simp)
  obtain ⟨A₂, fa₂, -⟩ := hq "a_2" (.varT "addr" []) (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  have hc : ∃ X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A₁, .case "CONST" (.tuple [.case "I32" (.tuple []), I₁]),
      .case "REF.ARRAY_ADDR" A₂, .case "CONST" (.tuple [.case "I32" (.tuple []), I₂]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨X, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := adminsToV_eq_six hcode
  obtain ⟨k₁, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i₁, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨k₂, rfl, rfl⟩ := decode_refArray h₃
  obtain ⟨i₂, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₄
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₅
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x₁, x₂, rfl⟩ := head_arrayCopy (Typing.adminToV_case h₆).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa₁ e₂
  have ev₁ : v₁ = .num (.natN (i₁.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₁))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hw, ?_⟩
  exact .aggregate (.arrayCopyOob₁ ha (BwdRead.gt_nat_inv hcmp))

/-- **`Step_read` 89 (`array.copy-oob2`), backward.** -/
theorem bwdV_arrayCopyOob₂ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 89 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayCopyOob2 hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A₁, fa₁, -⟩ := hq "a_1" (.varT "addr" []) (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" State.num32T (by simp)
  obtain ⟨A₂, fa₂, -⟩ := hq "a_2" (.varT "addr" []) (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  have hc : ∃ X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A₁, .case "CONST" (.tuple [.case "I32" (.tuple []), I₁]),
      .case "REF.ARRAY_ADDR" A₂, .case "CONST" (.tuple [.case "I32" (.tuple []), I₂]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨X, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := adminsToV_eq_six hcode
  obtain ⟨k₁, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i₁, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨k₂, rfl, rfl⟩ := decode_refArray h₃
  obtain ⟨i₂, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₄
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₅
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x₁, x₂, rfl⟩ := head_arrayCopy (Typing.adminToV_case h₆).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa₂ e₂
  have ev₁ : v₁ = .num (.natN (i₂.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi₂))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hw, ?_⟩
  exact .aggregate (.arrayCopyOob₂ ha (BwdRead.gt_nat_inv hcmp))

/-- **`Step_read` 94 (`array.init_elem-oob1`), backward.** -/
theorem bwdV_arrayInitElemOob₁ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 94 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayInitElemOob1 hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  have hc : ∃ X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_ELEM" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨X, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitElem (Typing.adminToV_case h₅).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa e₂
  have ev₁ : v₁ = .num (.natN (i.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hw, ?_⟩
  exact .aggregate (.arrayInitElemOob₁ ha (BwdRead.gt_nat_inv hcmp))

/-- **`Step_read` 99 (`array.init_data-oob1`), backward.** -/
theorem bwdV_arrayInitDataOob₁ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 99 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayInitDataOob1 hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  have hc : ∃ X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_DATA" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨X, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitData (Typing.adminToV_case h₅).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa e₂
  have ev₁ : v₁ = .num (.natN (i.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hw, ?_⟩
  exact .aggregate (.arrayInitDataOob₁ ha (BwdRead.gt_nat_inv hcmp))

/-- **`Step_read` 86 (`array.copy-null1`), backward.** No premise. -/
theorem bwdV_arrayCopyNull₁ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 86 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayCopyNull1 hf)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  have hc : ∃ Z I₁ I₂ N X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      caseNilV "REF.NULL_ADDR", .case "CONST" (.tuple [caseNilV "I32", I₁]), R,
      .case "CONST" (.tuple [caseNilV "I32", I₂]),
      .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" X]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨Z, I₁, I₂, N, X, hcfg, hw⟩ := hc
  obtain ⟨-, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := adminsToV_eq_six hcode
  obtain rfl := (Typing.ctrlDecode_simEnv B).refNull a₁ h₁
  obtain ⟨i₁, rfl⟩ := BwdRead.decode_constI32 h₂
  obtain ⟨r, rfl⟩ := BwdPureStep.ref_of_typed (valsOnly_bindVals σ) (h₃ ▸ hR)
  obtain ⟨i₂, rfl⟩ := BwdRead.decode_constI32 h₄
  obtain ⟨n, rfl⟩ := BwdRead.decode_constI32 h₅
  obtain ⟨x₁, x₂, rfl⟩ := head_arrayCopy (Typing.adminToV_case h₆).symm
  exact ⟨[.trap], BwdRead.trap_out hw, .aggregate .arrayCopyNull₁⟩

/-- **`Step_read` 87 (`array.copy-null2`), backward.** No premise. -/
theorem bwdV_arrayCopyNull₂ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 87 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayCopyNull2 hf)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  have hc : ∃ Z I₁ I₂ N X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      R, .case "CONST" (.tuple [caseNilV "I32", I₁]), caseNilV "REF.NULL_ADDR",
      .case "CONST" (.tuple [caseNilV "I32", I₂]),
      .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" X]]) ∧ w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨Z, I₁, I₂, N, X, hcfg, hw⟩ := hc
  obtain ⟨-, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := adminsToV_eq_six hcode
  obtain ⟨r, rfl⟩ := BwdPureStep.ref_of_typed (valsOnly_bindVals σ) (h₁ ▸ hR)
  obtain ⟨i₁, rfl⟩ := BwdRead.decode_constI32 h₂
  obtain rfl := (Typing.ctrlDecode_simEnv B).refNull a₃ h₃
  obtain ⟨i₂, rfl⟩ := BwdRead.decode_constI32 h₄
  obtain ⟨n, rfl⟩ := BwdRead.decode_constI32 h₅
  obtain ⟨x₁, x₂, rfl⟩ := head_arrayCopy (Typing.adminToV_case h₆).symm
  exact ⟨[.trap], BwdRead.trap_out hw, .aggregate .arrayCopyNull₂⟩

theorem head_arrayNewElem {a : Admin} (h : Typing.adminHead a = "ARRAY.NEW_ELEM") :
    ∃ x y, a = .plain (.arrayNewElem x y) := by
  revert h
  admin_head_inv

variable (NA : BwdRead.NoAcc B)
include NA

/-- **`Step_read` 95 (`array.init_elem-oob2`), backward.** The premise evaluates
`|$elem(z, y).REFS|`, so the segment resolves. -/
theorem bwdV_arrayInitElemOob₂ : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 95 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayInitElemOob2 hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_ELEM" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitElem (Typing.adminToV_case h₅).symm
  have eY : Y = idxV y.toNat := by
    have h₅' : Value.case "ARRAY.INIT_ELEM" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₅
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₅'
    exact h₅'.2.symm
  subst hZ eY
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ea, ei, hel, rfl⟩ := BwdRead.elemLen_inv B NA rfl fz fy e₂
  have ev₁ : v₁ = .num (.natN (j.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fj))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  exact .aggregate (.arrayInitElemOob₂ hel (BwdRead.gt_nat_inv hcmp))

/-- **`Step_read` 73 (`array.new_elem-oob`), backward.** The premise evaluates
`|$elem(z, y).REFS|`, so the segment resolves. -/
theorem bwdV_arrayNewElemOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 73 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayNewElemOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.NEW_ELEM" (.tuple [X, Y])]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₁
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₂
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := head_arrayNewElem (Typing.adminToV_case h₃).symm
  have eY : Y = idxV y.toNat := by
    have h₃' : Value.case "ARRAY.NEW_ELEM" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₃
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₃'
    exact h₃'.2.symm
  subst hZ eY
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ea, ei, hel, rfl⟩ := BwdRead.elemLen_inv B NA rfl fz fy e₂
  have ev₁ : v₁ = .num (.natN (i.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  exact .aggregate (.arrayNewElemOob hel (BwdRead.gt_nat_inv hcmp))

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
