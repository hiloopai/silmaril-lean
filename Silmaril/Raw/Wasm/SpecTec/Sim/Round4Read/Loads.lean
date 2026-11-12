module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Read.Common
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Loads
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.LoadRules

/-!
# Track r4-read: `Step_read/load-num-oob` (38), `load-pack-oob` (40), backward

The trapping scalar loads. The premise `i + ao.OFFSET + w/8 > |$mem(z, x).BYTES|` evaluates the
memory, so it resolves (`BwdRead.memLen_inv`); the access width `$size(nt)/8` (resp. `n/8`) is
read back by evaluating it forward (`FwdMem.evalExp_widthNum`, `Memory.evalExp_div8`) and using
that evaluation is a function. No validity is needed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv NoAcc)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_load {a : Admin} (h : Typing.adminHead a = "LOAD") :
    (∃ t p x arg, a = .plain (.intLoad t p x arg)) ∨ (∃ t x arg, a = .plain (.floatLoad t x arg)) := by
  revert h
  admin_head_inv

/-- **An unpacked `LOAD` image, decoded.** -/
theorem decode_loadNum {a : Admin} {NT X AO : Value}
    (h : adminToV a = .case "LOAD" (.tuple [NT, .opt none, X, AO])) :
    ∃ (t : NumType) (x : MemIdx) (arg : MemArg),
      ((∃ it, a = .plain (.intLoad it none x arg) ∧ t = .int it) ∨
        ∃ ft, a = .plain (.floatLoad ft x arg) ∧ t = .float ft) ∧
      NT = Encode.toValue t ∧ X = idxV x.toNat ∧ AO = memargV arg := by
  rcases head_load (Typing.adminToV_case h).symm with ⟨t, p, x, arg, rfl⟩ | ⟨t, x, arg, rfl⟩
  · cases p with
    | none =>
      have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.int t), .opt none,
          idxV x.toNat, memargV arg]) = _ := h
      simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h'
      exact ⟨.int t, x, arg, .inl ⟨t, rfl, rfl⟩, h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩
    | some q =>
      obtain ⟨sz, sx⟩ := q
      have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%_%" (.tuple [szV sz, sxV sx]))), idxV x.toNat, memargV arg]) = _ := h
      simp at h'
  · have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.float t), .opt none,
        idxV x.toNat, memargV arg]) = _ := h
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h'
    exact ⟨.float t, x, arg, .inr ⟨t, rfl, rfl⟩, h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩

/-- `concl_inv`, also reading absent options. -/
macro "concl_inv' " h:ident : tactic => `(tactic| (
  simp [evalExp_tupE_iff, Equiv.Validation.evalExps_cons_iff,
    Equiv.Validation.evalExps_nil_iff, evalExp_listE_iff, evalExp_caseE_iff, evalExp_varE_iff,
    evalExp_subE_iff, evalExp_optE_some_iff, evalExp_optE_none_iff,
    Silmaril.SpecTec.Equiv.Execution.caseNilV] at $h:ident ⊢
  aesop))

variable (B : Builtins) (NA : NoAcc B)
include NA

/-- **`Step_read` 38 (`load-num-oob`), backward.** -/
theorem bwdV_loadNumOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 38 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).loadNumOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨NT, fnt, -⟩ := hq "nt" (.varT "numtype" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AO, fao, -⟩ := hq "ao" (.varT "memarg" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "LOAD" (.tuple [NT, .opt none, X, AO])]]) ∧
      w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv' he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨t, x, arg, ha₂, rfl, rfl, rfl⟩ := decode_loadNum h₂
  obtain ⟨at_, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ma, mi, hm, rfl⟩ := BwdRead.memLen_inv B NA rfl fz fx e₂
  have ev₁ : v₁ = .num (.natN (b.toNat + arg.offset.val + t.width / 8)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var fi)
      (evalExp_var fao)) (FwdMem.evalExp_widthNum (State.growDefs_simEnv B)
        (Memory.sizeDefs_simEnv B) t (evalExp_var fnt)))
  subst ev₁
  have hlt := BwdRead.gt_nat_inv hcmp
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  rcases ha₂ with ⟨it, rfl, rfl⟩ | ⟨ft, rfl, rfl⟩
  · exact .memory (.loadIntOob hm (by unfold effAddr; exact hlt))
  · exact .memory (.loadFloatOob hm (by unfold effAddr; exact hlt))

omit NA in
/-- **A packed `LOAD` image, decoded.** -/
theorem decode_loadPack {a : Admin} {NT N SX X AO : Value}
    (h : adminToV a = .case "LOAD" (.tuple [NT, .opt (some (.case "%_%"
      (.tuple [.case "%" (.tuple [N]), SX]))), X, AO])) :
    ∃ (t : IntType) (sz : PackSize) (sx : Signedness) (x : MemIdx) (arg : MemArg),
      a = .plain (.intLoad t (some (sz, sx)) x arg) ∧ NT = Encode.toValue (NumType.int t) ∧
      N = .num (.natN sz.width) ∧ SX = sxV sx ∧ X = idxV x.toNat ∧ AO = memargV arg := by
  rcases head_load (Typing.adminToV_case h).symm with ⟨t, p, x, arg, rfl⟩ | ⟨t, x, arg, rfl⟩
  · cases p with
    | none =>
      have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.int t), .opt none,
          idxV x.toNat, memargV arg]) = _ := h
      simp at h'
    | some q =>
      obtain ⟨sz, sx⟩ := q
      have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.int t),
          .opt (some (.case "%_%" (.tuple [szV sz, sxV sx]))), idxV x.toNat, memargV arg]) = _ := h
      simp only [szV, Equiv.Execution.pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
        Value.opt.injEq, Option.some.injEq, true_and, and_true] at h'
      exact ⟨t, sz, sx, x, arg, rfl, h'.1.symm, h'.2.1.1.symm, h'.2.1.2.symm, h'.2.2.1.symm,
        h'.2.2.2.symm⟩
  · have h' : Value.case "LOAD" (.tuple [Encode.toValue (NumType.float t), .opt none,
        idxV x.toNat, memargV arg]) = _ := h
    simp at h'

/-- **`Step_read` 40 (`load-pack-oob`), backward.** -/
theorem bwdV_loadPackOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 40 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).loadPackOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨NT, fnt, -⟩ := hq "Inn" (.varT "Inn" []) (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨SX, fsx, -⟩ := hq "sx" (.varT "sx" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AO, fao, -⟩ := hq "ao" (.varT "memarg" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "LOAD" (.tuple [NT, .opt (some (.case "%_%"
        (.tuple [.case "%" (.tuple [N]), SX]))), X, AO])]]) ∧
      w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨t, sz, sx, x, arg, rfl, rfl, rfl, rfl, rfl, rfl⟩ := decode_loadPack h₂
  obtain ⟨at_, b, rfl, rfl, rfl⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ma, mi, hm, rfl⟩ := BwdRead.memLen_inv B NA rfl fz fx e₂
  have ev₁ : v₁ = .num (.natN (b.toNat + arg.offset.val + sz.width / 8)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (Memory.evalExp_effAddr (evalExp_var fi)
      (evalExp_var fao)) (Memory.evalExp_div8 (by cases sz <;> simp [PackSize.width])
        (evalExp_var fn)))
  subst ev₁
  have hlt := BwdRead.gt_nat_inv hcmp
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  exact .memory (.loadPackOob hm (by simpa [effAddr] using hlt))

end Silmaril.Wasm.SpecTec.Sim.Round4Read
