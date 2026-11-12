module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Common

/-!
# Track bwd-read: `Step_read/table.get-oob` (25), `table.get-val` (26), `table.fill-oob` (28),
`table.copy-oob` (31), `table.init-oob` (35), backward

Each lemma is the `Backward.read i` field at one index: the conclusion is read back by evaluation
(`concl_inv`), the code decoded by tag (`decode_aconst` and the opcode decoders below), and the
premise read back through the inverted accessors (`tableLen_inv`, `elemLen_inv`) into Core's
side condition. None needs a bound on the store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_tableGet {a : Admin} (h : Typing.adminHead a = "TABLE.GET") :
    ∃ x, a = .plain (.tableGet x) := by
  revert h
  admin_head_inv

theorem head_tableFill {a : Admin} (h : Typing.adminHead a = "TABLE.FILL") :
    ∃ x, a = .plain (.tableFill x) := by
  revert h
  admin_head_inv

theorem head_tableCopy {a : Admin} (h : Typing.adminHead a = "TABLE.COPY") :
    ∃ x y, a = .plain (.tableCopy x y) := by
  revert h
  admin_head_inv

theorem head_tableInit {a : Admin} (h : Typing.adminHead a = "TABLE.INIT") :
    ∃ x y, a = .plain (.tableInit x y) := by
  revert h
  admin_head_inv

theorem decode_tableGet {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.GET" X) :
    ∃ x : TableIdx, a = .plain (.tableGet x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_tableGet (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

theorem decode_tableFill {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.FILL" X) :
    ∃ x : TableIdx, a = .plain (.tableFill x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_tableFill (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

theorem decode_tableCopy {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.COPY" X) :
    ∃ (x y : TableIdx), a = .plain (.tableCopy x y) ∧ X = .tuple [idxV x.toNat, idxV y.toNat] := by
  obtain ⟨x, y, rfl⟩ := head_tableCopy (Typing.adminToV_case h).symm
  refine ⟨x, y, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

theorem decode_tableInit {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.INIT" X) :
    ∃ (x : TableIdx) (y : ElemIdx), a = .plain (.tableInit x y) ∧
      X = .tuple [idxV x.toNat, idxV y.toNat] := by
  obtain ⟨x, y, rfl⟩ := head_tableInit (Typing.adminToV_case h).symm
  refine ⟨x, y, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- An address operand `CONST at i` whose payload `i!%.0` a premise reads, decoded. -/
theorem aconst_of_proj {env : Env} {ρ : VarEnv} {xi : IL.Id} {I AT v : Value} {a : Admin}
    (fi : ρ.findVal? xi = some I) (ha : adminToV a = .case "CONST" (.tuple [AT, I]))
    (h : EvalExp env ρ (.projE (.uncaseE (.varE xi) "%") 0) v) :
    ∃ (t : AddrType) (b : BitVec t.intType.width), a = aconst t b ∧ AT = Encode.toValue t ∧
      v = .num (.natN b.toNat) := by
  obtain ⟨vs, rfl, hv⟩ := pct_of_proj fi h
  obtain ⟨t, b, rfl, hAT, hvs⟩ := decode_aconst ha
  have hvs' : vs = [.num (.natN b.toNat)] := Value.tuple.inj hvs
  have e : v = .num (.natN b.toNat) := by simpa [hvs'] using hv.symm
  exact ⟨t, b, rfl, hAT, e⟩

/-- The sum `i!%.0 + n` of an out-of-bounds premise, with the address operand `CONST at i` and
the count operand `CONST at' (% n)` decoded. -/
theorem oob_sum_inv {env : Env} {ρ : VarEnv} {xi : IL.Id} {I AT AT' N v : Value} {a a' : Admin}
    (fi : ρ.findVal? xi = some I) (fn : ρ.findVal? "n" = some N)
    (ha : adminToV a = .case "CONST" (.tuple [AT, I]))
    (ha' : adminToV a' = .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]))
    (h : EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE xi) "%") 0)
      (.varE "n")) v) :
    ∃ (t : AddrType) (b : BitVec t.intType.width) (t' : AddrType) (b' : BitVec t'.intType.width),
      a = aconst t b ∧ AT = Encode.toValue t ∧ a' = aconst t' b' ∧ AT' = Encode.toValue t' ∧
      v = .num (.natN (b.toNat + b'.toNat)) := by
  obtain ⟨u, hu, -⟩ := evalExp_binE_iff.1 h
  obtain ⟨t, b, rfl, hAT, rfl⟩ := aconst_of_proj fi ha hu
  obtain ⟨q, hq, rfl⟩ := add_nat_inv hu h
  obtain ⟨t', b', rfl, hAT', hN⟩ := decode_aconst ha'
  have eN : N = .num (.natN q) := EvalExp.unique (evalExp_var fn) hq
  have eq : q = b'.toNat := by simpa [eN] using hN
  exact ⟨t, b, t', b', rfl, hAT, rfl, hAT', by rw [eq]⟩

variable (B : Builtins) (NA : NoAcc B)
include NA

/-- **`Backward.read 25`** (`table.get-oob`). -/
theorem bwd_tableGetOob : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 25 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableGetOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      .case "TABLE.GET" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, his, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨x, ha₂, hX⟩ := decode_tableGet h₂
  have hpr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .geOp (.numT .natT)
      (.projE (.uncaseE (.varE "i") "%") 0)
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  obtain ⟨t, b, ha₁, -, hv₁⟩ := aconst_of_proj fi h₁ e₁
  obtain ⟨ta, ti, ht, hv₂⟩ := tableLen_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) e₂
  have hle : ti.refs.length ≤ b.toNat := ge_nat_inv (hv₁ ▸ hv₂ ▸ hcmp)
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    rw [his, ha₁, ha₂]
    exact .table (.getOob ht hle)
  exact ⟨[.trap], trap_out hc.2, hstep⟩

/-- **`Backward.read 26`** (`table.get-val`). -/
theorem bwd_tableGetVal : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 26 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableGetVal hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      .case "TABLE.GET" X]]) ∧ ∃ R, EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.idxE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")
          (.projE (.uncaseE (.varE "i") "%") 0)) R ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨R, hR, hw⟩ := hc.2
  obtain ⟨a₁, a₂, his, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨x, ha₂, hX⟩ : ∃ x : TableIdx, a₂ = .plain (.tableGet x) ∧ X = idxV x.toNat :=
    decode_tableGet h₂
  obtain ⟨rs, k, hrs, hk, hRk⟩ := evalExp_idxE_iff.1 hR
  obtain ⟨t, b, ha₁, -, hkb⟩ := aconst_of_proj fi h₁ hk
  obtain ⟨T, hT, hTR⟩ := evalExp_dotE_iff.1 hrs
  obtain ⟨ta, ti, ht, hTv⟩ := table_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) hT
  have ers : rs = .list (ti.refs.map refToValue) := by simpa [hTv] using hTR.symm
  have hk' : k = b.toNat := by simpa using hkb
  have hmap : (ti.refs[b.toNat]?).map refToValue = some R := by
    simpa [ers, hk', Value.idx?] using hRk
  obtain ⟨r, hr, hrR⟩ := Option.map_eq_some_iff.1 hmap
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.ref r]⟩ := by
    rw [his, ha₁, ha₂]
    exact .table (.getVal ht hr)
  exact ⟨[.ref r], by simp [hw, ← hrR, adminsToV, State.adminToV_ref], hstep⟩

/-- **`Backward.read 28`** (`table.fill-oob`). -/
theorem bwd_tableFillOob : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 28 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableFillOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      V, .case "CONST" (.tuple [AT, .case "%" (.tuple [N])]), .case "TABLE.FILL" X]]) ∧
      w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, ha₄, hX⟩ := decode_tableFill h₄
  obtain ⟨v, ha₂⟩ := (Typing.stateDecode_simEnv B).val a₂ _ (valsOnly_bindVals σ) (h₂ ▸ hV)
  have hpr : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.varE "n"))
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  obtain ⟨t, b, t', b', ha₁, hAT, ha₃, hAT', hv₁⟩ := oob_sum_inv fi fn h₁ h₃ e₁
  have et : t' = t := encode_addrType_inj (hAT'.symm.trans hAT)
  obtain ⟨ta, ti, ht, hv₂⟩ := tableLen_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) e₂
  have hlt : ti.refs.length < b.toNat + b'.toNat := gt_nat_inv (hv₁ ▸ hv₂ ▸ hcmp)
  have hstep : Step P host ⟨s, f, is⟩ ⟨s, f, [.trap]⟩ := by
    subst et
    rw [his, ha₁, ha₂, ha₃, ha₄]
    exact .table (.fillOob ht hlt)
  exact ⟨[.trap], trap_out hc.2, hstep⟩

end Silmaril.Wasm.SpecTec.Sim.BwdRead
