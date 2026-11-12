module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.TableOob

/-!
# Track r4-read: `Step_read/table.copy-zero` (32), `table.copy-le` (33), `table.copy-gt` (34),
backward, under validity

The three rules carry `otherwise`. Backwards, each of Core's side conditions is recovered by
showing that otherwise an earlier rule would fire on the same left-hand side: `table.copy-oob`
(31) when a range is out of bounds (`body_tableCopyOob`, at a fresh assignment, since rule 31 names
its indices `x_1`, `x_2`), `table.copy-zero` (32) when the count is zero, `table.copy-le` (33)
when the destination is not above the source. Those bodies evaluate both `$table` lookups:
index resolution (`ReadValid.idx`) is what makes them evaluate. The successors' `+ 1` and
`i + n - 1` do not wrap: both ranges are in bounds and tables have fewer than `2 ^ 32` entries.
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
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst decode_tableCopy)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `table.copy` configuration, as `Memory.copyCode`. -/
theorem configV_copy (s : Store H) (f : Frame) {t₁ t₂ t' : AddrType}
    (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width) (b' : BitVec t'.intType.width)
    (x₁ x₂ : TableIdx) :
    configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩ =
      cfgV (stV (storeV hn s) (frameV f)) (Memory.copyCode (Encode.toValue t₁) (Encode.toValue t₂)
        (Encode.toValue t') b₁.toNat b₂.toNat b'.toNat x₁.toNat x₂.toNat) := by
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  rfl

variable (B : Builtins)

/-- **`table.copy-oob` (31) fires** on an out-of-bounds `table.copy` whose tables resolve. -/
theorem body_tableCopyOob {D : Interp} {els : Prop} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (hz : TypedV (simEnv B) stateT (stV (storeV hn s) (frameV f)))
    (ht₁ : s.table? f x₁ = some (ta₁, ti₁)) (ht₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hoob : ti₁.refs.length < b₁.toNat + b'.toNat ∨ ti₂.refs.length < b₂.toNat + b'.toNat) :
    RuleBody (simEnv B) D els [] [] "%~>%" Equiv.ExecRead.tableCopyOobRule
      (.tuple [configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b',
        .plain (.tableCopy x₁ x₂)]⟩, .list [.case "TRAP" (.tuple [])]]) := by
  rw [configV_copy]
  have St := Typing.stateTyping_simEnv B
  let σ : List (IL.Id × Value) := [("z", stV (storeV hn s) (frameV f)), ("at_1", Encode.toValue t₁),
    ("i_1", idxV b₁.toNat), ("at_2", Encode.toValue t₂), ("i_2", idxV b₂.toNat),
    ("at'", Encode.toValue t'), ("n", .num (.natN b'.toNat)), ("x_1", idxV x₁.toNat),
    ("x_2", idxV x₂.toNat)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ho := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_tableLen' B (σ := σ) (zx := "x_1") rfl rfl ht₁) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_tableLen' B (σ := σ) (zx := "x_2") rfl rfl ht₂) rfl)
  rw [decide_eq_true hoob] at ho
  refine ⟨rfl, VarEnv.empty, σ, rfl,
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr t₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" t₁ b₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr t₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" t₂ b₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr t' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx _ x₁.value.isLt _ hρ)
      (QuantsOk.cons rfl (St.idx _ x₂.value.isLt _ hρ) QuantsOk.nil)))))))),
    by eval_tac, fun pr hpr => ?_⟩
  rw [List.mem_singleton.1 hpr]
  exact .ifPr ho

/-- The shared reading of a `table.copy-zero`/`-le`/`-gt` instance. -/
theorem copy_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {is : List Admin}
    {Z AT₁ I₁ AT₂ I₂ AT' N X Y : Value}
    (hv : ReadValid (⟨s, f, is⟩ : Config H))
    (hAT₁ : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT₁)
    (hAT₂ : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT₂)
    (hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "TABLE.COPY" (.tuple [X, Y])]])) :
    ∃ (t₁ t₂ t' : AddrType) (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width)
      (b' : BitVec t'.intType.width) (x₁ x₂ : TableIdx) (ta₁ ta₂ : Nat) (ti₁ ti₂ : TableInst),
      is = [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)] ∧
      Z = stV (storeV hn s) (frameV f) ∧ AT₁ = Encode.toValue t₁ ∧ I₁ = idxV b₁.toNat ∧
      AT₂ = Encode.toValue t₂ ∧ I₂ = idxV b₂.toNat ∧ AT' = Encode.toValue t' ∧
      N = .num (.natN b'.toNat) ∧ X = idxV x₁.toNat ∧ Y = idxV x₂.toNat ∧
      s.table? f x₁ = some (ta₁, ti₁) ∧ s.table? f x₂ = some (ta₂, ti₂) := by
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x₁, x₂, rfl, hX⟩ := decode_tableCopy h₄
  have hXY : X = idxV x₁.toNat ∧ Y = idxV x₂.toNat := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hX
  obtain ⟨t₁, b₁, rfl, hA₁, hI₁⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT₁
  obtain ⟨t₂, b₂, rfl, hA₂, hI₂⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₂ hAT₂
  obtain ⟨t', b', rfl, hA', hN⟩ := decode_aconst h₃
  obtain ⟨ix₁, ix₂⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ta₁, ti₁, ht₁⟩ := table_of_isSome ix₁
  obtain ⟨ta₂, ti₂, ht₂⟩ := table_of_isSome ix₂
  exact ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ta₁, ta₂, ti₁, ti₂, his, hZ, hA₁, hI₁, hA₂, hI₂, hA',
    by simpa using hN, hXY.1, hXY.2, ht₁, ht₂⟩

/-- `otherwise` for `table.copy-zero` (32) at an in-bounds `table.copy`. -/
theorem otherwise_tableCopyZero {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst} {c : Value}
    (ht₁ : s.table? f x₁ = some (ta₁, ti₁)) (ht₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : b₁.toNat + b'.toNat ≤ ti₁.refs.length ∧ b₂.toNat + b'.toNat ≤ ti₂.refs.length) :
    otherwiseAt (simEnv B) "Step_read" [] 32 (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩, c]) := by
  rw [configV_copy]
  exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).tableCopyZero
    (RefsGC.readTable_simEnv B) (i := 32) (by decide) (exc := [31]) Memory.lhsIn_tableCopy
    (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 31 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).tableCopyOob hr']
      exact Memory.not_tableCopyOob (State.stateDefs_simEnv B) (State.tableAt_of_table? hn ht₁)
        (State.tableInstV_REFS ti₁) (State.tableAt_of_table? hn ht₂) (State.tableInstV_REFS ti₂)
        (by simpa using hb))

/-- `otherwise` for `table.copy-le` (33) at an in-bounds, non-empty `table.copy`. -/
theorem otherwise_tableCopyLe {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst} {c : Value}
    (ht₁ : s.table? f x₁ = some (ta₁, ti₁)) (ht₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : b₁.toNat + b'.toNat ≤ ti₁.refs.length ∧ b₂.toNat + b'.toNat ≤ ti₂.refs.length)
    (hk : b'.toNat ≠ 0) :
    otherwiseAt (simEnv B) "Step_read" [] 33 (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩, c]) := by
  rw [configV_copy]
  exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).tableCopyLe
    (RefsGC.readTable_simEnv B) (i := 33) (by decide) (exc := [31, 32]) Memory.lhsIn_tableCopy
    (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 31 ∨ j = 32) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).tableCopyOob hr']
        exact Memory.not_tableCopyOob (State.stateDefs_simEnv B) (State.tableAt_of_table? hn ht₁)
          (State.tableInstV_REFS ti₁) (State.tableAt_of_table? hn ht₂)
          (State.tableInstV_REFS ti₂) (by simpa using hb)
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).tableCopyZero hr']
        exact Memory.not_tableCopyZero hk)

/-- The in-bounds facts every `otherwise` rule of `table.copy` recovers: no out-of-bounds range
(else rule 31 fires), and, for rules after 32, a non-zero count (else rule 32 fires). -/
theorem copy_inBounds {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst} {k : Nat} {w : Value}
    (hk : 31 < k)
    (hz : TypedV (simEnv B) stateT (stV (storeV hn s) (frameV f)))
    (ht₁ : s.table? f x₁ = some (ta₁, ti₁)) (ht₂ : s.table? f x₂ = some (ta₂, ti₂))
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩, w])) :
    b₁.toNat + b'.toNat ≤ ti₁.refs.length ∧ b₂.toNat + b'.toNat ≤ ti₂.refs.length := by
  by_contra hn'
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).tableCopyOob
    ⟨_, _, _, rfl, rfl⟩ (body_tableCopyOob B hz ht₁ ht₂ ?_)
  omega

/-- **`Step_read` 32 (`table.copy-zero`), backward, under validity.** -/
theorem bwdV_tableCopyZero : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 32 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableCopyZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "TABLE.COPY" (.tuple [X, Y])]])
      ∧ w = .list [] := by
    concl_inv he
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ta₁, ta₂, ti₁, ti₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := copy_inv B hv hAT₁ hAT₂ hc.1
  have h0 : Value.num (.natN b'.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (evalExp_var fn) RefsGC.evalExp_num'
  have hb' : b' = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hb'
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have hb := copy_inBounds B (k := 32) (by decide) hz ht₁ ht₂ (else_head hp)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .table (.copyZero ht₁ ht₂ (by simpa using hb))

/-- The scope of a `table.copy-zero`/`-le`/`-gt` instance, read back. -/
structure CopyScope (B : Builtins) (σ : List (IL.Id × Value)) (s : Store H) (f : Frame)
    (t₁ t₂ t' : AddrType) (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width)
    (b' : BitVec t'.intType.width) (x₁ x₂ : TableIdx) : Prop where
  fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f))
  fa₁ : (VarEnv.empty.bindVals σ).findVal? "at_1" = some (Encode.toValue t₁)
  fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some (idxV b₁.toNat)
  fa₂ : (VarEnv.empty.bindVals σ).findVal? "at_2" = some (Encode.toValue t₂)
  fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some (idxV b₂.toNat)
  fa' : (VarEnv.empty.bindVals σ).findVal? "at'" = some (Encode.toValue t')
  fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat))
  fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x₁.toNat)
  fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV x₂.toNat)

/-- `table.copy-le`'s right-hand side, evaluated. -/
theorem rhs_tableCopyLe {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} (S : CopyScope (hn := hn) B σ s f t₁ t₂ t' b₁ b₂ b' x₁ x₂)
    (hk : 1 ≤ b'.toNat) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "TABLE.GET" (.varE "y"), .caseE "TABLE.SET" (.varE "x"),
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0)
          (.numE (.natN 1))])]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
          (.numE (.natN 1))])]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
          (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])]),
      .caseE "TABLE.COPY" (.tupE [.varE "x", .varE "y"])])
      (.list [aconstV (Encode.toValue t₁) b₁.toNat, aconstV (Encode.toValue t₂) b₂.toNat,
        .case "TABLE.GET" (idxV x₂.toNat), .case "TABLE.SET" (idxV x₁.toNat),
        aconstV (Encode.toValue t₁) (b₁.toNat + 1), aconstV (Encode.toValue t₂) (b₂.toNat + 1),
        aconstV (Encode.toValue t') (b'.toNat - 1),
        .case "TABLE.COPY" (.tuple [idxV x₁.toNat, idxV x₂.toNat])]) := by
  have ea₁ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa₁)
  have ea₂ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa₂)
  have ea' := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa')
  exact RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₁ (evalExp_var S.fi₁)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₂ (evalExp_var S.fi₂)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var S.fy))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var S.fx))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₁ (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var S.fi₁)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₂ (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var S.fi₂)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_predNat
      (evalExp_var S.fn) hk))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var S.fx) (evalExp_var S.fy)))
      RefsGC.evalExps_nil'))))))))

/-- The two `+ 1` successors of `table.copy-le`, as Core's. -/
theorem adminsToV_copyLe {t₁ t₂ t' : AddrType} {b₁ : BitVec t₁.intType.width}
    {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width} {x₁ x₂ : TableIdx}
    (hw₁ : b₁.toNat + 1 < 2 ^ t₁.intType.width) (hw₂ : b₂.toNat + 1 < 2 ^ t₂.intType.width)
    (hk : b' ≠ 0) :
    adminsToV [aconst t₁ b₁, aconst t₂ b₂, .plain (.tableGet x₂), .plain (.tableSet x₁),
        aconst t₁ (b₁ + 1), aconst t₂ (b₂ + 1), aconst t' (b' - 1), .plain (.tableCopy x₁ x₂)] =
      [aconstV (Encode.toValue t₁) b₁.toNat, aconstV (Encode.toValue t₂) b₂.toNat,
        .case "TABLE.GET" (idxV x₂.toNat), .case "TABLE.SET" (idxV x₁.toNat),
        aconstV (Encode.toValue t₁) (b₁.toNat + 1), aconstV (Encode.toValue t₂) (b₂.toNat + 1),
        aconstV (Encode.toValue t') (b'.toNat - 1),
        .case "TABLE.COPY" (.tuple [idxV x₁.toNat, idxV x₂.toNat])] := by
  simp only [adminsToV, State.adminToV_aconst, Memory.toNat_add_one hw₁,
    Memory.toNat_add_one hw₂, Memory.toNat_sub_one hk]
  rfl

/-- A copy-family instance reads its scope back. -/
theorem copyScope_of {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fa₁ : (VarEnv.empty.bindVals σ).findVal? "at_1" = some (Encode.toValue t₁))
    (fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some (idxV b₁.toNat))
    (fa₂ : (VarEnv.empty.bindVals σ).findVal? "at_2" = some (Encode.toValue t₂))
    (fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some (idxV b₂.toNat))
    (fa' : (VarEnv.empty.bindVals σ).findVal? "at'" = some (Encode.toValue t'))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x₁.toNat))
    (fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV x₂.toNat)) :
    CopyScope (hn := hn) B σ s f t₁ t₂ t' b₁ b₂ b' x₁ x₂ :=
  ⟨fz, fa₁, fi₁, fa₂, fi₂, fa', fn, fx, fy⟩

/-- A non-zero count, recovered from `otherwise` after `table.copy-zero` (32). -/
theorem copy_nonzero {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : TableIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst} {k : Nat} {w : Value} {L : Exp}
    (hk : 32 < k)
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "at_1" (.varT "addrtype" []), .expP "i_1" (.varT "num_" [.expA (.subE (.varE "at_1")
        (.varT "addrtype" []) (.varT "numtype" []))]), .expP "at_2" (.varT "addrtype" []),
      .expP "i_2" (.varT "num_" [.expA (.subE (.varE "at_2") (.varT "addrtype" [])
        (.varT "numtype" []))]), .expP "at'" (.varT "addrtype" []), .expP "n" (.varT "n" []),
      .expP "x" (.varT "idx" []), .expP "y" (.varT "idx" [])])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) L
      (configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩))
    (hL : L = .caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "TABLE.COPY" (.tupE [.varE "x", .varE "y"])]]))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat)))
    (ht₁ : s.table? f x₁ = some (ta₁, ti₁)) (ht₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : b₁.toNat + b'.toNat ≤ ti₁.refs.length ∧ b₂.toNat + b'.toNat ≤ ti₂.refs.length)
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.tableCopy x₁ x₂)]⟩, w])) : b' ≠ 0 := by
  subst hL
  rintro rfl
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).tableCopyZero
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq,
      evalExp_tup2 hl (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise_tableCopyZero B ht₁ ht₂ hb)
  · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simpa using RefsGC.evalExp_num'))

/-- **`Step_read` 33 (`table.copy-le`), backward, under validity.** -/
theorem bwdV_tableCopyLe : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 33 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableCopyLe hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "TABLE.COPY" (.tuple [X, Y])]])
      := by
    concl_inv hl
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ta₁, ta₂, ti₁, ti₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := copy_inv B hv hAT₁ hAT₂ hc
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have ho := else_head hp
  have hb := copy_inBounds B (k := 33) (by decide) hz ht₁ ht₂ ho
  have hk := copy_nonzero B (k := 33) (by decide) hq hl rfl fn ht₁ ht₂ hb ho
  have hle : b₁.toNat ≤ b₂.toNat := by
    have := Memory.cmp_true (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (RefsGC.evalExp_unpct (evalExp_var fi₁))
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) rfl
    simpa using this
  have hk1 : 1 ≤ b'.toNat := Nat.one_le_iff_ne_zero.2 fun h => hk (BitVec.eq_of_toNat_eq h)
  have hw₁ := lt_width (a := t₁) (table_lt32 hv.store ht₁)
  have hw₂ := lt_width (a := t₂) (table_lt32 hv.store ht₂)
  have hw : w = _ := EvalExp.unique (RefsGC.rhs_of_concl he)
    (rhs_tableCopyLe B (copyScope_of B fz fa₁ fi₁ fa₂ fi₂ fa' fn fx fy) hk1)
  refine ⟨_, ?_, .table (.copyLe ht₁ ht₂ hb hk hle)⟩
  rw [hw, adminsToV_copyLe (by omega) (by omega) hk]

/-- **`Step_read` 34 (`table.copy-gt`), backward, under validity.** -/
theorem bwdV_tableCopyGt : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 34 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableCopyGt hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "TABLE.COPY" (.tuple [X, Y])]])
      := by
    concl_inv hl
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ta₁, ta₂, ti₁, ti₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := copy_inv B hv hAT₁ hAT₂ hc
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have ho := else_head hp
  have hb := copy_inBounds B (k := 34) (by decide) hz ht₁ ht₂ ho
  have hk := copy_nonzero B (k := 34) (by decide) hq hl rfl fn ht₁ ht₂ hb ho
  have hk0 : b'.toNat ≠ 0 := fun h => hk (BitVec.eq_of_toNat_eq h)
  have hk1 : 1 ≤ b'.toNat := Nat.one_le_iff_ne_zero.2 hk0
  have hgt : b₂.toNat < b₁.toNat := by
    refine Nat.lt_of_not_le fun hle => BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).tableCopyLe ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl,
        hq, evalExp_tup2 hl (rhs_tableCopyLe B (copyScope_of B fz fa₁ fi₁ fa₂ fi₂ fa' fn fx fy)
          hk1), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact .elsePr (otherwise_tableCopyLe B ht₁ ht₂ hb hk0)
    · exact .ifPr (RefsGC.evalExp_leNat (RefsGC.evalExp_unpct (evalExp_var fi₁))
        (RefsGC.evalExp_unpct (evalExp_var fi₂)) hle)
  have hw₁ := lt_width (a := t₁) (table_lt32 hv.store ht₁)
  have hw₂ := lt_width (a := t₂) (table_lt32 hv.store ht₂)
  have ea₁ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var fa₁)
  have ea₂ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var fa₂)
  have ea' := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var fa')
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₁ (RefsGC.evalExp_predNat
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fi₁))
        (evalExp_var fn)) (by omega)))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₂ (RefsGC.evalExp_predNat
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fi₂))
        (evalExp_var fn)) (by omega)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fy))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₁ (evalExp_var fi₁)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₂ (evalExp_var fi₂)))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_predNat
      (evalExp_var fn) hk1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
      RefsGC.evalExps_nil')))))))))
  refine ⟨[aconst t₁ (b₁ + BitVec.ofNat _ b'.toNat - 1), aconst t₂ (b₂ + BitVec.ofNat _ b'.toNat - 1),
    .plain (.tableGet x₂), .plain (.tableSet x₁), aconst t₁ b₁, aconst t₂ b₂, aconst t' (b' - 1),
    .plain (.tableCopy x₁ x₂)], ?_, .table (.copyGt ht₁ ht₂ hb hk hgt)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_aconst,
    Memory.toNat_add_ofNat_sub_one b₁ hk0 (by omega),
    Memory.toNat_add_ofNat_sub_one b₂ hk0 (by omega), Memory.toNat_sub_one hk]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round4Read
