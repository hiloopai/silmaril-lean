module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.MemOob

/-!
# Track r4-read: `Step_read/memory.copy-zero` (57), `memory.copy-le` (58), `memory.copy-gt` (59),
backward, under validity

The three rules carry `otherwise`. Backwards, each of Core's side conditions is recovered by
showing that otherwise an earlier rule would fire on the same left-hand side: `memory.copy-oob`
(56) when a range is out of bounds (`body_memoryCopyOob`, at a fresh assignment; all four memory
rules name their indices `x_1`, `x_2`), `memory.copy-zero` (57) when the count is zero, `memory.copy-le` (58)
when the destination is not above the source. Those bodies evaluate both `$mem` lookups:
index resolution (`ReadValid.idx`) is what makes them evaluate. The successors' `+ 1` and
`i + n - 1` do not wrap: both ranges are in bounds and memories have fewer than `2 ^ 32` bytes.
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
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `memory.copy` configuration, as `Memory.mcopyCode`. -/
theorem configV_mcopy (s : Store H) (f : Frame) {t₁ t₂ t' : AddrType}
    (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width) (b' : BitVec t'.intType.width)
    (x₁ x₂ : MemIdx) :
    configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩ =
      cfgV (stV (storeV hn s) (frameV f)) (Memory.mcopyCode (Encode.toValue t₁) (Encode.toValue t₂)
        (Encode.toValue t') b₁.toNat b₂.toNat b'.toNat x₁.toNat x₂.toNat) := by
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  rfl

variable (B : Builtins)

/-- **`memory.copy-oob` (56) fires** on an out-of-bounds `memory.copy` whose memories resolve. -/
theorem body_memoryCopyOob {D : Interp} {els : Prop} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (hz : TypedV (simEnv B) stateT (stV (storeV hn s) (frameV f)))
    (ht₁ : s.mem? f x₁ = some (ma₁, mi₁)) (ht₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hoob : mi₁.bytes.size < b₁.toNat + b'.toNat ∨ mi₂.bytes.size < b₂.toNat + b'.toNat) :
    RuleBody (simEnv B) D els [] [] "%~>%" Equiv.ExecRead.memoryCopyOobRule
      (.tuple [configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b',
        .plain (.memoryCopy x₁ x₂)]⟩, .list [.case "TRAP" (.tuple [])]]) := by
  rw [configV_mcopy]
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
      (evalExp_memLen' B (σ := σ) (zx := "x_1") rfl rfl ht₁) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_memLen' B (σ := σ) (zx := "x_2") rfl rfl ht₂) rfl)
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

/-- The shared reading of a `memory.copy-zero`/`-le`/`-gt` instance. -/
theorem mcopy_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {is : List Admin}
    {Z AT₁ I₁ AT₂ I₂ AT' N X Y : Value}
    (hv : ReadValid (⟨s, f, is⟩ : Config H))
    (hAT₁ : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT₁)
    (hAT₂ : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT₂)
    (hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "MEMORY.COPY" (.tuple [X, Y])]])) :
    ∃ (t₁ t₂ t' : AddrType) (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width)
      (b' : BitVec t'.intType.width) (x₁ x₂ : MemIdx) (ma₁ ma₂ : Nat) (mi₁ mi₂ : MemInst),
      is = [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)] ∧
      Z = stV (storeV hn s) (frameV f) ∧ AT₁ = Encode.toValue t₁ ∧ I₁ = idxV b₁.toNat ∧
      AT₂ = Encode.toValue t₂ ∧ I₂ = idxV b₂.toNat ∧ AT' = Encode.toValue t' ∧
      N = .num (.natN b'.toNat) ∧ X = idxV x₁.toNat ∧ Y = idxV x₂.toNat ∧
      s.mem? f x₁ = some (ma₁, mi₁) ∧ s.mem? f x₂ = some (ma₂, mi₂) := by
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x₁, x₂, rfl, hX⟩ := decode_memoryCopy h₄
  have hXY : X = idxV x₁.toNat ∧ Y = idxV x₂.toNat := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hX
  obtain ⟨t₁, b₁, rfl, hA₁, hI₁⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT₁
  obtain ⟨t₂, b₂, rfl, hA₂, hI₂⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₂ hAT₂
  obtain ⟨t', b', rfl, hA', hN⟩ := decode_aconst h₃
  obtain ⟨ix₁, ix₂⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ma₁, mi₁, ht₁⟩ := mem_of_isSome ix₁
  obtain ⟨ma₂, mi₂, ht₂⟩ := mem_of_isSome ix₂
  exact ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ma₁, ma₂, mi₁, mi₂, his, hZ, hA₁, hI₁, hA₂, hI₂, hA',
    by simpa using hN, hXY.1, hXY.2, ht₁, ht₂⟩

/-- `otherwise` for `memory.copy-zero` (57) at an in-bounds `memory.copy`. -/
theorem otherwise_memoryCopyZero {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst} {c : Value}
    (ht₁ : s.mem? f x₁ = some (ma₁, mi₁)) (ht₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : b₁.toNat + b'.toNat ≤ mi₁.bytes.size ∧ b₂.toNat + b'.toNat ≤ mi₂.bytes.size) :
    otherwiseAt (simEnv B) "Step_read" [] 57 (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩, c]) := by
  rw [configV_mcopy]
  exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).memoryCopyZero
    (RefsGC.readTable_simEnv B) (i := 57) (by decide) (exc := [56]) Memory.lhsIn_memoryCopy
    (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 56 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).memoryCopyOob hr']
      exact Memory.not_memoryCopyOob (State.stateDefs_simEnv B) (Memory.memAt_of_mem? hn ht₁)
        (Memory.memInstV_BYTES mi₁) (Memory.memAt_of_mem? hn ht₂) (Memory.memInstV_BYTES mi₂)
        (by simpa using hb))

/-- `otherwise` for `memory.copy-le` (58) at an in-bounds, non-empty `memory.copy`. -/
theorem otherwise_memoryCopyLe {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst} {c : Value}
    (ht₁ : s.mem? f x₁ = some (ma₁, mi₁)) (ht₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : b₁.toNat + b'.toNat ≤ mi₁.bytes.size ∧ b₂.toNat + b'.toNat ≤ mi₂.bytes.size)
    (hk : b'.toNat ≠ 0) :
    otherwiseAt (simEnv B) "Step_read" [] 58 (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩, c]) := by
  rw [configV_mcopy]
  exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).memoryCopyLe
    (RefsGC.readTable_simEnv B) (i := 58) (by decide) (exc := [56, 57]) Memory.lhsIn_memoryCopy
    (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 56 ∨ j = 57) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).memoryCopyOob hr']
        exact Memory.not_memoryCopyOob (State.stateDefs_simEnv B) (Memory.memAt_of_mem? hn ht₁)
          (Memory.memInstV_BYTES mi₁) (Memory.memAt_of_mem? hn ht₂)
          (Memory.memInstV_BYTES mi₂) (by simpa using hb)
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).memoryCopyZero hr']
        exact Memory.not_memoryCopyZero hk)

/-- The in-bounds facts every `otherwise` rule of `memory.copy` recovers: no out-of-bounds range
(else rule 31 fires), and, for rules after 32, a non-zero count (else rule 32 fires). -/
theorem mcopy_inBounds {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst} {k : Nat} {w : Value}
    (hk : 56 < k)
    (hz : TypedV (simEnv B) stateT (stV (storeV hn s) (frameV f)))
    (ht₁ : s.mem? f x₁ = some (ma₁, mi₁)) (ht₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩, w])) :
    b₁.toNat + b'.toNat ≤ mi₁.bytes.size ∧ b₂.toNat + b'.toNat ≤ mi₂.bytes.size := by
  by_contra hn'
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).memoryCopyOob
    ⟨_, _, _, rfl, rfl⟩ (body_memoryCopyOob B hz ht₁ ht₂ ?_)
  omega

/-- **`Step_read` 57 (`memory.copy-zero`), backward, under validity.** -/
theorem bwdV_memoryCopyZero : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 57 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryCopyZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "x_2" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "MEMORY.COPY" (.tuple [X, Y])]])
      ∧ w = .list [] := by
    concl_inv he
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ma₁, ma₂, mi₁, mi₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := mcopy_inv B hv hAT₁ hAT₂ hc.1
  have h0 : Value.num (.natN b'.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (evalExp_var fn) RefsGC.evalExp_num'
  have hb' : b' = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hb'
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have hb := mcopy_inBounds B (k := 57) (by decide) hz ht₁ ht₂ (else_head hp)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .memory (.copyZero ht₁ ht₂ (by simpa using hb))

/-- The scope of a `memory.copy-zero`/`-le`/`-gt` instance, read back. -/
structure MCopyScope (B : Builtins) (σ : List (IL.Id × Value)) (s : Store H) (f : Frame)
    (t₁ t₂ t' : AddrType) (b₁ : BitVec t₁.intType.width) (b₂ : BitVec t₂.intType.width)
    (b' : BitVec t'.intType.width) (x₁ x₂ : MemIdx) : Prop where
  fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f))
  fa₁ : (VarEnv.empty.bindVals σ).findVal? "at_1" = some (Encode.toValue t₁)
  fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some (idxV b₁.toNat)
  fa₂ : (VarEnv.empty.bindVals σ).findVal? "at_2" = some (Encode.toValue t₂)
  fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some (idxV b₂.toNat)
  fa' : (VarEnv.empty.bindVals σ).findVal? "at'" = some (Encode.toValue t')
  fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat))
  fx : (VarEnv.empty.bindVals σ).findVal? "x_1" = some (idxV x₁.toNat)
  fy : (VarEnv.empty.bindVals σ).findVal? "x_2" = some (idxV x₂.toNat)

/-- `memory.copy-le`'s right-hand side, evaluated. -/
theorem rhs_memoryCopyLe {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} (S : MCopyScope (hn := hn) B σ s f t₁ t₂ t' b₁ b₂ b' x₁ x₂)
    (hk : 1 ≤ b'.toNat) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "LOAD" (.tupE [.caseE "I32" (.tupE []), .optE (some (.caseE "%_%" (.tupE [
        .caseE "%" (.tupE [.numE (.natN 8)]), .caseE "U" (.tupE [])]))), .varE "x_2",
        .callE "memarg0" []]),
      .caseE "STORE" (.tupE [.caseE "I32" (.tupE []), .optE (some (.caseE "%" (.tupE [
        .caseE "%" (.tupE [.numE (.natN 8)])]))), .varE "x_1", .callE "memarg0" []]),
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0)
          (.numE (.natN 1))])]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
          (.numE (.natN 1))])]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
          (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])]),
      .caseE "MEMORY.COPY" (.tupE [.varE "x_1", .varE "x_2"])])
      (.list [aconstV (Encode.toValue t₁) b₁.toNat, aconstV (Encode.toValue t₂) b₂.toNat,
        Memory.load8uV x₂.toNat, Memory.store8V x₁.toNat,
        aconstV (Encode.toValue t₁) (b₁.toNat + 1), aconstV (Encode.toValue t₂) (b₂.toNat + 1),
        aconstV (Encode.toValue t') (b'.toNat - 1),
        .case "MEMORY.COPY" (.tuple [idxV x₁.toNat, idxV x₂.toNat])]) := by
  have ea₁ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa₁)
  have ea₂ := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa₂)
  have ea' := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var S.fa')
  exact RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₁ (evalExp_var S.fi₁)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₂ (evalExp_var S.fi₂)))
    (RefsGC.evalExps_cons' (Memory.evalExp_load8u (Memory.memarg0Ok_simEnv B σ) (evalExp_var S.fy))
    (RefsGC.evalExps_cons' (Memory.evalExp_store8 (Memory.memarg0Ok_simEnv B σ) (evalExp_var S.fx))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₁ (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var S.fi₁)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea₂ (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var S.fi₂)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_predNat
      (evalExp_var S.fn) hk))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var S.fx) (evalExp_var S.fy)))
      RefsGC.evalExps_nil'))))))))

/-- The two `+ 1` successors of `memory.copy-le`, as Core's. -/
theorem adminsToV_mcopyLe {t₁ t₂ t' : AddrType} {b₁ : BitVec t₁.intType.width}
    {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width} {x₁ x₂ : MemIdx}
    (hw₁ : b₁.toNat + 1 < 2 ^ t₁.intType.width) (hw₂ : b₂.toNat + 1 < 2 ^ t₂.intType.width)
    (hk : b' ≠ 0) :
    adminsToV [aconst t₁ b₁, aconst t₂ b₂, load8u x₂, store8 x₁,
        aconst t₁ (b₁ + 1), aconst t₂ (b₂ + 1), aconst t' (b' - 1), .plain (.memoryCopy x₁ x₂)] =
      [aconstV (Encode.toValue t₁) b₁.toNat, aconstV (Encode.toValue t₂) b₂.toNat,
        Memory.load8uV x₂.toNat, Memory.store8V x₁.toNat,
        aconstV (Encode.toValue t₁) (b₁.toNat + 1), aconstV (Encode.toValue t₂) (b₂.toNat + 1),
        aconstV (Encode.toValue t') (b'.toNat - 1),
        .case "MEMORY.COPY" (.tuple [idxV x₁.toNat, idxV x₂.toNat])] := by
  simp only [adminsToV, State.adminToV_aconst, Memory.adminToV_load8u,
    Memory.adminToV_store8, Memory.toNat_add_one hw₁,
    Memory.toNat_add_one hw₂, Memory.toNat_sub_one hk]
  rfl

/-- A copy-family instance reads its scope back. -/
theorem mcopyScope_of {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fa₁ : (VarEnv.empty.bindVals σ).findVal? "at_1" = some (Encode.toValue t₁))
    (fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some (idxV b₁.toNat))
    (fa₂ : (VarEnv.empty.bindVals σ).findVal? "at_2" = some (Encode.toValue t₂))
    (fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some (idxV b₂.toNat))
    (fa' : (VarEnv.empty.bindVals σ).findVal? "at'" = some (Encode.toValue t'))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x_1" = some (idxV x₁.toNat))
    (fy : (VarEnv.empty.bindVals σ).findVal? "x_2" = some (idxV x₂.toNat)) :
    MCopyScope (hn := hn) B σ s f t₁ t₂ t' b₁ b₂ b' x₁ x₂ :=
  ⟨fz, fa₁, fi₁, fa₂, fi₂, fa', fn, fx, fy⟩

/-- A non-zero count, recovered from `otherwise` after `memory.copy-zero` (57). -/
theorem mcopy_nonzero {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t₁ t₂ t' : AddrType}
    {b₁ : BitVec t₁.intType.width} {b₂ : BitVec t₂.intType.width} {b' : BitVec t'.intType.width}
    {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst} {k : Nat} {w : Value} {L : Exp}
    (hk : 57 < k)
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "at_1" (.varT "addrtype" []), .expP "i_1" (.varT "num_" [.expA (.subE (.varE "at_1")
        (.varT "addrtype" []) (.varT "numtype" []))]), .expP "at_2" (.varT "addrtype" []),
      .expP "i_2" (.varT "num_" [.expA (.subE (.varE "at_2") (.varT "addrtype" [])
        (.varT "numtype" []))]), .expP "at'" (.varT "addrtype" []), .expP "n" (.varT "n" []),
      .expP "x_1" (.varT "idx" []), .expP "x_2" (.varT "idx" [])])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) L
      (configV hn ⟨s, f, [aconst t₁ b₁, aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩))
    (hL : L = .caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "MEMORY.COPY" (.tupE [.varE "x_1", .varE "x_2"])]]))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b'.toNat)))
    (ht₁ : s.mem? f x₁ = some (ma₁, mi₁)) (ht₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (hb : b₁.toNat + b'.toNat ≤ mi₁.bytes.size ∧ b₂.toNat + b'.toNat ≤ mi₂.bytes.size)
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t₁ b₁,
      aconst t₂ b₂, aconst t' b', .plain (.memoryCopy x₁ x₂)]⟩, w])) : b' ≠ 0 := by
  subst hL
  rintro rfl
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).memoryCopyZero
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq,
      evalExp_tup2 hl (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise_memoryCopyZero B ht₁ ht₂ hb)
  · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simpa using RefsGC.evalExp_num'))

/-- **`Step_read` 58 (`memory.copy-le`), backward, under validity.** -/
theorem bwdV_memoryCopyLe : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 58 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryCopyLe hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "x_2" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "MEMORY.COPY" (.tuple [X, Y])]])
      := by
    concl_inv hl
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ma₁, ma₂, mi₁, mi₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := mcopy_inv B hv hAT₁ hAT₂ hc
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have ho := else_head hp
  have hb := mcopy_inBounds B (k := 58) (by decide) hz ht₁ ht₂ ho
  have hk := mcopy_nonzero B (k := 58) (by decide) hq hl rfl fn ht₁ ht₂ hb ho
  have hle : b₁.toNat ≤ b₂.toNat := by
    have := Memory.cmp_true (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (RefsGC.evalExp_unpct (evalExp_var fi₁))
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) rfl
    simpa using this
  have hk1 : 1 ≤ b'.toNat := Nat.one_le_iff_ne_zero.2 fun h => hk (BitVec.eq_of_toNat_eq h)
  have hw₁ := lt_width (a := t₁) (mem_lt32 hv.store ht₁)
  have hw₂ := lt_width (a := t₂) (mem_lt32 hv.store ht₂)
  have hw : w = _ := EvalExp.unique (RefsGC.rhs_of_concl he)
    (rhs_memoryCopyLe B (mcopyScope_of B fz fa₁ fi₁ fa₂ fi₂ fa' fn fx fy) hk1)
  refine ⟨_, ?_, .memory (.copyLe ht₁ ht₂ hb hk hle)⟩
  rw [hw, adminsToV_mcopyLe (by omega) (by omega) hk]

/-- **`Step_read` 59 (`memory.copy-gt`), backward, under validity.** -/
theorem bwdV_memoryCopyGt : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 59 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv htc hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryCopyGt hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT₁, fa₁, hAT₁⟩ := hq "at_1" State.addrtypeT (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" (State.numAtT "at_1") (by simp)
  obtain ⟨AT₂, fa₂, hAT₂⟩ := hq "at_2" State.addrtypeT (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" (State.numAtT "at_2") (by simp)
  obtain ⟨AT', fa', -⟩ := hq "at'" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "x_2" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT₁, I₁]), .case "CONST" (.tuple [AT₂, I₂]),
      .case "CONST" (.tuple [AT', .case "%" (.tuple [N])]), .case "MEMORY.COPY" (.tuple [X, Y])]])
      := by
    concl_inv hl
  obtain ⟨t₁, t₂, t', b₁, b₂, b', x₁, x₂, ma₁, ma₂, mi₁, mi₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, ht₁, ht₂⟩ := mcopy_inv B hv hAT₁ hAT₂ hc
  have hz := State.typedV_state (Typing.typingFacts_simEnv B hn) htc
  have ho := else_head hp
  have hb := mcopy_inBounds B (k := 59) (by decide) hz ht₁ ht₂ ho
  have hk := mcopy_nonzero B (k := 59) (by decide) hq hl rfl fn ht₁ ht₂ hb ho
  have hk0 : b'.toNat ≠ 0 := fun h => hk (BitVec.eq_of_toNat_eq h)
  have hk1 : 1 ≤ b'.toNat := Nat.one_le_iff_ne_zero.2 hk0
  have hgt : b₂.toNat < b₁.toNat := by
    refine Nat.lt_of_not_le fun hle => BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).memoryCopyLe ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl,
        hq, evalExp_tup2 hl (rhs_memoryCopyLe B (mcopyScope_of B fz fa₁ fi₁ fa₂ fi₂ fa' fn fx fy)
          hk1), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact .elsePr (otherwise_memoryCopyLe B ht₁ ht₂ hb hk0)
    · exact .ifPr (RefsGC.evalExp_leNat (RefsGC.evalExp_unpct (evalExp_var fi₁))
        (RefsGC.evalExp_unpct (evalExp_var fi₂)) hle)
  have hw₁ := lt_width (a := t₁) (mem_lt32 hv.store ht₁)
  have hw₂ := lt_width (a := t₂) (mem_lt32 hv.store ht₂)
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
    (RefsGC.evalExps_cons' (Memory.evalExp_load8u (Memory.memarg0Ok_simEnv B σ) (evalExp_var fy))
    (RefsGC.evalExps_cons' (Memory.evalExp_store8 (Memory.memarg0Ok_simEnv B σ) (evalExp_var fx))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₁ (evalExp_var fi₁)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea₂ (evalExp_var fi₂)))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_predNat
      (evalExp_var fn) hk1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
      RefsGC.evalExps_nil')))))))))
  refine ⟨[aconst t₁ (b₁ + BitVec.ofNat _ b'.toNat - 1), aconst t₂ (b₂ + BitVec.ofNat _ b'.toNat - 1),
    load8u x₂, store8 x₁, aconst t₁ b₁, aconst t₂ b₂, aconst t' (b' - 1),
    .plain (.memoryCopy x₁ x₂)], ?_, .memory (.copyGt ht₁ ht₂ hb hk hgt)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_aconst, Memory.adminToV_load8u,
    Memory.adminToV_store8, Memory.toNat_add_ofNat_sub_one b₁ hk0 (by omega),
    Memory.toNat_add_ofNat_sub_one b₂ hk0 (by omega), Memory.toNat_sub_one hk]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round4Read
