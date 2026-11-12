module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Loads

/-!
# Track memory: `table.grow` and `memory.grow` succeeding, Core → SpecTec

`Step/table.grow-succeed` (15) and `Step/memory.grow-succeed` (26). Both rules bind the grown
instance as a quantifier and test it against `$growtable`/`$growmem`, whose only clauses bind
variables in `if` premises; under the evaluator those clauses fail definitely and `callDef`
falls back to the builtins (gap G3). `GrowFuns` states what `B` has to supply: the image of
Core's `TableInst.grow?`/`MemInst.grow?`. The updated state goes through the defined
`$with_tableinst`/`$with_meminst`, evaluated by their clauses (`withInstDefs_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs StateTyping HasClause1 modAddr)

/-! ## The environment facts -/

/-- `z, x, ti` (`$with_tableinst`) or `z, x, mi` (`$with_meminst`). -/
abbrev zxyPat (y : IL.Id) : List Arg := [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE y)]

/-- The body of `$with_tableinst`/`$with_meminst`: `$sof(z)[.F[…] = y]; $fof(z)`. -/
def withInstBody (F : AtomS) (y : IL.Id) : Exp :=
  .caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
      (.idxP (.dotP .rootP F) (modAddr F)) (.varE y),
    .callE "fof" [.expA (.varE "z")]])

/-- The definitions of the instance updaters. -/
structure WithInstDefs (env : Env) : Prop where
  withTableinst : HasClause1 env "with_tableinst" (zxyPat "ti") (withInstBody "TABLES" "ti")
  withMeminst : HasClause1 env "with_meminst" (zxyPat "mi") (withInstBody "MEMS" "mi")

set_option maxRecDepth 100000 in
/-- `baseEnv` has them. -/
theorem withInstDefs_baseEnv : WithInstDefs baseEnv := ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- So does every `simEnv B`. -/
theorem withInstDefs_simEnv (B : Builtins) : WithInstDefs (simEnv B) :=
  ⟨withInstDefs_baseEnv.withTableinst.withBuiltins B,
    withInstDefs_baseEnv.withMeminst.withBuiltins B⟩

/-- **What `B` supplies for growth** (gap G3): `$growtable` and `$growmem` on encoded instances
are the images of Core's `TableInst.grow?` and `MemInst.grow?` where those succeed. Stated in
term-only scopes (`ValsOnly`): a scope binding the definition variable `growtable` to another
function would make the call evaluate that one, so the unrestricted statement held in no
environment (the same defect as round 1's `RefsGC.RFuns`; fixed in the integration branch). -/
structure GrowFuns (env : Env) : Prop where
  /-- `$growtable(ti, n, r)`. -/
  growtable : ∀ (ρ : VarEnv), ValsOnly ρ → ∀ (e₁ e₂ e₃ : Exp) (ti ti' : TableInst) (n : Nat) (r : Ref),
    ti.grow? n r = some ti' → EvalExp env ρ e₁ (tableInstToValue CT ti) →
    EvalExp env ρ e₂ (.num (.natN n)) → EvalExp env ρ e₃ (refToValue r) →
    EvalExp env ρ (.callE "growtable" [.expA e₁, .expA e₂, .expA e₃]) (tableInstToValue CT ti')
  /-- `$growmem(mi, n)`. -/
  growmem : ∀ (ρ : VarEnv), ValsOnly ρ → ∀ (e₁ e₂ : Exp) (mi mi' : MemInst) (n : Nat),
    mi.grow? n = some mi' → EvalExp env ρ e₁ (memInstToValue mi) →
    EvalExp env ρ e₂ (.num (.natN n)) →
    EvalExp env ρ (.callE "growmem" [.expA e₁, .expA e₂]) (memInstToValue mi')

/-- **Typing of the grown instances** (for family E): a table or memory of a typed state is a
typed `tableinst`/`meminst`. -/
structure InstTyping (env : Env) : Prop where
  tableinst : ∀ {H : Type} (hn : H → String) (s : Store H) (f : Frame) (ti : TableInst),
    ti ∈ s.tables → TypedV env stateT (stateV hn s f) →
      TypedV env (.varT "tableinst" []) (tableInstToValue CT ti)
  meminst : ∀ {H : Type} (hn : H → String) (s : Store H) (f : Frame) (mi : MemInst),
    mi ∈ s.mems → TypedV env stateT (stateV hn s f) →
      TypedV env (.varT "meminst" []) (memInstToValue mi)

/-! ## Evaluating the updaters -/

section Eval

variable {env : Env} (D : StateDefs env) (W : WithInstDefs env) {ρ : VarEnv}

include D in
/-- `$sof(z)[.F[$fof(z).MODULE.F[x]] = Y]; $fof(z)` in the updater's scope `ρ₀`. -/
theorem evalExp_withInstBody {ρ₀ : VarEnv} {F' : AtomS} {y : IL.Id} {S F S' M Y : Value}
    {Ls As : List Value} {n a : Nat} (hf : ρ₀.findDef? "fof" = none)
    (hs : ρ₀.findDef? "sof" = none) (fz : ρ₀.findVal? "z" = some (stV S F))
    (fx : ρ₀.findVal? "x" = some (idxV n)) (fy : ρ₀.findVal? y = some Y)
    (hS : S.field? F' = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? F' = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hl : a < Ls.length) (hS' : S.setField F' (.list (Ls.set a Y)) = some S') :
    EvalExp env ρ₀ (withInstBody F' y) (stV S' F) := by
  have hidx : EvalExp env ρ₀ (modAddr F') (.num (.natN a)) :=
    State.evalExp_modAddr D hf fz fx hM hA ha
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof D hf (evalExp_var fz)))
  refine evalExp_updE_iff.2 ⟨S, Y, State.evalExp_sof D hs (evalExp_var fz), evalExp_var fy, ?_⟩
  exact State.pathSet_idx (State.pathGet_dot State.pathGet_root hS) hidx
    (by simp [Value.setIdx, hl]) (State.pathSet_dot State.pathGet_root hS' State.pathSet_root)

end Eval

/-- The scope `$with_tableinst`/`$with_meminst` match their arguments into. -/
theorem matchArgs_zxyPat {env : Env} {y : IL.Id} {Z X Y : Value}
    (hy : ((VarEnv.empty.bindVal "z" Z).bindVal "x" X).findVal? y = none) :
    MatchArgs env VarEnv.empty (zxyPat y) [.val Z, .val X, .val Y]
      (((VarEnv.empty.bindVal "z" Z).bindVal "x" X).bindVal y Y) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE hy)) matchArgs_nil))

/-- A table replaced in a store is a table of the new store. -/
theorem mem_setTable {H : Type} {s : Store H} {a : Nat} {t : TableInst}
    (ha : a < s.tables.length) : t ∈ (s.setTable a t).tables := by
  rw [Store.setTable, List.mem_iff_getElem?]
  exact ⟨a, by simp [ha]⟩

/-- A memory replaced in a store is a memory of the new store. -/
theorem mem_setMem {H : Type} {s : Store H} {a : Nat} {m : MemInst}
    (ha : a < s.mems.length) : m ∈ (s.setMem a m).mems := by
  rw [Store.setMem, List.mem_iff_getElem?]
  exact ⟨a, by simp [ha]⟩

/-! ## Forward, at the Core encoding -/

section Forward

variable {H : Type} (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (GF : GrowFuns (simEnv B)) (IT : InstTyping (simEnv B))
include T St GF IT

/-- `TableStep.growSucceed`, forward, for a table shorter than `2 ^ |at|` (in any profile: the
SpecTec rule has no resource premise). -/
theorem fwd_tableGrowSucceed {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {n : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti ti' : TableInst}
    (ht : s.table? f x = some (ta, ti)) (hg : ti.grow? n.toNat r = some ti')
    (hw : ti.refs.length < 2 ^ a.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [.ref r, aconst a n, .plain (.tableGrow x)]⟩
      ⟨s.setTable ta ti', f, [aconst a (BitVec.ofNat _ ti.refs.length)]⟩ := by
  intro hc hc'
  obtain ⟨hta, hti⟩ := State.Store.table?_eq_some ht
  have hl : ta < s.tables.length := (List.getElem?_eq_some_iff.1 hti).1
  have hT' : TypedV (simEnv B) (.varT "tableinst" []) (tableInstToValue CT ti') :=
    IT.tableinst hn _ f ti' (mem_setTable hl) (State.typedV_state T hc')
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("ref", refToValue r),
    ("at", Encode.toValue a), ("n", .num (.natN n.toNat)), ("x", idxV x.toNat),
    ("ti", tableInstToValue CT ti')]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have et : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) (tableInstToValue CT ti) :=
    State.evalExp_table_of (State.stateDefs_simEnv B) rfl (evalExp_var rfl) (evalExp_var rfl)
      (State.tableAt_of_table? hn ht)
  have ew : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "with_tableinst" [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "ti")])
      (stateV hn (s.setTable ta ti') f) :=
    State.evalExp_call1 (withInstDefs_simEnv B).withTableinst rfl
      (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
        (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
          (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
            Silmaril.SpecTec.Equiv.evalArgs_nil)))
      (matchArgs_zxyPat rfl)
      (evalExp_withInstBody (State.stateDefs_simEnv B) rfl rfl rfl rfl rfl
        (State.storeV_TABLES hn s) (State.frameV_MODULE f) (State.moduleV_TABLES _)
        (State.getElem?_map_natN hta) (by simpa using hl) (State.storeV_setTable hn s ta ti'))
  have elen : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS"))
      (.num (.natN ti.refs.length)) := by
    simpa only [List.length_map] using RefsGC.evalExp_len (RefsGC.evalExp_dot et
      (State.tableInstV_REFS ti))
  show SStep _ (cfgV _ [adminToV (.ref r), adminToV (aconst a n), _])
    (cfgV _ [adminToV (aconst a (BitVec.ofNat _ ti.refs.length))])
  rw [State.adminToV_ref, State.adminToV_aconst, State.adminToV_aconst, toNat_ofNat_of_lt hw]
  exact dderives_of_ruleAt (hasRuleAt_simEnv B
      Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.tableGrowSucceed) σ
    (QuantsOk.cons rfl (State.typedV_state T hc _ hρ)
      (QuantsOk.cons rfl (State.typedV_ref_of_mem B T St hc (by simp) _ hρ)
      (QuantsOk.cons rfl (St.addr a _ hρ) (QuantsOk.cons rfl (St.nat _ _ hρ)
      (QuantsOk.cons rfl (St.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (hT' _ hρ)
        QuantsOk.nil))))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ew
      (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
        (evalExp_constPct (evalExp_subAt rfl) elen) RefsGC.evalExps_nil')))))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl)
      (GF.growtable _ hρ _ _ _ ti ti' n.toNat r hg et (evalExp_var rfl) (evalExp_var rfl)))))

omit T St GF IT in
/-- `$mem(z, x).BYTES| / (64 · $Ki)`, for a memory of `p` whole pages. -/
theorem evalExp_pages {σ : List (IL.Id × Value)} {e : Exp} {p : Nat}
    (he : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) e (.num (.natN (p * 65536)))) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT))
        .ratT .natT) (.num (.natN p)) := by
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cvtE e .natT .ratT)
      (.num (.ratN ((p * 65536 : Nat) : ℚ))) := evalExp_cvtE_iff.2 ⟨_, _, he, rfl, rfl⟩
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT)
      (.num (.ratN ((65536 : Nat) : ℚ))) :=
    evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_mulNat RefsGC.evalExp_num' (kiOk_simEnv B σ), rfl, rfl⟩
  have hq : ((p * 65536 : Nat) : ℚ) / ((65536 : Nat) : ℚ) = (p : ℚ) := by
    rw [Rat.natCast_mul]
    exact Rat.mul_div_cancel (by decide)
  have e₃ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
        (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT))
      (.num (.ratN (p : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show ((65536 : Nat) : ℚ) ≠ 0 by decide, ↓reduceIte, hq]
      rfl⟩⟩
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, by simp [Num.cvt], rfl⟩

/-- `MemoryStep.growSucceed`, forward, for a memory of whole pages, fewer than `2 ^ |at|` of
them (in any profile). -/
theorem fwd_memoryGrowSucceed {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi mi' : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (hg : mi.grow? n.toNat = some mi')
    (hpg : mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0)
    (hw : mi.pages < 2 ^ a.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩
      ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩ := by
  intro hc hc'
  obtain ⟨hma, hmi⟩ := Store.mem?_eq_some hm
  have hl : ma < s.mems.length := (List.getElem?_eq_some_iff.1 hmi).1
  have hM' : TypedV (simEnv B) (.varT "meminst" []) (memInstToValue mi') :=
    IT.meminst hn _ f mi' (mem_setMem hl) (State.typedV_state T hc')
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("at", Encode.toValue a),
    ("n", .num (.natN n.toNat)), ("x", idxV x.toNat), ("mi", memInstToValue mi')]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have em : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) (memInstToValue mi) :=
    evalExp_mem_of (State.stateDefs_simEnv B) (evalExp_var rfl) (evalExp_var rfl)
      (memAt_of_mem? hn hm)
  have ew : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "with_meminst" [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "mi")])
      (stateV hn (s.setMem ma mi') f) :=
    State.evalExp_call1 (withInstDefs_simEnv B).withMeminst rfl
      (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
        (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
          (Silmaril.SpecTec.Equiv.evalArgs_cons (evalExp_var rfl)
            Silmaril.SpecTec.Equiv.evalArgs_nil)))
      (matchArgs_zxyPat rfl)
      (evalExp_withInstBody (State.stateDefs_simEnv B) rfl rfl rfl rfl rfl
        (State.storeV_MEMS hn s) (State.frameV_MODULE f) (State.moduleV_MEMS _)
        (State.getElem?_map_natN hma) (by simpa using hl) (by simp [storeV, Store.setMem,
          List.map_set]))
  have hp : (bytesL mi.bytes).length = mi.pages * 65536 := by
    rw [bytesL_length, MemInst.pages]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpg)).symm
  have elen : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"))
      (.num (.natN (mi.pages * 65536))) :=
    hp ▸ RefsGC.evalExp_len (RefsGC.evalExp_dot em (memInstV_BYTES mi))
  show SStep _ (cfgV _ [adminToV (aconst a n), _])
    (cfgV _ [adminToV (aconst a (BitVec.ofNat _ mi.pages))])
  rw [State.adminToV_aconst, State.adminToV_aconst, toNat_ofNat_of_lt hw]
  exact dderives_of_ruleAt (hasRuleAt_simEnv B
      Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.memoryGrowSucceed) σ
    (QuantsOk.cons rfl (State.typedV_state T hc _ hρ)
      (QuantsOk.cons rfl (St.addr a _ hρ) (QuantsOk.cons rfl (St.nat _ _ hρ)
      (QuantsOk.cons rfl (St.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (hM' _ hρ)
        QuantsOk.nil)))))
    (evalExp_tup2 (by mem_eval_tac) (evalExp_case (evalExp_tup2 ew
      (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
        (evalExp_constPct (evalExp_subAt rfl) (evalExp_pages B elen))
        RefsGC.evalExps_nil')))))
    (prems_one (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl)
      (GF.growmem _ hρ _ _ mi mi' n.toNat hg em (evalExp_var rfl)))))

end Forward

end Silmaril.Wasm.SpecTec.Sim.Memory
