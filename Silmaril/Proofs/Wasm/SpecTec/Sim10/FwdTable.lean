module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRestQ
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallIndirectTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureBrTable

/-!
# The 1.0 script forward at `br_table` and the four `call_indirect` cases

* `fwdAt10_brTable`: V1's single `PureStep.brTable` is `Step_pure/br_table-lt` (12) in range and
  `br_table-ge` (13) out of range. The rules are 2.0's with 1.0's quantifiers (`PureBrTable`), so
  2.0's environment-generic conclusion evaluation (`Sim20.Pure.eval_brTableLhs`) applies. The
  index `i : val_(I32)` is typed from the code (`typedV_valI32_of_const10`), and every label index
  is a typed `labelidx` (`typedV_labelidx10`).
* `fwdAt10_callIndirect`: `Step_read/call_indirect-call` (3) fires forward, from the typed
  state; the firing itself is round 2's `body10_callIndirect`.
* `fwdAt10_callIndirectBounds`, `…Null`, `…Type`: `Step_read/call_indirect-trap` (4) is
  `otherwise`. Its premise holds when rules 0–3 of `Step_read` do not fire on the same left-hand
  side (`otherwise_read10`): rules 0–2 (`block`, `loop`, `call`) have a one-instruction left-hand
  side (`not_body10_one`), and rule 3's premises are false at a missing entry, a null entry and a
  function of another type (`not_callBody10`, read back with round 2's `entry_of_eval10` and
  `typeMatch_of_eval10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  frameTable)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst TableInst FuncAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV evalExp_imm_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV RuleBody PremW DDerives otherwise otherwiseAt
  noElse SameLhs ValsOnly evalExp_case evalExp_tup2 evalExp_list1 typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## `br_table` -/

/-- The image of `CONST I32 c; BR_TABLE ls d`. -/
theorem adminsToV_brTable10 (c : BitVec 32) (ls : List LabelIdx) (d : LabelIdx) :
    adminsToV [value (.int .i32 c), .source (.brTable ls d)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
        .case "BR_TABLE" (.tuple [.list (ls.map idxV), idxV d])] := by
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- Every list of V1 label indices is a typed `labelidx*`. -/
theorem typedV_labelidxs10 (ls : List LabelIdx) :
    TypedV (simEnv10 B) (.iterT (.varT "labelidx" []) .list) (.list (ls.map idxV)) :=
  typedV_list_iff.2 fun _ hv => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hv
    exact typedV_labelidx10 l

/-- The scope of the `br_table` rules. -/
abbrev brTableScope10 (c : BitVec 32) (ls : List LabelIdx) (d : LabelIdx) :
    List (IL.Id × Value) :=
  [("i", pctV c.toNat), ("l*", .list (ls.map idxV)), ("l'", idxV d)]

/-- The quantifiers of the 1.0 `br_table` rules, typed in their scope. -/
theorem brTable_quants10 {c : BitVec 32} {ls : List LabelIdx} {d : LabelIdx}
    (hc : TypedV (simEnv10 B) valI32T (pctV c.toNat)) :
    QuantsOk (simEnv10 B) (VarEnv.empty.bindVals (brTableScope10 c ls d)) brTableQs10 :=
  QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl
    (typedV_labelidxs10 ls _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (typedV_labelidx10 d _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))

/-- `l*` in the `br_table` scope. -/
theorem evalExp_brTableLs10 {c : BitVec 32} {ls : List LabelIdx} {d : LabelIdx} :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals (brTableScope10 c ls d))
      (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])) (.list (ls.map idxV)) :=
  Sim20.Pure.evalExp_iter (by decide) rfl

/-- **`br_table-lt` fires forward** at an index in range. -/
theorem fires10_brTableLt {c : BitVec 32} {ls : List LabelIdx} {d l : LabelIdx}
    (hc : TypedV (simEnv10 B) valI32T (pctV c.toNat)) (hl : ls[c.toNat]? = some l) :
    Fires (simEnv10 B) "Step_pure" 12 (.tuple [.list (adminsToV
      [value (.int .i32 c), .source (.brTable ls d)]), .list (adminsToV [.source (.br l)])]) := by
  have hlt : c.toNat < ls.length := (List.getElem?_eq_some_iff.1 hl).1
  have hidx : (Value.list (ls.map idxV)).idx? c.toNat = some (idxV l) := by
    simp [Value.idx?, List.getElem?_map, hl]
  rw [adminsToV_brTable10]
  refine fires_of_ruleAt (hasRuleAt10_brTableLt B) (brTableScope10 c ls d) (brTable_quants10 hc)
    (evalExp_tup2 (Sim20.Pure.eval_brTableLhs rfl rfl rfl) (evalExp_list1 (evalExp_case
      (evalExp_idxE_iff.2 ⟨_, _, evalExp_brTableLs10, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩,
        hidx⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨_, evalExp_brTableLs10, rfl⟩, ?_⟩)))
  simp [cmpValues, Num.cmp, Res.ofOption, hlt]

/-- **`br_table-ge` fires forward** at an index out of range. -/
theorem fires10_brTableGe {c : BitVec 32} {ls : List LabelIdx} {d : LabelIdx}
    (hc : TypedV (simEnv10 B) valI32T (pctV c.toNat)) (hge : ls.length ≤ c.toNat) :
    Fires (simEnv10 B) "Step_pure" 13 (.tuple [.list (adminsToV
      [value (.int .i32 c), .source (.brTable ls d)]), .list (adminsToV [.source (.br d)])]) := by
  rw [adminsToV_brTable10]
  refine fires_of_ruleAt (hasRuleAt10_brTableGe B) (brTableScope10 c ls d) (brTable_quants10 hc)
    (evalExp_tup2 (Sim20.Pure.eval_brTableLhs rfl rfl rfl)
      (evalExp_list1 (evalExp_case (Sim.evalExp_var rfl))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨_, evalExp_brTableLs10, rfl⟩, ?_⟩)))
  simp [cmpValues, Num.cmp, Res.ofOption, hge]

/-- **`br_table` forward**: V1's `brTable`, by `br_table-lt` or `br_table-ge`. -/
theorem fwdAt10_brTable (s : Store H) (f : Frame) (ls : List LabelIdx) (d : LabelIdx)
    (c : BitVec 32) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.brTable ls d)]⟩
      ⟨s, f, [.source (.br (ls[c.toNat]?.getD d))]⟩ := by
  refine fwdAt10_of_spure' fun hcode => ?_
  have hc : TypedV (simEnv10 B) valI32T (pctV c.toNat) := typedV_valI32_of_const10 (by
    have h := typedV_head10 hcode
    rwa [adminToV_value] at h)
  match hl : ls[c.toNat]? with
  | some l => exact spure10_of_fires (fires10_brTableLt hc hl)
  | none =>
    exact spure10_of_fires (fires10_brTableGe hc (List.getElem?_eq_none_iff.1 hl))

/-! ## `call_indirect-call` -/

/-- The image of `CONST I32 c; CALL_INDIRECT x`. -/
theorem adminsToV_callIndirect10 (c : BitVec 32) (x : TypeIdx) :
    adminsToV [value (.int .i32 c), .source (.callIndirect x)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]), .case "CALL_INDIRECT" (idxV x)] := by
  rw [adminsToV_map10, List.map_cons, adminToV_value]
  rfl

/-- The index of a typed `CONST I32 c; CALL_INDIRECT x` is a `val_(I32)`. -/
theorem typedV_ci10 {c : BitVec 32} {x : TypeIdx}
    (h : TypedV (simEnv10 B) adminsT
      (.list (adminsToV [value (.int .i32 c), .source (.callIndirect x)]))) :
    TypedV (simEnv10 B) valI32T (pctV c.toNat) :=
  typedV_valI32_of_const10 (by
    have h' := typedV_head10 h
    rwa [adminToV_value] at h')

/-- **`call_indirect-call` forward**: V1's `callIndirect`. -/
theorem fwdAt10_callIndirect (s : Store H) (f : Frame) (x : TypeIdx) (c : BitVec 32)
    (t : TableInst) (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType)
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[c.toNat]? = some (some a)) (hfn : s.funcs[a.value]? = some fn)
    (hty : fn.type = ft) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ ⟨s, f, [.invoke a]⟩ := by
  refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (k := 3) ?_
  have hc := typedV_ci10 hcode
  obtain ⟨ps, tt, rules, hrel, rfl, h3⟩ := hasRuleAt10_callIndirect B
  have hρ := Sim20.Pure.valsOnly_bindVals (ciScope (stateV hn s f) (pctV c.toNat) (idxV x) a)
  exact ⟨tt, rules, _, hrel, h3, body10_callIndirect (hz _ hρ) (hc _ hρ)
    (typedV_idxAll10 x _ hρ) ht hft hent hfn hty⟩

/-! ## `call_indirect-trap`: the `otherwise` premise -/

/-- Two rules at one index of one relation are equal. -/
theorem ruleAt_eq10 {env : Env} {x : IL.Id} {op op' : MixopS} {k : Nat} {r r' : Rule}
    (h : HasRuleAt env x op k r) (h' : HasRuleAt env x op' k r') : r = r' := by
  obtain ⟨ps, t, rules, hrel, -, hk⟩ := h
  obtain ⟨ps', t', rules', hrel', -, hk'⟩ := h'
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  rw [hrel'.2.2.2] at hk
  exact Option.some.inj (hk.symm.trans hk')

/-- **`otherwise` at rule `i` of 1.0's `Step_read`**, from a refutation of every earlier rule on
the same left-hand side. -/
theorem otherwise_read10 {i : Nat} {a₀ b₀ : Value}
    (h : ∀ j, j < i → ∀ r, HasRuleAt (simEnv10 B) "Step_read" "%~>%" j r → ∀ d,
      ¬ RuleBody (simEnv10 B) (DDerives (simEnv10 B) noElse)
        (otherwiseAt (simEnv10 B) "Step_read" [] j (.tuple [a₀, d])) [] [] "%~>%" r
        (.tuple [a₀, d])) :
    otherwiseAt (simEnv10 B) "Step_read" [] i (.tuple [a₀, b₀]) := by
  rw [otherwiseAt]
  intro j hj ps op t rules r hrel hr w hw
  obtain ⟨ps', t', rules', hrel', rfl, -⟩ := hasRuleAt10_block B
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  obtain ⟨rfl, rfl, -, -⟩ := hrel'
  obtain ⟨a, b, d, hv, rfl⟩ := hw
  obtain ⟨rfl, -⟩ : a₀ = a ∧ b₀ = b := by simpa using hv
  exact h j hj r ⟨[], t, rules, hrel, rfl, hr⟩ d

/-- A rule body `z; es ~> rh` at a configuration, inverted (any interpretation). -/
theorem bodyCfg10_inv {env : Env} {D : Sim.Interp} {els : Prop} {nm : IL.Id} {qs : List Param}
    {es : List Exp} {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (hb : RuleBody env D els [] [] "%~>%"
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems)
      (.tuple [configV hn c, w])) :
    ∃ σ, (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps env (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      ∀ pr ∈ prems, PremW env D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨-, ρ₀, σ, hρ, -, he, hp⟩ := hb
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hρ).symm
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨u₁, u₂, hZ, hL, hU⟩ := Sim.State.evalExp_tup2_inv (hu' ▸ hu)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hU
  obtain ⟨rfl, rfl⟩ := hU
  exact ⟨σ, evalExp_varE_iff.1 hZ, Sim.RefsGC.elems_of_list hL, hp⟩

/-- A rule whose left-hand side has one instruction does not apply to two. -/
theorem not_body10_one {D : Sim.Interp} {els : Prop} {nm : IL.Id} {qs : List Param} {e rh : Exp}
    {prems : List Prem} {s : Store H} {f : Frame} {a₁ a₂ : Admin} {w : Value}
    (hb : RuleBody (simEnv10 B) D els [] [] "%~>%"
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [e]]), rh]) prems)
      (.tuple [configV hn ⟨s, f, [a₁, a₂]⟩, w])) : False := by
  obtain ⟨σ, -, hes, -⟩ := bodyCfg10_inv hb
  obtain ⟨a, he, -⟩ := codes10_one hes
  simp at he

/-- **`call_indirect-call`'s body, read back**: the entry at `c` names a function, of the named
type. -/
theorem callBody10_inv {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame} {x : TypeIdx}
    {c : BitVec 32} {t : TableInst} {w : Value} (ht : frameTable s f = some t)
    (hb : RuleBody (simEnv10 B) D els [] [] "%~>%" callIndirectRule10
      (.tuple [configV hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩, w])) :
    ∃ fa, t.refs[c.toNat]? = some (some fa) ∧ ∀ (ft : V1.FuncType) (fn : FuncInst V1.Func H),
      f.module.types[x.toNat]? = some ft → s.funcs[fa.value]? = some fn → fn.type = ft := by
  obtain ⟨σ, fz, hes, hp⟩ := bodyCfg10_inv hb
  obtain ⟨a₁, a₂, he, h₁, h₂⟩ := codes10_two hes
  obtain ⟨rfl, rfl⟩ : value (.int .i32 c) = a₁ ∧ (.source (.callIndirect x) : Admin) = a₂ := by
    simpa using he
  obtain ⟨c', hcc, fi⟩ := constI32_of_lhs10 h₁
  obtain rfl : c = c' := by
    simp only [value, Execution.Runtime.Value.int] at hcc
    cases hcc
    rfl
  have fx := evalExp_varE_iff.1 (idx_of_caseE10 h₂ rfl)
  obtain ⟨fa, hent, fa'⟩ := entry_of_eval10 fz (evalExp_varE_iff.1 fi) ht rfl
    (Sim20.Pure.ifPrem (hp _ (.head _)))
  exact ⟨fa, hent, fun ft fn hft hfn => typeMatch_of_eval10 fz fx fa' hft hfn rfl rfl
    (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))⟩

/-- **`call_indirect-trap`'s `otherwise` holds** where the entry at `c` does not name a function
of the named type. -/
theorem otherwise_callIndirectTrap10 {s : Store H} {f : Frame} {x : TypeIdx} {c : BitVec 32}
    {t : TableInst} {b₀ : Value} (ht : frameTable s f = some t)
    (hno : ¬ ∃ fa, t.refs[c.toNat]? = some (some fa) ∧ ∀ (ft : V1.FuncType)
      (fn : FuncInst V1.Func H), f.module.types[x.toNat]? = some ft →
        s.funcs[fa.value]? = some fn → fn.type = ft) :
    otherwiseAt (simEnv10 B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩, b₀]) :=
  otherwise_read10 fun j hj r hr d hb =>
    match j, hj with
    | 0, _ => by
      obtain rfl := ruleAt_eq10 hr (hasRuleAt10_block B)
      exact not_body10_one hb
    | 1, _ => by
      obtain rfl := ruleAt_eq10 hr (hasRuleAt10_loop B)
      exact not_body10_one hb
    | 2, _ => by
      obtain rfl := ruleAt_eq10 hr (hasRuleAt10_call B)
      exact not_body10_one hb
    | 3, _ => by
      obtain rfl := ruleAt_eq10 hr (hasRuleAt10_callIndirect B)
      exact hno (callBody10_inv ht hb)
    | _ + 4, hj => absurd hj (by omega)

/-! ## `call_indirect-trap` forward -/

/-- **`call_indirect-trap` forward**, wherever the entry at `c` does not name a function of the
named type. -/
theorem fwdAt10_callIndirectTrap (s : Store H) (f : Frame) (x : TypeIdx) (c : BitVec 32)
    (t : TableInst) (ht : frameTable s f = some t)
    (hno : ¬ ∃ fa, t.refs[c.toNat]? = some (some fa) ∧ ∀ (ft : V1.FuncType)
      (fn : FuncInst V1.Func H), f.module.types[x.toNat]? = some ft →
        s.funcs[fa.value]? = some fn → fn.type = ft) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10_of_sread fun hz hcode => sread10_of_fires (k := 4) ?_
  have hc := typedV_ci10 hcode
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV c.toNat), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hlhs : configV hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [.case "CONST" (.tuple [caseNilV "I32",
        pctV c.toNat]), .case "CALL_INDIRECT" (idxV x)]]) := by
    rw [configV_eq_cfgV10, adminsToV_callIndirect10]
  have ho := otherwise_callIndirectTrap10 (B := B) (hn := hn) (b₀ := .list (adminsToV [.trap]))
    ht hno
  rw [hlhs] at ho ⊢
  exact fires_of_ruleAt (hasRuleAt10_callIndirectTrap B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fi (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fx (typedV_idxAll10 x _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (Sim.evalExp_var fx)))))
      (evalExp_list1 Sim20.Pure.evalExp_caseNil))
    (prems_one (.elsePr ho))

/-- **`call_indirect` out of bounds, forward.** -/
theorem fwdAt10_callIndirectBounds (s : Store H) (f : Frame) (x : TypeIdx) (c : BitVec 32)
    (t : TableInst) (ht : frameTable s f = some t) (hnone : t.refs[c.toNat]? = none) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_callIndirectTrap s f x c t ht fun ⟨_, h, _⟩ => by simp [hnone] at h

/-- **`call_indirect` at a null entry, forward.** -/
theorem fwdAt10_callIndirectNull (s : Store H) (f : Frame) (x : TypeIdx) (c : BitVec 32)
    (t : TableInst) (ht : frameTable s f = some t) (hnull : t.refs[c.toNat]? = some none) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_callIndirectTrap s f x c t ht fun ⟨_, h, _⟩ => by simp [hnull] at h

/-- **`call_indirect` at a function of another type, forward.** -/
theorem fwdAt10_callIndirectType (s : Store H) (f : Frame) (x : TypeIdx) (c : BitVec 32)
    (t : TableInst) (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType)
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[c.toNat]? = some (some a)) (hfn : s.funcs[a.value]? = some fn)
    (hty : fn.type ≠ ft) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect x)]⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_callIndirectTrap s f x c t ht fun ⟨a', h, hall⟩ => by
    obtain rfl : a = a' := by simpa [hent] using h
    exact hty (hall ft fn hft hfn)

end Silmaril.Wasm.SpecTec.Sim10.Whole
