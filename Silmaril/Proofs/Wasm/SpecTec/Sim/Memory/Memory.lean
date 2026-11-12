module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Table

/-!
# Track memory: `memory.fill`, `memory.copy`, `memory.init`, Core → SpecTec (rules)

`Step_read` 53–62, constructed for arbitrary state values, by the same pattern as the table
rules (`Memory/Table.lean`): the `otherwise` premises are discharged by opcode, refuting by hand
the earlier rules of the same instruction. The residual instructions the iterating rules produce
(`STORE I32 8 x $memarg0`, `LOAD I32 (8 _ U) x $memarg0`) call `$memarg0`, taken as the
hypothesis `hm0` (discharged at `simEnv B` by `evalExp_memarg0_simEnv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open State (StateDefs StateTyping aconstV idxV)

/-! ## Memories, data segments, `$memarg0` -/

section Generic

variable {env : Env}

/-- The memory the frame's module lists at index `n` is `m`, in the store `S`. -/
def MemAt (S F : Value) (n : Nat) (m : Value) : Prop :=
  ∃ M Ls As a, S.field? "MEMS" = some (.list Ls) ∧ F.field? "MODULE" = some M ∧
    M.field? "MEMS" = some (.list As) ∧ As[n]? = some (.num (.natN a)) ∧ Ls[a]? = some m

/-- `$mem(z, x)` on a state whose memory at `n` is `m`. -/
theorem evalExp_mem_of (D : StateDefs env) {σ : List (IL.Id × Value)} {ez ex : Exp}
    {S F m : Value} {n : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (hm : MemAt S F n m) :
    EvalExp env (VarEnv.empty.bindVals σ) (.callE "mem" [.expA ez, .expA ex]) m := by
  obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := hm
  exact State.evalExp_mem D (findDef_bindVals_empty σ _) hz hx hS hM hA ha hr

/-- The length of the `BYTES` of the memory at `n`. -/
theorem evalExp_memBytesLen (D : StateDefs env) {σ : List (IL.Id × Value)} {ez ex : Exp}
    {S F m : Value} {bs : List Value} {n : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs)) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "mem" [.expA ez, .expA ex]) "BYTES")) (.num (.natN bs.length)) :=
  RefsGC.evalExp_len (RefsGC.evalExp_dot (evalExp_mem_of D hz hx hm) hB)

/-- `$memarg0`'s value, `{ALIGN 0, OFFSET 0}`. -/
abbrev memarg0V : Value := memargV Silmaril.Wasm.Execution.Core.memarg0

/-- `STORE I32 8 x $memarg0`. -/
abbrev store8V (n : Nat) : Value :=
  .case "STORE" (.tuple [i32V, .opt (some (.case "%" (.tuple [idxV 8]))), idxV n, memarg0V])

/-- `LOAD I32 (8 _ U) x $memarg0`. -/
abbrev load8uV (n : Nat) : Value :=
  .case "LOAD" (.tuple [i32V, .opt (some (.case "%_%" (.tuple [idxV 8, .case "U" (.tuple [])]))),
    idxV n, memarg0V])

/-- `$memarg0()` evaluates to `{ALIGN 0, OFFSET 0}` in every rule assignment. -/
def Memarg0Ok (env : Env) : Prop :=
  ∀ σ : List (IL.Id × Value), EvalExp env (VarEnv.empty.bindVals σ) (.callE "memarg0" []) memarg0V

variable {ρ : VarEnv}

/-- `STORE I32 8 X $memarg0`, evaluated. -/
theorem evalExp_store8 (hm0 : EvalExp env ρ (.callE "memarg0" []) memarg0V) {X : IL.Id}
    {n : Nat} (hx : EvalExp env ρ (.varE X) (idxV n)) :
    EvalExp env ρ (.caseE "STORE" (.tupE [.caseE "I32" (.tupE []),
      .optE (some (.caseE "%" (.tupE [.caseE "%" (.tupE [.numE (.natN 8)])]))), .varE X,
      .callE "memarg0" []])) (store8V n) :=
  evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' (by eval_tac)
    (RefsGC.evalExps_cons' (evalExp_optE_some_iff.2 ⟨_, by eval_tac, rfl⟩)
    (RefsGC.evalExps_cons' hx (RefsGC.evalExps_cons' hm0 RefsGC.evalExps_nil')))))

/-- `LOAD I32 (8 _ U) X $memarg0`, evaluated. -/
theorem evalExp_load8u (hm0 : EvalExp env ρ (.callE "memarg0" []) memarg0V) {X : IL.Id}
    {n : Nat} (hx : EvalExp env ρ (.varE X) (idxV n)) :
    EvalExp env ρ (.caseE "LOAD" (.tupE [.caseE "I32" (.tupE []),
      .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE [.numE (.natN 8)]),
        .caseE "U" (.tupE [])]))), .varE X, .callE "memarg0" []])) (load8uV n) :=
  evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' (by eval_tac)
    (RefsGC.evalExps_cons' (evalExp_optE_some_iff.2 ⟨_, by eval_tac, rfl⟩)
    (RefsGC.evalExps_cons' hx (RefsGC.evalExps_cons' hm0 RefsGC.evalExps_nil')))))

end Generic

/-! ## `memory.fill` -/

section MFill

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- The code of a `memory.fill` step. -/
abbrev mfillCode (A V : Value) (i k n : Nat) : List Value :=
  [aconstV A i, V, aconstV A k, .case "MEMORY.FILL" (idxV n)]

/-- The bindings a `memory.fill` left-hand side forces. -/
theorem binds_memoryFill {ρ : VarEnv} {z : Value} {A V : Value} {i k n : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "MEMORY.FILL" (.varE "x")]])) (cfgV z (mfillCode A V i k n))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i") (idxV i) ∧
      EvalExp env ρ (.varE "n") (.num (.natN k)) ∧ EvalExp env ρ (.varE "x") (idxV n) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl), RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl)⟩

include D in
/-- `memory.fill-oob` does not fire in bounds. -/
theorem not_memoryFillOob {Dr : Interp} {els : Prop} {S F t A V c : Value} {rs : List Value}
    {i k n : Nat} (ht : MemAt S F n t) (hR : t.field? "BYTES" = some (.list rs))
    (h : i + k ≤ rs.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryFillOobRule
      (.tuple [cfgV (stV S F) (mfillCode A V i k n), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi, hk, hx⟩ := binds_memoryFill (RefsGC.lhs_of_concl he)
  have hc := cmp_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi) hk) (evalExp_memBytesLen D hz hx ht hR) rfl
  simp only [decide_eq_true_eq] at hc
  omega

/-- `memory.fill-zero` does not fire on a non-zero count. -/
theorem not_memoryFillZero {Dr : Interp} {els : Prop} {z A V c : Value} {i k n : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryFillZeroRule
      (.tuple [cfgV z (mfillCode A V i k n), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, hk', -⟩ := binds_memoryFill (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- The left-hand side of a `memory.fill` step has its constructors among `MEMORY.FILL` and those
of values. -/
theorem lhsIn_memoryFill {z A : Value} {i k n : Nat} {v : Silmaril.Wasm.Execution.Core.Val} :
    RefsGC.LhsIn (["MEMORY.FILL"] ++ RefsGC.valTags) (cfgV z (mfillCode A (valV v) i k n)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_val (RefsGC.valTags_sub _) v)
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/memory.fill-oob`: `z; (CONST at i) val (CONST at n) (MEMORY.FILL x) ~> TRAP` when
`i + n > |$mem(z, x).BYTES|`. -/
theorem sread_memoryFillOob (h : HasRuleAt env "Step_read" "%~>%" 53 memoryFillOobRule)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {i : BitVec a.intType.width}
    {v : Silmaril.Wasm.Execution.Core.Val} {k n : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hV : TypedV env State.valT (valV v)) (ht : MemAt S F n t)
    (hR : t.field? "BYTES" = some (.list rs)) (hi : rs.length < i.toNat + k) :
    SRead env (cfgV (stV S F) (mfillCode (Encode.toValue a) (valV v) i.toNat k n))
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", valV v), ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (hV _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          QuantsOk.nil))))))
    (by eval_tac)
    (prems_one (.ifPr (RefsGC.evalExp_gtNat
      (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_memBytesLen D (evalExp_var rfl) (evalExp_var rfl) ht hR) hi)))

/-- `Step_read/memory.fill-zero`: `z; (CONST at i) val (CONST at 0) (MEMORY.FILL x) ~> ε`, when
`memory.fill-oob` does not apply. -/
theorem sread_memoryFillZero (h : HasRuleAt env "Step_read" "%~>%" 54 memoryFillZeroRule)
    (h₅₃ : HasRuleAt env "Step_read" "%~>%" 53 memoryFillOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {i : BitVec a.intType.width}
    {v : Silmaril.Wasm.Execution.Core.Val} {n : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hV : TypedV env State.valT (valV v)) (ht : MemAt S F n t)
    (hR : t.field? "BYTES" = some (.list rs)) (hi : i.toNat ≤ rs.length) :
    SRead env (cfgV (stV S F) (mfillCode (Encode.toValue a) (valV v) i.toNat 0 n)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", valV v), ("n", .num (.natN 0)), ("x", idxV n)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 54) (b := .list []) (by decide) (exc := [53])
    (a := (cfgV (stV S F) (mfillCode (Encode.toValue a) (valV v) i.toNat 0 n)))
    lhsIn_memoryFill (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 53 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₅₃ hr']
      exact not_memoryFillOob D ht hR (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (hV _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          QuantsOk.nil))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/memory.fill-succ`: `z; (CONST at i) val (CONST at n) (MEMORY.FILL x) ~>
(CONST at i) val (STORE I32 8 x $memarg0) (CONST at (i + 1)) val (CONST at (n - 1)) (MEMORY.FILL x)`, when
neither `memory.fill-oob` nor `memory.fill-zero` applies. -/
theorem sread_memoryFillSucc (h : HasRuleAt env "Step_read" "%~>%" 55 memoryFillSuccRule)
    (h₅₃ : HasRuleAt env "Step_read" "%~>%" 53 memoryFillOobRule)
    (h₅₄ : HasRuleAt env "Step_read" "%~>%" 54 memoryFillZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType} {i : BitVec a.intType.width}
    {v : Silmaril.Wasm.Execution.Core.Val} {k n : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hV : TypedV env State.valT (valV v)) (ht : MemAt S F n t)
    (hR : t.field? "BYTES" = some (.list rs)) (hi : i.toNat + k ≤ rs.length) (hk : k ≠ 0)
    (hm0 : Memarg0Ok env) :
    SRead env (cfgV (stV S F) (mfillCode (Encode.toValue a) (valV v) i.toNat k n))
      [aconstV (Encode.toValue a) i.toNat, valV v, store8V n,
        aconstV (Encode.toValue a) (i.toNat + 1), valV v, aconstV (Encode.toValue a) (k - 1),
        .case "MEMORY.FILL" (idxV n)] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", valV v), ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a) i.toNat, valV v, store8V n, aconstV (Encode.toValue a) (i.toNat + 1), valV v, aconstV (Encode.toValue a) (k - 1), .case "MEMORY.FILL" (idxV n)])
    (i := 55) (by decide) (exc := [53, 54])
    (a := (cfgV (stV S F) (mfillCode (Encode.toValue a) (valV v) i.toNat k n)))
    lhsIn_memoryFill (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 53 ∨ j = 54) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₅₃ hr']
        exact not_memoryFillOob D ht hR hi
      · rw [RefsGC.relRules_of_ruleAt h₅₄ hr']
        exact not_memoryFillZero hk)
  have ea : EvalExp env (VarEnv.empty.bindVals σ)
      (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])) (Encode.toValue a) :=
    RefsGC.evalExp_sub_of (evalExp_var rfl)
  refine dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (hV _ hρ)
        (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
          QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons'
        (evalExp_store8 (hm0 σ) (evalExp_var (x := "x") rfl))
      (RefsGC.evalExps_cons' (evalExp_constPct ea (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (evalExp_constPct ea (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk))) (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))
    (prems_one (.elsePr hel))

end MFill

/-! ## `memory.copy` -/

section MCopy

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- The code of a `memory.copy` step. -/
abbrev mcopyCode (A₁ A₂ A' : Value) (i₁ i₂ k n₁ n₂ : Nat) : List Value :=
  [aconstV A₁ i₁, aconstV A₂ i₂, aconstV A' k, .case "MEMORY.COPY" (.tuple [idxV n₁, idxV n₂])]

/-- The bindings a `memory.copy` left-hand side forces (the index variables are named `X`, `Y`:
`x_1`, `x_2` in `memory.copy-oob`, `x`, `y` in the others). -/
theorem binds_memoryCopy {ρ : VarEnv} {X Y : IL.Id} {z A₁ A₂ A' : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_1"]),
      .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i_2"]),
      .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "MEMORY.COPY" (.tupE [.varE X, .varE Y])]]))
      (cfgV z (mcopyCode A₁ A₂ A' i₁ i₂ k n₁ n₂))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i_1") (idxV i₁) ∧
      EvalExp env ρ (.varE "i_2") (idxV i₂) ∧ EvalExp env ρ (.varE "n") (.num (.natN k)) ∧
      EvalExp env ρ (.varE X) (idxV n₁) ∧ EvalExp env ρ (.varE Y) (idxV n₂) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  have hxy := tup2_inv (RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl))
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_inv (RefsGC.evalExps_get hs 1 rfl rfl), const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl),
    hxy.1, hxy.2⟩

include D in
/-- `memory.copy-oob` does not fire when both ranges are in bounds. -/
theorem not_memoryCopyOob {Dr : Interp} {els : Prop} {S F t₁ t₂ A₁ A₂ A' c : Value}
    {rs₁ rs₂ : List Value} {i₁ i₂ k n₁ n₂ : Nat} (ht₁ : MemAt S F n₁ t₁)
    (hR₁ : t₁.field? "BYTES" = some (.list rs₁)) (ht₂ : MemAt S F n₂ t₂)
    (hR₂ : t₂.field? "BYTES" = some (.list rs₂)) (h : i₁ + k ≤ rs₁.length ∧ i₂ + k ≤ rs₂.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryCopyOobRule
      (.tuple [cfgV (stV S F) (mcopyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi₁, hi₂, hk, hx, hy⟩ := binds_memoryCopy (RefsGC.lhs_of_concl he)
  have ho := or_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi₁) hk) (evalExp_memBytesLen D hz hx ht₁ hR₁)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi₂) hk) (evalExp_memBytesLen D hz hy ht₂ hR₂)
  omega

/-- `memory.copy-zero` does not fire on a non-zero count. -/
theorem not_memoryCopyZero {Dr : Interp} {els : Prop} {z A₁ A₂ A' c : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryCopyZeroRule
      (.tuple [cfgV z (mcopyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, -, hk', -, -⟩ := binds_memoryCopy (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- `memory.copy-le` does not fire when the destination is above the source. -/
theorem not_memoryCopyLe {Dr : Interp} {els : Prop} {z A₁ A₂ A' c : Value} {i₁ i₂ k n₁ n₂ : Nat}
    (hgt : i₂ < i₁) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryCopyLeRule
      (.tuple [cfgV z (mcopyCode A₁ A₂ A' i₁ i₂ k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, hi₁, hi₂, -, -, -⟩ := binds_memoryCopy (RefsGC.lhs_of_concl he)
  have hc := cmp_true (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    (RefsGC.evalExp_unpct hi₁) (RefsGC.evalExp_unpct hi₂) rfl
  simp only [decide_eq_true_eq] at hc
  omega

/-- The left-hand side of a `memory.copy` step has its constructors among `MEMORY.COPY` and
`CONST`. -/
theorem lhsIn_memoryCopy {z A₁ A₂ A' : Value} {i₁ i₂ k n₁ n₂ : Nat} :
    RefsGC.LhsIn (["MEMORY.COPY"] ++ RefsGC.valTags) (cfgV z (mcopyCode A₁ A₂ A' i₁ i₂ k n₁ n₂)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/memory.copy-oob`. -/
theorem sread_memoryCopyOob (h : HasRuleAt env "Step_read" "%~>%" 56 memoryCopyOobRule)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : MemAt S F n₁ t₁) (hR₁ : t₁.field? "BYTES" = some (.list rs₁))
    (ht₂ : MemAt S F n₂ t₂) (hR₂ : t₂.field? "BYTES" = some (.list rs₂))
    (hoob : rs₁.length < i₁.toNat + k ∨ rs₂.length < i₂.toNat + k) :
    SRead env (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)) [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x_1", idxV n₁), ("x_2", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ho := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_memBytesLen D ez (evalExp_var (x := "x_1") rfl) ht₁ hR₁) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_memBytesLen D ez (evalExp_var (x := "x_2") rfl) ht₂ hR₂) rfl)
  rw [decide_eq_true hoob] at ho
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac) (prems_one (.ifPr ho))

/-- `Step_read/memory.copy-zero`. -/
theorem sread_memoryCopyZero (h : HasRuleAt env "Step_read" "%~>%" 57 memoryCopyZeroRule)
    (h₅₆ : HasRuleAt env "Step_read" "%~>%" 56 memoryCopyOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : MemAt S F n₁ t₁) (hR₁ : t₁.field? "BYTES" = some (.list rs₁))
    (ht₂ : MemAt S F n₂ t₂) (hR₂ : t₂.field? "BYTES" = some (.list rs₂))
    (hb : i₁.toNat ≤ rs₁.length ∧ i₂.toNat ≤ rs₂.length) :
    SRead env (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat 0 n₁ n₂)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN 0)), ("x_1", idxV n₁), ("x_2", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 57) (b := .list []) (by decide) (exc := [56])
    (a := (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat 0 n₁ n₂)))
    lhsIn_memoryCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j = 56 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₅₆ hr']
      exact not_memoryCopyOob D ht₁ hR₁ ht₂ hR₂ (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/memory.copy-le`. -/
theorem sread_memoryCopyLe (h : HasRuleAt env "Step_read" "%~>%" 58 memoryCopyLeRule)
    (h₅₆ : HasRuleAt env "Step_read" "%~>%" 56 memoryCopyOobRule)
    (h₅₇ : HasRuleAt env "Step_read" "%~>%" 57 memoryCopyZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : MemAt S F n₁ t₁) (hR₁ : t₁.field? "BYTES" = some (.list rs₁))
    (ht₂ : MemAt S F n₂ t₂) (hR₂ : t₂.field? "BYTES" = some (.list rs₂))
    (hb : i₁.toNat + k ≤ rs₁.length ∧ i₂.toNat + k ≤ rs₂.length) (hk : k ≠ 0)
    (hle : i₁.toNat ≤ i₂.toNat) (hm0 : Memarg0Ok env) :
    SRead env (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂))
      [aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat,
        load8uV n₂, store8V n₁,
        aconstV (Encode.toValue a₁) (i₁.toNat + 1), aconstV (Encode.toValue a₂) (i₂.toNat + 1),
        aconstV (Encode.toValue a') (k - 1), .case "MEMORY.COPY" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x_1", idxV n₁), ("x_2", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat, load8uV n₂, store8V n₁, aconstV (Encode.toValue a₁) (i₁.toNat + 1), aconstV (Encode.toValue a₂) (i₂.toNat + 1), aconstV (Encode.toValue a') (k - 1), .case "MEMORY.COPY" (.tuple [idxV n₁, idxV n₂])])
    (i := 58) (by decide) (exc := [56, 57])
    (a := (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)))
    lhsIn_memoryCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 56 ∨ j = 57) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₅₆ hr']
        exact not_memoryCopyOob D ht₁ hR₁ ht₂ hR₂ hb
      · rw [RefsGC.relRules_of_ruleAt h₅₇ hr']
        exact not_memoryCopyZero hk)
  refine dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons'
        (evalExp_load8u (hm0 σ) (evalExp_var (x := "x_2") rfl))
      (RefsGC.evalExps_cons' (evalExp_store8 (hm0 σ) (evalExp_var (x := "x_1") rfl))
        (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_1") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_2") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at'") rfl) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))) ?_
  exact prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_leNat
    (RefsGC.evalExp_unpct (evalExp_var rfl)) (RefsGC.evalExp_unpct (evalExp_var rfl)) hle))

/-- `Step_read/memory.copy-gt`. -/
theorem sread_memoryCopyGt (h : HasRuleAt env "Step_read" "%~>%" 59 memoryCopyGtRule)
    (h₅₆ : HasRuleAt env "Step_read" "%~>%" 56 memoryCopyOobRule)
    (h₅₇ : HasRuleAt env "Step_read" "%~>%" 57 memoryCopyZeroRule)
    (h₅₈ : HasRuleAt env "Step_read" "%~>%" 58 memoryCopyLeRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t₁ t₂ : Value} {rs₁ rs₂ : List Value} {a₁ a₂ a' : Silmaril.Wasm.AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht₁ : MemAt S F n₁ t₁) (hR₁ : t₁.field? "BYTES" = some (.list rs₁))
    (ht₂ : MemAt S F n₂ t₂) (hR₂ : t₂.field? "BYTES" = some (.list rs₂))
    (hb : i₁.toNat + k ≤ rs₁.length ∧ i₂.toNat + k ≤ rs₂.length) (hk : k ≠ 0)
    (hgt : i₂.toNat < i₁.toNat) (hm0 : Memarg0Ok env) :
    SRead env (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂)
      (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂))
      [aconstV (Encode.toValue a₁) (i₁.toNat + k - 1), aconstV (Encode.toValue a₂) (i₂.toNat + k - 1),
        load8uV n₂, store8V n₁,
        aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat,
        aconstV (Encode.toValue a') (k - 1), .case "MEMORY.COPY" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at_1", Encode.toValue a₁),
    ("i_1", idxV i₁.toNat), ("at_2", Encode.toValue a₂), ("i_2", idxV i₂.toNat),
    ("at'", Encode.toValue a'), ("n", .num (.natN k)), ("x_1", idxV n₁), ("x_2", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a₁) (i₁.toNat + k - 1), aconstV (Encode.toValue a₂) (i₂.toNat + k - 1), load8uV n₂, store8V n₁, aconstV (Encode.toValue a₁) i₁.toNat, aconstV (Encode.toValue a₂) i₂.toNat, aconstV (Encode.toValue a') (k - 1), .case "MEMORY.COPY" (.tuple [idxV n₁, idxV n₂])])
    (i := 59) (by decide) (exc := [56, 57, 58])
    (a := (cfgV (stV S F) (mcopyCode (Encode.toValue a₁) (Encode.toValue a₂) (Encode.toValue a') i₁.toNat i₂.toNat k n₁ n₂)))
    lhsIn_memoryCopy (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 56 ∨ j = 57 ∨ j = 58) with rfl | rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₅₆ hr']
        exact not_memoryCopyOob D ht₁ hR₁ ht₂ hR₂ hb
      · rw [RefsGC.relRules_of_ruleAt h₅₇ hr']
        exact not_memoryCopyZero hk
      · rw [RefsGC.relRules_of_ruleAt h₅₈ hr']
        exact not_memoryCopyLe hgt)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a₁ _ hρ)
      (QuantsOk.cons rfl (St.num "at_1" a₁ i₁ _ hρ rfl) (QuantsOk.cons rfl (St.addr a₂ _ hρ)
      (QuantsOk.cons rfl (St.num "at_2" a₂ i₂ _ hρ rfl) (QuantsOk.cons rfl (St.addr a' _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_1") rfl) (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_1") rfl)) (evalExp_var (x := "n") rfl)) (by omega)))
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at_2") rfl) (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i_2") rfl)) (evalExp_var (x := "n") rfl)) (by omega))) (RefsGC.evalExps_cons'
        (evalExp_load8u (hm0 σ) (evalExp_var (x := "x_2") rfl))
      (RefsGC.evalExps_cons' (evalExp_store8 (hm0 σ) (evalExp_var (x := "x_1") rfl))
        (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (by eval_tac) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at'") rfl) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil'))))))))))
    (prems_one (.elsePr hel))

end MCopy

/-! ## `memory.init` -/

section MInit

variable {env : Env} (D : StateDefs env) (St : StateTyping env)

/-- The data segment the frame's module lists at index `n` is `e`, in the store `S`. -/
def DataAt (S F : Value) (n : Nat) (e : Value) : Prop :=
  ∃ M Ls As a, S.field? "DATAS" = some (.list Ls) ∧ F.field? "MODULE" = some M ∧
    M.field? "DATAS" = some (.list As) ∧ As[n]? = some (.num (.natN a)) ∧ Ls[a]? = some e

include D in
/-- `$data(z, x)` on a state whose data segment at `n` is `e`. -/
theorem evalExp_data_of {σ : List (IL.Id × Value)} {ez ex : Exp} {S F e : Value} {n : Nat}
    (hz : EvalExp env (VarEnv.empty.bindVals σ) ez (stV S F))
    (hx : EvalExp env (VarEnv.empty.bindVals σ) ex (idxV n)) (he : DataAt S F n e) :
    EvalExp env (VarEnv.empty.bindVals σ) (.callE "data" [.expA ez, .expA ex]) e := by
  obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := he
  exact State.evalExp_data D (findDef_bindVals_empty σ _) hz hx hS hM hA ha hr

/-- The code of a `memory.init` step. -/
abbrev minitCode (A : Value) (i j k n₁ n₂ : Nat) : List Value :=
  [aconstV A i, aconstV i32V j, aconstV i32V k, .case "MEMORY.INIT" (.tuple [idxV n₁, idxV n₂])]

/-- The bindings a `memory.init` left-hand side forces. -/
theorem binds_memoryInit {ρ : VarEnv} {z A : Value} {i j k n₁ n₂ : Nat}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "MEMORY.INIT" (.tupE [.varE "x", .varE "y"])]]))
      (cfgV z (minitCode A i j k n₁ n₂))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i") (idxV i) ∧
      EvalExp env ρ (.varE "j") (idxV j) ∧ EvalExp env ρ (.varE "n") (.num (.natN k)) ∧
      EvalExp env ρ (.varE "x") (idxV n₁) ∧ EvalExp env ρ (.varE "y") (idxV n₂) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  have hxy := tup2_inv (RefsGC.case_inv (RefsGC.evalExps_get hs 3 rfl rfl))
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl),
    const_inv (RefsGC.evalExps_get hs 1 rfl rfl), const_pct_inv (RefsGC.evalExps_get hs 2 rfl rfl),
    hxy.1, hxy.2⟩

include D in
/-- `memory.init-oob` does not fire when both ranges are in bounds. -/
theorem not_memoryInitOob {Dr : Interp} {els : Prop} {S F t e A c : Value}
    {rs es : List Value} {i j k n₁ n₂ : Nat} (ht : MemAt S F n₁ t)
    (hR : t.field? "BYTES" = some (.list rs)) (he : DataAt S F n₂ e)
    (hE : e.field? "BYTES" = some (.list es)) (h : i + k ≤ rs.length ∧ j + k ≤ es.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryInitOobRule
      (.tuple [cfgV (stV S F) (minitCode A i j k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he', hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi, hj, hk, hx, hy⟩ := binds_memoryInit (RefsGC.lhs_of_concl he')
  have ho := or_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi) hk) (evalExp_memBytesLen D hz hx ht hR)
    (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hj) hk)
    (RefsGC.evalExp_len (RefsGC.evalExp_dot (evalExp_data_of D hz hy he) hE))
  omega

/-- `memory.init-zero` does not fire on a non-zero count. -/
theorem not_memoryInitZero {Dr : Interp} {els : Prop} {z A c : Value} {i j k n₁ n₂ : Nat}
    (hk : k ≠ 0) :
    ¬ RuleBody env Dr els [] [] "%~>%" memoryInitZeroRule
      (.tuple [cfgV z (minitCode A i j k n₁ n₂), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨-, -, -, hk', -, -⟩ := binds_memoryInit (RefsGC.lhs_of_concl he)
  have h0 := RefsGC.eq_of_evalExp_eq
    (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) hk'
    RefsGC.evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hk h0

/-- The left-hand side of a `memory.init` step has its constructors among `MEMORY.INIT` and
`CONST`. -/
theorem lhsIn_memoryInit {z A : Value} {i j k n₁ n₂ : Nat} :
    RefsGC.LhsIn (["MEMORY.INIT"] ++ RefsGC.valTags) (cfgV z (minitCode A i j k n₁ n₂)) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) (RefsGC.tagsIn_cons
      (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil)))⟩

include D St

/-- `Step_read/memory.init-oob`. -/
theorem sread_memoryInitOob (h : HasRuleAt env "Step_read" "%~>%" 60 memoryInitOobRule)
    {S F t e : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : MemAt S F n₁ t) (hR : t.field? "BYTES" = some (.list rs))
    (he : DataAt S F n₂ e) (hE : e.field? "BYTES" = some (.list es))
    (hoob : rs.length < i.toNat + k ∨ es.length < j.toNat + k) :
    SRead env (cfgV (stV S F) (minitCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂))
      [.case "TRAP" (.tuple [])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN k)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ho := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl))
        (evalExp_var (x := "n") rfl))
      (evalExp_memBytesLen D ez (evalExp_var (x := "x") rfl) ht hR) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl))
        (evalExp_var (x := "n") rfl))
      (RefsGC.evalExp_len (RefsGC.evalExp_dot
        (evalExp_data_of D ez (evalExp_var (x := "y") rfl) he) hE)) rfl)
  rw [decide_eq_true hoob] at ho
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (prems_one (.ifPr ho))

/-- `Step_read/memory.init-zero`. -/
theorem sread_memoryInitZero (h : HasRuleAt env "Step_read" "%~>%" 61 memoryInitZeroRule)
    (h₆₀ : HasRuleAt env "Step_read" "%~>%" 60 memoryInitOobRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t e : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : MemAt S F n₁ t) (hR : t.field? "BYTES" = some (.list rs))
    (he : DataAt S F n₂ e) (hE : e.field? "BYTES" = some (.list es))
    (hb : i.toNat ≤ rs.length ∧ j.toNat ≤ es.length) :
    SRead env (cfgV (stV S F) (minitCode (Encode.toValue a) i.toNat j.toNat 0 n₁ n₂)) [] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN 0)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (i := 61) (b := .list []) (by decide) (exc := [60])
    (a := (cfgV (stV S F) (minitCode (Encode.toValue a) i.toNat j.toNat 0 n₁ n₂)))
    lhsIn_memoryInit (by decide) (by
      intro j' hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      obtain rfl : j' = 60 := by simpa using hj
      rw [RefsGC.relRules_of_ruleAt h₆₀ hr']
      exact not_memoryInitOob D ht hR he hE (by omega))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (by eval_tac)
    (prems_two (.elsePr hel) (.ifPr (RefsGC.evalExp_eq_true (evalExp_var rfl) RefsGC.evalExp_num')))

/-- `Step_read/memory.init-succ`. -/
theorem sread_memoryInitSucc (h : HasRuleAt env "Step_read" "%~>%" 62 memoryInitSuccRule)
    (h₆₀ : HasRuleAt env "Step_read" "%~>%" 60 memoryInitOobRule)
    (h₆₁ : HasRuleAt env "Step_read" "%~>%" 61 memoryInitZeroRule)
    (hT : ((RefsGC.relRules env "Step_read").map RefsGC.ruleTags).take 103 = RefsGC.readTagTable)
    {S F t e : Value} {rs es : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {k n₁ n₂ : Nat}
    (hz : TypedV env stateT (stV S F)) (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32)
    (ht : MemAt S F n₁ t) (hR : t.field? "BYTES" = some (.list rs))
    (he : DataAt S F n₂ e) (hE : e.field? "BYTES" = some (.list es))
    (hb : i.toNat + k ≤ rs.length ∧ j.toNat + k ≤ es.length) (hk : k ≠ 0)
    {byte : Nat} (hr : es[j.toNat]? = some (idxV byte))
    (hm0 : Memarg0Ok env) :
    SRead env (cfgV (stV S F) (minitCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂))
      [aconstV (Encode.toValue a) i.toNat, aconstV i32V byte, store8V n₁,
        aconstV (Encode.toValue a) (i.toNat + 1), aconstV i32V (j.toNat + 1),
        aconstV i32V (k - 1), .case "MEMORY.INIT" (.tuple [idxV n₁, idxV n₂])] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("j", idxV j.toNat), ("n", .num (.natN k)), ("x", idxV n₁),
    ("y", idxV n₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hel := RefsGC.otherwise_of_ruleAt h hT (b := .list [aconstV (Encode.toValue a) i.toNat, aconstV i32V byte, store8V n₁, aconstV (Encode.toValue a) (i.toNat + 1), aconstV i32V (j.toNat + 1), aconstV i32V (k - 1), .case "MEMORY.INIT" (.tuple [idxV n₁, idxV n₂])])
    (i := 62) (by decide) (exc := [60, 61])
    (a := (cfgV (stV S F) (minitCode (Encode.toValue a) i.toNat j.toNat k n₁ n₂)))
    lhsIn_memoryInit (by decide) (by
      intro j' hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j' = 60 ∨ j' = 61) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt h₆₀ hr']
        exact not_memoryInitOob D ht hR he hE hb
      · rw [RefsGC.relRules_of_ruleAt h₆₁ hr']
        exact not_memoryInitZero hk)
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.addr a _ hρ)
      (QuantsOk.cons rfl (St.num "at" a i _ hρ rfl) (QuantsOk.cons rfl (St.num32 j _ hρ)
      (QuantsOk.cons rfl (St.nat _ _ hρ) (QuantsOk.cons rfl (St.idx n₁ hn₁ _ hρ)
      (QuantsOk.cons rfl (St.idx n₂ hn₂ _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (by eval_tac)
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (et := .caseE "I32" (.tupE [])) (by eval_tac) (RefsGC.evalExp_unpct (RefsGC.evalExp_idx (RefsGC.evalExp_dot (evalExp_data_of D ez (evalExp_var (x := "y") rfl) he) hE) (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) hr))) (RefsGC.evalExps_cons'
        (evalExp_store8 (hm0 σ) (evalExp_var (x := "x") rfl))
      (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (evalExp_subAt (x := "at") rfl) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "i") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (et := .caseE "I32" (.tupE [])) (by eval_tac) (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var (x := "j") rfl)) (RefsGC.evalExp_num' (m := .natN 1)))) (RefsGC.evalExps_cons' (evalExp_constPct (env := env) (ρ := VarEnv.empty.bindVals σ) (et := .caseE "I32" (.tupE [])) (by eval_tac) (RefsGC.evalExp_predNat (evalExp_var (x := "n") rfl) (Nat.one_le_iff_ne_zero.2 hk)))
      (RefsGC.evalExps_cons' (by eval_tac) RefsGC.evalExps_nil')))))))))
    (prems_one (.elsePr hel))

end MInit

/-! ## `memory.size` -/

/-- `$Ki()` evaluates to `1024` in every rule assignment. -/
def KiOk (env : Env) : Prop :=
  ∀ σ : List (IL.Id × Value),
    EvalExp env (VarEnv.empty.bindVals σ) (.callE "Ki" []) (.num (.natN 1024))

section Size

variable {env : Env} (D : StateDefs env) (St : StateTyping env)
include D St

/-- `Step_read/memory.size`: `z; (MEMORY.SIZE x) ~> (CONST at (% n))` where
`n · 64 Ki = |BYTES|` and the memory's type is `at lim PAGE`. -/
theorem sread_memorySize (h : HasRuleAt env "Step_read" "%~>%" 52 memorySizeRule)
    (hKi : KiOk env) {S F m L : Value} {bs : List Value} {a : Silmaril.Wasm.AddrType} {n p : Nat}
    (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32) (hL : TypedV env Memory.limitsT L)
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hT : m.field? "TYPE" = some (.case "%%PAGE" (.tuple [Encode.toValue a, L])))
    (hp : p * (64 * 1024) = bs.length) :
    SRead env (cfgV (stV S F) [.case "MEMORY.SIZE" (idxV n)]) [aconstV (Encode.toValue a) p] := by
  let σ : List (IL.Id × Value) := [("z", stV S F), ("x", idxV n), ("at", Encode.toValue a),
    ("n", .num (.natN p)), ("lim", L)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ez : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F) := evalExp_var rfl
  have ex : EvalExp env (VarEnv.empty.bindVals σ) (.varE "x") (idxV n) := evalExp_var rfl
  have el : EvalExp env (VarEnv.empty.bindVals σ) (.binE .mulOp (.numT .natT) (.varE "n")
      (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])))
      (.num (.natN bs.length)) := by
    rw [← hp]
    exact RefsGC.evalExp_mulNat (evalExp_var rfl) (RefsGC.evalExp_mulNat RefsGC.evalExp_num' (hKi σ))
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (St.idx n hn _ hρ)
      (QuantsOk.cons rfl (St.addr a _ hρ) (QuantsOk.cons rfl (St.nat _ _ hρ)
        (QuantsOk.cons rfl (hL _ hρ) QuantsOk.nil)))))
    (by eval_tac)
    (prems_two
      (.ifPr (RefsGC.evalExp_eq_true el (evalExp_memBytesLen D ez ex hm hB)))
      (.ifPr (RefsGC.evalExp_eq_true
        (RefsGC.evalExp_dot (evalExp_mem_of D ez ex hm) hT) (by eval_tac))))

end Size

end Silmaril.Wasm.SpecTec.Sim.Memory
