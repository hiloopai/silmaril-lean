module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Agg

/-!
# Round 5: the memory SIMD stores do not fire (`Step` 22–25), *at the provisional
encoding*

The memory SIMD instructions are still encoded by `schemaInstrV` (`Sim.instrToV`, *provisional*):
their memory argument is `schemaV (encodeMemArg arg)`, a `$record` **case**, not the IL record
`memargV arg` the scalar loads and stores use. Every one of `vstore-oob` (22), `vstore-val` (23),
`vstore_lane-oob` (24) and `vstore_lane-val` (25) needs `ao.OFFSET` (in its premise or in its
right-hand side), and a field access on a case has no value. So none of the four rules fires on
the image of a Core configuration, and their backward obligation holds vacuously.

**This is a statement about the current encoding.** It is what makes the forward direction fail
for these instructions (round 4's `Open4`, memory SIMD); once their encoding is written against
the IL type `instr` (as for `LOAD`/`STORE`), these lemmas stop compiling and the rules need real
backward proofs (as `store-num-val`, `Store.lean`, with `$vbytes_`/`$lanes_` in `B`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (fires_step codes_three payload_of_caseE head_of_caseE rhs_nil)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H} {B : Builtins}

theorem head_vecStore {a : Admin} (h : Typing.adminHead a = "VSTORE") :
    ∃ m arg, a = .plain (.vecStore m arg) := by
  revert h
  admin_head_inv

theorem head_vecStoreLane {a : Admin} (h : Typing.adminHead a = "VSTORE_LANE") :
    ∃ sz m arg l, a = .plain (.vecStoreLane sz m arg l) := by
  revert h
  admin_head_inv

/-- The provisional image of `v128.store`. -/
theorem adminToV_vecStore (m : MemIdx) (arg : MemArg) :
    adminToV (.plain (.vecStore m arg)) = .case "VSTORE" (.tuple
      [schemaV (Silmaril.Wasm.SpecTecEnc.encodeVecType .v128),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned m.toNat),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg arg)]) := by
  simp [adminToV, instrToV, schemaInstrV, Silmaril.Wasm.SpecTecEnc.encodeInstruction,
    Silmaril.Wasm.SpecTecEnc.field]

/-- The provisional image of `v128.store*_lane`. -/
theorem adminToV_vecStoreLane (sz : PackSize) (m : MemIdx) (arg : MemArg) (l : LaneIdx) :
    adminToV (.plain (.vecStoreLane sz m arg l)) = .case "VSTORE_LANE" (.tuple
      [schemaV (Silmaril.Wasm.SpecTecEnc.encodeVecType .v128),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodePackSize sz),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned m.toNat),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg arg),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned l.val)]) := by
  simp [adminToV, instrToV, schemaInstrV, Silmaril.Wasm.SpecTecEnc.encodeInstruction,
    Silmaril.Wasm.SpecTecEnc.field]

/-- The provisional image of a memory argument is a case, with no `OFFSET` field. -/
theorem schemaMemArg_field (arg : MemArg) :
    (schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg arg)).field? "OFFSET" = none := rfl

/-- `ao.OFFSET!%.0` has no value when `ao` is bound to a value without an `OFFSET` field. -/
theorem not_offset {env : Env} {ρ : VarEnv} {u v : Value} (fao : ρ.findVal? "ao" = some u)
    (hu : u.field? "OFFSET" = none)
    (h : EvalExp env ρ (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0) v) : False := by
  obtain ⟨vs, hvs, -⟩ := evalExp_projE_iff.1 h
  obtain ⟨w, hw, hf⟩ := evalExp_dotE_iff.1 (evalExp_uncaseE_iff.1 hvs)
  rw [EvalExp.unique hw (evalExp_var fao), hu] at hf
  cases hf

/-- The right operand of an arithmetic operator has a value whenever the whole does. -/
theorem binE_right {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} {v : Value}
    (hop : ∀ u, boolShort op u = none) (h : EvalExp env ρ (.binE op t e₁ e₂) v) :
    ∃ v₂, EvalExp env ρ e₂ v₂ := by
  obtain ⟨v₁, -, hs⟩ := evalExp_binE_iff.1 h
  rcases hs with hs | ⟨-, v₂, h₂, -⟩
  · rw [hop] at hs
    cases hs
  · exact ⟨v₂, h₂⟩

/-- The left operand of an arithmetic operator has a value whenever the whole does. -/
theorem binE_left {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.binE op t e₁ e₂) v) : ∃ v₁, EvalExp env ρ e₁ v₁ := by
  obtain ⟨v₁, h₁, -⟩ := evalExp_binE_iff.1 h
  exact ⟨v₁, h₁⟩

theorem boolShort_add (u : Value) : boolShort .addOp u = none := by
  cases u <;> rfl

/-- `i!%.0 + ao.OFFSET!%.0` has no value when `ao` has no `OFFSET` field. -/
theorem not_effAddr {env : Env} {ρ : VarEnv} {u v : Value} (fao : ρ.findVal? "ao" = some u)
    (hu : u.field? "OFFSET" = none)
    (h : EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
      (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) v) : False := by
  obtain ⟨v₂, h₂⟩ := binE_right boolShort_add h
  exact not_offset fao hu h₂

/-- The binding of `ao` in a firing `VSTORE`/`VSTORE_LANE` rule. -/
theorem ao_vstore {env : Env} {ρ : VarEnv} {a : Admin} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.caseE "VSTORE" (.tupE [e₁, e₂, .varE "ao"])) (adminToV a)) :
    ∃ u, ρ.findVal? "ao" = some u ∧ u.field? "OFFSET" = none := by
  obtain ⟨m, arg, rfl⟩ := head_vecStore (head_of_caseE h)
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  have he' : Value.case "VSTORE" (.tuple [schemaV (Silmaril.Wasm.SpecTecEnc.encodeVecType .v128),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned m.toNat),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg arg)]) = .case "VSTORE" u :=
    (adminToV_vecStore m arg).symm.trans he
  have eu := (Value.case.inj he').2.symm
  subst eu
  have h₃ := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup hu)).2).2).1
  exact ⟨_, evalExp_varE_iff.1 h₃, schemaMemArg_field arg⟩

/-- The binding of `ao` in a firing `VSTORE_LANE` rule. -/
theorem ao_vstoreLane {env : Env} {ρ : VarEnv} {a : Admin} {e₁ e₂ e₃ e₅ : Exp}
    (h : EvalExp env ρ (.caseE "VSTORE_LANE" (.tupE [e₁, e₂, e₃, .varE "ao", e₅]))
      (adminToV a)) :
    ∃ u, ρ.findVal? "ao" = some u ∧ u.field? "OFFSET" = none := by
  obtain ⟨sz, m, arg, l, rfl⟩ := head_vecStoreLane (head_of_caseE h)
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  have he' : Value.case "VSTORE_LANE" (.tuple
      [schemaV (Silmaril.Wasm.SpecTecEnc.encodeVecType .v128),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodePackSize sz),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned m.toNat),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeMemArg arg),
      schemaV (Silmaril.Wasm.SpecTecEnc.encodeUnsigned l.val)]) = .case "VSTORE_LANE" u :=
    (adminToV_vecStoreLane sz m arg l).symm.trans he
  have eu := (Value.case.inj he').2.symm
  subst eu
  have h₄ := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup hu)).2).2).2).1
  exact ⟨_, evalExp_varE_iff.1 h₄, schemaMemArg_field arg⟩

/-- The access end `i + ao.OFFSET + k` of an `-oob` premise has no value without `ao.OFFSET`. -/
theorem not_oobPrem {env : Env} {ρ : VarEnv} {u : Value} {ek el : Exp} {v : Value}
    (fao : ρ.findVal? "ao" = some u) (hu : u.field? "OFFSET" = none)
    (h : EvalExp env ρ (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) ek) el) v) : False := by
  obtain ⟨v₁, -, e₁, -, -⟩ := evalExp_cmpE_iff.1 h
  obtain ⟨v₁', e₁'⟩ := binE_left e₁
  exact not_effAddr fao hu e₁'

/-- A `$with_mem(z, x, i + ao.OFFSET, k, b*)` call has no value without `ao.OFFSET`. -/
theorem not_withMem {env : Env} {ρ : VarEnv} {u : Value} {ek eb : Exp} {v : Value}
    (fao : ρ.findVal? "ao" = some u) (hu : u.field? "OFFSET" = none)
    (h : EvalExp env ρ (.callE "with_mem" [.expA (.varE "z"), .expA (.varE "x"),
      .expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)), .expA ek, .expA eb]) v) :
    False := by
  obtain ⟨ws, hws⟩ := args_of_call h
  obtain ⟨-, ws₁, -, hws₁, -⟩ := evalArgs_cons_inv hws
  obtain ⟨-, ws₂, -, hws₂, -⟩ := evalArgs_cons_inv hws₁
  obtain ⟨v₃, ws₃, h₃, -, -⟩ := evalArgs_cons_inv hws₂
  exact not_effAddr fao hu h₃

/-- **`Step/vstore-oob` (22) does not fire** on the image of a configuration (provisional
encoding). -/
theorem not_fires_vstoreOob {c : Config H} {w : Value} :
    ¬ Fires (simEnv B) "Step" 22 (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨σ, -, -, hes, -, hp⟩ := fires_step (hasStepRules_simEnv B).vstoreOob hf
  obtain ⟨a₁, a₂, a₃, -, -, -, h₃⟩ := codes_three hes
  obtain ⟨u, fao, hu⟩ := ao_vstore h₃
  exact not_oobPrem fao hu (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))

/-- **`Step/vstore-val` (23) does not fire** (provisional encoding). -/
theorem not_fires_vstoreVal {c : Config H} {w : Value} :
    ¬ Fires (simEnv B) "Step" 23 (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨σ, -, -, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).vstoreVal hf
  obtain ⟨a₁, a₂, a₃, -, -, -, h₃⟩ := codes_three hes
  obtain ⟨u, fao, hu⟩ := ao_vstore h₃
  obtain ⟨W, hW, -⟩ := rhs_nil hr
  exact not_withMem fao hu hW

/-- **`Step/vstore_lane-oob` (24) does not fire** (provisional encoding). -/
theorem not_fires_vstoreLaneOob {c : Config H} {w : Value} :
    ¬ Fires (simEnv B) "Step" 24 (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨σ, -, -, hes, -, hp⟩ := fires_step (hasStepRules_simEnv B).vstoreLaneOob hf
  obtain ⟨a₁, a₂, a₃, -, -, -, h₃⟩ := codes_three hes
  obtain ⟨u, fao, hu⟩ := ao_vstoreLane h₃
  exact not_oobPrem fao hu (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))

/-- **`Step/vstore_lane-val` (25) does not fire** (provisional encoding). -/
theorem not_fires_vstoreLaneVal {c : Config H} {w : Value} :
    ¬ Fires (simEnv B) "Step" 25 (.tuple [configV hn c, w]) := by
  intro hf
  obtain ⟨σ, -, -, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).vstoreLaneVal hf
  obtain ⟨a₁, a₂, a₃, -, -, -, h₃⟩ := codes_three hes
  obtain ⟨u, fao, hu⟩ := ao_vstoreLane h₃
  obtain ⟨W, hW, -⟩ := rhs_nil hr
  exact not_withMem fao hu hW

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
