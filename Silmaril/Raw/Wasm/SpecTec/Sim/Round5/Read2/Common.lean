module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round4Read.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Thms

/-!
# Round 5, pass 3, track read: shared inversions

* `type_inv_at`: `$type(z, x)` read back, at any name of the index variable (track bwdstep's
  `BwdStep.type_inv` fixes it to `x`);
* `expandArray_inv`: the premise `Expand($type(z, x), ARRAY (mut? zt))` read back at any names
  of `x` and `zt`: the type resolves, Core's expansion is an array type and `zt` is the image of
  its storage type;
* `and_true_inv`: a true conjunction has true conjuncts;
* `quantsOk_sub`: a scope typing the quantifiers of one rule types those of a rule with fewer.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **`$type(z, x)`, read back**, at any name `xv` of the index variable. -/
theorem type_inv_at {ρ : VarEnv} (hρ : ValsOnly ρ) {xv : IL.Id} {s : Store H} {f : Frame}
    {x : TypeIdx} {T : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? xv = some (Encode.toValue x))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.callE "type" [.expA (.varE "z"), .expA (.varE xv)]) T) :
    ∃ d, f.type? x = some d ∧ T = CT.defType d := by
  have D := Aggregates.aggDefs_simEnv (BI P hn host)
  have SD := State.stateDefs_simEnv (BI P hn host)
  have hbody := BwdPureStep.evalExp_call1_inv D.type_ (Prims.findDef_none_of_valsOnly hρ _)
    (BwdStep.call_type_none _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      Equiv.evalArgs_nil)) State.matchArgs_zxPat h
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hbody
  have eL : L = .list (f.module.types.map CT.defType) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof SD rfl (evalExp_var rfl), Aggregates.frameV_module f⟩,
      Aggregates.moduleV_types f.module⟩)
  have ej : Value.num (.natN j) = .num (.natN x.toNat) :=
    EvalExp.unique hj (State.evalExp_idxPayload rfl)
  simp only [Value.num.injEq, Num.natN.injEq] at ej
  subst eL ej
  simp only [Value.idx?, List.getElem?_map] at hLj
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hLj
  exact ⟨d, hd, rfl⟩

/-- **The array `Expand` premise, read back**, at any names `xv`, `ztv` of the type index and the
storage type. -/
theorem expandArray_inv {σ : List (IL.Id × Value)} {xv ztv : IL.Id} {s : Store H} {f : Frame}
    {x : TypeIdx} {O : ElseI}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fx : (VarEnv.empty.bindVals σ).findVal? xv = some (Encode.toValue x)) {w : Value}
    (hw : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE xv)],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE ztv]))]) w)
    (hD : DDerives (simEnv (BI P hn host)) O "Expand" "%~~%" [] w) :
    ∃ d m zt, f.type? x = some d ∧ Expand d (.array (.field m zt)) ∧
      (VarEnv.empty.bindVals σ).findVal? ztv = some (tyV zt) ∧
      w = .tuple [CT.defType d, tyV ((Ty.field m zt).array : CCompType)] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨v₁, vs', h₁, hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨d, hd, rfl⟩ := type_inv_at (valsOnly_bindVals σ) fz fx h₁
  obtain ⟨v₂, vs'', h₂, hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host O d _ hD
  obtain ⟨m, zt, rfl⟩ := BwdStep.array_of_tyV h₂
  have h₃ := RefsGC.case_inv (RefsGC.case_inv h₂)
  have hzt := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup h₃)).2).1
  exact ⟨d, m, zt, hd, hct, evalExp_varE_iff.1 hzt, rfl⟩

/-- **A true conjunction has true conjuncts.** -/
theorem and_true_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp}
    (h : EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool true)) :
    EvalExp env ρ e₁ (.bool true) ∧ EvalExp env ρ e₂ (.bool true) := by
  obtain ⟨v₁, h₁, hs | ⟨hs, v₂, h₂, hb⟩⟩ := evalExp_binE_iff.1 h
  · exfalso
    unfold boolShort at hs
    split at hs <;> simp_all
  · cases v₁ <;> cases v₂ <;> simp [binValues] at hb
    rename_i b₁ b₂
    cases b₁ <;> cases b₂ <;> simp_all [boolBin]

/-- A scope typing a rule's quantifiers types every sublist of them. -/
theorem quantsOk_sub {env : Env} {ρ : VarEnv} {qs qs' : List Param} (hq : QuantsOk env ρ qs)
    (h : qs' ⊆ qs) : QuantsOk env ρ qs' :=
  fun x t hm => hq x t (h hm)

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
