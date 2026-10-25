module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEval
public import Silmaril.Wasm.Binaryen.Toolkit.InitSession

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Execution.Core.Sim Numerics Validation
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)
open GrowOOM (forced_trans forced_label forced_frame)

variable {H : Type} {P : Profile}

theorem callRef_noargs_unique {s : Store H} {a : Nat} {fi : FuncInst H}
    {fn : Func} {rs : Ty (.list .val)} {outer : Frame} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func .nil rs)) (hfn : fi.code = .wasm fn)
    {c : Config H} (hs : Step P closedHost ⟨s, outer, [.ref (.func a), .callRefType fi.type]⟩ c) :
    c = ⟨s, outer, [.frame rs.length (Frame.forCall fi.module [] fn.locals)
      [.label rs.length [] (expression fn.body)]]⟩ := by
  unfold closedHost at hs
  have hs' : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, outer, vals [Val.ref (.func a)] ++ [.callRefType fi.type]⟩ c := by
    simpa [invoke, hf, vals, Val.toAdmin] using hs
  obtain ⟨pre, args, c₀, hw, hh, hc⟩ := Step.head_inv hs' rfl (by simp) (by simp)
  cases hh with
  | parametric h => exact (by have h' := (famOf_of_shape (ParametricStep.shape h)).2; cases h')
  | numeric h => exact (by have h' := (famOf_of_shape (NumericStep.shape h)).2; cases h')
  | vector h => exact (by have h' := (famOf_of_shape (VectorStep.shape h)).2; cases h')
  | «variable» h => exact (by have h' := (famOf_of_shape (VariableStep.shape h)).2; cases h')
  | table h => exact (by have h' := (famOf_of_shape (TableStep.shape h)).2; cases h')
  | memory h => exact (by have h' := (famOf_of_shape (MemoryStep.shape h)).2; cases h')
  | reference h => exact (by have h' := (famOf_of_shape (RefStep.shape h)).2; cases h')
  | aggregate h => exact (by have h' := (famOf_of_shape (AggregateStep.shape h)).2; cases h')
  | callRefNull _ =>
    have h := ((append_singleton_inj (l₁ := [])).mp hw).2
    cases h
  | callRefFunc ha _ hf' he' hn hfn' =>
    rw [ha, ← List.append_assoc] at hw
    obtain ⟨hpre, haddr⟩ := (append_singleton_inj (l₁ := [])).mp hw
    simp only [List.nil_eq_append_iff] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    cases haddr
    have hfi := hf.symm.trans hf'
    cases hfi
    have htypes := (Expand.iff.mp he).symm.trans (Expand.iff.mp he')
    simp only [Option.some.injEq, Ty.func.injEq] at htypes
    obtain ⟨rfl, rfl⟩ := htypes
    cases hfn.symm.trans hfn'
    simpa [vals, Ty.length] using hc


theorem invoke_noargs_unique {s : Store H} {a : Nat} {fi : FuncInst H}
    {fn : Func} {rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func .nil rs)) (hfn : fi.code = .wasm fn)
    {c : Config H} (hs : Step P closedHost (invoke s a []) c) :
    c = ⟨s, {}, [.frame rs.length (Frame.forCall fi.module [] fn.locals)
      [.label rs.length [] (expression fn.body)]]⟩ := by
  have hs' : Step P closedHost ⟨s, {}, [.ref (.func a), .callRefType fi.type]⟩ c := by
    simpa [invoke, hf, vals] using hs
  exact callRef_noargs_unique hf he hfn hs'


theorem head_globalGet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c : Config H} (h : Head P s f args (.plain (.globalGet x)) c) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c = ⟨s, f, [g.value.toAdmin]⟩ := by
  have hv := h.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hv
  generalize he : (⟨s, f, vals args ++ [Admin.plain (.globalGet x)]⟩ : Config H) = cfg at hv
  cases hv with
  | @globalGet s' f' y address gi hg =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨ha, hx⟩ := (append_singleton_inj (l₂ := [])).mp he
    simp only [Admin.plain.injEq, Instr.globalGet.injEq] at hx
    subst y
    exact ⟨GuardSim.vals_eq_nil ha, address, gi, hg, rfl⟩
  | _ => have hh := congrArg (fun c : Config H => c.code.getLast?) he; simp at hh

theorem head_globalSet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c : Config H} (h : Head P s f args (.plain (.globalSet x)) c) :
    ∃ v a g, args = [v] ∧ s.global? f x = some (a, g) ∧ c = ⟨s.setGlobal a v, f, []⟩ := by
  have hv := h.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hv
  generalize he : (⟨s, f, vals args ++ [Admin.plain (.globalSet x)]⟩ : Config H) = cfg at hv
  cases hv with
  | @globalSet s' f' y address gi v hg =>
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, he⟩ := he
    obtain ⟨ha, hx⟩ := (append_singleton_inj (l₂ := [v.toAdmin])).mp he
    simp only [Admin.plain.injEq, Instr.globalSet.injEq] at hx
    subst y
    exact ⟨v, address, gi, vals_inj.mp ha, hg, rfl⟩
  | _ => have hh := congrArg (fun c : Config H => c.code.getLast?) he; simp at hh

/-- Reading one known global is forced at every profile. -/
theorem globalGet_unique {s : Store H} {f : Frame} {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} {c : Config H}
    (hg : s.global? f x = some (a, g))
    (h : Step P closedHost ⟨s, f, [.plain (.globalGet x)]⟩ c) :
    c = ⟨s, f, [g.value.toAdmin]⟩ := by
  have h' : Step P closedHost ⟨s, f, vals [] ++ .plain (.globalGet x) :: []⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨rfl, address, gi, hg', rfl⟩ := head_globalGet hh
  have hp : pre = [] := by simpa using hw.symm
  subst pre
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg.symm.trans hg'))
  exact hc

/-- A known global update has one successor, retaining the actual full store. -/
theorem globalSet_unique {s : Store H} {f : Frame} {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} {v : Val} {c : Config H}
    (hg : s.global? f x = some (a, g))
    (h : Step P closedHost ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ c) :
    c = ⟨s.setGlobal a v, f, []⟩ := by
  have h' : Step P closedHost ⟨s, f, vals [v] ++ .plain (.globalSet x) :: []⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨w, address, gi, rfl, hg', rfl⟩ := head_globalSet hh
  obtain ⟨rfl, hw⟩ := (append_singleton_inj (l₁ := [])).mp hw
  subst w
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hg.symm.trans hg'))
  exact hc

/-- Direct start-call resolution does not depend on numerical choices. -/
theorem call_unique {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) {c : Config H}
    (h : Step P closedHost ⟨s, f, [.plain (.call x)]⟩ c) :
    c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  obtain ⟨cfg, hh, hc⟩ := LoopCex.head_single h rfl (by simp) (by simp)
  cases hh with
  | call hx' hf' =>
    obtain rfl := Option.some.inj (hx.symm.trans hx')
    obtain rfl := Option.some.inj (hf.symm.trans hf')
    exact hc
  | _ => fam_absurd

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
