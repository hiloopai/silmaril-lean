module

public import Silmaril.Wasm.Binaryen.GrowOOMLiteral
public import Silmaril.Wasm.Binaryen.GrowOOMRun
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)
open GrowOOM (forced_trans forced_label forced_frame)

variable {H : Type} {P : Profile}

/-- Preserve both typed literal operands when inverting an integer comparison. -/
theorem head_intRel {s : Store H} {f : Frame} {args : List Val} {t : IntType}
    {op : IntRelOp} {c : Config H}
    (h : Head P s f args (.plain (.intRelOp t op)) c) :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      c = ⟨s, f, [constI32 (intRelOp t op x y)]⟩ := by
  have hv := h.fam_inv (by simp [famOf])
  simp only [famOf, FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize he : vals args ++ [Admin.plain (.intRelOp t op)] = code at hv
  cases hv with
  | @intRelOp t' op' x y =>
    obtain ⟨ha, hi⟩ := (append_singleton_inj
      (l₂ := [Admin.plain (.intConst t' x), Admin.plain (.intConst t' y)])).mp he
    simp only [Admin.plain.injEq, Instr.intRelOp.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨x, y, vals_inj.mp ha, rfl⟩
  | _ => have hh := congrArg List.getLast? he; simp at hh

theorem intRel_step_unique {s : Store H} {f : Frame} {t : IntType}
    {op : IntRelOp} {x y : BitVec t.width} {rest : List Admin} {c : Config H}
    (h : Step P closedHost ⟨s, f,
      [.plain (.intConst t x), .plain (.intConst t y), .plain (.intRelOp t op)] ++ rest⟩ c) :
    c = ⟨s, f, constI32 (intRelOp t op x y) :: rest⟩ := by
  have h' : Step P closedHost
      ⟨s, f, vals [Val.num ⟨.int t, x⟩, Val.num ⟨.int t, y⟩] ++
        .plain (.intRelOp t op) :: rest⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨u, v, rfl, rfl⟩ := head_intRel hh
  have hl : pre = [] := by
    cases pre with
    | nil => rfl
    | cons z zs => have := congrArg List.length hw; simp at this
  subst pre
  have hxy : x = u ∧ y = v := by cases t <;> cases hw <;> exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hxy
  exact hc

theorem localGet_step_unique {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.local? x = some (some v)) {c : Config H}
    (h : Step P closedHost ⟨s, f, [.plain (.localGet x)]⟩ c) :
    c = ⟨s, f, [v.toAdmin]⟩ := by
  have h' : Step P closedHost ⟨s, f, vals [] ++ .plain (.localGet x) :: []⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨rfl, w, hw', rfl⟩ := GuardSim.head_localGet hh
  have hpre : pre = [] := by simpa using hw.symm
  subst pre
  obtain rfl := Option.some.inj (Option.some.inj (hv.symm.trans hw'))
  exact hc

def guardRest (a : AddrType) : List Admin :=
  [.plain (.localTee ⟨0⟩), .plain (.intConst a.intType (BitVec.allOnes _)),
    .plain (.intRelOp a.intType .eq),
    .plain (.if_ (.value (.num (.int a.intType))) [.unreachable] [.localGet ⟨0⟩])]

def guardResult (a : AddrType) (x : BitVec a.intType.width) : Result :=
  if x = BitVec.allOnes _ then .trap else .values [addrVal a x]

theorem block_get_forced (s : Store H) (f : Frame) (a : AddrType)
    (x : BitVec a.intType.width) (hx : f.local? ⟨0⟩ = some (some (addrVal a x))) :
    Forced (P := P)
      ⟨s, f, [.plain (.block (.value (.num (.int a.intType))) [.localGet ⟨0⟩])]⟩
      ⟨s, f, [aconst a x]⟩ := by
  refine .step (by simpa [vals] using
    (Step.block (P := P) (host := closedHost) (s := s) (f := f) (vs := [])
      (t₁ := []) (t₂ := [.num (.int a.intType)]) rfl rfl))
    (fun _ h => GrowOOM.block_value_step_unique h) ?_
  have get : Forced (P := P) ⟨s, f, [.plain (.localGet ⟨0⟩)]⟩ ⟨s, f, vals [addrVal a x]⟩ :=
    .step (.variable (.localGet hx)) (fun _ h => localGet_step_unique hx h) (.done _)
  apply forced_trans (d := ⟨s, f, [.label 1 [] (vals [addrVal a x])]⟩)
  · simpa [expression] using forced_label get 1 []
  · simpa [vals, addrVal, Val.toAdmin, aconst] using
      (Forced.step (Step.labelVals (P := P) (host := closedHost) (s := s) (f := f)
        (n := 1) (cont := []) (vs := [addrVal a x]))
        (fun _ h => GrowWrapper.label_values_unique h) (.done _))

/-- Save the actual grow result; the comparison and both exits are forced at
any profile. Only the fresh local changes, and the complete store is retained. -/
theorem guard_forced (s : Store H) (f : Frame) (a : AddrType)
    (x : BitVec a.intType.width) (hx : 0 < f.locals.length) :
    Forced (P := P) ⟨s, f, aconst a x :: guardRest a⟩
      ⟨s, f.setLocal ⟨0⟩ (addrVal a x), (guardResult a x).toAdmin⟩ := by
  let v := addrVal a x
  let g := f.setLocal ⟨0⟩ v
  let tail : List Admin := [.plain (.intConst a.intType (BitVec.allOnes _)),
    .plain (.intRelOp a.intType .eq),
    .plain (.if_ (.value (.num (.int a.intType))) [.unreachable] [.localGet ⟨0⟩])]
  refine .step (d := ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet ⟨0⟩)] ++ tail⟩)
    (by simpa [guardRest, tail, v, addrVal, aconst, Val.toAdmin] using
      Step.append_right (.variable (VariableStep.localTee (s := s) (f := f) (x := ⟨0⟩) (v := v))) tail)
    (fun c h => by
      have h' : Step P closedHost ⟨s, f, vals [] ++ [v.toAdmin, .plain (.localTee ⟨0⟩)] ++ tail⟩ c := by
        simpa [guardRest, tail, v, addrVal, aconst, Val.toAdmin] using h
      simpa [vals] using SimplifyLocalsLite.localTee_step_unique h') ?_
  refine .step (d := ⟨s, g, v.toAdmin :: tail⟩)
    (by simpa [g, vals] using Step.append_right (Step.vals_left
      (.variable (VariableStep.localSet (s := s) (f := f) (x := ⟨0⟩) (v := v) hx)) [v]) tail)
    (fun _ h => by simpa [g, vals] using
      SimplifyLocalsLite.localSet_step_unique (vs := [v]) h) ?_
  have read : g.local? ⟨0⟩ = some (some (addrVal a x)) := by
    simp [g, v, Frame.local?, Frame.setLocal, Idx.toNat, hx]
  have compare : intRelOp a.intType .eq x (BitVec.allOnes _) =
      if x = BitVec.allOnes _ then 1 else 0 := by simp [intRelOp, bool32]
  have cmp := Step.numeric (P := P) (host := closedHost) (s := s) (f := g)
    (NumericStep.intRelOp (t := a.intType) (op := .eq) (x := x) (y := BitVec.allOnes _))
  have cmpAppend := Step.append_right cmp
    [.plain (.if_ (.value (.num (.int a.intType))) [.unreachable] [.localGet ⟨0⟩])]
  refine .step (d := ⟨s, g, [constI32 (if x = BitVec.allOnes _ then 1 else 0),
      .plain (.if_ (.value (.num (.int a.intType))) [.unreachable] [.localGet ⟨0⟩])]⟩)
    (by simpa [tail, v, addrVal, Val.toAdmin, compare] using cmpAppend)
    (fun _ h => by simpa [tail, v, addrVal, Val.toAdmin, compare] using intRel_step_unique h) ?_
  by_cases failure : x = BitVec.allOnes _
  · simp only [failure, ↓reduceIte]
    refine .step (.ifTrue (by decide)) (fun _ h => by simpa using GrowOOM.if_step_unique h) ?_
    simpa [guardResult, failure, Result.toAdmin, g, v] using GrowOOM.block_trap_forced (P := P) s g a
  · simp only [failure, ↓reduceIte]
    refine .step .ifFalse (fun _ h => by simpa using GrowOOM.if_step_unique h) ?_
    simpa [guardResult, failure, Result.toAdmin, vals, addrVal, Val.toAdmin, aconst, g, v] using
      block_get_forced (P := P) s g a x read

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
