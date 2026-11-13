module

public import Silmaril.Proofs.Wasm.Det.Core.Litmus.Leaf

/-!
# Litmus module: explicit Core runs (proofs)

Core 3.0 runs of the litmus module `litMod` (`Silmaril.Wasm.Det.Core.Litmus`), built rule by rule
(`callRefFunc`, the body under `ctxtFrame`/`ctxtLabel`, `labelVals`, `frameVals`):

* `nan_run`: at every profile with the specification's NaN semantics, the invocation of
  function `1` (`f32.add` of two canonical NaNs) returns the positive and also the negative
  canonical NaN;
* `set_run`: function `2` writes `5` to the global at address `1`;
* `get_run`: function `3` returns the global's value.

The shapes of the allocated functions are computed by kernel evaluation (`decide +kernel`) of
Boolean checks (`litShape`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Core.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Det.Core.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-! ## Invocations of nullary functions -/

/-- Steps under a call frame and its label. -/
theorem steps_frame_label' {P : Profile} {host : HostSemantics Nat} {f : Frame} {n m : Nat}
    {cont : List Instr} {c c' : Config Nat} (h : Steps P host c c') :
    Steps P host ⟨c.store, f, [.frame n c.frame [.label m cont c.code]]⟩
      ⟨c'.store, f, [.frame n c'.frame [.label m cont c'.code]]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rename_i x y _
    rcases x with ⟨sx, fx, cx⟩
    rcases y with ⟨sy, fy, cy⟩
    exact ih.tail (.ctxtFrame (.ctxtLabel hs))

/-- Body steps under a call frame and its label. -/
theorem steps_frame_label {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat}
    {f fi fi' : Frame} {n m : Nat} {cont : List Instr} {is is' : List Admin}
    (h : Steps P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Steps P host ⟨s, f, [.frame n fi [.label m cont is]]⟩
      ⟨s', f, [.frame n fi' [.label m cont is']]⟩ :=
  steps_frame_label' (f := f) (n := n) (m := m) (cont := cont) h

/-- **A run of a nullary function**: if its body runs to values `out` in its call frame, the
invocation returns `out`. -/
theorem steps_invoke_nil {P : Profile} {s s' : Store Nat} {a : Nat} {fi : FuncInst Nat}
    {fn : Func} {ps rs : Validation.Ty (.list .val)} (hf : s.funcs[a]? = some fi)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hcode : fi.code = .wasm fn) {f' : Frame} {out : List Val}
    (hbody : Steps P Det.noHost ⟨s, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
      ⟨s', f', vals out⟩) (hout : out.length = rs.length) :
    Steps P Det.noHost (invoke s a []) ⟨s', {}, vals out⟩ := by
  have h₁ : Step P Det.noHost (invoke s a [])
      ⟨s, {}, [.frame rs.length (Frame.forCall fi.module [] fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ :=
    Step.callRefFunc (vs := []) (c := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default))
      trivial hf he hps.symm hcode
  have h₂ : Steps P Det.noHost
      ⟨s, {}, [.frame rs.length (Frame.forCall fi.module [] fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩
      ⟨s', {}, [.frame rs.length f' [.label rs.length [] (vals out)]]⟩ :=
    steps_frame_label hbody
  have h₃ : Step P Det.noHost ⟨s', {}, [.frame rs.length f' [.label rs.length [] (vals out)]]⟩
      ⟨s', {}, [.frame rs.length f' (vals out)]⟩ :=
    .ctxtFrame .labelVals
  have h₄ : Step P Det.noHost ⟨s', {}, [.frame rs.length f' (vals out)]⟩ ⟨s', {}, vals out⟩ :=
    .frameVals hout
  exact ((Relation.ReflTransGen.single h₁).trans h₂).tail h₃ |>.tail h₄

/-- A function type read off `funcType?` expands. -/
theorem expand_of_funcType? {d : Validation.DefType} {ps' rs' : List Validation.CValType}
    (h : d.funcType? = some (ps', rs')) :
    ∃ ps rs, Validation.Expand d (.func ps rs) ∧ ps.toList = ps' ∧ rs.toList = rs' := by
  unfold Validation.DefType.funcType? at h
  split at h
  · rename_i ps rs heq
    have h' : ps.toList = ps' ∧ rs.toList = rs' := by simpa only [Option.some.injEq,
      Prod.mk.injEq] using h
    exact ⟨ps, rs, Validation.Expand.iff.mpr heq, h'.1, h'.2⟩
  · cases h

/-! ## Shapes of the allocated functions -/

/-- The body of function `1`: `f32.const nan; f32.const nan; f32.add`. -/
def nanBody : List Instr → Bool
  | [.floatConst .f32 x, .floatConst .f32 y, .floatBinOp .f32 .add] =>
    decide (x.toNat = nanP.toNat ∧ y.toNat = nanP.toNat)
  | _ => false

/-- The body of function `2`: `i32.const 5; global.set 0`. -/
def setBody : List Instr → Bool
  | [.intConst .i32 x, .globalSet g] => decide (x = 5 ∧ g = ⟨0⟩)
  | _ => false

/-- The body of function `3`: `global.get 0`. -/
def getBody : List Instr → Bool
  | [.globalGet g] => decide (g = ⟨0⟩)
  | _ => false

/-- Wasm code without locals whose body passes `body`. -/
def codeIs (body : List Instr → Bool) : FuncCode Nat → Bool
  | .wasm fn => fn.locals.isEmpty && body fn.body
  | .host _ => false

/-- The shape of a function instance of `litMod`: its code, its type, and the global `0` of its
module instance in `litStore` and after the write of function `2`. -/
def litShape (body : List Instr → Bool) (ty : List Validation.CValType × List Validation.CValType)
    (fi : FuncInst Nat) : Bool :=
  codeIs body fi.code && decide (fi.type.funcType? = some ty) &&
    decide (((litStore.global? (Frame.forCall fi.module [] []) ⟨0⟩).map
      fun p => (p.1, p.2.value)) = some (1, Val.i32 0)) &&
    decide ((((litStore.setGlobal 1 (Val.i32 5)).global? (Frame.forCall fi.module [] []) ⟨0⟩).map
      fun p => (p.1, p.2.value)) = some (1, Val.i32 5))

theorem lit_shape1 :
    (litStore.funcs[1]?.map (litShape nanBody ([], [.num (.float .f32)]))) = some true := by
  decide +kernel
theorem lit_shape2 : (litStore.funcs[2]?.map (litShape setBody ([], []))) = some true := by
  decide +kernel
theorem lit_shape3 :
    (litStore.funcs[3]?.map (litShape getBody ([], [.num (.int .i32)]))) = some true := by
  decide +kernel

/-- What a shape check gives. -/
theorem litShape_spec {i : Nat} {body : List Instr → Bool}
    {ty : List Validation.CValType × List Validation.CValType}
    (h : litStore.funcs[i]?.map (litShape body ty) = some true) :
    ∃ fi fn, litStore.funcs[i]? = some fi ∧ fi.code = .wasm fn ∧ fn.locals = [] ∧
      body fn.body = true ∧ fi.type.funcType? = some ty ∧
      (∃ g, litStore.global? (Frame.forCall fi.module [] []) ⟨0⟩ = some (1, g) ∧
        g.value = Val.i32 0) ∧
      (∃ g, (litStore.setGlobal 1 (Val.i32 5)).global? (Frame.forCall fi.module [] []) ⟨0⟩ =
        some (1, g) ∧ g.value = Val.i32 5) := by
  rcases hfi : litStore.funcs[i]? with _ | fi
  · rw [hfi] at h
    cases h
  · show ∃ fi' fn, some fi = some fi' ∧ _
    rw [hfi] at h
    have hs : litShape body ty fi = true := Option.some.inj h
    have hs' : (codeIs body fi.code = true ∧ fi.type.funcType? = some ty) ∧
        ((litStore.global? (Frame.forCall fi.module [] []) ⟨0⟩).map
          fun p => (p.1, p.2.value)) = some (1, Val.i32 0) ∧
        (((litStore.setGlobal 1 (Val.i32 5)).global? (Frame.forCall fi.module [] []) ⟨0⟩).map
          fun p => (p.1, p.2.value)) = some (1, Val.i32 5) := by
      simpa only [litShape, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hs
    rcases hc : fi.code with fn | hh
    · show ∃ fi' fn, some fi = some fi' ∧ _
      have hcode : fn.locals.isEmpty = true ∧ body fn.body = true := by
        simpa only [hc, codeIs, Bool.and_eq_true] using hs'.1.1
      have hg₀ : ∃ g, litStore.global? (Frame.forCall fi.module [] []) ⟨0⟩ = some (1, g) ∧
          g.value = Val.i32 0 := by
        obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp hs'.2.1
        exact ⟨p.2, by rw [hp, ← (Prod.mk.inj hpe).1], (Prod.mk.inj hpe).2⟩
      have hg₁ : ∃ g, (litStore.setGlobal 1 (Val.i32 5)).global? (Frame.forCall fi.module [] [])
          ⟨0⟩ = some (1, g) ∧ g.value = Val.i32 5 := by
        obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp hs'.2.2
        exact ⟨p.2, by rw [hp, ← (Prod.mk.inj hpe).1], (Prod.mk.inj hpe).2⟩
      exact ⟨fi, fn, rfl, hc, List.isEmpty_iff.mp hcode.1, hcode.2, hs'.1.2, hg₀, hg₁⟩
    · have hb : codeIs body fi.code = true := hs'.1.1
      rw [hc] at hb
      cases hb

theorem nanBody_eq {b : List Instr} (h : nanBody b = true) :
    b = [.floatConst .f32 nanP, .floatConst .f32 nanP, .floatBinOp .f32 .add] := by
  unfold nanBody at h
  split at h
  · rename_i x y
    have h' : x.toNat = nanP.toNat ∧ y.toNat = nanP.toNat := of_decide_eq_true h
    have hx : x = nanP := BitVec.eq_of_toNat_eq h'.1
    have hy : y = nanP := BitVec.eq_of_toNat_eq h'.2
    rw [hx, hy]
  · cases h

theorem setBody_eq {b : List Instr} (h : setBody b = true) :
    b = [.intConst .i32 5, .globalSet ⟨0⟩] := by
  unfold setBody at h
  split at h
  · rename_i x g
    have h' : x = 5 ∧ g = ⟨0⟩ := of_decide_eq_true h
    rw [h'.1, h'.2]
  · cases h

theorem getBody_eq {b : List Instr} (h : getBody b = true) : b = [.globalGet ⟨0⟩] := by
  unfold getBody at h
  split at h
  · rename_i g
    have h' : g = ⟨0⟩ := of_decide_eq_true h
    rw [h']
  · cases h

/-- A function of `litMod` without parameters is invoked on no arguments (in every store with
the functions of `litStore`). -/
theorem invokeOk_nil {i : Nat} {body : List Instr → Bool} {rs' : List Validation.CValType}
    (h : litStore.funcs[i]?.map (litShape body ([], rs')) = some true) {s : Store Nat}
    (hs : s.funcs = litStore.funcs) : InvokeOk s i [] := by
  obtain ⟨fi, -, hfi, -, -, -, hty, -, -⟩ := litShape_spec h
  obtain ⟨ps, rs, he, hps, -⟩ := expand_of_funcType? hty
  refine ⟨fi, ps, rs, by rw [hs]; exact hfi, he, ?_⟩
  rw [hps]
  exact .nil

/-! ## The runs -/

/-- The value of an `f32` result. -/
def f32v (z : BitVec 32) : Val := .num ⟨.float .f32, z⟩

/-- **Function `1` may return any NaN `f32.add` allows**: at a profile with the specification's
NaN semantics, every result the profile allows for the sum of the two NaNs is returned. -/
theorem nan_run {P : Profile} (hP : P.nan = .spec) {z : BitVec 32}
    (hz : Numerics.floatBinOpRel .f32 .add nanP nanP z) :
    Steps P Det.noHost (invoke litStore 1 []) ⟨litStore, {}, vals [f32v z]⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hloc, hb, hty, -, -⟩ := litShape_spec lit_shape1
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hbody : fn.body = [.floatConst .f32 nanP, .floatConst .f32 nanP, .floatBinOp .f32 .add] :=
    nanBody_eq hb
  have hzP : Numerics.floatBinOpP P .f32 .add nanP nanP z := by
    simpa only [Numerics.floatBinOpP, hP] using hz
  have hstep : Steps P Det.noHost
      ⟨litStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
      ⟨litStore, Frame.forCall fi.module [] fn.locals, vals [f32v z]⟩ := by
    rw [hbody]
    exact Relation.ReflTransGen.single (.numeric (.floatBinOp hzP))
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : [f32v z].length = rs.length := by
    show 1 = rs.toList.length
    rw [hrs]
    rfl
  exact steps_invoke_nil hfi he hps0 hcode hstep hout

/-- The two canonical NaNs are allowed sums of the canonical NaN with itself. -/
theorem nanP_allowed : Numerics.floatBinOpRel .f32 .add nanP nanP nanP := by
  show Silmaril.Numeric.Ieee754.F32.binaryResult (Numerics.floatBinOp32 .add)
    (Numerics.asF32 nanP) (Numerics.asF32 nanP) (Numerics.asF32 nanP)
  decide +kernel

theorem nanN_allowed : Numerics.floatBinOpRel .f32 .add nanP nanP nanN := by
  show Silmaril.Numeric.Ieee754.F32.binaryResult (Numerics.floatBinOp32 .add)
    (Numerics.asF32 nanP) (Numerics.asF32 nanP) (Numerics.asF32 nanN)
  decide +kernel

/-- **Function `2` writes `5` to the global at address `1`**, at every profile. -/
theorem set_run (P : Profile) :
    Steps P Det.noHost (invoke litStore 2 []) ⟨litStore.setGlobal 1 (Val.i32 5), {}, vals []⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hloc, hb, hty, ⟨g, hg, -⟩, -⟩ := litShape_spec lit_shape2
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hbody : fn.body = [.intConst .i32 5, .globalSet ⟨0⟩] := setBody_eq hb
  have hg' : litStore.global? (Frame.forCall fi.module [] fn.locals) ⟨0⟩ = some (1, g) := by
    rw [hloc]
    exact hg
  have hstep : Steps P Det.noHost
      ⟨litStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
      ⟨litStore.setGlobal 1 (Val.i32 5), Frame.forCall fi.module [] fn.locals, vals []⟩ := by
    rw [hbody]
    exact Relation.ReflTransGen.single (.variable (.globalSet (v := Val.i32 5) hg'))
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : ([] : List Val).length = rs.length := by
    show 0 = rs.toList.length
    rw [hrs]
    rfl
  exact steps_invoke_nil hfi he hps0 hcode hstep hout

/-- **Function `3` returns the global**: `0` in `litStore`, `5` after the write. -/
theorem get_run (P : Profile) :
    Steps P Det.noHost (invoke litStore 3 []) ⟨litStore, {}, vals [Val.i32 0]⟩ ∧
      Steps P Det.noHost (invoke (litStore.setGlobal 1 (Val.i32 5)) 3 [])
        ⟨litStore.setGlobal 1 (Val.i32 5), {}, vals [Val.i32 5]⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hloc, hb, hty, ⟨g₀, hg₀, hv₀⟩, ⟨g₁, hg₁, hv₁⟩⟩ :=
    litShape_spec lit_shape3
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hbody : fn.body = [.globalGet ⟨0⟩] := getBody_eq hb
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : [Val.i32 0].length = rs.length := by
    show 1 = rs.toList.length
    rw [hrs]
    rfl
  have hfi' : (litStore.setGlobal 1 (Val.i32 5)).funcs[3]? = some fi := hfi
  constructor
  · show Steps P Det.noHost (invoke litStore 3 []) ⟨litStore, {}, vals [Val.i32 0]⟩
    have hg : litStore.global? (Frame.forCall fi.module [] fn.locals) ⟨0⟩ = some (1, g₀) := by
      rw [hloc]
      exact hg₀
    have hstep : Steps P Det.noHost
        ⟨litStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
        ⟨litStore, Frame.forCall fi.module [] fn.locals, vals [Val.i32 0]⟩ := by
      rw [hbody]
      have h₁ := Relation.ReflTransGen.single (r := Step P Det.noHost) (.variable (.globalGet hg))
      rw [hv₀] at h₁
      exact h₁
    exact steps_invoke_nil hfi he hps0 hcode hstep hout
  · show Steps P Det.noHost (invoke (litStore.setGlobal 1 (Val.i32 5)) 3 [])
      ⟨litStore.setGlobal 1 (Val.i32 5), {}, vals [Val.i32 5]⟩
    have hg : (litStore.setGlobal 1 (Val.i32 5)).global? (Frame.forCall fi.module [] fn.locals)
        ⟨0⟩ = some (1, g₁) := by
      rw [hloc]
      exact hg₁
    have hstep : Steps P Det.noHost
        ⟨litStore.setGlobal 1 (Val.i32 5), Frame.forCall fi.module [] fn.locals, expression fn.body⟩
        ⟨litStore.setGlobal 1 (Val.i32 5), Frame.forCall fi.module [] fn.locals,
          vals [Val.i32 5]⟩ := by
      rw [hbody]
      have h₁ := Relation.ReflTransGen.single (r := Step P Det.noHost) (.variable (.globalGet hg))
      rw [hv₁] at h₁
      exact h₁
    exact steps_invoke_nil hfi' he hps0 hcode hstep hout

end Silmaril.Proofs.Wasm.Det.Core.Litmus
