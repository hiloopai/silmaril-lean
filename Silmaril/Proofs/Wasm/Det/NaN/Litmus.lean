module

public import Silmaril.Wasm.Det.NaN.Thms
public import Silmaril.Wasm.Det.NaN.Litmus.Defs

/-!
# Litmus module for determinism up to NaN payloads: explicit Core runs (proofs)

Core 3.0 runs of `nanMod` (`Silmaril.Wasm.Det.NaN.Litmus`), built rule by rule:

* `guard_run`, `cmp_run`: at the deterministic profile `profile neverFail`, on any two `f32`
  arguments, `guard` and `cmp` return a value that is not a NaN (`guard` returns the sum only
  when `sum == sum`, which fails for every NaN: `eq_self_nan`);
* `raw_run`: at a profile with the specification's NaN semantics, `raw` on two NaNs returns
  every NaN that `f32.add` allows, in particular `+nan` and `-nan` (`nanP_allowed`,
  `nanN_allowed`).

The shapes of the allocated functions are computed by kernel evaluation of Boolean checks
(`shapeOk`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Det.NaN Silmaril.Wasm.Det.NaN.Litmus
open Silmaril.Wasm.Numerics (Profile floatBinOp floatRelOp)

/-! ## Shapes -/

theorem shape_spec {i : Nat} {body : List Instr → Bool} {locals : List ValType}
    {ty : List Validation.CValType × List Validation.CValType}
    (h : nanStore.funcs[i]?.map (shapeOk body locals ty) = some true) :
    ∃ fi fn, nanStore.funcs[i]? = some fi ∧ fi.code = .wasm fn ∧ body fn.body = true ∧
      fn.locals = locals ∧ fi.type.funcType? = some ty := by
  rcases hfi : nanStore.funcs[i]? with _ | fi
  · rw [hfi] at h
    cases h
  · rw [hfi] at h
    have hs : shapeOk body locals ty fi = true := Option.some.inj h
    rcases hc : fi.code with fn | hh
    · have hs' : (body fn.body = true ∧ fn.locals = locals) ∧ fi.type.funcType? = some ty := by
        simpa only [shapeOk, hc, Bool.and_eq_true, decide_eq_true_eq] using hs
      exact ⟨fi, fn, rfl, hc, hs'.1.1, hs'.1.2, hs'.2⟩
    · have hs' : false = true := by simpa only [shapeOk, hc, Bool.false_and] using hs
      cases hs'

theorem shape0 : nanStore.funcs[0]?.map (shapeOk rawB [] tyFF) = some true := by decide +kernel
theorem shape1 : nanStore.funcs[1]?.map (shapeOk guardB [.f32] tyFF) = some true := by
  decide +kernel
theorem shape2 : nanStore.funcs[2]?.map (shapeOk cmpB [] tyFI) = some true := by decide +kernel

theorem rawB_eq {b : List Instr} (h : rawB b = true) : b = rawBody := by
  unfold rawB at h
  split at h
  · rename_i a c
    have h' : a = ⟨0⟩ ∧ c = ⟨1⟩ := of_decide_eq_true h
    rw [h'.1, h'.2]
    rfl
  · cases h

theorem guardB_eq {b : List Instr} (h : guardB b = true) : b = guardBody := by
  unfold guardB at h
  split at h
  · rename_i a c t z d e
    have h' : a = ⟨0⟩ ∧ c = ⟨1⟩ ∧ t = ⟨2⟩ ∧ z.toNat = 0 ∧ d = ⟨2⟩ ∧ e = ⟨2⟩ := of_decide_eq_true h
    have hz : z = 0 := BitVec.eq_of_toNat_eq h'.2.2.2.1
    rw [h'.1, h'.2.1, h'.2.2.1, hz, h'.2.2.2.2.1, h'.2.2.2.2.2]
    rfl
  · cases h

theorem cmpB_eq {b : List Instr} (h : cmpB b = true) : b = cmpBody := by
  unfold cmpB at h
  split at h
  · rename_i a c z
    have h' : a = ⟨0⟩ ∧ c = ⟨1⟩ ∧ z.toNat = one32.toNat := of_decide_eq_true h
    have hz : z = one32 := BitVec.eq_of_toNat_eq h'.2.2
    rw [h'.1, h'.2.1, hz]
    rfl
  · cases h

/-- A function type read off `funcType?` expands. -/
theorem expand_of_funcType? {d : Validation.DefType} {ps' rs' : List Validation.CValType}
    (h : d.funcType? = some (ps', rs')) :
    ∃ ps rs, Validation.Expand d (.func ps rs) ∧ ps.toList = ps' ∧ rs.toList = rs' := by
  unfold Validation.DefType.funcType? at h
  split at h
  · rename_i ps rs heq
    have h' : ps.toList = ps' ∧ rs.toList = rs' := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using h
    exact ⟨ps, rs, Validation.Expand.iff.mpr heq, h'.1, h'.2⟩
  · cases h

/-- Typed arguments of a function with two `f32` parameters are two `f32` values. -/
theorem args_f32 {s : Store Nat} {a : Nat} {vs : List Val} {fi : FuncInst Nat}
    {rs' : List Validation.CValType} (hfi : s.funcs[a]? = some fi)
    (hty : fi.type.funcType? = some ([.num (.float .f32), .num (.float .f32)], rs'))
    (hok : InvokeOk s a vs) : ∃ x y, vs = [f32v x, f32v y] := by
  obtain ⟨fi', ps, rs, hfi', he, hvs⟩ := hok
  have hfe : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst hfe
  have hty' : fi'.type.funcType? = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?
    rw [Validation.Expand.iff.mp he]
  have hps : ps.toList = [.num (.float .f32), .num (.float .f32)] := by
    rw [hty] at hty'
    exact (Prod.mk.inj (Option.some.inj hty')).1.symm
  rw [hps] at hvs
  match vs, hvs with
  | [.num ⟨t₁, x⟩, .num ⟨t₂, y⟩], .cons h₁ (.cons h₂ .nil) =>
    cases h₁
    cases h₂
    exact ⟨x, y, rfl⟩

/-! ## Invocations -/

theorem steps_frame_label' {P : Profile} {f : Frame} {n m : Nat} {cont : List Instr}
    {c c' : Config Nat} (h : Steps P Det.noHost c c') :
    Steps P Det.noHost ⟨c.store, f, [.frame n c.frame [.label m cont c.code]]⟩
      ⟨c'.store, f, [.frame n c'.frame [.label m cont c'.code]]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rename_i x y _
    rcases x with ⟨sx, fx, cx⟩
    rcases y with ⟨sy, fy, cy⟩
    exact ih.tail (.ctxtFrame (.ctxtLabel hs))

/-- **A run of an invocation**: if the body runs to values `out` in its call frame, the
invocation returns `out`. -/
theorem steps_invoke {P : Profile} {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {fn : Func}
    {ps rs : Validation.Ty (.list .val)} {vs : List Val} (hf : s.funcs[a]? = some fi)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : vs.length = ps.length)
    (hcode : fi.code = .wasm fn) {f' : Frame} {out : List Val}
    (hbody : Steps P Det.noHost ⟨s, Frame.forCall fi.module vs fn.locals, expression fn.body⟩
      ⟨s, f', vals out⟩) (hout : out.length = rs.length) :
    Steps P Det.noHost (invoke s a vs) ⟨s, {}, vals out⟩ := by
  have h₁ : Step P Det.noHost (invoke s a vs)
      ⟨s, {}, [.frame rs.length (Frame.forCall fi.module vs fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ :=
    Step.callRefFunc (c := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default))
      trivial hf he hps hcode
  have h₂ : Steps P Det.noHost
      ⟨s, {}, [.frame rs.length (Frame.forCall fi.module vs fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩
      ⟨s, {}, [.frame rs.length f' [.label rs.length [] (vals out)]]⟩ :=
    steps_frame_label' (f := {}) (n := rs.length) (m := rs.length) (cont := []) hbody
  have h₃ : Step P Det.noHost ⟨s, {}, [.frame rs.length f' [.label rs.length [] (vals out)]]⟩
      ⟨s, {}, [.frame rs.length f' (vals out)]⟩ :=
    .ctxtFrame .labelVals
  have h₄ : Step P Det.noHost ⟨s, {}, [.frame rs.length f' (vals out)]⟩ ⟨s, {}, vals out⟩ :=
    .frameVals hout
  exact ((Relation.ReflTransGen.single h₁).trans h₂).tail h₃ |>.tail h₄

/-- One step of the body, at a position. -/
theorem lift {P : Profile} (vs : List Val) (rest : List Admin) {a b : Config Nat}
    (h : Step P Det.noHost a b) :
    Relation.ReflTransGen (Step P Det.noHost) ⟨a.store, a.frame, vals vs ++ a.code ++ rest⟩
      ⟨b.store, b.frame, vals vs ++ b.code ++ rest⟩ :=
  .single (Det.lift_instrs vs rest a b h)

/-! ## The body runs -/

/-- `x == x` fails for every `f32` NaN. -/
theorem eq_self_nan {z : BitVec 32} (hz : (Numerics.asF32 z).IsNaN) :
    floatRelOp .f32 .eq z z = 0 := by
  show Numerics.bool32 (Silmaril.Numeric.Ieee754.F32.equal (Numerics.asF32 z) (Numerics.asF32 z))
    = 0
  simp only [Silmaril.Numeric.Ieee754.F32.equal, model_nan32 hz]
  decide

/-- The body of `guard`, at the deterministic profile: the sum if it is not a NaN, else `0`. -/
theorem guard_body (s : Store Nat) (m : ModuleInst) (x y : BitVec 32) :
    ∃ v f', Steps (profile neverFail) Det.noHost
      ⟨s, Frame.forCall m [f32v x, f32v y] [.f32], expression guardBody⟩ ⟨s, f', vals [v]⟩ ∧
      nanVal v = false := by
  let F0 := Frame.forCall m [f32v x, f32v y] [.f32]
  let z := floatBinOp .f32 .add x y
  let F1 := F0.setLocal ⟨2⟩ (f32v z)
  let c := floatRelOp .f32 .eq z z
  let lg (i : Nat) (hi : i < 2 ^ 32) : Admin := .plain (.localGet ⟨⟨i, hi⟩⟩)
  have run₁ : Steps (profile neverFail) Det.noHost ⟨s, F0, expression guardBody⟩
      ⟨s, F0, [(f32v z).toAdmin, .plain (.localTee ⟨2⟩), .plain (.floatConst .f32 0),
        lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq),
        .plain (.select none)]⟩ := by
    refine .trans (lift (P := profile neverFail) [] [lg 1 (by decide),
      .plain (.floatBinOp .f32 .add), .plain (.localTee ⟨2⟩), .plain (.floatConst .f32 0),
      lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localGet (s := s) (f := F0) (x := ⟨0⟩) (v := f32v x) rfl))) ?_
    refine .trans (lift (P := profile neverFail) [f32v x] [.plain (.floatBinOp .f32 .add),
      .plain (.localTee ⟨2⟩), .plain (.floatConst .f32 0), lg 2 (by decide), lg 2 (by decide),
      .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localGet (s := s) (f := F0) (x := ⟨1⟩) (v := f32v y) rfl))) ?_
    exact lift (P := profile neverFail) [] [.plain (.localTee ⟨2⟩), .plain (.floatConst .f32 0),
      lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.numeric (s := s) (f := F0) (.floatBinOp (t := .f32) (op := .add) (x := x) (y := y)
        (z := z) rfl))
  have run₂ : Steps (profile neverFail) Det.noHost
      ⟨s, F0, [(f32v z).toAdmin, .plain (.localTee ⟨2⟩), .plain (.floatConst .f32 0),
        lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq),
        .plain (.select none)]⟩
      ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, lg 2 (by decide), lg 2 (by decide),
        .plain (.floatRelOp .f32 .eq), .plain (.select none)]⟩ := by
    refine .trans (lift (P := profile neverFail) [] [.plain (.floatConst .f32 0),
      lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localTee (s := s) (f := F0) (x := ⟨2⟩) (v := f32v z)))) ?_
    exact lift (P := profile neverFail) [f32v z] [.plain (.floatConst .f32 0),
      lg 2 (by decide), lg 2 (by decide), .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localSet (s := s) (f := F0) (x := ⟨2⟩) (v := f32v z)
        (by exact (by decide : (2 : Nat) < 3))))
  have run₃ : Steps (profile neverFail) Det.noHost
      ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, lg 2 (by decide), lg 2 (by decide),
        .plain (.floatRelOp .f32 .eq), .plain (.select none)]⟩
      ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, constI32 c, .plain (.select none)]⟩ := by
    refine .trans (lift (P := profile neverFail) [f32v z, f32v 0] [lg 2 (by decide),
      .plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localGet (s := s) (f := F1) (x := ⟨2⟩) (v := f32v z) rfl))) ?_
    refine .trans (lift (P := profile neverFail) [f32v z, f32v 0, f32v z]
      [.plain (.floatRelOp .f32 .eq), .plain (.select none)]
      (.variable (.localGet (s := s) (f := F1) (x := ⟨2⟩) (v := f32v z) rfl))) ?_
    exact lift (P := profile neverFail) [f32v z, f32v 0] [.plain (.select none)]
      (.numeric (s := s) (f := F1) (.floatRelOp (t := .f32) (op := .eq) (x := z) (y := z)))
  have run : Steps (profile neverFail) Det.noHost ⟨s, F0, expression guardBody⟩
      ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, constI32 c, .plain (.select none)]⟩ :=
    (run₁.trans run₂).trans run₃
  by_cases hc : c = 0
  · have hsel : Step (profile neverFail) Det.noHost
        ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, constI32 c, .plain (.select none)]⟩
        ⟨s, F1, [(f32v 0).toAdmin]⟩ := by
      rw [hc]
      exact .parametric (.selectFalse _ _ _)
    exact ⟨f32v 0, F1, run.tail hsel, by decide⟩
  · have hsel : Step (profile neverFail) Det.noHost
        ⟨s, F1, [(f32v z).toAdmin, (f32v 0).toAdmin, constI32 c, .plain (.select none)]⟩
        ⟨s, F1, [(f32v z).toAdmin]⟩ :=
      .parametric (.selectTrue hc)
    have hz : ¬ (Numerics.asF32 z).IsNaN := fun hz => hc (eq_self_nan hz)
    refine ⟨f32v z, F1, run.tail hsel, ?_⟩
    simpa [nanVal, nanBits, f32v, Silmaril.Numeric.Ieee754.F32.isNaN] using hz

/-- The body of `cmp`, at the deterministic profile: an `i32`. -/
theorem cmp_body (s : Store Nat) (m : ModuleInst) (x y : BitVec 32) :
    ∃ v f', Steps (profile neverFail) Det.noHost
      ⟨s, Frame.forCall m [f32v x, f32v y] [], expression cmpBody⟩ ⟨s, f', vals [v]⟩ ∧
      nanVal v = false := by
  let F0 := Frame.forCall m [f32v x, f32v y] []
  let z := floatBinOp .f32 .add x y
  have run : Steps (profile neverFail) Det.noHost ⟨s, F0, expression cmpBody⟩
      ⟨s, F0, [constI32 (floatRelOp .f32 .lt z one32)]⟩ := by
    refine .trans (lift (P := profile neverFail) [] [.plain (.localGet ⟨1⟩), .plain (.floatBinOp .f32 .add),
      .plain (.floatConst .f32 one32), .plain (.floatRelOp .f32 .lt)]
      (.variable (.localGet (s := s) (f := F0) (x := ⟨0⟩) (v := f32v x) rfl))) ?_
    refine .trans (lift (P := profile neverFail) [f32v x] [.plain (.floatBinOp .f32 .add),
      .plain (.floatConst .f32 one32), .plain (.floatRelOp .f32 .lt)]
      (.variable (.localGet (s := s) (f := F0) (x := ⟨1⟩) (v := f32v y) rfl))) ?_
    refine .trans (lift (P := profile neverFail) [] [.plain (.floatConst .f32 one32), .plain (.floatRelOp .f32 .lt)]
      (.numeric (s := s) (f := F0) (.floatBinOp (t := .f32) (op := .add) (x := x) (y := y)
        (z := z) rfl))) ?_
    exact lift (P := profile neverFail) [] []
      (.numeric (s := s) (f := F0) (.floatRelOp (t := .f32) (op := .lt) (x := z) (y := one32)))
  exact ⟨Val.i32 (floatRelOp .f32 .lt z one32), F0, run, rfl⟩

/-- The body of `raw` at a profile with the specification's NaN semantics returns every
allowed sum. -/
theorem raw_body {P : Profile} (hP : P.nan = .spec) (s : Store Nat) (m : ModuleInst)
    {x y z : BitVec 32} (hz : Numerics.floatBinOpRel .f32 .add x y z) :
    Steps P Det.noHost ⟨s, Frame.forCall m [f32v x, f32v y] [], expression rawBody⟩
      ⟨s, Frame.forCall m [f32v x, f32v y] [], vals [f32v z]⟩ := by
  let F0 := Frame.forCall m [f32v x, f32v y] []
  have hzP : Numerics.floatBinOpP P .f32 .add x y z := by
    simpa only [Numerics.floatBinOpP, hP] using hz
  refine .trans (lift (P := P) [] [.plain (.localGet ⟨1⟩), .plain (.floatBinOp .f32 .add)]
    (.variable (.localGet (s := s) (f := F0) (x := ⟨0⟩) (v := f32v x) rfl))) ?_
  refine .trans (lift (P := P) [f32v x] [.plain (.floatBinOp .f32 .add)]
    (.variable (.localGet (s := s) (f := F0) (x := ⟨1⟩) (v := f32v y) rfl))) ?_
  exact lift (P := P) [] [] (.numeric (s := s) (f := F0) (.floatBinOp (t := .f32) (op := .add) hzP))

theorem nanP_allowed : Numerics.floatBinOpRel .f32 .add nanP nanP nanP := by
  show Silmaril.Numeric.Ieee754.F32.binaryResult (Numerics.floatBinOp32 .add)
    (Numerics.asF32 nanP) (Numerics.asF32 nanP) (Numerics.asF32 nanP)
  decide +kernel

theorem nanN_allowed : Numerics.floatBinOpRel .f32 .add nanP nanP nanN := by
  show Silmaril.Numeric.Ieee754.F32.binaryResult (Numerics.floatBinOp32 .add)
    (Numerics.asF32 nanP) (Numerics.asF32 nanP) (Numerics.asF32 nanN)
  decide +kernel

end Silmaril.Proofs.Wasm.Det.NaN.Litmus
