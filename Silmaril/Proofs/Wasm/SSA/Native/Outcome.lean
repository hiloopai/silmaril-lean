module

public import Silmaril.Proofs.Wasm.SSA.Native.BwdRun

@[expose] public section

/-!
# Every native result of an arity-checked body is observable (proofs)

`native_outcome`: on an arity-checked fragment function (`FragFunc.native`), every result of
silmaril's native interpreter on its body has a call outcome (`flowOut`), and the function
runs to it. With `native_backward` this says the interpreter never ends a checked body with an
unobservable flow (an outer branch, an exception, a non-integer result). New proof, from the
backward simulation `bwd`.
-/

namespace Silmaril.Proofs.Wasm.SSA.Native.Bwd

open Silmaril.Wasm hiding Expr
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

/-- A value of the result arity, carried out of a body, has a call outcome. -/
theorem flowOut_carried {res : Option IntType} {r : Option WVal} (har : arR r = arOf res)
    (junk : List Val) :
    (∃ o, flowOut res (.normal (r.toList.map WVal.toVal ++ junk)) = some o) ∧
    (∃ o, flowOut res (.brk 0 (r.toList.map WVal.toVal ++ junk)) = some o) ∧
    (∃ o, flowOut res (.ret (r.toList.map WVal.toVal ++ junk)) = some o) := by
  cases res with
  | none => exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  | some t =>
    cases r with
    | none => simp [arOf] at har
    | some w =>
      have hv : WVal.ofVal? (WVal.toVal w) = some w := ofVal_toVal w
      exact ⟨⟨.ret (some w), by simp [flowOut, hv]⟩, ⟨.ret (some w), by simp [flowOut, hv]⟩,
        ⟨.ret (some w), by simp [flowOut, hv]⟩⟩

/-- A completed body pushes the values of an optional result of its arity. -/
theorem pushed_carried {res : Option IntType} {P : List WVal} {b : Ar} (hb : arOf res = b)
    (h : P = [] ∧ b = .none ∨ ∃ w, P = [w] ∧ b = .one) :
    ∃ r : Option WVal, (P.map WVal.toVal).reverse ++ [] = r.toList.map WVal.toVal ++ [] ∧
      arR r = arOf res := by
  rcases h with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩
  · exact ⟨none, rfl, hb.symm⟩
  · exact ⟨some w, rfl, hb.symm⟩

/-- **Every native result of an arity-checked body has a call outcome**, which the function
reaches. -/
theorem native_outcome {H : Type} {s : Store H} {mi : ModuleInst} {f : FragFunc}
    {bs : List BExpr} (hb : ofBExprs? bs = some f.body) (hn : f.native = true)
    {args : List WVal} (hty : args.map WVal.type = f.params) {s' : Store H} {fr : Frame}
    {fl : Flow} (h : Binaryen.Eval s (frameOf mi (f.initLocals args)) [] bs (s', fr, fl)) :
    ∃ o, flowOut f.result fl = some o ∧ f.Run args o := by
  suffices ho : ∃ o, flowOut f.result fl = some o by
    obtain ⟨o, ho⟩ := ho
    exact ⟨o, ho, native_backward hb hn hty h ho⟩
  obtain ⟨a, hseqty⟩ : ∃ a, tySeq [arOf f.result] (arOf f.result)
      (f.params.length + f.locals.length) f.body = some a := arFits_some hn
  have hfit : arFits (arOf f.result) (some a) = true := by
    rw [← hseqty]
    exact hn
  obtain ⟨ob, hT, hc⟩ := bwd h rfl hb (tyL_of_tySeq hseqty)
  obtain ⟨-, hP⟩ := execT_seq hseqty hT
  rcases corr_flow hc with ⟨ls', P, hob, -, -, hfl⟩ | ⟨l, ls', r, junk, hob, -, -, hfl, hl⟩ |
      ⟨r, junk, hob, -, hfl, hR⟩ | ⟨hob, -, hfl⟩
  · show ∃ o, flowOut f.result fl = some o
    obtain ⟨b, rfl, hPb⟩ := hP _ _ hob
    have hb' : arOf f.result = b := arFits_eq hfit
    obtain ⟨r, hr, har⟩ := pushed_carried hb' hPb
    rw [hfl, hr]
    exact (flowOut_carried har []).1
  · show ∃ o, flowOut f.result fl = some o
    rcases l with _ | l
    · have har : arR r = arOf f.result := by simpa using hl.symm
      rw [hfl]
      exact (flowOut_carried har junk).2.1
    · simp at hl
  · rw [hfl]
    exact (flowOut_carried hR.symm junk).2.2
  · exact ⟨.trap, by rw [hfl]; rfl⟩

end Silmaril.Proofs.Wasm.SSA.Native.Bwd
