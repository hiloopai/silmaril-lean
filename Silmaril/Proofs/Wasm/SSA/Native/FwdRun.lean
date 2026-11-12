module

public import Silmaril.Proofs.Wasm.SSA.Native.FwdCtl

/-!
# Native adequacy, forward direction

`native_forward`: for a fragment function that passes the arity check
(`FragFunc.native`), every terminating run is matched by silmaril's native
Binaryen interpreter (`Binaryen.Eval`) on any tree list recognised as the
body, with the same call outcome (`flowOut`). The store is unchanged and any
module instance may be used: the fragment touches neither.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType)
open Silmaril.Wasm.Binaryen (BExpr evalFlat Flow Eval arity Next)
open Silmaril.Wasm.Execution.Core (Val Store Frame ModuleInst)
open Silmaril.Wasm.SSA

section
variable {H : Type} {s : Store H} {mi : ModuleInst}

mutual

theorem fwdE : ∀ {ls : List WVal} {e : Expr} {o : Out (Option WVal)}, Exec ls e o → FE s mi ls e o
  | _, _, _, .op ha hev => fe_op (fwdA ha) hev
  | _, _, _, .op_trap ha hev => fe_op_trap (fwdA ha) hev
  | _, _, _, .op_abrupt ha hab => fe_args_abrupt (fwdA ha) hab shape_op
  | _, _, _, .localGet h => fe_localGet h
  | _, _, _, .localSet he => fe_localSet (fwdE he)
  | _, _, _, .localSet_abrupt he hab => fe_one_abrupt (fwdE he) hab (shape_one 0 _ rfl)
  | _, _, _, .localTee he => fe_localTee (fwdE he)
  | _, _, _, .localTee_abrupt he hab => fe_one_abrupt (fwdE he) hab (shape_one 1 _ rfl)
  | _, _, _, .drop he => fe_drop (fwdE he)
  | _, _, _, .drop_abrupt he hab => fe_one_abrupt (fwdE he) hab (shape_one (i₀ := 0) 2 _ rfl)
  | _, _, _, .nop => fe_nop
  | _, _, _, .unreachable => fe_unreachable
  | _, _, _, .block hs hx => fe_block (fwdS hs) hx
  | _, _, _, .loop hs hx => fe_loop (fwdS hs) hx
  | _, _, _, .loop_back hs hr => fe_loop_back (fwdS hs) (fwdE hr)
  | _, _, _, .if_ hc hb hs hx => fe_if (fwdE hc) hb (fwdS hs) hx
  | _, _, _, .if_abrupt hc hab => fe_if_abrupt (fwdE hc) hab
  | _, _, _, .br ha => fe_br (fwdA ha) ha
  | _, _, _, .br_abrupt ha hab => fe_args_abrupt (fwdA ha) hab shape_br
  | _, _, _, .brIf ha hc hb => fe_brIf (fwdA ha) ha hc hb
  | _, _, _, .brIf_abrupt ha hab => fe_args_abrupt (fwdA ha) hab shape_brIf
  | _, _, _, .return_ ha => fe_return (fwdA ha) ha
  | _, _, _, .return_abrupt ha hab => fe_args_abrupt (fwdA ha) hab shape_return

theorem fwdA : ∀ {ls : List WVal} {es : List Expr} {o : Out (List WVal)}, Args ls es o → FA s mi ls es o
  | _, _, _, .nil => fa_nil
  | _, _, _, .cons he ha => fa_cons (fwdE he) (fwdA ha)
  | _, _, _, .head_abrupt he hab => fa_head (fwdE he) hab
  | _, _, _, .tail_abrupt he ha hab => fa_tail (fwdE he) (fwdA ha) hab

theorem fwdS : ∀ {ls : List WVal} {r : Option WVal} {es : List Expr} {o : Out (Option WVal)},
    Silmaril.Wasm.SSA.Seq ls r es o → FS s mi ls r es o
  | _, _, _, _, .nil => fs_nil
  | _, _, _, _, .cons he hs => fs_cons (fwdE he) (fwdS hs) hs
  | _, _, _, _, .abrupt he hab => fs_abrupt (fwdE he) hab

end

end

theorem flowOut_ret {res : Option IntType} {r : Option WVal} (junk : List Val)
    (hR : arOf res = arR r) : flowOut res (.ret (vOf r ++ junk)) = some (.ret (blockRes res r)) := by
  cases res with
  | none => rfl
  | some t =>
      cases r with
      | none => simp [arOf, arR] at hR
      | some v => simp [flowOut, vOf, blockRes, ofVal?_toVal]

/-- Normal completion of a body returns like a `return`. -/
private theorem flowOut_normal {res : Option IntType} {r : Option WVal} (junk : List Val)
    (hR : arOf res = arR r) :
    flowOut res (.normal (vOf r ++ junk)) = some (.ret (blockRes res r)) := by
  have h : flowOut res (.normal (vOf r ++ junk)) = flowOut res (.ret (vOf r ++ junk)) := by
    cases res <;> rfl
  rw [h]
  exact flowOut_ret junk hR

/-- A branch to a function body's own label returns like a `return`. -/
private theorem flowOut_brk0 {res : Option IntType} {r : Option WVal} (junk : List Val)
    (hR : arOf res = arR r) :
    flowOut res (.brk 0 (vOf r ++ junk)) = some (.ret (blockRes res r)) := by
  have h : flowOut res (.brk 0 (vOf r ++ junk)) = flowOut res (.ret (vOf r ++ junk)) := by
    cases res <;> rfl
  rw [h]
  exact flowOut_ret junk hR

/-- A body that completes with result `r` and fits the arity `a` has arity `arR r`. -/
private theorem arR_of_fits {a : Ar} {ta : Option Ar} {r : Option WVal} (har : ta = some (arR r))
    (hfit : ta = some a ∨ ta = none) : a = arR r := by
  rcases hfit with h | h
  · exact (Option.some.inj (har.symm.trans h)).symm
  · exact absurd (har.symm.trans h) (Option.some_ne_none _)

/-- **Forward native adequacy.** -/
theorem native_forward {H : Type} (s : Store H) (mi : ModuleInst)
    {f : FragFunc} {bs : List BExpr} (hb : ofBExprs? bs = some f.body) (hn : f.native = true)
    {args : List WVal} {o : FOut} (h : f.Run args o) :
    ∃ fr fl, Eval s (frameOf mi (f.initLocals args)) [] bs (s, fr, fl) ∧
      flowOut f.result fl = some o := by
  obtain ⟨-, out, hseq, hexit⟩ := h
  have hn' : arFits (arOf f.result)
      (tySeq [arOf f.result] (arOf f.result) (f.params.length + f.locals.length) f.body) = true := hn
  obtain ⟨ta, hta, hta'⟩ := arFits_inv hn'
  obtain ⟨x, hx, hc, har⟩ := fwdS (s := s) (mi := mi) hseq rfl [arOf f.result] (arOf f.result) _ bs [] ta hb hta
  cases out with
  | ok ls r =>
      obtain rfl : x = (s, frameOf mi ls, .normal (vOf r ++ [])) := hc
      obtain rfl : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
      have hR : arOf f.result = arR r := arR_of_fits har hta'
      exact ⟨_, _, hx, flowOut_normal [] hR⟩
  | brk l ls r =>
      show ∃ fr fl, Eval s (frameOf mi (f.initLocals args)) [] bs (s, fr, fl) ∧
        flowOut f.result fl = some o
      cases l with
      | succ => nomatch hexit
      | zero =>
          obtain ⟨junk, rfl, hl⟩ : ∃ junk, x = (s, frameOf mi ls, .brk 0 (vOf r ++ junk)) ∧
              [arOf f.result][0]? = some (arR r) := hc
          obtain rfl : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
          have hR : arOf f.result = arR r := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hl
          exact ⟨_, _, hx, flowOut_brk0 junk hR⟩
  | ret r =>
      obtain ⟨fr, junk, rfl, hR⟩ : ∃ fr junk, x = (s, fr, .ret (vOf r ++ junk)) ∧
          arOf f.result = arR r := hc
      obtain rfl : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
      exact ⟨_, _, hx, flowOut_ret junk hR⟩
  | trap =>
      obtain ⟨fr, rfl⟩ : ∃ fr, x = (s, fr, .trap) := hc
      obtain rfl : o = .trap := (Option.some.inj hexit).symm
      exact ⟨_, _, hx, rfl⟩

end Silmaril.Proofs.Wasm.SSA.Native
