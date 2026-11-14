module

public import Silmaril.Project.WasmP3Rust.StdioK.Defs
public import Silmaril.Project.WasmP3Rust.TasksX.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Observations of `p3xWorld` traces, event by event

The OS image (`osTrace3`), the stdout bytes, `runOk`, the wait discipline `waitTh3x`, the stdin
scan (`stdinBytesX`) and the last `get-arguments` answer, as functions of the last event and a
state (`Obs`), so that the invariant of `DenX.den` with `stdioK` needs no trace induction.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The bytes of OS write events. -/
def wbytes (l : List Silmaril.Process.LPS.Event) : List (BitVec 8) :=
  l.filterMap fun
    | .writeEv _ b => some b
    | _ => none

/-- The OS image state after `t`. -/
def osSt (t : List WEv) : OsSt := t.foldl (fun q e => (osStep3 0 q e).1) {}

theorem osRun3_append (q : OsSt) (t u : List WEv) :
    osRun3 0 q (t ++ u) = osRun3 0 q t ++ osRun3 0 (t.foldl (fun q e => (osStep3 0 q e).1) q) u := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    rcases h : osStep3 0 q e with ⟨q', out⟩
    simp only [List.cons_append, osRun3, h, List.foldl_cons, ih, List.append_assoc]

theorem stdoutBytes_concat (t : List WEv) (e : WEv) :
    stdoutBytes (t ++ [e]) = stdoutBytes t ++ wbytes (osStep3 0 (osSt t) e).2 := by
  have h : osTrace3 0 (t ++ [e]) = osTrace3 0 t ++ (osStep3 0 (osSt t) e).2 := by
    rcases h : osStep3 0 (osSt t) e with ⟨q', out⟩
    simp only [osTrace3, osRun3_append, osSt] at h ⊢
    simp only [osRun3, h, List.append_nil]
  simp only [stdoutBytes, h, List.filterMap_append]
  rfl

/-- `run` returned `ok` at the event `e`. -/
def okEv : WEv → Bool
  | .ret f _ (some [v]) => decide (f = run3) && resultOk v
  | _ => false

theorem runOk_concat (t : List WEv) (e : WEv) : runOk (t ++ [e]) = (runOk t || okEv e) := by
  simp only [runOk, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  rfl

/-- `e` is a call of `run`. -/
def callEv : WEv → Bool
  | .call f _ => decide (f = run3)
  | _ => false

theorem runCalls_concat (t : List WEv) (e : WEv) :
    runCalls (t ++ [e]) = runCalls t + if callEv e then 1 else 0 := by
  simp only [runCalls, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
  rfl

/-- The readable ends of stdin after `t`. -/
def rsOf (rs : List Nat) (t : List WEv) : List Nat := t.foldl (fun rs e => (inStep rs e).1) rs

theorem stdinScanX_append (rs : List Nat) (t u : List WEv) :
    stdinScanX rs (t ++ u) = stdinScanX rs t ++ stdinScanX (rsOf rs t) u := by
  induction t generalizing rs with
  | nil => rfl
  | cons e t ih =>
    simp only [List.cons_append, stdinScanX, ih, List.append_assoc, rsOf, List.foldl_cons]

theorem stdinBytesX_concat (t : List WEv) (e : WEv) :
    stdinBytesX (t ++ [e]) = stdinBytesX t ++ (inStep (rsOf [] t) e).2 := by
  simp only [stdinBytesX, stdinScanX_append, stdinScanX, List.append_nil]

/-- The last `get-arguments` answer, decoded. -/
def argsStep (a : Option (List (List (BitVec 8)))) : WEv → Option (List (List (BitVec 8)))
  | .imp f _ r => if f = getArgs3 then argsOf r else a
  | _ => a

/-- The last `get-arguments` answer along `t`. -/
def argsSeen (t : List WEv) : Option (List (List (BitVec 8))) := t.foldl argsStep none

/-! ## Observation states -/

/-- What the guarantee and the invariant read of a trace. -/
structure Obs where
  os : OsSt
  out : List (BitVec 8)
  ok : Bool
  wp : Option (List Nat × List Nat)
  rs : List Nat
  inp : List (BitVec 8)
  args : Option (List (List (BitVec 8)))

/-- The observations of a trace. -/
def obsOf (t : List WEv) : Obs :=
  ⟨osSt t, stdoutBytes t, runOk t, waitTh3x.run ([], []) t, rsOf [] t, stdinBytesX t, argsSeen t⟩

/-- One more event. -/
def obsStep (o : Obs) (e : WEv) : Obs :=
  ⟨(osStep3 0 o.os e).1, o.out ++ wbytes (osStep3 0 o.os e).2, o.ok || okEv e,
    o.wp.bind fun q => waitStepX q e, (inStep o.rs e).1, o.inp ++ (inStep o.rs e).2,
    argsStep o.args e⟩

theorem obsOf_concat (t : List WEv) (e : WEv) : obsOf (t ++ [e]) = obsStep (obsOf t) e := by
  simp only [obsOf, obsStep, stdoutBytes_concat, runOk_concat, Protocol.run_concat,
    stdinBytesX_concat]
  congr 1
  · simp only [osSt, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [rsOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [argsSeen, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem obsOf_nil : obsOf [] = ⟨{}, [], false, some ([], []), [], [], none⟩ := rfl

/-! ## The theories see the host's view -/

theorem waitStepX_of_not_imp {q : List Nat × List Nat} {e : WEv} (h : e.isImp = false) :
    waitStepX q e = some q := by
  cases e <;> first | rfl | exact absurd h (by simp [WEv.isImp])

theorem waitTh3x_run_hostView (q : List Nat × List Nat) (t : List WEv) :
    waitTh3x.run q (hostView t) = waitTh3x.run q t := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    cases hi : e.isImp
    · have hv : hostView (e :: t) = hostView t := by simp [hostView, hi]
      have hs : waitTh3x.step q e = some q := waitStepX_of_not_imp hi
      rw [hv, ih, Protocol.run_cons, hs]
      rfl
    · have hv : hostView (e :: t) = e :: hostView t := by simp [hostView, hi]
      rw [hv, Protocol.run_cons, Protocol.run_cons]
      cases waitTh3x.step q e with
      | none => rfl
      | some q' => exact ih q'

/-! ## Events that the observations ignore -/

/-- A function whose answers no observation reads. -/
def Quiet (f : FnName) : Prop :=
  f ≠ cStreamNew ∧ f ≠ stdoutWrite3 ∧ f ≠ cStreamWrite ∧ f ≠ cWait ∧ f ≠ cStreamRead ∧
    f ≠ stdinRead3 ∧ f ≠ getArgs3

theorem os_quiet {f : FnName} (h1 : f ≠ cStreamNew) (h2 : f ≠ stdoutWrite3) (h3 : f ≠ cStreamWrite)
    (h4 : f ≠ cWait) (q : OsSt) (a : List Val) (r : Option (List Val)) :
    osStep3 0 q (.imp f a r) = (q, []) := by
  unfold osStep3
  simp only [h1, h2, h3, h4, ite_false]

theorem waitStepX_quiet {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cStreamRead) (h3 : f ≠ cWait)
    (q : List Nat × List Nat) (a : List Val) (r : Option (List Val)) :
    waitStepX q (.imp f a r) = some q := by
  simp only [waitStepX, h1, h2, h3, ite_false]

theorem inStep_quiet {f : FnName} (h1 : f ≠ stdinRead3) (h2 : f ≠ cStreamRead) (h3 : f ≠ cWait)
    (rs : List Nat) (a : List Val) (r : Option (List Val)) :
    inStep rs (.imp f a r) = (rs, []) := by
  unfold inStep
  simp only [h1, h2, h3, ite_false]

theorem argsStep_other {f : FnName} (h : f ≠ getArgs3) (x : Option (List (List (BitVec 8))))
    (a : List Val) (r : Option (List Val)) : argsStep x (.imp f a r) = x := by
  simp only [argsStep, h, ite_false]

theorem obsStep_quiet {f : FnName} (hf : Quiet f) (o : Obs) (a : List Val)
    (r : Option (List Val)) : obsStep o (.imp f a r) = o := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  simp only [obsStep, os_quiet h1 h2 h3 h4, waitStepX_quiet h3 h5 h4, inStep_quiet h6 h5 h4,
    argsStep_other h7, wbytes, List.filterMap_nil, List.append_nil, okEv, Bool.or_false]
  cases wp <;> rfl

theorem obsStep_req (o : Obs) (f : FnName) (a : List Val) : obsStep o (.req f a) = o := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  have hos : osStep3 0 os (.req f a) = (os, []) := rfl
  have hin : inStep rs (.req f a) = (rs, []) := by unfold inStep; rfl
  have har : argsStep args (.req f a) = args := rfl
  have hw : ∀ q, waitStepX q (.req f a) = some q := fun _ => rfl
  simp only [obsStep, hos, hin, har, hw, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false]
  cases wp <;> rfl

theorem obsStep_call (o : Obs) (f : FnName) (a : List Val) : obsStep o (.call f a) = o := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  have hos : osStep3 0 os (.call f a) = (os, []) := rfl
  have hin : inStep rs (.call f a) = (rs, []) := by unfold inStep; rfl
  have har : argsStep args (.call f a) = args := rfl
  have hw : ∀ q, waitStepX q (.call f a) = some q := fun _ => rfl
  simp only [obsStep, hos, hin, har, hw, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false]
  cases wp <;> rfl

theorem obsStep_ret (o : Obs) (f : FnName) (a : List Val) (r : Option (List Val)) :
    obsStep o (.ret f a r) = { o with ok := o.ok || okEv (.ret f a r) } := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  have hos : osStep3 0 os (.ret f a r) = (os, []) := rfl
  have hin : inStep rs (.ret f a r) = (rs, []) := by unfold inStep; rfl
  have har : argsStep args (.ret f a r) = args := rfl
  have hw : ∀ q, waitStepX q (.ret f a r) = some q := fun _ => rfl
  simp only [obsStep, hos, hin, har, hw, wbytes, List.filterMap_nil, List.append_nil]
  cases wp <;> rfl

theorem quiet_wsNew : Quiet cWsNew := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_join : Quiet cJoin := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_dropW : Quiet cStreamDropW := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_fread : Quiet cFutureRead := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
