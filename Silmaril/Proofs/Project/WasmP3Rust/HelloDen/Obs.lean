module

public import Silmaril.Project.WasmP3Rust.HelloDen.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Observations of WASI 0.3 traces, event by event

The OS image (`osTrace3`), the stdout bytes, `runOk`, `runCalls` and the wait discipline, as
functions of the last event and of a state (`Obs`), so that invariants of `den` need no trace
induction.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
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

theorem waitStep_of_not_imp {q : List Nat} {e : WEv} (h : e.isImp = false) :
    waitStep q e = some q := by
  cases e <;> first | rfl | exact absurd h (by simp [WEv.isImp])

theorem waitTh3_run_hostView (q : List Nat) (t : List WEv) :
    waitTh3.run q (hostView t) = waitTh3.run q t := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    cases hi : e.isImp
    · have hv : hostView (e :: t) = hostView t := by simp [hostView, hi]
      have hs : waitTh3.step q e = some q := waitStep_of_not_imp hi
      rw [hv, ih, Protocol.run_cons, hs]
      rfl
    · have hv : hostView (e :: t) = e :: hostView t := by simp [hostView, hi]
      rw [hv, Protocol.run_cons, Protocol.run_cons]
      cases waitTh3.step q e with
      | none => rfl
      | some q' => exact ih q'

/-! ## Observation states -/

/-- What the guarantee and the invariant read of a trace. -/
structure Obs where
  os : OsSt
  out : List (BitVec 8)
  ok : Bool
  wp : Option (List Nat)

/-- The observations of a trace. -/
def obsOf (t : List WEv) : Obs := ⟨osSt t, stdoutBytes t, runOk t, waitTh3.run [] t⟩

/-- One more event. -/
def obsStep (o : Obs) (e : WEv) : Obs :=
  ⟨(osStep3 0 o.os e).1, o.out ++ wbytes (osStep3 0 o.os e).2, o.ok || okEv e,
    o.wp.bind fun q => waitStep q e⟩

theorem obsOf_concat (t : List WEv) (e : WEv) : obsOf (t ++ [e]) = obsStep (obsOf t) e := by
  simp only [obsOf, obsStep, stdoutBytes_concat, runOk_concat, Protocol.run_concat]
  congr 1
  simp only [osSt, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem obsOf_nil : obsOf [] = ⟨{}, [], false, some []⟩ := rfl

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
