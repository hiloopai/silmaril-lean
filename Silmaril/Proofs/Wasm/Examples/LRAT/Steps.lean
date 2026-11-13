module

public import Silmaril.Proofs.Wasm.Examples.LRAT.AddLit

@[expose] public section

/-!
# `step_begin`, `step_lit`, `step_end`, `delete` and `unsat`, every run

From a store whose view satisfies `Good xs`, every run of each of these bodies falls through in
a store whose view satisfies `Good xs` (they do not extend the DIMACS stream); `unsat` returns
the `unsat` flag, which is nonzero only if the formula of `xs` is unsatisfiable. Every profile
and host relation; symbolic execution along every path, with the invariant steps of
`Silmaril.Proofs.Wasm.Examples.LRAT.GoodInput`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Logic.SAT

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}
variable {s : Store H} {xs : List Int} {m t c S cf sid u n : BitVec 32} {B : ByteArray}

set_option maxHeartbeats 4000000 in
theorem stepBegin_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (id : BitVec 32) :
    HWP P host s (fr X.mi [id, 0]) (vals ([] : List Val).reverse ++ expression stepBeginBody ++ [])
      (stepPost X [m, t, c, S, cf, sid, u, n] B []) := by
  simp only [stepBeginBody, expression, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.append_nil]
  by_cases hm : m = 2#32
  · subst hm
    wrun
    exact w_end (stepPost_same hS)
  · by_cases hid : id.toNat < 1024
    · by_cases hSt : S.toNat < 536870912
      · wrun [hm, hid, hSt]
        exact w_end (stepPost_of (by assumption) fun _ hG => by rw [List.append_nil]; exact hG.begin hm hid hSt)
      · have hSt' := eq_false hSt
        wrun [hm, hid, hSt']
        exact w_end (stepPost_same hS)
    · have hid' := eq_false hid
      wrun [hm, hid']
      exact w_end (stepPost_same hS)

/-- The code of `step_lit(x)` from the view `G`, `B`. -/
abbrev StepLitHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (G : List (BitVec 32)) (B : ByteArray) (x : BitVec 32) : Prop :=
  HWP P host s (fr X.mi [x, 0, 0]) (vals ([] : List Val).reverse ++ expression stepLitBody ++ [])
    (stepPost X G B [])

/-- Unfold the body of `step_lit`. -/
macro "stepLit_unfold" : tactic => `(tactic| simp only [StepLitHwp, stepLitBody, validLitCode,
  assignCode, valAddrCode, negAddrCode, stamp2Code, expression, List.cons_append, List.nil_append,
  List.map_cons, List.map_nil, List.append_nil])

/-- Leaving a step keeps the invariant (for `stepPost` with no stream change). -/
theorem stepPost_abort {s : Store H} {f : Frame} {t c S cf sid u n : BitVec 32} {B : ByteArray}
    (hS : Shape X s [1#32, c, c, S, cf, sid, u, n] B) :
    stepPost X [2#32, t, c, S, cf, sid, u, n] B [] s f (.normal ([] : List Val).reverse) :=
  stepPost_of hS fun _ hG => by rw [List.append_nil]; exact hG.abort

set_option maxHeartbeats 1000000 in
/-- `step_lit` outside a step: nothing changes. -/
theorem stepLit_idle (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hm : ¬ m = 2#32) (x : BitVec 32) : StepLitHwp P host X s [m, t, c, S, cf, sid, u, n] B x := by
  stepLit_unfold
  wrun [hm]
  exact w_end (stepPost_same hS)

set_option maxHeartbeats 1000000 in
/-- `step_lit(0)` aborts the step. -/
theorem stepLit_zero (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B) :
    StepLitHwp P host X s [2#32, t, c, S, cf, sid, u, n] B 0#32 := by
  stepLit_unfold
  wrun
  exact w_end (stepPost_abort (by assumption))

set_option maxHeartbeats 1000000 in
/-- `step_lit(x)`, `x` out of range, aborts the step. -/
theorem stepLit_range (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {x : BitVec 32} (hx : ¬ x = 0#32) (hv : ¬ (x + 1023#32).toNat < 2047) :
    StepLitHwp P host X s [2#32, t, c, S, cf, sid, u, n] B x := by
  stepLit_unfold
  have hv' := eq_false hv
  wrun [hx, hv']
  exact w_end (stepPost_abort (by assumption))

set_option maxHeartbeats 1000000 in
/-- `step_lit(x)` with a full arena aborts the step. -/
theorem stepLit_full (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {x : BitVec 32} (hx : ¬ x = 0#32) (hv : (x + 1023#32).toNat < 2047) (ht : ¬ t.toNat < 65536) :
    StepLitHwp P host X s [2#32, t, c, S, cf, sid, u, n] B x := by
  stepLit_unfold
  have ht' := eq_false ht
  wrun [hx, hv, ht']
  exact w_end (stepPost_abort (by assumption))

set_option maxHeartbeats 1000000 in
/-- `step_lit(x)`: `x` joins the step's clause, assigned false. -/
theorem stepLit_add (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {x : BitVec 32} (hx : ¬ x = 0#32) (hv : (x + 1023#32).toNat < 2047) (ht : t.toNat < 65536)
    (ht4 : 4 ∣ t.toNat) : StepLitHwp P host X s [2#32, t, c, S, cf, sid, u, n] B x := by
  stepLit_unfold
  have hav : ValidLit x := ⟨hx, hv⟩
  wrun [hx, hv, ht]
  have e1 : (BitVec.ofNat 32 valBase + x * 4#32).toNat = litAddr x := rfl
  have e2 : (BitVec.ofNat 32 valBase - x * 4#32).toNat = negAddr x := rfl
  have e3 : S * 2#32 + 0#32 = S * 2#32 := BitVec.add_zero _
  have e4 : BitVec.ofNat 32 (1 - 0) = 1#32 := rfl
  simp only [e1, e2, e3, e4] at *
  exact w_end (stepPost_of (by assumption) fun _ hG => by
    rw [List.append_nil]; exact hG.stepLit hav ht)

/-- **`step_lit(x)`, every run.** -/
theorem stepLit_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (x : BitVec 32) :
    StepLitHwp P host X s [m, t, c, S, cf, sid, u, n] B x := by
  by_cases hm : m = 2#32
  · subst hm
    by_cases hx : x = 0#32
    · subst hx; exact stepLit_zero hX hS
    · by_cases hv : (x + 1023#32).toNat < 2047
      · by_cases ht : t.toNat < 65536
        · exact stepLit_add hX hS hx hv ht hG.top_dvd
        · exact stepLit_full hX hS hx hv ht
      · exact stepLit_range hX hS hx hv
  · exact stepLit_idle hX hS hm x

/-- The code of `step_end` from the view `G`, `B`. -/
abbrev StepEndHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (G : List (BitVec 32)) (B : ByteArray) : Prop :=
  HWP P host s (fr X.mi [0, 0, 0]) (vals ([] : List Val).reverse ++ expression stepEndBody ++ [])
    (stepPost X G B [])

/-- Unfold the body of `step_end`. -/
macro "stepEnd_unfold" : tactic => `(tactic| simp only [StepEndHwp, stepEndBody, expression,
  List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil])

set_option maxHeartbeats 1000000 in
/-- `step_end` outside a step: nothing changes. -/
theorem stepEnd_idle (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hm : ¬ m = 2#32) : StepEndHwp P host X s [m, t, c, S, cf, sid, u, n] B := by
  stepEnd_unfold
  wrun [hm]
  exact w_end (stepPost_same hS)

set_option maxHeartbeats 1000000 in
/-- `step_end` without a conflict: the clause is dropped. -/
theorem stepEnd_noConfl (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, 0#32, sid, u, n] B) :
    StepEndHwp P host X s [2#32, t, c, S, 0#32, sid, u, n] B := by
  stepEnd_unfold
  wrun
  exact w_end (stepPost_abort (by assumption))

set_option maxHeartbeats 1000000 in
/-- `step_end` inside a RAT group: the clause is dropped. -/
theorem stepEnd_cand (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hc : ¬ wd B 20480 = 0#32) : StepEndHwp P host X s [2#32, t, c, S, cf, sid, u, n] B := by
  stepEnd_unfold
  wrun [hc]
  exact w_end (stepPost_abort (by assumption))

set_option maxHeartbeats 1000000 in
/-- `step_end` after a conflict, empty clause: `unsat` is set. -/
theorem stepEnd_empty (hX : MiOk X) (hS : Shape X s [2#32, t, t, S, cf, sid, u, n] B)
    (hcf : ¬ cf = 0#32) (hc : wd B 20480 = 0#32) :
    StepEndHwp P host X s [2#32, t, t, S, cf, sid, u, n] B := by
  stepEnd_unfold
  wrun [hcf, hc]
  have hc0 : candOf B = 0 := by unfold candOf; rw [show candAddr = 20480 from rfl, hc]; rfl
  exact w_end (stepPost_of (by assumption) fun _ hG => by
    rw [List.append_nil]; exact hG.endConflEmpty hcf hc0)

set_option maxHeartbeats 1000000 in
/-- `step_end` after a conflict, nonempty clause: it is stored. -/
theorem stepEnd_commit (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hcf : ¬ cf = 0#32) (htc : ¬ t = c) (hsid : sid.toNat < 1024) (hc : wd B 20480 = 0#32) :
    StepEndHwp P host X s [2#32, t, c, S, cf, sid, u, n] B := by
  stepEnd_unfold
  wrun [hcf, htc, hc]
  have hc0 : candOf B = 0 := by unfold candOf; rw [show candAddr = 20480 from rfl, hc]; rfl
  have ha : (BitVec.ofNat 32 startBase + sid * 4#32).toNat = startBase + 4 * sid.toNat := by
    simp only [startBase]; bv_omega
  have hb : (BitVec.ofNat 32 lenBase + sid * 4#32).toNat = lenBase + 4 * sid.toNat := by
    simp only [lenBase]; bv_omega
  simp only [ha, hb] at *
  exact w_end (stepPost_of (by assumption) fun _ hG => by
    rw [List.append_nil]; exact hG.endCommit hcf hc0)

/-- **`step_end`, every run.** -/
theorem stepEnd_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) :
    StepEndHwp P host X s [m, t, c, S, cf, sid, u, n] B := by
  by_cases hm : m = 2#32
  · subst hm
    by_cases hcf : cf = 0#32
    · subst hcf; exact stepEnd_noConfl hX hS
    · by_cases hc : wd B 20480 = 0#32
      · by_cases htc : t = c
        · subst htc; exact stepEnd_empty hX hS hcf hc
        · exact stepEnd_commit hX hS hcf htc (hG.step rfl).id_lt hc
      · exact stepEnd_cand hX hS hc
  · exact stepEnd_idle hX hS hm

set_option maxHeartbeats 4000000 in
theorem delete_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B) (id : BitVec 32) :
    HWP P host s (fr X.mi [id]) (vals ([] : List Val).reverse ++ expression deleteBody ++ [])
      (stepPost X [m, t, c, S, cf, sid, u, n] B []) := by
  simp only [deleteBody, expression, List.map_cons, List.map_nil, List.append_nil]
  by_cases hm : m = 2#32
  · subst hm
    wrun
    exact w_end (stepPost_same hS)
  by_cases hid : id.toNat < 1024
  · wrun [hid, hm]
    have hb : (BitVec.ofNat 32 lenBase + id * 4#32).toNat = lenBase + 4 * id.toNat := by
      simp only [lenBase]; bv_omega
    simp only [hb] at *
    exact w_end (stepPost_of (by assumption) fun _ hG => by
      rw [List.append_nil]; exact hG.delete hm hid)
  · have hid' := eq_false hid
    wrun [hid', hm]
    exact w_end (stepPost_same hS)

/-- The postcondition of `unsat`: it returns the flag, which is nonzero only for an
unsatisfiable formula, and the store keeps the invariant. -/
def unsatPost (X : Fix H) (G : List (BitVec 32)) (B : ByteArray) : Post H := fun s' _ o =>
  ∃ v : BitVec 32, o = .normal [Val.i32 v] ∧ Shape X s' G B ∧
    ∀ xs, Good xs G B → v ≠ 0#32 → (Dimacs.cnf xs).Unsat

theorem unsat_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B) :
    HWP P host s (fr X.mi []) (vals ([] : List Val).reverse ++ expression unsatBody ++ [])
      (unsatPost X [m, t, c, S, cf, sid, u, n] B) := by
  simp only [unsatBody, expression, List.map_cons, List.map_nil, List.append_nil]
  wrun
  exact w_end ⟨u, rfl, hS, fun _ hG => hG.unsat⟩

end Silmaril.Wasm.Examples.LRAT
