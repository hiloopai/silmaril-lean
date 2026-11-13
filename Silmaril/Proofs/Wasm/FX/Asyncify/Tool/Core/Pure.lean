module

public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Defs

/-!
# The pure instructions of the frame machine as Core 3.0 steps

`pexec_core`: when the machine's `pexec` runs a pure instruction on locals `ls` and operands
`ops`, Core 3.0 runs the same instruction from the frame with locals `ls` and the operands as
value instructions, to the frame with the new locals and the new operands, under any code after
it. `pexec_div_trap`: an `i32` division the machine traps on traps in Core.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool

variable {H : Type} {Pf : Profile} {host : HostSemantics H}

/-- A step lifts under the values below and the code after. -/
theorem step_ctx {s s' : Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame} {X Y : List Admin}
    (vs : List Val) (rest : List Admin) (h : Step Pf host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Step Pf host ⟨s, f, vals vs ++ X ++ rest⟩ ⟨s', f', vals vs ++ Y ++ rest⟩ := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv
    simpa only [vals, List.map_nil, List.nil_append, List.append_nil] using h
  · have hne : vs ≠ [] ∨ rest ≠ [] := by
      by_cases h1 : vs = []
      · exact .inr fun h2 => hv ⟨h1, h2⟩
      · exact .inl h1
    exact .ctxtInstrs h hne

theorem stackA_cons (v : W) (ops : List W) :
    stackA (v :: ops) = vals (ops.reverse.map Val.i32) ++ [(Val.i32 v).toAdmin] := by
  simp only [stackA, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    vals, List.map_cons, List.map_nil]

theorem stackA_cons2 (y x : W) (ops : List W) :
    stackA (y :: x :: ops) =
      vals (ops.reverse.map Val.i32) ++ [(Val.i32 x).toAdmin, (Val.i32 y).toAdmin] := by
  simp only [stackA, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    vals, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

theorem i32_toAdmin (v : W) : (Val.i32 v).toAdmin = .plain (.intConst .i32 v) := rfl

theorem local_get (f : Silmaril.Wasm.Execution.Core.Frame) {ls : List W} {i : LocalIdx} {v : W}
    (h : ls[i.value.val]? = some v) : (localsF f ls).local? i = some (some (Val.i32 v)) := by
  show (ls.map fun w => some (Val.i32 w))[i.value.val]? = _
  rw [List.getElem?_map, h]
  rfl

theorem local_set (f : Silmaril.Wasm.Execution.Core.Frame) (ls : List W) (i : LocalIdx) (v : W) :
    (localsF f ls).setLocal i (Val.i32 v) = localsF f (ls.set i.value.val v) := by
  show { f with locals := (ls.map fun w => some (Val.i32 w)).set i.value.val (some (Val.i32 v)) } =
    { f with locals := (ls.set i.value.val v).map fun w => some (Val.i32 w) }
  rw [List.map_set]

/-- One Core step from the stack `ops` before `i`, as a run. -/
theorem one {s : Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame} {X Y : List Admin}
    (h : Step Pf host ⟨s, f, X⟩ ⟨s, f', Y⟩) : Execution.Core.Steps Pf host ⟨s, f, X⟩ ⟨s, f', Y⟩ :=
  Relation.ReflTransGen.single h

/-! ## The instructions -/

section Ins

variable (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)

/-- The Core run of a pure instruction. -/
abbrev Runs (i : Instr) (ls ops ls' ops' : List W) : Prop :=
  Execution.Core.Steps Pf host ⟨s, localsF f ls, stackA ops ++ .plain i :: rest⟩
    ⟨s, localsF f ls', stackA ops' ++ rest⟩

theorem run_nop {ls ops ls' ops' : List W} (h : some (ls, ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest .nop ls ops ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hs := step_ctx (Pf := Pf) (host := host) (s := s) (f := localsF f ls) (ops.reverse.map Val.i32)
    rest (.parametric .nop)
  unfold Runs
  exact one (by simpa [stackA, vals, i32_toAdmin, constI32] using hs)

theorem run_drop {ls ops ls' ops' : List W} (v : W) (h : some (ls, ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest .drop ls (v :: ops) ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hs := step_ctx (Pf := Pf) (host := host) (s := s) (f := localsF f ls) (ops.reverse.map Val.i32)
    rest (.parametric (.drop (Val.i32 v)))
  unfold Runs
  rw [stackA_cons]
  exact one (by simpa [stackA, vals, i32_toAdmin, constI32] using hs)

theorem run_const {ls ops ls' ops' : List W} (b : W) (h : some (ls, b :: ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.intConst .i32 b) ls ops ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  unfold Runs
  rw [stackA_cons, List.append_assoc]
  exact Relation.ReflTransGen.refl

theorem run_get {ls ops ls' ops' : List W} (i : LocalIdx)
    (h : (ls[i.value.val]?).map (fun v => (ls, v :: ops)) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.localGet i) ls ops ls' ops' := by
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, rfl⟩ : ls = ls' ∧ v :: ops = ops' := by simpa using he
  have hs := step_ctx (Pf := Pf) (host := host) (s := s) (ops.reverse.map Val.i32) rest
    (.variable (.localGet (local_get f hv)))
  unfold Runs
  rw [stackA_cons]
  exact one (by simpa [stackA, vals, i32_toAdmin, constI32] using hs)

theorem run_set {ls ops ls' ops' : List W} (i : LocalIdx) (v : W)
    (h : (if i.value.val < ls.length then some (ls.set i.value.val v, ops) else none) =
      some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.localSet i) ls (v :: ops) ls' ops' := by
  have hi : i.value.val < ls.length := by
    by_contra hn
    simp [hn] at h
  obtain ⟨rfl, rfl⟩ : ls.set i.value.val v = ls' ∧ ops = ops' := by simpa [hi] using h
  have hx : i.toNat < (localsF f ls).locals.length := by simpa [localsF, Idx.toNat] using hi
  have hs := step_ctx (Pf := Pf) (host := host) (s := s) (ops.reverse.map Val.i32) rest
    (.variable (.localSet (v := Val.i32 v) hx))
  rw [local_set] at hs
  unfold Runs
  rw [stackA_cons]
  exact one (by simpa [stackA, vals, i32_toAdmin, constI32] using hs)

theorem run_tee {ls ops ls' ops' : List W} (i : LocalIdx) (v : W)
    (h : (if i.value.val < ls.length then some (ls.set i.value.val v, v :: ops) else none) =
      some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.localTee i) ls (v :: ops) ls' ops' := by
  have hi : i.value.val < ls.length := by
    by_contra hn
    simp [hn] at h
  obtain ⟨rfl, rfl⟩ : ls.set i.value.val v = ls' ∧ v :: ops = ops' := by simpa [hi] using h
  have h1 := step_ctx (Pf := Pf) (host := host) (s := s) (f := localsF f ls)
    (ops.reverse.map Val.i32) rest (.variable (.localTee (x := i) (v := Val.i32 v)))
  have h2 : Execution.Core.Steps Pf host
      ⟨s, localsF f ls, stackA (v :: v :: ops) ++ .plain (.localSet i) :: rest⟩
      ⟨s, localsF f (ls.set i.value.val v), stackA (v :: ops) ++ rest⟩ :=
    run_set s f rest i v (by simp [hi])
  have h1' : Step Pf host ⟨s, localsF f ls, stackA (v :: ops) ++ .plain (.localTee i) :: rest⟩
      ⟨s, localsF f ls, stackA (v :: v :: ops) ++ .plain (.localSet i) :: rest⟩ := by
    rw [stackA_cons2, stackA_cons]
    simpa using h1
  exact Relation.ReflTransGen.head h1' h2

theorem run_res1 {ls ops : List W} {i : Instr} (x r : W)
    (hs : Step Pf host
      ⟨s, localsF f ls, vals (ops.reverse.map Val.i32) ++ [(Val.i32 x).toAdmin, .plain i] ++ rest⟩
      ⟨s, localsF f ls, vals (ops.reverse.map Val.i32) ++ [(Val.i32 r).toAdmin] ++ rest⟩) :
    Runs (Pf := Pf) (host := host) s f rest i ls (x :: ops) ls (r :: ops) := by
  unfold Runs
  rw [stackA_cons, stackA_cons]
  exact one (by simpa using hs)

theorem run_res2 {ls ops : List W} {i : Instr} (y x r : W)
    (hs : Step Pf host
      ⟨s, localsF f ls, vals (ops.reverse.map Val.i32) ++
        [(Val.i32 x).toAdmin, (Val.i32 y).toAdmin, .plain i] ++ rest⟩
      ⟨s, localsF f ls, vals (ops.reverse.map Val.i32) ++ [(Val.i32 r).toAdmin] ++ rest⟩) :
    Runs (Pf := Pf) (host := host) s f rest i ls (y :: x :: ops) ls (r :: ops) := by
  unfold Runs
  rw [stackA_cons2, stackA_cons]
  exact one (by simpa using hs)

theorem run_un {ls ops ls' ops' : List W} (op : IntUnOp) (x : W)
    (h : some (ls, Numerics.intUnOp .i32 op x :: ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.intUnOp .i32 op) ls (x :: ops) ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact run_res1 s f rest x _ (step_ctx _ rest (.numeric (.intUnOp (t := .i32) (op := op) (x := x))))

theorem run_test {ls ops ls' ops' : List W} (op : IntTestOp) (x : W)
    (h : some (ls, Numerics.intTestOp .i32 op x :: ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.intTestOp .i32 op) ls (x :: ops) ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact run_res1 s f rest x _
    (step_ctx _ rest (.numeric (.intTestOp (t := .i32) (op := op) (x := x))))

theorem run_rel {ls ops ls' ops' : List W} (op : IntRelOp) (y x : W)
    (h : some (ls, Numerics.intRelOp .i32 op x y :: ops) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.intRelOp .i32 op) ls (y :: x :: ops) ls' ops' := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact run_res2 s f rest y x _
    (step_ctx _ rest (.numeric (.intRelOp (t := .i32) (op := op) (x := x) (y := y))))

theorem run_bin {ls ops ls' ops' : List W} (op : IntBinOp) (y x : W)
    (h : (match Numerics.intBinOp .i32 op x y with
      | .ok r => some (ls, r :: ops)
      | .error _ => none) = some (ls', ops')) :
    Runs (Pf := Pf) (host := host) s f rest (.intBinOp .i32 op) ls (y :: x :: ops) ls' ops' := by
  cases hb : Numerics.intBinOp .i32 op x y with
  | error e => rw [hb] at h; cases h
  | ok z =>
    rw [hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact run_res2 s f rest y x z (step_ctx _ rest (.numeric (.intBinOp (t := .i32) (op := op) hb)))

end Ins

/-- **A pure instruction of the machine is a Core 3.0 run.** -/
theorem pexec_core (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) {i : Instr}
    {ls ops ls' ops' : List W} (h : pexec i ls ops = some (ls', ops')) (rest : List Admin) :
    Runs (Pf := Pf) (host := host) s f rest i ls ops ls' ops' := by
  unfold pexec at h
  split at h
  · exact run_nop s f rest h
  · exact run_drop s f rest _ h
  · exact run_get s f rest _ h
  · exact run_set s f rest _ _ h
  · exact run_tee s f rest _ _ h
  · exact run_const s f rest _ h
  · exact run_un s f rest _ _ h
  · exact run_bin s f rest _ _ _ h
  · exact run_test s f rest _ _ h
  · exact run_rel s f rest _ _ _ h
  · cases h

/-- **A division the machine traps on traps in Core 3.0.** -/
theorem pexec_div_trap (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (ls ops : List W)
    (op : IntBinOp) (y x : W) {e : Numerics.IntTrap} (hb : Numerics.intBinOp .i32 op x y = .error e)
    (rest : List Admin) :
    Step Pf host ⟨s, localsF f ls, stackA (y :: x :: ops) ++ .plain (.intBinOp .i32 op) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ := by
  have hs := step_ctx (Pf := Pf) (host := host) (s := s) (f := localsF f ls)
    (ops.reverse.map Val.i32) rest (.numeric (.intBinOpTrap (t := .i32) (op := op) hb))
  rw [stackA_cons2]
  simpa [stackA, vals, i32_toAdmin, constI32] using hs

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core
