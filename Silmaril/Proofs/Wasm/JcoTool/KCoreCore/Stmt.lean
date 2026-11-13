module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreCore.Expr

/-!
# KCore `local.set` and `global.set` on Core 3.0: proofs

`Holds s ls gs`: every Core local and global holds the `i32` of the fragment's (below `2 ^ 32`).
`lset_core`, `gset_core`: the Core run of `e; local.set i` (`e; global.set i`) ends with the
local (global) set to the expression's value, and `Holds` is kept for the fragment's state after
`exec`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (E Bin St M32 upd exec)
open Silmaril.Wasm.JcoTool.KCoreCore
open Silmaril.Wasm.FX.Asyncify.Tool (W gidx pexec stackA localsF GlobalsAre pure_core global_set_core)

/-- The Core locals and globals hold the fragment's. -/
structure Holds (s : St) (ls gs : List W) : Prop where
  l : ∀ i (h : i < ls.length), ls[i] = w (s.l i) ∧ s.l i < M32
  g : ∀ i (h : i < gs.length), gs[i] = w (s.g i) ∧ s.g i < M32

theorem upd_same (l : Nat → Nat) (i v : Nat) : upd l i v i = v := by simp [upd]

theorem upd_other (l : Nat → Nat) {i j : Nat} (v : Nat) (h : j ≠ i) : upd l i v j = l j := by
  simp [upd, h]

/-- Setting a local keeps `Holds`. -/
theorem Holds.setL {s : St} {ls gs : List W} (h : Holds s ls gs) (i v : Nat) (hv : v < M32) :
    Holds { s with l := upd s.l i v } (ls.set i (w v)) gs := by
  refine ⟨fun j hj => ?_, h.g⟩
  have hj' : j < ls.length := by simpa using hj
  show (ls.set i (w v))[j] = w (upd s.l i v j) ∧ upd s.l i v j < M32
  by_cases hji : j = i
  · subst hji
    rw [upd_same]
    exact ⟨by simp, hv⟩
  · rw [upd_other _ _ hji, List.getElem_set_ne (Ne.symm hji)]
    exact h.l j hj'

/-- Setting a global keeps `Holds`. -/
theorem Holds.setG {s : St} {ls gs : List W} (h : Holds s ls gs) (i v : Nat) (hv : v < M32) :
    Holds { s with g := upd s.g i v } ls (gs.set i (w v)) := by
  refine ⟨h.l, fun j hj => ?_⟩
  have hj' : j < gs.length := by simpa using hj
  show (gs.set i (w v))[j] = w (upd s.g i v j) ∧ upd s.g i v j < M32
  by_cases hji : j = i
  · subst hji
    rw [upd_same]
    exact ⟨by simp, hv⟩
  · rw [upd_other _ _ hji, List.getElem_set_ne (Ne.symm hji)]
    exact h.g j hj'

theorem lset_pexec {i : Nat} (hi : i < 2 ^ 32) {ls : List W} (hl : i < ls.length) (v : W)
    (ops : List W) : pexec (.localSet (lidx i)) ls (v :: ops) = some (ls.set i v, ops) := by
  have hv : (lidx i).value.val = i := Nat.mod_eq_of_lt hi
  simp [pexec, hv, hl]

variable {H : Type}

theorem code_snoc (ops : List W) (code : List Instr) (j : Instr) (rest : List Admin) :
    stackA ops ++ ((code ++ [j]).map Admin.plain ++ rest) =
      stackA ops ++ (code.map Admin.plain ++ (Admin.plain j :: rest)) := by
  simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]

/-- **`e; local.set i` on Core 3.0**: the local holds the value `exec` assigns. -/
theorem lset_core (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs)
    {i : Nat} {e : E} {code : List Instr} (hc : e.code? = some code) (he : e.Fits s ls gs)
    (hi : i < 2 ^ 32) (hl : i < ls.length) (ops : List W) (rest : List Admin) :
    Steps Pf host ⟨cs, localsF f ls, stackA ops ++ ((code ++ [Instr.localSet (lidx i)]).map Admin.plain ++ rest)⟩
      ⟨cs, localsF f (ls.set i (w (e.eval s))), stackA ops ++ rest⟩ := by
  rw [code_snoc]
  exact (code_runs Pf host cs f hg e hc he ops _).trans
    (pure_core Pf host cs f (lset_pexec hi hl _ ops) rest)

/-- **`e; global.set i` on Core 3.0**: the global holds the value `exec` assigns, in the store
after the run. -/
theorem gset_core (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs)
    {i : Nat} {e : E} {code : List Instr} (hc : e.code? = some code) (he : e.Fits s ls gs)
    (hi : i < 2 ^ 32) (hl : i < gs.length) (ops : List W) (rest : List Admin) :
    ∃ cs', GlobalsAre cs' f (gs.set i (w (e.eval s))) ∧
      Steps Pf host ⟨cs, localsF f ls, stackA ops ++ ((code ++ [Instr.globalSet (gidx i)]).map Admin.plain ++ rest)⟩
        ⟨cs', localsF f ls, stackA ops ++ rest⟩ := by
  have hv : (gidx i).value.val = i := gidx_val hi
  obtain ⟨a, gi, -, hg', hrun⟩ := global_set_core Pf host cs f rest (ls := ls) (ops := ops) hg (gidx i)
    (w (e.eval s)) (by rw [hv]; exact hl)
  rw [hv] at hg'
  refine ⟨_, hg', ?_⟩
  rw [code_snoc]
  exact (code_runs Pf host cs f hg e hc he ops _).trans hrun

end Silmaril.Proofs.Wasm.JcoTool.KCoreCore
