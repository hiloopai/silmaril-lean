module

public import Silmaril.Wasm.JcoTool.KCoreCore.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KCoreCore.Expr
public import Silmaril.Proofs.Wasm.JcoTool.KCoreCore.Stmt

/-!
# KCore expressions on silmaril-lean's Core 3.0 `Step`

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KCoreCore.Expr`.

For every profile `Pf` and host semantics of silmaril-lean's Core 3.0 (`Execution.Core.Steps`),
a KCore expression `e` that fits the Core frame (`E.Fits s ls gs e`: its locals and globals are
held as `i32` in the frame's locals `ls` and the store's globals `gs`, values below `2 ^ 32`,
nonzero divisors):

* **`expr_core`**: `e` compiles (`E.code? e = some code`), and the Core run of `code` from any
  operand stack, under any code after it, pushes `i32 (E.eval s e)` (the value `exec` gives),
  leaving store, locals and globals unchanged;
* `expr_lt`: that value is below `2 ^ 32`;
* `bin_core`: each binary operator of the fragment on Core `i32`s is the fragment's `Bin.eval`;
* **`lset_sim`, `gset_sim`**: the statements `local.set i e` and `global.set i e` — `exec` gives
  the state `s'`, and the Core run of `e; local.set i` (`e; global.set i`) ends in a frame (and a
  store) whose locals and globals hold `s'`'s (`Holds`, kept).

This is the expression level of the link between the fragment's `exec` and Core 3.0 that
`Silmaril.Wasm.JcoTool.KCore.Thms` lists as not proved. **Not covered yet**: `i32.load8_u`,
the statements `i32.store8` and `memory.copy`, sequences of statements, control (`block`,
`loop`, `br`, `br_if`, `if`, `return`), the calls of the canonical built-ins as host functions,
and the callback runtime; so the generated modules are not yet proved against Core 3.0.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (E Bin St M32)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA localsF GlobalsAre pexec)

variable {H : Type}

/-- **A fragment expression is a Core 3.0 run** that pushes its value. -/
theorem expr_core (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs)
    (e : E) (he : e.Fits s ls gs) :
    ∃ code, e.code? = some code ∧ ∀ (ops : List W) (rest : List Admin),
      Steps Pf host ⟨cs, localsF f ls, stackA ops ++ (code.map Admin.plain ++ rest)⟩
        ⟨cs, localsF f ls, stackA (BitVec.ofNat 32 (e.eval s) :: ops) ++ rest⟩ := by
  obtain ⟨code, hc⟩ := Silmaril.Proofs.Wasm.JcoTool.KCoreCore.code_some he
  exact ⟨code, hc, Silmaril.Proofs.Wasm.JcoTool.KCoreCore.code_runs Pf host cs f hg e hc he⟩

theorem expr_lt {s : St} {ls gs : List W} {e : E} (he : e.Fits s ls gs) : e.eval s < M32 :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreCore.eval_lt he

/-- **The fragment's operators are Core's** on `i32`s (nonzero divisors). -/
theorem bin_core (o : Bin) {a b : Nat} (ha : a < M32) (hb : b < M32)
    (hd : (o = .divu ∨ o = .remu) → b ≠ 0) (ls ops : List W) :
    pexec o.core ls (BitVec.ofNat 32 b :: BitVec.ofNat 32 a :: ops) =
      some (ls, BitVec.ofNat 32 (o.eval a b) :: ops) :=
  Silmaril.Proofs.Wasm.JcoTool.KCoreCore.bin_pexec o ha hb hd ls ops

open Silmaril.Proofs.Wasm.JcoTool.KCoreCore (Holds)
open Silmaril.Wasm.FX.Asyncify.Tool (gidx)

/-- **`local.set i e`**: `exec`'s state, and the Core run ending in a frame that holds it. -/
theorem lset_sim (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs)
    (hH : Holds s ls gs) {i : Nat} {e : E} (he : e.Fits s ls gs) (hi : i < 2 ^ 32)
    (hl : i < ls.length) (fuel : Nat) :
    ∃ code s' ls', (Silmaril.Wasm.JcoTool.KCore.S.lset i e).code? = some code ∧
      Silmaril.Wasm.JcoTool.KCore.exec (.lset i e) fuel s = some (.norm, s') ∧ Holds s' ls' gs ∧
      ∀ (ops : List W) (rest : List Admin),
        Steps Pf host ⟨cs, localsF f ls, stackA ops ++ (code.map Admin.plain ++ rest)⟩
          ⟨cs, localsF f ls', stackA ops ++ rest⟩ := by
  obtain ⟨code, hc⟩ := Silmaril.Proofs.Wasm.JcoTool.KCoreCore.code_some he
  have hS : (Silmaril.Wasm.JcoTool.KCore.S.lset i e).code? = some (code ++ [Instr.localSet (lidx i)]) := by
    simp [Silmaril.Wasm.JcoTool.KCore.S.code?, hc]
  exact ⟨_, _, _, hS, rfl, hH.setL i _ (expr_lt he),
    Silmaril.Proofs.Wasm.JcoTool.KCoreCore.lset_core Pf host cs f hg hc he hi hl⟩

/-- **`global.set i e`**: `exec`'s state, and the Core run ending in a store that holds it. -/
theorem gset_sim (Pf : Profile) (host : HostSemantics H) (cs : Store H)
    (f : Silmaril.Wasm.Execution.Core.Frame) {s : St} {ls gs : List W} (hg : GlobalsAre cs f gs)
    (hH : Holds s ls gs) {i : Nat} {e : E} (he : e.Fits s ls gs) (hi : i < 2 ^ 32)
    (hl : i < gs.length) (fuel : Nat) (ops : List W) (rest : List Admin) :
    ∃ code s' gs' cs', (Silmaril.Wasm.JcoTool.KCore.S.gset i e).code? = some code ∧
      Silmaril.Wasm.JcoTool.KCore.exec (.gset i e) fuel s = some (.norm, s') ∧ Holds s' ls gs' ∧
      GlobalsAre cs' f gs' ∧
      Steps Pf host ⟨cs, localsF f ls, stackA ops ++ (code.map Admin.plain ++ rest)⟩
        ⟨cs', localsF f ls, stackA ops ++ rest⟩ := by
  obtain ⟨code, hc⟩ := Silmaril.Proofs.Wasm.JcoTool.KCoreCore.code_some he
  have hS : (Silmaril.Wasm.JcoTool.KCore.S.gset i e).code? = some (code ++ [Instr.globalSet (gidx i)]) := by
    simp [Silmaril.Wasm.JcoTool.KCore.S.code?, hc]
  obtain ⟨cs', hg', hrun⟩ := Silmaril.Proofs.Wasm.JcoTool.KCoreCore.gset_core Pf host cs f hg hc he hi hl
    ops rest
  exact ⟨_, _, _, cs', hS, rfl, hH.setG i _ (expr_lt he), hg', hrun⟩

end Silmaril.Wasm.JcoTool.KCoreCore
