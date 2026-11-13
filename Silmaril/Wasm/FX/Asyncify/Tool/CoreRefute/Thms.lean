module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreRefute.Basic

/-!
# `Task.machine_core` is false

The header of `Defs`; proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreRefute.Basic`.

**`not_machine_core`**: the frozen open target `Task.machine_core` does not hold. Take silmaril's
deterministic profile without host, the program `cxP` (one function returning its parameter; its
asyncified prologue restores the locals from the shadow stack when `state = 2`), `cap = 12`, the
store `cxS` (`state = 2`, `sp = 9`, twelve zero bytes) and the Core call of the function with
argument `3`. Both the zero word memory and `m7` (zero at the aligned words, `7` at address 1)
satisfy `MemAre` for the store, so `Task.machine_core` relates the **same** Core call to both
machine entries. The machine returns `[0]` on one and `[7]` on the other (it reads its word memory
at the unaligned `sp - 8 = 1`), so the `done` clause gives Core runs of one configuration to
`[0]` and to `[7]`, which determinism of Core `Step` (up to bubbling, `Det.DStep.join'`) rules out.

The restatement that holds is `machine_core_ginv` (`Silmaril.Wasm.FX.Asyncify.Tool.CoreSim`): the
same simulation for initial globals with `GInv` (two globals, `sp` a multiple of 4), which the host
protocol meets at every round.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreRefute

/-- One machine entry of `cxFd` that returns `[v]` gives a Core run of the call to `[v]`. -/
theorem cx_core {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} {R : Cfg → Config Unit → Prop}
    (hi : ∀ m : Nat → W, MemAre cxS ⟨[], cxMI⟩ m 12 →
      R ⟨[entry 0 cxFd [3]], [2, 9], m⟩
        ⟨cxS, ⟨[], cxMI⟩, vals ([3].map Val.i32) ++ [.plain (.call (fidx 0))]⟩)
    (hn : ∀ c C c', R c C → stepB 12 (asyncifyProg cxP) c = .next c' →
      ∃ C', Execution.Core.Steps (Numerics.Profile.deterministic o) SingleThreaded.Det.noHost
        C C' ∧ R c' C')
    (hd : ∀ c C vs c', R c C → stepB 12 (asyncifyProg cxP) c = .done vs c' →
      ∃ s', Execution.Core.Steps (Numerics.Profile.deterministic o) SingleThreaded.Det.noHost C
        ⟨s', C.frame, stackA vs⟩)
    (m : Nat → W) (v : W) (hm : ∀ a, a % 4 = 0 → m a = 0)
    (hr : runTo 12 (asyncifyProg cxP) 50 ⟨[entry 0 cxFd [3]], [2, 9], m⟩ = some [v]) :
    ∃ s' f', Execution.Core.Steps (Numerics.Profile.deterministic o) SingleThreaded.Det.noHost
      ⟨cxS, ⟨[], cxMI⟩, vals ([3].map Val.i32) ++ [.plain (.call (fidx 0))]⟩
      ⟨s', f', vals [Val.i32 v]⟩ := by
  obtain ⟨c', c'', hs, hdn⟩ := runTo_sound hr
  obtain ⟨C, hC, hR⟩ := bsteps_core hn hs (hi m (cx_mem m hm))
  obtain ⟨s', h1⟩ := hd _ _ _ _ hR hdn
  exact ⟨s', C.frame, hC.trans h1⟩

/-- **`Task.machine_core` is false**: with `sp` not a multiple of 4, the frame machine's word
memory is not determined by Core's bytes. -/
theorem not_machine_core : ¬ Task.machine_core := by
  intro h
  let o : Numerics.GrowKind → Nat → Nat → Nat → Bool := fun _ _ _ _ => false
  obtain ⟨R, hi, hn, hd, -⟩ := h (H := Unit) (Numerics.Profile.deterministic o)
    SingleThreaded.Det.noHost cxP cxP_wf 12 (by decide) (by decide) (by decide)
  have hi' : ∀ m : Nat → W, MemAre cxS ⟨[], cxMI⟩ m 12 →
      R ⟨[entry 0 cxFd [3]], [2, 9], m⟩
        ⟨cxS, ⟨[], cxMI⟩, vals ([3].map Val.i32) ++ [.plain (.call (fidx 0))]⟩ :=
    fun m hm => hi 0 cxFd [3] cxS cxMI [2, 9] m cx_holds (Nat.zero_le _) cxP_fn rfl cx_globals hm
  have hd' : ∀ c C vs c', R c C → stepB 12 (asyncifyProg cxP) c = .done vs c' →
      ∃ s', Execution.Core.Steps (Numerics.Profile.deterministic o) SingleThreaded.Det.noHost C
        ⟨s', C.frame, stackA vs⟩ := fun c C vs c' hR hs =>
    let ⟨s', h1, _⟩ := hd c C vs c' hR hs
    ⟨s', h1⟩
  obtain ⟨_, _, h₇⟩ := cx_core hi' hn hd' m7 7 m7_aligned cx_run7
  obtain ⟨_, _, h₀⟩ := cx_core hi' hn hd' (fun _ => 0) 0 (fun _ _ => rfl) cx_run0
  have heq : vals [Val.i32 7] = vals [Val.i32 0] := vals_unique h₇ h₀
  have hv : Val.i32 7 = Val.i32 0 := by simpa [vals] using heq
  cases hv

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.not_machine_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_machine_core

end Silmaril.Wasm.FX.Asyncify.Tool
