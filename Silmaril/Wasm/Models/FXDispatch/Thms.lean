module

public import Silmaril.Proofs.Wasm.Models.FXDispatch.Run

/-!
# The `br_table` dispatch prologue in Core 3.0: results

The header of `Defs`. For every profile, host, store and frame of Core 3.0 `Step`:

* **`dispatch_joins`**: if global `g` holds the resume index `i` (an `i32`) and the function body
  is cut into segments `segs` at its resume points, with `i < segs.length`, then the prologue
  `prologue g segs` and the code `resumeAt segs i` (the function written to start at resume point
  `i`) both run to the same configuration: segment `i` running inside the labels of the blocks
  after it. The prologue takes `segs.length` block entries, a `global.get`, a `br_table` and
  `i + 1` branch steps.

* **`check_modes`**: the call-site check `global.get m; if … end` on the mode register `m`
  is a no-op when `m` holds `0` and enters the save code otherwise (four and three steps).

This is the Core 3.0 counterpart of `FXAsyncPC.disp`, the dispatch of a rewound record on its
resume index, and of the register `mode` that `fstep`'s checks read. What it does **not** give: the operands and locals of the saved frame (restored
in asyncify by loads before the prologue), the save code at the checks, the record heap and the
unwinding checks; and no compilation of `fstep` programs to Core modules is defined. See
"Stretch, fxcps2" in `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXDispatch

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The dispatch prologue and the code from resume point `i` meet.** -/
theorem dispatch_joins (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    {g : GlobalIdx} {a : Nat} {gi : GlobalInst} {i : BitVec 32}
    (hg : s.global? f g = some (a, gi)) (hv : gi.value = Val.i32 i) (segs : List (List Instr))
    (hi : i.toNat < segs.length) :
    ∃ c : Config H, Steps P host ⟨s, f, expression (prologue g segs)⟩ c ∧
      Steps P host ⟨s, f, expression (resumeAt segs i.toNat)⟩ c := by
  obtain ⟨seg, hseg, hrun⟩ := Silmaril.Proofs.Wasm.Models.FXDispatch.prologue_run (P := P)
    (host := host) hg hv hi
  exact ⟨_, hrun, Silmaril.Proofs.Wasm.Models.FXDispatch.resumeAt_run hseg⟩

/-- **The call-site check on the mode register**: with `i32 0` in `m` (normal mode) it steps to
the code after it; with any other value it enters the save code. -/
theorem check_modes (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    {m : GlobalIdx} {a : Nat} {gi : GlobalInst} (hg : s.global? f m = some (a, gi))
    (save : List Instr) (rest : List Admin) :
    (gi.value = Val.i32 0 →
      Steps P host ⟨s, f, expression (check m save) ++ rest⟩ ⟨s, f, rest⟩) ∧
    (∀ c : BitVec 32, gi.value = Val.i32 c → c ≠ 0 →
      Steps P host ⟨s, f, expression (check m save) ++ rest⟩
        ⟨s, f, .label 0 [] (expression save) :: rest⟩) :=
  ⟨fun hv => Silmaril.Proofs.Wasm.Models.FXDispatch.CSteps.steps
      (Silmaril.Proofs.Wasm.Models.FXDispatch.check_normal hg hv save rest),
    fun _ hv hc => Silmaril.Proofs.Wasm.Models.FXDispatch.CSteps.steps
      (Silmaril.Proofs.Wasm.Models.FXDispatch.check_save hg hv hc save rest)⟩

/-- info: 'Silmaril.Wasm.Models.FXDispatch.dispatch_joins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dispatch_joins

end Silmaril.Wasm.Models.FXDispatch
