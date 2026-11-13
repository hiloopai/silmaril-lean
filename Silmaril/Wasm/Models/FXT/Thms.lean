module

public import Silmaril.Wasm.Models.FXT.Defs
public import Silmaril.Proofs.Wasm.Models.FXL.Refute

/-!
# `StepFXT`: conservativity and storing a continuation

* `lift_steps`, **`ret_of_stepsFX'`**: every `StepFX'` run (host `blockI host intr`) is a
  `StepFXT` run with the table unchanged, so each finished `StepFX'` behaviour is a `StepFXT`
  behaviour with the initial log;
* **`cset_cont`**: a call of the intrinsic `cset i` stores a continuation reference in cell `i`
  in one step, and **`cget_cont`** reads it back. In `StepFX'` the corresponding
  `ref.cont k; local.set i` is stuck: **`stepFX'_localSet_cont_stuck`** (no host calls; proof
  in `Silmaril.Proofs.Wasm.Models.FXL.Refute`). This is why the explainer's dynamic schedulers,
  which keep the next thread in the local `$nextk`, cannot be written in `StepFX'`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr}

/-- `StepFX'` runs are `StepFXT` runs. -/
theorem lift_steps {c d : ConfigFX H} {t : Tbl} (h : StepsFX' P (blockI host intr) fx c d) :
    StepsT P host fx intr ⟨c, t⟩ ⟨d, t⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.lift hs)

/-- **A finished `StepFX'` run is a `StepFXT` behaviour** with the log of the initial table. -/
theorem ret_of_stepsFX' {c d : ConfigFX H} {t : Tbl} {r : Result}
    (h : StepsFX' P (blockI host intr) fx c d) (hd : d.code = r.toAdmin.map .core) :
    ObsT.ret t.log r.toBehaviour ∈ behavioursT P host fx intr ⟨c, t⟩ :=
  Or.inl ⟨⟨d, t⟩, r, lift_steps h, hd, rfl⟩

/-- **Storing a continuation in a cell**: `ref.cont k; ref.func a; call_ref` where `a` is the
intrinsic `cset i`. -/
theorem cset_cont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k a i : Nat}
    {fi : FuncInst H} {h : H} {cc : Admin} {t : Tbl} (hc : cc.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hi : intr h = some (.cset i))
    (hlt : i < t.cells.length) :
    StepFXT P host fx intr
      ⟨⟨s, K, f, [.contRef k, .core (.ref (.func a)), .core cc]⟩, t⟩
      ⟨⟨s, K, f, []⟩, { t with cells := t.cells.set i (.cont k) }⟩ := by
  have hr : Intr.run (.cset i) [.cont k] t =
      some ([], { t with cells := t.cells.set i (.cont k) }) := by
    simp [Intr.run, hlt]
  exact StepFXT.intr (E := .hole) (args := [.cont k]) hc hf hcode hi hr

/-- **Reading a continuation from a cell** with the intrinsic `cget i`. -/
theorem cget_cont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k a i : Nat}
    {fi : FuncInst H} {h : H} {cc : Admin} {t : Tbl} (hc : cc.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hi : intr h = some (.cget i))
    (hk : t.cells[i]? = some (.cont k)) :
    StepFXT P host fx intr
      ⟨⟨s, K, f, [.core (.ref (.func a)), .core cc]⟩, t⟩ ⟨⟨s, K, f, [.contRef k]⟩, t⟩ := by
  have hr : Intr.run (.cget i) [] t = some ([.cont k], t) := by simp [Intr.run, hk]
  exact StepFXT.intr (E := .hole) (args := []) hc hf hcode hi hr

/-- **`StepFX'` cannot store a continuation in a local**: FX values ending in `ref.cont k`,
then `local.set i`, then any code, have no `StepFX'` step (no host calls). -/
theorem stepFX'_localSet_cont_stuck {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {V : List FVal} {k : Nat} {i : LocalIdx}
    {T : List AdminFX} {y : ConfigFX H} :
    ¬ StepFX' P Silmaril.Wasm.SingleThreaded.Det.noHost fx
      ⟨s, K, f, fvals (V ++ [.cont k]) ++ .core (.plain (.localSet i)) :: T⟩ y :=
  fun h => Silmaril.Proofs.Wasm.Models.FXL.localSet_cont_stuck h V k i T rfl

end Silmaril.Wasm.Models.FXT
