module

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs

/-!
# The flat status view and store extension of the concrete Core 3.0 engine

* `flatStatus` is the flat view of a single-threaded status: values are converted to flat
  values (`SingleThreaded.toFlat?`), and a result or a callout whose values are not all numeric
  is `stuck`. The status of `core3 o` is the flat view of the computable status
  `statusC (stepI o)` (`statusE_eq_flatStatus`).
* `flatStatus_running_iff`, `flatStatus_eq_callout`: only `running` is `running`, and a flat
  callout comes from a callout.
* `Grows.extends`: untyped store growth (`Grows`, Engine/Core3/Grows.lean) is store extension
  of the concrete engine (`CoreEngine.Extends`, Engine/Laws.lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The flat status view -/

/-- The flat view of a single-threaded status (the body of `statusE`). -/
def flatStatus : SingleThreaded.Status H → Status H
  | .running => .running
  | .returned (.values vs) =>
    match vs.mapM SingleThreaded.toFlat? with
    | some fvs => .returned (.values fvs)
    | none => .stuck
  | .returned .trap => .returned .trap
  | .callout h args =>
    match args.mapM SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck
  | .stuck => .stuck

theorem statusE_eq_flatStatus (o : SingleThreaded.GrowOracle) (s : Store H)
    (t : SingleThreaded.Thread) :
    statusE o s t = flatStatus (SingleThreaded.statusC (SingleThreaded.Exec.stepI o) s t) := by
  unfold statusE flatStatus
  rfl

/-- A flat callout is the flat view of a callout. -/
theorem flatStatus_eq_callout {st : SingleThreaded.Status H} {hc : H} {args : List FlatValue}
    (h : flatStatus st = .callout hc args) : ∃ hc' args', st = .callout hc' args' := by
  rcases st with _ | (vs | _) | ⟨hc', args'⟩ | _
  · cases h
  · simp only [flatStatus] at h
    split at h <;> cases h
  · cases h
  · exact ⟨hc', args', rfl⟩
  · cases h

/-! ## Growth is store extension -/

/-- Untyped store growth is store extension of the concrete engine. -/
theorem Grows.extends {o : SingleThreaded.GrowOracle} {s s' : Store H} (hg : Grows s s') :
    (core3 o).Extends s s' where
  funcType _ _ h := hg.funcType h
  memAddrType _ _ h := hg.memAddrType h
  memSize _ _ h := hg.memSize h
  tableAddrType _ _ h := hg.tableAddrType h
  callout t _ _ h :=
    (statusE_eq_flatStatus o s' t).trans
      (hg.status_callout_of flatStatus (fun _ e => flatStatus_eq_callout e)
        ((statusE_eq_flatStatus o s t).symm.trans h))

/-- The status of a thread whose code is neither values, a trap nor a throw: a callout when the
code decomposes at a host call, otherwise `running` or `stuck` as the step function says. -/
theorem statusC_of_live {stepC : Config H → Option (Config H)} {s : Store H}
    {t : SingleThreaded.Thread}
    (h1 : ¬ (SingleThreaded.splitVals (t.config s).code).2.isEmpty = true)
    (h2 : ¬ SingleThreaded.isTrap? (t.config s).code = true)
    (h3 : ¬ SingleThreaded.isThrowing? (t.config s).code = true) :
    SingleThreaded.statusC stepC s t =
      match SingleThreaded.decompose? s (t.config s).code with
      | some (_, _, h, args) => .callout h args
      | none => if (stepC (t.config s)).isSome then .running else .stuck := by
  simp only [SingleThreaded.statusC, h1, h2, h3, Bool.false_eq_true, ite_false]
  rfl

end Silmaril.Wasm.Component.Engine.Core3

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core
variable {H : Type}

theorem flatStatus_running_iff {st : SingleThreaded.Status H} :
    flatStatus st = .running ↔ st = .running := by
  constructor
  · intro h
    rcases st with _ | (vs | _) | ⟨hc, args⟩ | _
    · rfl
    · simp only [flatStatus] at h
      split at h <;> cases h
    · cases h
    · simp only [flatStatus] at h
      split at h <;> cases h
    · cases h
  · rintro rfl
    rfl

end Silmaril.Wasm.Component.Engine.Core3
