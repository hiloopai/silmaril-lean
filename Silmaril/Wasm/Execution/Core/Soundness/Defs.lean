module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-! # Shared definitions for the soundness proofs

`ResultTyped`, the host contract `HostOk`, and the split of the reference
instruction family between `RefStep` and `AggregateStep`. The per-family
preservation/progress lemmas live in `Soundness/<Family>.lean`; the assembled
theorems in `Soundness/Preservation.lean`, `Soundness/Progress.lean` and
`Soundness.lean`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- A result is typed by a result type. -/
def ResultTyped (s : Store H) : Result → List CValType → Prop
  | .values vs, ts => List.Forall₂ (ValOk s) vs ts
  | .throw a, _ => ∃ e, s.exns[a]? = some e
  | .trap, _ => True

/-- The host contract. -/
def HostOk (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (fi : FuncInst H) (h : H) (vs : List Val) (ps rs : Ty (.list .val)),
    StoreOk s → fi ∈ s.funcs → fi.code = .host h → Expand fi.type (.func ps rs) →
    List.Forall₂ (ValOk s) vs ps.toList →
      (∃ out, host h s vs out) ∧
      ∀ out, host h s vs out → match out with
        | .diverged => True
        | .returned s' r => StoreOk s' ∧ Extend s s' ∧ ResultTyped s' r rs.toList

/-- The GC aggregate instructions (reduced by `AggregateStep`); the other
`RefInstrOk` instructions are reduced by `RefStep`. -/
def _root_.Silmaril.Wasm.Instr.IsAggregate : Instr → Prop
  | .structNew _ | .structNewDefault _ | .structGet _ _ _ | .structSet _ _
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ | .arrayNewData _ _
  | .arrayNewElem _ _ | .arrayGet _ _ | .arraySet _ | .arrayLen | .arrayFill _
  | .arrayCopy _ _ | .arrayInitData _ _ | .arrayInitElem _ _ => True
  | _ => False

/-- Typing of administrative code is stable under store extension, for frames.
(Statement change: needs `StoreOk s`, see `AdminsOk.extend`.) -/
theorem FrameOk.extend {s s' : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : FrameOk s f C) : FrameOk s' f C :=
  FrameOk.extend_of_storeOk hs he h

end Silmaril.Wasm.Execution.Core
