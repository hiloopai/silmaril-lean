module

public import Silmaril.Wasm.Models.FXV.Defs

/-!
# `StepFX'` with continuation cells, a continuation queue and a log: `StepFXT`

A relation **next to** `StepFX'` (`Silmaril.Wasm.Models.FXV`), without changing it, that adds the
three things the explainer's schedulers need and `StepFX'` lacks: a place other than the
operand stack to keep a continuation, the explainer's queue of continuations, and `print_i32`
as an observation.

* `Tbl`: **cells** (continuation-valued locals: FX values, so a cell can hold `ref.cont k`), a
  **queue** of FX values, and the **log** of printed values (oldest first).
* `Intr`: **intrinsics**, host functions whose behaviour is given by the model instead of by
  the host relation: `log` (`print_i32`), `enq`, `deq` (`ref.null` on an empty queue),
  `qEmpty`, `cget i`, `cset i` (read and write cell `i`), `isNull` (`ref.is_null` on an FX
  value). `intr : H → Option Intr` marks the host codes that are intrinsics, as `fx` marks
  the FX functions.
* **`StepFXT P host fx intr`** on `ConfigT` (an FX configuration and a table) has two rules:
  `lift`, a `StepFX'` step with the host `blockI host intr` (which refuses intrinsic codes),
  table unchanged; and `intr`, a call (`ref.func a; call_ref`, as `StepFX'.invoke`) of an
  intrinsic function with FX-value arguments, in any evaluation context (`CtxV`), replaced by
  its results while the table is updated (`Intr.run`).
* `behavioursT`: the log and Wasm behaviour of a finished run (`ObsT.ret`), or divergence.

The examples of `Silmaril.Wasm.FX.Examples.Threads` are proved in the deterministic machine
`StepFXL` (`Silmaril.Wasm.Models.FXL`), and, compiled to FX code over these intrinsics
(`Silmaril.Wasm.Models.FXLComp`), shown to be `StepFXT` behaviours by a sound interpreter
(`Silmaril.Wasm.Models.FXTRun`, `Silmaril.Wasm.FX.Examples.ThreadsT`); a general simulation from
`StepFXL` is open (docs/projects/wasm-wasi.md).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

/-- The table: continuation cells, the queue and the log. -/
structure Tbl where
  cells : List FVal
  queue : List FVal
  log : List Val

/-- Intrinsic functions. -/
inductive Intr where
  | log
  | enq
  | deq
  | qEmpty
  | cget (i : Nat)
  | cset (i : Nat)
  | isNull

/-- `1` or `0` as an `i32` FX value. -/
def flag (b : Bool) : FVal := .val (Val.i32 (if b then 1 else 0))

/-- Is an FX value `ref.null`? -/
def isNullV : FVal → Bool
  | .val (.ref .null) => true
  | _ => false

/-- **What an intrinsic does**: from its arguments (in stack order) and the table, its results
and the new table; `none` for the wrong number of arguments or a missing cell. -/
def Intr.run : Intr → List FVal → Tbl → Option (List FVal × Tbl)
  | .log, [.val v], t => some ([], { t with log := t.log ++ [v] })
  | .enq, [v], t => some ([], { t with queue := t.queue ++ [v] })
  | .deq, [], t =>
    match t.queue with
    | [] => some ([.val (.ref .null)], t)
    | v :: q => some ([v], { t with queue := q })
  | .qEmpty, [], t => some ([flag t.queue.isEmpty], t)
  | .cget i, [], t => t.cells[i]?.map fun v => ([v], t)
  | .cset i, [v], t =>
    if i < t.cells.length then some ([], { t with cells := t.cells.set i v }) else none
  | .isNull, [v], t => some ([flag (isNullV v)], t)
  | _, _, _ => none

/-- A configuration: an FX configuration and a table. -/
structure ConfigT (H : Type) where
  cfg : ConfigFX H
  tbl : Tbl

variable {H : Type}

/-- The host of the lifted steps: intrinsic codes have no host behaviour. -/
def blockI (host : HostSemantics H) (intr : H → Option Intr) : HostSemantics H :=
  fun h s vs out => intr h = none ∧ host h s vs out

/-- **The step relation.** -/
inductive StepFXT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (intr : H → Option Intr) : ConfigT H → ConfigT H → Prop where
  /-- A `StepFX'` step; intrinsic codes are refused by the host. -/
  | lift {c c' : ConfigFX H} {t : Tbl} (h : StepFX' P (blockI host intr) fx c c') :
      StepFXT P host fx intr ⟨c, t⟩ ⟨c', t⟩
  /-- A call of an intrinsic function, in an evaluation context. -/
  | intr {s : Store H} {K : List (Option ContFX)} {f : Frame} {E : CtxV} {args res : List FVal}
      {a : Nat} {fi : FuncInst H} {h : H} {op : Intr} {cc : Admin} {t t' : Tbl}
      (hc : cc.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h)
      (hi : intr h = some op) (hr : op.run args t = some (res, t')) :
      StepFXT P host fx intr
        ⟨⟨s, K, f, E.plug (fvals args ++ [.core (.ref (.func a)), .core cc])⟩, t⟩
        ⟨⟨s, K, f, E.plug (fvals res)⟩, t'⟩

/-- Runs. -/
abbrev StepsT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (intr : H → Option Intr) :=
  Relation.ReflTransGen (StepFXT P host fx intr)

/-- Observations: the log and the Wasm behaviour of a finished run, or divergence. -/
inductive ObsT where
  | ret (log : List Val) (b : Behaviour Val)
  | diverges

/-- **The behaviours** of a configuration. -/
def behavioursT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (intr : H → Option Intr) (c : ConfigT H) : Set ObsT :=
  {o | ∃ (d : ConfigT H) (r : Result), StepsT P host fx intr c d ∧
      d.cfg.code = r.toAdmin.map .core ∧ o = .ret d.tbl.log r.toBehaviour} ∪
  {o | o = .diverges ∧ Silmaril.InfiniteTrace (StepFXT P host fx intr) c}

end Silmaril.Wasm.Models.FXT
