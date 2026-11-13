module

public import Silmaril.Wasi.Versions.WitImport.Compare.Defs

@[expose] public section

/-!
# WIT typing with traps

`witOk T` (`Silmaril.Wasi.Versions.WitImport`) asks a WIT-typed call of a function of `T` to be
answered with a value of the WIT result type; a trap (`none`) is not well typed. Several
hand-written WASI theories admit traps on purpose: `write` beyond the permit of `check-write`
and `poll([])` (`wasi:io` 0.2: "will trap"), `exit` (which does not return), `connect` and
`send` of 0.3 (safety theories). `witTrapOk T` is `witOk T` that also admits a trap:

* `witTrapOk T e = true` when `e` is not an import answer, its function is not in `T`, its
  arguments are not of the WIT parameter types, its answer is a trap, or its answer has the WIT
  result type.

`witTrapTh T` is the pointwise theory. `witOk T e → witTrapOk T e` (`witOk_trap`, in
`Silmaril.Wasi.Versions.WitImport.Io2`).

**Direction.** `tyOk` accepts every value for a named type (`Binary.Ty.ref`: `stream-error`,
`error-code`, `datetime`, `filesize`, …). So `witOk`/`witTrapOk` are *weaker* than a typing that
resolves named types. The sound comparisons are therefore *hand-written ⇒ WIT* (a hand-written
theory that checks a named type at all checks at least what `tyOk` checks). The converse fails
whenever the hand-written theory constrains a named type or a behaviour (refuted on examples in
the comparison modules).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi

/-- **WIT typing of import answers, traps admitted.** -/
def witTrapOk (T : Table) : WEv → Bool
  | .imp f a r => match T.lookup f with
    | some s => !argsOk s a || r.isNone || resOk s r
    | none => true
  | _ => true

/-- The WIT typing theory of a table, traps admitted. -/
def witTrapTh (T : Table) : Silmaril.Wasm.Resource.Protocol Unit WEv := pointwise (witTrapOk T)

end Silmaril.Wasi.Versions.WitImport
