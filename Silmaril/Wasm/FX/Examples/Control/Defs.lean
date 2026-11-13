module

public import Silmaril.Wasm.Models.FXL.Defs

/-!
# Delimited continuations: `control0`/`prompt0` through a universal tag, as `StepFXL` programs

The WasmFX explainer (pinned in docs/projects/wasm-wasi.md, section "Delimited continuations") implements
`control0`/`prompt0` with one *universal* tag `$control` whose payload is the function `h` to
run on the captured continuation, and a function `$prompt` that resumes its argument under a
handler for `$control`; on `$control` the handler applies `h` to the continuation `k`
(`call_ref (local.get $k) (local.get $h)`), outside the prompt. Here the module is written in the
machine of `Silmaril.Wasm.Models.FXL` (locals and call arguments of any value, so a continuation
can be passed to `h`), with one change: `StepFXL` has no function references, so `call_ref` is
**defunctionalized**. The payload of `$control` is an `i32` code of `h`, and `$apply` calls the
handler function of that code (`0` or not `0`, through `if`). Everything else is the explainer's
shape:

* tag `0` is `$control`, with payload arity `1` (`ctlAr`);
* `0`: `$prompt` (parameter `$nextk`): `block $on_control (result i32 (ref $cont))`
  `(resume (on $control $on_control) (local.get $nextk)) (return) end`, then `call $apply`
  (the explainer's `let … call_ref` with the payload and the continuation still on the stack);
* `1`: `$apply` (parameters `$h`, `$k`): `local.get $h; if (local.get $k; call 3)
  (local.get $k; call 2)`;
* `2`, `3`: the handler functions of codes `0` and `1` (parameter `$k`);
* `control0 h` at a use site is `i32.const h; suspend $control` (`control0`).

The explainer gives no program that uses `$control` and `$prompt` other than the lightweight
threads over them (which need `cont.bind` and `func.bind`, not in `StepFXL`). The programs below
are written for this workflow; each tests one property of `control0`/`prompt0`, observed by the
log (`print_i32`):

* `abortP`: `h` drops `k` (an abort): log `1 2 4`;
* `resumeP`: `h` resumes `k` once and then continues: log `1 2 3 4 5`;
* `escapeP`: **the continuation does not include the prompt**: `h` resumes `k` *without* a
  handler, so the second `control0` in `k` is caught by the *outer* prompt (and the rest of `k`
  and of `h` is discarded): log `1 2 3 5 9 10`. With `shift0`/`reset0` (a continuation that
  reinstalls its prompt) the inner prompt would catch it, and the log would be
  `1 2 3 5 9 6 8 10`;
* `outsideP`: **`h` runs outside the prompt**: a `control0` inside `h` is caught by the outer
  prompt: log `1 2 3 4 5`;
* `twiceP`: continuations are **one-shot**: `h` resumes `k` twice; the second `resume` traps,
  with log `1 2`.

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Control

open Silmaril.Wasm.Models.FXL

/-- A function without parameters, locals or results. -/
def proc (body : List I) : Fn := ⟨0, 0, 0, body⟩

/-- A handler function: parameter `$k` (local `0`), no results. -/
def hfun (body : List I) : Fn := ⟨1, 0, 0, body⟩

/-- `print_i32 n`. -/
def logC (n : Int) : List I := [.const n, .log]

/-- `control0 h`: suspend with the universal tag `$control` (tag `0`), payload the code `h`. -/
def control0 (h : Int) : List I := [.const h, .suspend 0]

/-- **`$prompt`** (function `0`): resume `$nextk` under `(on $control $on_control)`; on
`$control`, apply the payload to the continuation (function `1`). -/
def promptF : Fn :=
  ⟨1, 0, 0, [.block 2 [.localGet 0, .resume [(0, 0)], .ret], .call 1]⟩

/-- **`$apply`** (function `1`): the defunctionalized `call_ref`: code `0` calls function `2`,
any other code calls function `3`, with the continuation as argument. -/
def applyF : Fn :=
  ⟨2, 0, 0, [.localGet 0, .if_ [.localGet 1, .call 3] [.localGet 1, .call 2]]⟩

/-- Tag payload arities: `$control` carries one value. -/
def ctlAr : Nat → Nat := fun _ => 1

/-- A program of the module: `$prompt`, `$apply`, the handler functions `h0`, `h1`, then the
other functions `rest` (from index `4`). -/
def ctlP (h0 h1 : Fn) (rest : List Fn) : Prog := [promptF, applyF, h0, h1] ++ rest

/-- `prompt0 (cont.new f)`. -/
def prompt0 (f : Nat) : List I := [.contNew f, .call 0]

/-! ## The programs -/

/-- **Abort**: `prompt0 (log 1; control0 h; log 3); log 4` with `h k = log 2`. Main is `5`. -/
def abortP : Prog :=
  ctlP (hfun (logC 2)) (hfun []) [proc (logC 1 ++ control0 0 ++ logC 3),
    proc (prompt0 4 ++ logC 4)]

/-- **Resume once**: `prompt0 (log 1; control0 h; log 3); log 5` with
`h k = log 2; resume k; log 4`. Main is `5`. -/
def resumeP : Prog :=
  ctlP (hfun (logC 2 ++ [.localGet 0, .resume []] ++ logC 4)) (hfun [])
    [proc (logC 1 ++ control0 0 ++ logC 3), proc (prompt0 4 ++ logC 5)]

/-- **The continuation excludes the prompt**:
`prompt0 (log 1; prompt0 (log 2; control0 h₀; log 5; control0 h₁; log 7); log 8); log 10` with
`h₀ k = log 3; resume k; log 6` and `h₁ k = log 9`. Inner body `4`, outer body `5`, main `6`. -/
def escapeP : Prog :=
  ctlP (hfun (logC 3 ++ [.localGet 0, .resume []] ++ logC 6)) (hfun (logC 9))
    [proc (logC 2 ++ control0 0 ++ logC 5 ++ control0 1 ++ logC 7),
     proc (logC 1 ++ prompt0 4 ++ logC 8),
     proc (prompt0 5 ++ logC 10)]

/-- **The handler runs outside the prompt**:
`prompt0 (log 1; prompt0 (log 2; control0 h₀; log 6); log 7); log 5` with
`h₀ k = log 3; control0 h₁; log 8` and `h₁ k = log 4`. Inner body `4`, outer body `5`, main `6`. -/
def outsideP : Prog :=
  ctlP (hfun (logC 3 ++ control0 1 ++ logC 8)) (hfun (logC 4))
    [proc (logC 2 ++ control0 0 ++ logC 6),
     proc (logC 1 ++ prompt0 4 ++ logC 7),
     proc (prompt0 5 ++ logC 5)]

/-- **One-shot**: `prompt0 (log 1; control0 h; log 2)` with `h k = resume k; resume k`.
Main is `5`. -/
def twiceP : Prog :=
  ctlP (hfun [.localGet 0, .resume [], .localGet 0, .resume []]) (hfun [])
    [proc (logC 1 ++ control0 0 ++ logC 2), proc (prompt0 4)]

/-! ## Expected logs -/

def abortLog : List Int := [1, 2, 4]
def resumeLog : List Int := [1, 2, 3, 4, 5]
def escapeLog : List Int := [1, 2, 3, 5, 9, 10]
def outsideLog : List Int := [1, 2, 3, 4, 5]
def twiceLog : List Int := [1, 2]

end Silmaril.Wasm.FX.Examples.Control
