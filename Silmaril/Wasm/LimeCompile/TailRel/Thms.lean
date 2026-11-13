module

public import Silmaril.Proofs.Wasm.LimeCompile.TailRel.Exit

/-!
# The non-local shapes of the tail-call rewrite: different exit kernels, same callee

The two shapes of `TailRel.Defs` reach the same outcomes by different exit kernels, at every
profile and every host (proofs in `Silmaril.Proofs.Wasm.LimeCompile.TailRel.Exit`):

* **`src_call`, `tgt_call`**: at a tail call of a Wasm function `a`, the source leaves its labels
  and frame (`return_call_ref-label`, `-frame-addr`) and then calls, the target calls inside its
  wrapper; both create the **same callee frame** `calleeFrame fn vs code` (same store);
* `src_host`, **`tgt_host`**: at a tail call of a host function that returns `r`, both reach
  `r` in the same store, provided `r` has as many values as the caller's arity (the host
  contract `HostOk` and validity give this);
* `wrap_step`: every step of the callee lifts into the target's wrapper;
* `wrap_vals`, `wrap_trap`, `wrap_throw`: the callee's outcome leaves the wrapper (by `return`,
  or the trap and exception bubbling rules) as the source's callee outcome leaves nothing.

These are the non-local cases of the simulation `Tail.Task.tailSim` needs; the remaining open
part is the closure of this pairing under every other rule and context (labels, handlers,
frames, nested wrappers when the callee itself tail-calls, the store relation between source
and rewritten bodies, and the arity invariant from typing), see `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailRel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.LimeCompile.TailRel

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The callee's frame (`call_ref-func`). -/
def calleeFrame (fn : FuncInst H) (rs : Ty (.list .val)) (vs : List Val) (code : Func) : Admin :=
  .frame rs.length (Frame.forCall fn.module vs code.locals)
    [.label rs.length [] (expression code.body)]

/-- Leaving a frame turns a `RETURN_CALL_REF` into a `CALL_REF`. -/
theorem retToCallIn_isCallRef {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    (c.retToCallIn m).IsCallRef :=
  match c, hc with
  | .plain (.returnCallRef y), _ => by
    simp only [Admin.retToCallIn]
    split <;> trivial
  | .returnCallRefType d, _ => trivial

/-- **Source**: the pending tail call of a Wasm function leaves the caller and enters the callee. -/
theorem src_call {s : Store H} {f fi : Frame} {k : Nat} {pre pre' vs : List Val} {L : LabCtx}
    {a : Nat} {c : Admin} {restL rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    {code : Func} (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn)
    (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fn.code = .wasm code) :
    Steps P host ⟨s, f, [srcPending k fi pre L pre' vs a c restL rest]⟩
      ⟨s, f, [calleeFrame fn rs vs code]⟩ :=
  (src_exit hc hf he hn).tail (.callRefFunc (retToCallIn_isCallRef hc fi.module) hf he hn hcode)

/-- **Target**: the call of a Wasm function enters the callee inside the caller's wrapper. -/
theorem tgt_call {s : Store H} {f fi : Frame} {k : Nat} {pre pre' vs : List Val} {L : LabCtx}
    {a : Nat} {c : Admin} {restL rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    {code : Func} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fn)
    (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fn.code = .wasm code) :
    Step P host ⟨s, f, [tgtWrap k fi pre L pre' (vals vs ++ [.ref (.func a), c]) restL rest]⟩
      ⟨s, f, [tgtWrap k fi pre L pre' [calleeFrame fn rs vs code] restL rest]⟩ :=
  wrap_step (.callRefFunc hc hf he hn hcode)

/-- **Source**: the pending tail call of a host function that returns `r`. -/
theorem src_host {s s' : Store H} {f fi : Frame} {k : Nat} {pre pre' vs : List Val} {L : LabCtx}
    {a : Nat} {c : Admin} {restL rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    {h : H} {r : Result} (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn)
    (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fn.code = .host h)
    (hh : host h s vs (.returned s' r)) :
    Steps P host ⟨s, f, [srcPending k fi pre L pre' vs a c restL rest]⟩ ⟨s', f, r.toAdmin⟩ :=
  (src_exit hc hf he hn).tail (.callRefHost (retToCallIn_isCallRef hc fi.module) hf he hn hcode hh)

/-- **Target**: the call of a host function that returns `r` inside the wrapper; the wrapper
then reduces to `r`, when `r` has as many values as the caller's arity. -/
theorem tgt_host {s s' : Store H} {f fi : Frame} {k : Nat} {pre pre' vs : List Val} {L : LabCtx}
    {a : Nat} {c : Admin} {restL rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    {h : H} {r : Result} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fn)
    (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fn.code = .host h)
    (hh : host h s vs (.returned s' r)) (hk : ∀ ws, r = .values ws → ws.length = k) :
    Steps P host ⟨s, f, [tgtWrap k fi pre L pre' (vals vs ++ [.ref (.func a), c]) restL rest]⟩
      ⟨s', f, r.toAdmin⟩ := by
  have h₁ : Step P host
      ⟨s, f, [tgtWrap k fi pre L pre' (vals vs ++ [.ref (.func a), c]) restL rest]⟩
      ⟨s', f, [tgtWrap k fi pre L pre' r.toAdmin restL rest]⟩ :=
    wrap_step (.callRefHost hc hf he hn hcode hh)
  have h₂ : Steps P host ⟨s', f, [tgtWrap k fi pre L pre' r.toAdmin restL rest]⟩
      ⟨s', f, r.toAdmin⟩ := by
    cases r with
    | values ws => exact wrap_vals (hk ws rfl)
    | throw b => exact wrap_throw b
    | trap => exact wrap_trap
  exact .head h₁ h₂

/-- info: 'Silmaril.Wasm.LimeCompile.TailRel.tgt_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tgt_host

end Silmaril.Wasm.LimeCompile.TailRel
