module

public import Silmaril.Wasm.Instantiation.Defs
public import Silmaril.Proofs.Wasm.Instantiation.Prepare

/-!
# Completeness of executable Core 3.0 instantiation: theorems

silmaril-lean proves `prepare?`, `initSegments?`, `instantiateInit?` and `prepareDirect?`
sound. These are the converses, so the executable instantiation computes exactly the
specification's `Instantiate` followed by the segment-initialisation run.

* `prepare?_complete`: relative to `EvalComplete`, `prepare?` returns the store and frame of
  every `Instantiate` derivation, with code `initCode m` and the module's start function. This
  holds at every profile and host.
* `initSegments?_complete`: in the host-free deterministic profile `profile o`, a run of
  `initCode m` to the empty code is computed by `initSegments?`, for an evaluator complete on
  frame-preserving single-value evaluations whose offsets keep the frame and yield one value.
  Without the offset hypothesis the statement is false: an offset that leaves two values can be
  compensated by a later segment's offset code (source docstring).
* **`instantiateInit?_complete`, `instantiateDirect?_complete`**: unconditional in
  `profile o` with the host-free `noHost`. The offsets of a module that `Instantiate` accepts
  are validated constant expressions, so `evalConst?` finds them.
* **`instantiateInit?_iff`, `instantiateDirect?_iff`**: for valid modules with typed imports,
  the executable functions succeed exactly on the `Instantiate` derivations followed by a run of
  `initCode m` to the empty code.
* `prepareDirect?_complete`, `prepareDirect?_iff`: the same for an arbitrary evaluator, under
  evaluator hypotheses.

Scope: as in the source, the completeness results other than `prepare?_complete` are about
the deterministic profile `profile o` and the host-free `noHost`; the general profile is not
attempted.

Proofs: `Silmaril.Proofs.Wasm.Instantiation.{Segments,Prepare}`, ported from
an earlier development `Silmaril/Wasm/Execution/Core/Exec/{PrepareComplete,
SegmentInitComplete,InstantiateInitComplete,PrepareDirectComplete}.lean` and cleaned up (one
segment proof instead of two, one offset lemma instead of two copies, an unused hypothesis
dropped).
-/

@[expose] public section

namespace Silmaril.Wasm.Instantiation

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Completeness of `prepare?`** relative to `EvalComplete`, at every profile and host. -/
theorem prepare?_complete {P : Profile} {host : HostSemantics H}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} (hev : EvalComplete P host ev)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    (h : Instantiate P host s m xas c) :
    prepare? ev s m xas = some (⟨c.store, c.frame, initCode m⟩, m.start) :=
  Silmaril.Proofs.Wasm.Instantiation.prepare?_complete hev h

/-- **Completeness of segment initialisation** from frame `f`, given offset completeness at
`f`. -/
theorem initSegments?_completeAt {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {f f' : Frame}
    {m : Module} (hc : ∀ e, IsOffset m e → OffsetCompleteAt o ev f e)
    (h : Steps (profile o) noHost ⟨s, f, initCode m⟩ ⟨s', f', []⟩) :
    initSegments? ev s f m = some (s', f') :=
  Silmaril.Proofs.Wasm.Instantiation.initSegments?_completeAt hc h

/-- **Relative completeness of segment initialisation** for an arbitrary evaluator. -/
theorem initSegments?_complete {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {f f' : Frame}
    {m : Module}
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (h : Steps (profile o) noHost ⟨s, f, initCode m⟩ ⟨s', f', []⟩) :
    initSegments? ev s f m = some (s', f') :=
  Silmaril.Proofs.Wasm.Instantiation.initSegments?_complete hevc hoff h

/-- **Completeness of `instantiateInit?`** (host-free deterministic profile, unconditional). -/
theorem instantiateInit?_complete {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    instantiateInit? s m xas = some ((⟨s', f', []⟩ : Config H).withStart m.start) :=
  Silmaril.Proofs.Wasm.Instantiation.instantiateInit?_complete hI hS

/-- **`instantiateInit?` is the specification's instantiation**, for valid modules with typed
imports. -/
theorem instantiateInit?_iff {o : GrowOracle} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c' : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateInit? s m xas = some c' ↔
      ∃ c, Instantiate (profile o) noHost s m xas c ∧ ∃ (s' : Store H) (f' : Frame),
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ ∧
        c' = (⟨s', f', []⟩ : Config H).withStart m.start :=
  Silmaril.Proofs.Wasm.Instantiation.instantiateInit?_iff hvalid

/-- **Completeness of `instantiateDirect?`** (host-free deterministic profile,
unconditional). -/
theorem instantiateDirect?_complete {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    instantiateDirect? s m xas = some (s', f', m.start) :=
  Silmaril.Proofs.Wasm.Instantiation.instantiateDirect?_complete hI hS

/-- **`instantiateDirect?` is the specification's instantiation**, for valid modules with typed
imports. -/
theorem instantiateDirect?_iff {o : GrowOracle} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateDirect? s m xas = some (s', f', st) ↔
      st = m.start ∧ ∃ c, Instantiate (profile o) noHost s m xas c ∧
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ :=
  Silmaril.Proofs.Wasm.Instantiation.instantiateDirect?_iff hvalid

/-- **Relative completeness of `prepareDirect?`** for an arbitrary evaluator. -/
theorem prepareDirect?_complete {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} {f' : Frame}
    (hev : EvalComplete (profile o) noHost ev)
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (hI : Instantiate (profile o) noHost s m xas c)
    (hS : Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩) :
    prepareDirect? ev s m xas = some (s', f', m.start) :=
  Silmaril.Proofs.Wasm.Instantiation.prepareDirect?_complete hev hevc hoff hI hS

/-- `prepareDirect?` characterised by the reduction semantics, for a sound and complete
evaluator. -/
theorem prepareDirect?_iff {o : GrowOracle}
    {ev : Store H → Frame → Expr → Option (Store H × Val)} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (hes : EvalSound (profile o) noHost ev)
    (hev : EvalComplete (profile o) noHost ev)
    (hevc : ∀ s f e s' v, EvalExpr (profile o) noHost s f e s' f [v] → ev s f e = some (s', v))
    (hoff : ∀ e, IsOffset m e → ∀ (s : Store H) (f : Frame) (s' : Store H) (f' : Frame) vs,
      EvalExpr (profile o) noHost s f e s' f' vs → f' = f ∧ vs.length = 1)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    prepareDirect? ev s m xas = some (s', f', st) ↔
      st = m.start ∧ ∃ c, Instantiate (profile o) noHost s m xas c ∧
        Steps (profile o) noHost ⟨c.store, c.frame, initCode m⟩ ⟨s', f', []⟩ :=
  Silmaril.Proofs.Wasm.Instantiation.prepareDirect?_iff hes hev hevc hoff hvalid

/-- `instantiateInit?` is `instantiateDirect?` followed by the start call. -/
theorem instantiateInit?_eq (s : Store H) (m : Module) (xas : List ExternAddr) :
    instantiateInit? s m xas =
      (instantiateDirect? s m xas).map fun (s', f', st) =>
        (⟨s', f', []⟩ : Config H).withStart st :=
  Silmaril.Proofs.Wasm.Instantiation.instantiateInit?_eq s m xas

end Silmaril.Wasm.Instantiation
