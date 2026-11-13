module

public import Silmaril.Machine.X86.Open.Thms
public import Silmaril.X86.CallingConvention

/-!
# Generic System V function contracts

`FnContract I` is a **total** System V AMD64 function contract over any segment-VC machine
`I : Silmaril.X86.SegVC.Isa σ` (the open machine `Open.isa`, the Linux process machine
`Isa.sys`, …). It replaces per-callee glue such as
`Silmaril.Apps.Sha256sum.Binary.Digest.compressCall`: `FnContract.toCall` is the callee as a
contracted call of the segment VC generator.

A contract has a spec (`FnContract.Spec`) and its proof (`total`):

* `entry s`: the function's own precondition at its entry state (code loaded, arguments,
  separation of its buffers, …). The ABI part, `AbiEntry` (`rsp ≡ 8 mod 16`, a readable
  return address at `[rsp]`), is supplied by every caller and is not repeated in `entry`.
* `footprint s`: the byte addresses the function may write (its frame, red zone, output
  buffers). Code and everything else outside it is unchanged (`WritesWithin`).
* `post s t`: the functional postcondition, from the entry state `s` to the returned state `t`.
* `total`: from every live entry state satisfying `AbiEntry` and `entry`, the machine reaches a
  state `t` with `Spec.Result`: only the core and the memory changed (`silent`), `rip` is the
  return address, `rsp` is popped past it and the six callee-saved registers are restored
  (`AbiReturn`), memory changed only inside the footprint, and `post`.

The return address is read from the entry state (`Open.retOf`), so a contract mentions no
designated exit; on the open machine `ret` is an ordinary step.

**First return.** `Spec.Total` is *angelic*: on the open machine a run continues into the
caller after the return, so it only promises *some* reachable returned state. `RunsIn I P`
(runs whose every step is taken from a state satisfying `P`), `Returned`, `FirstReturn`,
`Spec.TotalIn` and `Spec.Strict` (a `TotalIn` whose run never passes a returned state before
its last step) make the first return the meaning of a contract; `FnContract.Strict` is a
contract with that proof. `Spec.Strict.total` (in `Thms`) recovers `Spec.Total`. `Below`
is the stack-depth invariant (the stack pointer never rises above the entry's before the
return) that a recursive or calling first-return argument needs.

This is the **core** of the contract layer: it needs only the open machine and public
`Silmaril.X86`. The bridges to the System V ABI model
(`Silmaril.Machine.SystemV.Abi.Ffi`), to the integer `Silmaril.Machine.SystemV.Realizes` and to
`Decompile` certificates (`decompiledSpec`, `Open.ffiExecute`, `toRealizes`,
`toFfiRealizes`, `ofDecompiled`) are in `FnContract/SystemV`. Neither is an ABI-conformance
claim beyond the stated hypotheses.
-/

@[expose] public section

namespace Silmaril.Machine.X86

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

namespace FnContract

/-- The System V entry obligations every caller supplies: the entry stack pointer is
`8 mod 16` (the caller was 16-byte aligned and `call` pushed eight bytes) and the return
address is readable at `[rsp]`. -/
structure AbiEntry (core : State) (memory : Memory) : Prop where
  aligned : (core.read .rsp).toNat % 16 = 8
  returnAddress : memory.readBytes (core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [Open.retOf core memory])

/-- The System V return obligations, from an entry core and memory to the final core: `rip`
at the return address, `rsp` popped past it, the callee-saved registers restored. -/
structure AbiReturn (core : State) (memory : Memory) (final : State) : Prop where
  pc : final.rip = Open.retOf core memory
  stack : final.read .rsp = core.read .rsp + 8#64
  calleeSaved : ∀ r ∈ sysv64.calleeSaved, final.read r = core.read r

/-- A function spec: precondition, write footprint and postcondition, over states `σ`. -/
structure Spec (σ : Type) where
  entry : σ → Prop
  footprint : σ → Nat → Prop
  post : σ → σ → Prop

variable {σ : Type}

/-- What a call of a function with spec `S` guarantees from its entry state `s` to `t`. -/
structure Spec.Result (I : Isa σ) (S : Spec σ) (s t : σ) : Prop where
  /-- Only the core and the memory changed (for a process machine: no kernel state). -/
  silent : I.upd s (I.core t) (I.mem t) = t
  abi : AbiReturn (I.core s) (I.mem s) (I.core t)
  frame : (I.mem s).WritesWithin (I.mem t) (S.footprint s)
  post : S.post s t

/-- Total correctness of a spec on a machine. -/
def Spec.Total (I : Isa σ) (S : Spec σ) : Prop :=
  ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
    ∃ t, Reaches I.step s t ∧ S.Result I s t

/-- `S` refines `T`: a weaker precondition, and under `T`'s precondition a smaller footprint
and a stronger postcondition. -/
structure Spec.Sub (S T : Spec σ) : Prop where
  entry : ∀ s, T.entry s → S.entry s
  footprint : ∀ s a, T.entry s → S.footprint s a → T.footprint s a
  post : ∀ s t, T.entry s → S.post s t → T.post s t

/-- A memory predicate untouched by writes inside `fp`. -/
def Stable (fp : Nat → Prop) (F : Memory → Prop) : Prop :=
  ∀ m m', m.WritesWithin m' fp → F m → F m'

end FnContract

/-- **A total System V function contract** over the machine `I`. -/
structure FnContract {σ : Type} (I : Isa σ) extends FnContract.Spec σ where
  total : toSpec.Total I

namespace FnContract

variable {σ : Type} {I : Isa σ}

/-- The result of a call, for a contract. -/
abbrev Result (C : FnContract I) (s t : σ) : Prop := C.toSpec.Result I s t

/-- **The callee as a contracted call of the segment VC generator.** At the callee's entry,
the ABI entry obligations and the contract's precondition; after it, `Spec.Result`. -/
def toCall (C : FnContract I) : Call I where
  pre s := AbiEntry (I.core s) (I.mem s) ∧ C.entry s
  post := C.Result
  runs s hl h := C.total s hl h.1 h.2

/-- Weaken a contract along a refinement of its spec. -/
def mono (C : FnContract I) (T : Spec σ) (h : C.toSpec.Sub T) : FnContract I where
  toSpec := T
  total s hl ha he := by
    obtain ⟨t, hr, res⟩ := C.total s hl ha (h.entry s he)
    exact ⟨t, hr, res.silent, res.abi,
      res.frame.mono (fun a ha' => h.footprint s a he ha'), h.post s t he res.post⟩

/-- **The frame rule.** A memory predicate untouched by the footprint holds after the call
if it held before. -/
def frame (C : FnContract I) (F : Memory → Prop) (hF : ∀ s, Stable (C.footprint s) F) :
    FnContract I where
  entry s := C.entry s ∧ F (I.mem s)
  footprint := C.footprint
  post s t := C.post s t ∧ F (I.mem t)
  total s hl ha he := by
    obtain ⟨t, hr, res⟩ := C.total s hl ha he.1
    exact ⟨t, hr, res.silent, res.abi, res.frame, res.post, hF s _ _ res.frame he.2⟩

/-- What a returning-run proof must provide about the final state (`Open`-machine
constructors in `FnContract/Thms.lean`). -/
structure ReturnsPost (S : Spec MState) (m fin : MState) : Prop where
  stack : fin.core.read .rsp = m.core.read .rsp + 8#64
  calleeSaved : ∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r
  frame : m.memory.WritesWithin fin.memory (S.footprint m)
  post : S.post m fin

/-! ## First return -/

/-- Runs of the machine `I` that take every step from a state satisfying `P` (the final
state is unconstrained). Generic over the machine; `Silmaril.Machine.Abi.OpenMachine.RunsIn`
is the open-machine instance (`OpenMachine.runsIn_iff`). -/
inductive RunsIn (I : Isa σ) (P : σ → Prop) : σ → σ → Prop
  | refl (s : σ) : RunsIn I P s s
  | step {s s' t : σ} : P s → I.step s = some s' → RunsIn I P s' t → RunsIn I P s t

/-- The function entered at `s` has returned in `m`: `rip` at the entry's return address
and `rsp` popped past it. -/
def Returned (I : Isa σ) (s m : σ) : Prop :=
  (I.core m).rip = Open.retOf (I.core s) (I.mem s) ∧
    (I.core m).read .rsp = (I.core s).read .rsp + 8#64

/-- `t` is the **first** returned state of the run from `s`. -/
def FirstReturn (I : Isa σ) (s t : σ) : Prop :=
  RunsIn I (fun m => ¬ Returned I s m) s t ∧ Returned I s t

/-- The stack-depth invariant: the stack pointer of `m` is at or below the entry's (as
unsigned numbers). With `(rsp s).toNat + 8 < 2^64` it excludes `Returned I s m`
(`not_returned_of_below`), and it composes across calls. -/
def Below (I : Isa σ) (s m : σ) : Prop :=
  ((I.core m).read .rsp).toNat ≤ ((I.core s).read .rsp).toNat

/-- The program counter lies inside `len` bytes of code at `base`. -/
def InCode (I : Isa σ) (base : Word) (len : Nat) (m : σ) : Prop :=
  ∃ o, o < len ∧ (I.core m).rip = base + BitVec.ofNat 64 o

/-- The return address of the entry state lies outside `len` bytes of code at `base`. -/
def RetOutside (I : Isa σ) (base : Word) (len : Nat) (s : σ) : Prop :=
  ∀ o, o < len → Open.retOf (I.core s) (I.mem s) ≠ base + BitVec.ofNat 64 o

/-- `Spec.Total` with the run restricted to steps from states satisfying `P s` (`s` the entry
state). -/
def Spec.TotalIn (I : Isa σ) (S : Spec σ) (P : σ → σ → Prop) : Prop :=
  ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
    ∃ t, RunsIn I (P s) s t ∧ S.Result I s t

/-- **Strict (first-return) total correctness**: from every entry state, the run reaches a
result state without passing through a returned state before (so the result is the
*first* return, `Spec.Strict.firstReturn`). -/
def Spec.Strict (I : Isa σ) (S : Spec σ) : Prop :=
  S.TotalIn I fun s m => ¬ Returned I s m

/-- Strict total correctness with the stack-depth invariant `Below`: the form that composes
across calls (a caller sees no return of its own inside a deeper callee's run). -/
def Spec.StrictBelow (I : Isa σ) (S : Spec σ) : Prop :=
  S.TotalIn I fun s m => ¬ Returned I s m ∧ Below I s m

/-- `S` with its precondition strengthened by `P` (for instance by `RetOutside`). -/
def Spec.restrict (S : Spec σ) (P : σ → Prop) : Spec σ where
  entry s := S.entry s ∧ P s
  footprint := S.footprint
  post := S.post

end FnContract

/-- **A strict (first-return) System V function contract**: a `FnContract` whose spec is
also strictly totally correct (`Spec.Strict`). -/
structure FnContract.Strict {σ : Type} (I : Isa σ) extends FnContract I where
  strict : toSpec.Strict I

namespace FnContract

end FnContract

end Silmaril.Machine.X86
