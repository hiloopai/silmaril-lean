module

public import Silmaril.X86.Extends.Defs
public import Silmaril.X86.CallingConvention

/-!
# System V function contracts over any x86 machine

`FnContract I` is a **total** System V AMD64 function contract over a segment-VC machine
`I : SegVC.Isa σ` (the open machines `Open.isa` and `Open9.isa`, or a machine with more
state). It has a spec (`Spec`) and its proof (`total`):

* `entry s`: the function's own precondition at its entry state (code loaded, arguments,
  separation of its buffers, …). The ABI part, `AbiEntry` (`rsp ≡ 8 mod 16`, a readable
  return address at `[rsp]`), is supplied by every caller and is not repeated in `entry`;
* `footprint s`: the byte addresses the function may write (its frame, red zone, output
  buffers). Everything outside it is unchanged (`Memory.WritesWithin`);
* `post s t`: the functional postcondition, from the entry state `s` to the returned state;
* `total`: from every live entry state with `AbiEntry` and `entry`, the machine reaches a
  state `t` with `Spec.Result`: only core and memory changed (`silent`), `rip` is the return
  address, `rsp` is popped past it and the six callee-saved registers are restored
  (`AbiReturn`), memory changed only inside the footprint, and `post` holds.

The return address is read from the entry state (`retOf`), so a contract names no designated
exit: on an open machine `ret` is an ordinary step. `Spec.Total` is *angelic*: it promises
some reachable returned state, not the first one.

`FnContract.toCall` is a contract as a contracted call of the segment VC generator
(`SegVC.Call`). `Spec.comap` pulls a spec back along a machine extension's view; the transfer
theorem `Spec.Total.lift` is in `FnContract/Thms.lean`.

**First return.** On an open machine a run continues into the caller after the return, so
`Spec.Total` only promises *some* reachable returned state. The first-return layer makes the
first return the meaning of a contract:

* `RunsIn I P s t`: a run from `s` to `t` whose every step is taken from a state satisfying
  `P` (the final state is unconstrained);
* `Returned I s m`: the function entered at `s` has returned in `m` (`rip` at the entry's
  return address, `rsp` popped past it); `FirstReturn I s t`: `t` is the first such state;
* `Spec.TotalIn I S P`: `Spec.Total` with the run inside `P s`; `Spec.Strict`: a `TotalIn`
  whose run passes no returned state before its last step, so its result is the first
  return; `Spec.StrictBelow`: `Strict` with the stack-depth invariant `Below` (the stack
  pointer never rises above the entry's), the form that composes across calls;
* `InCode`, `RetOutside`: the program counter inside the code, the return address outside
  it (a run inside the code is strict when the return address is outside);
* `FnContract.Strict`: a contract with a strict proof.

`Spec.Strict.total` recovers `Spec.Total`; the transfers along machine extensions
(`Spec.Strict.lift`, `Spec.StrictBelow.lift`, `Strict.lift`) are in `FnContract/Thms.lean`.

This is a contract layer over the handwritten machine models, not an ABI-conformance claim
beyond the stated hypotheses.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (State MState Word Reg sysv64)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

namespace FnContract

/-- The return address at the top of the stack of a core and memory (`0` if unreadable). -/
def retOf (core : State) (memory : Memory) : Word :=
  ((memory.readBytes (core.read .rsp).toNat 8).bind wordOfBytes?).getD 0

/-- The System V entry obligations every caller supplies: the entry stack pointer is
`8 mod 16` (the caller was 16-byte aligned and `call` pushed eight bytes) and the return
address is readable at `[rsp]`. -/
structure AbiEntry (core : State) (memory : Memory) : Prop where
  aligned : (core.read .rsp).toNat % 16 = 8
  returnAddress : memory.readBytes (core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [retOf core memory])

/-- The System V return obligations, from an entry core and memory to the final core: `rip`
at the return address, `rsp` popped past it, the callee-saved registers restored. -/
structure AbiReturn (core : State) (memory : Memory) (final : State) : Prop where
  pc : final.rip = retOf core memory
  stack : final.read .rsp = core.read .rsp + 8#64
  calleeSaved : ∀ r ∈ sysv64.calleeSaved, final.read r = core.read r

/-- A function spec over states `σ`: precondition, write footprint, postcondition. -/
structure Spec (σ : Type) where
  entry : σ → Prop
  footprint : σ → Nat → Prop
  post : σ → σ → Prop

variable {σ τ : Type}

/-- What a call of a function with spec `S` guarantees from its entry state `s` to `t`. -/
structure Spec.Result (I : Isa σ) (S : Spec σ) (s t : σ) : Prop where
  /-- Only the core and the memory changed. -/
  silent : I.upd s (I.core t) (I.mem t) = t
  abi : AbiReturn (I.core s) (I.mem s) (I.core t)
  frame : (I.mem s).WritesWithin (I.mem t) (S.footprint s)
  post : S.post s t

/-- **Total correctness** of a spec on a machine. -/
def Spec.Total (I : Isa σ) (S : Spec σ) : Prop :=
  ∀ s, I.live s → AbiEntry (I.core s) (I.mem s) → S.entry s →
    ∃ t, Reaches I.step s t ∧ S.Result I s t

/-- `S` refines `T`: a weaker precondition, and under `T`'s precondition a smaller footprint
and a stronger postcondition. -/
structure Spec.Sub (S T : Spec σ) : Prop where
  entry : ∀ s, T.entry s → S.entry s
  footprint : ∀ s a, T.entry s → S.footprint s a → T.footprint s a
  post : ∀ s t, T.entry s → S.post s t → T.post s t

/-- A spec on `σ` read on `τ` through `f` (for an extension, `f` is its `view`). -/
def Spec.comap (f : τ → σ) (S : Spec σ) : Spec τ where
  entry x := S.entry (f x)
  footprint x := S.footprint (f x)
  post x y := S.post (f x) (f y)

/-- A memory predicate untouched by writes inside `fp`. -/
def Stable (fp : Nat → Prop) (F : Memory → Prop) : Prop :=
  ∀ m m', m.WritesWithin m' fp → F m → F m'

/-- What a returning-run proof provides about the final state, besides `rip`. -/
structure ReturnsPost (S : Spec MState) (m fin : MState) : Prop where
  stack : fin.core.read .rsp = m.core.read .rsp + 8#64
  calleeSaved : ∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r
  frame : m.memory.WritesWithin fin.memory (S.footprint m)
  post : S.post m fin

/-! ## First return -/

/-- Runs of the machine `I` that take every step from a state satisfying `P` (the final
state is unconstrained). -/
inductive RunsIn (I : Isa σ) (P : σ → Prop) : σ → σ → Prop
  | refl (s : σ) : RunsIn I P s s
  | step {s s' t : σ} : P s → I.step s = some s' → RunsIn I P s' t → RunsIn I P s t

/-- The function entered at `s` has returned in `m`: `rip` at the entry's return address
and `rsp` popped past it. -/
def Returned (I : Isa σ) (s m : σ) : Prop :=
  (I.core m).rip = retOf (I.core s) (I.mem s) ∧
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
  ∀ o, o < len → retOf (I.core s) (I.mem s) ≠ base + BitVec.ofNat 64 o

/-- `Spec.Total` with the run restricted to steps from states satisfying `P s` (`s` the
entry state). -/
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

end FnContract

/-- **A strict (first-return) System V function contract**: a `FnContract` whose spec is
also strictly totally correct (`Spec.Strict`). -/
structure FnContract.Strict {σ : Type} (I : Isa σ) extends FnContract I where
  strict : toSpec.Strict I

end Silmaril.X86
