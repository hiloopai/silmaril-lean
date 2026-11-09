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

end Silmaril.X86
