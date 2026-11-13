module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Defs

/-!
# The single-threaded lift through translation validation: a one-thread x86 test

`ownWrite` is a one-thread x86 test made of bytes of the corpus
(`SB`'s store `movl $1, 0x10000` followed by the load `movl 0x10000, %eax` of `SB`'s second
thread): a thread that reads back its own write. Its condition, `forall 0:rax = 1`, says the
thread sees its write. `ownWriteTv` adds the certificate that lifts the bytes into CIR, as the
`litmus-x86 cir` proposer would (a store and a load at the same cell).

The theorems (`Seq.Tv.Thms`) check the certificate against the bytes and conclude, by
translation validation and the single-threaded lift, that under every model `M ⊑ XL` the x86
bytes end with `eax = 1`, from one sequential run of the CIR thread and no enumeration of
candidate executions.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Seq.Tv

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (Test)

/-- A thread reads back its own write (bytes from the corpus test `SB`). -/
def ownWrite : Test where
  name := "own-write"
  source := "SB thread 0's store and SB thread 1's load of the same cell"
  doc := "PodWR on one location, one thread"
  locs := [⟨"x", 0x10000, 4, 0x0⟩]
  threads := [
    { insns := [
        ⟨"movl $1, 0x10000", [0xc7, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00],
          some [⟨.store, 0x10000, 4, false⟩]⟩,
        ⟨"movl 0x10000, %eax", [0x8b, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00],
          some [⟨.load, 0x10000, 4, false⟩]⟩]
      regs := [] }]
  quant := .forall_
  cond := .atom (.reg 0 .rax 32 0x1)
  coverage := .tso
  tso := some .forbidden
  xl := .forbidden
  sc := some .forbidden
  basis := "one thread; by the single-threaded lift the outcome eax != 1 is forbidden under every model"

/-- `ownWrite` with its CIR certificate. -/
def ownWriteTv : TvTest where
  test := ownWrite
  certs := [
    { pro := [],
      items := [
        -- movl $1, 0x10000
        ⟨11, [.store .rel 4 .wb (.lit 0x10000) (.lit 0x1)]⟩,
        -- movl 0x10000, %eax
        ⟨7, [.load .rax .acq 4 .wb (.lit 0x10000)]⟩] }]

/-- The non-vacuity check for `ownWrite`: the bytes extract to one thread's
traces, every extracted action is `ActOk`, and some trace replays sequentially from the initial
memory. By `axReach_one_iff` this gives `ownWrite` a behaviour under every `SC ⊑ M ⊑ XL`, so
`ownWrite_eax` is not vacuous. -/
def ownWriteCheck : Bool :=
  match ownWrite.traces with
  | some [T] => decide (∀ tr ∈ T, ∀ a ∈ tr.acts, ActOk a) &&
      T.any fun tr => (actsReplay ownWrite.initMem tr.acts).isSome
  | _ => false

end Silmaril.X86.Concurrency.Cir.Seq.Tv
