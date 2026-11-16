module

public import Silmaril.Wasi.Component.Accept.Ref.Examples
public import Silmaril.Wasm.Component.Engine.Core3K.Defs

/-! # Component acceptors on the reference machine over `KMem` memories (`decide +kernel`)

`Ref.Examples.acceptHiBytes` is a component whose core module has a 64 KiB linear memory with a
data segment `"hi!"`; its exported `run` calls the imported `accept: func(list<u8>)` on those
bytes. Over the `ByteArray` engine `core3 neverFail` the run is only checked natively
(`#guard runHi`), as the kernel cannot evaluate it with a 64 KiB `ByteArray` memory.

Over `core3K neverFail` (`Engine.Core3K`: the same Core 3.0 engine with memories as `KMem` trees)
the whole pipeline runs in the kernel: decoding and validation (`decodeValid`), REF root
instantiation with the host `accept`, core instantiation with the data segment, the call of
`run`, and the lift of `list<u8>` from linear memory.

* `runHiK_true`: the run records `[list<u8> "hi!"]`, checked by `decide +kernel`.
* `acceptedK_hi`: so the decoded component is `Accepted` on REF over `core3K neverFail`, by the
  executable soundness theorem `acceptRun_sound` (which holds for every core engine).

`acceptedK_hi` is a statement about REF over `core3K`. `refBytesSystem` is stated over
`core3 neverFail`; carrying REF runs from `core3K` to `core3` needs a REF-level simulation, which
is not proved yet (`docs/projects/wasm-memrep.md`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine

/-- The deterministic first-alternative oracle over the `KMem` engine. -/
abbrev firstK : Oracle (core3K Silmaril.Wasm.SingleThreaded.neverFail) := Oracle.first

/-- Instantiate, invoke `run` once on the `KMem` engine, and check that `accept` recorded
`"hi!"`. -/
def runHiK : Bool :=
  match decodeValid (prof := first.prof) acceptHiBytes with
  | none => false
  | some a =>
    match acceptRun (core3ExecK Silmaril.Wasm.SingleThreaded.neverFail) firstK 4000 a.comp
        [("run", [])] with
    | none => false
    | some st => st.any fun args => Value.Val.beqList args [bytesVal hi]

/-- **The run, in the kernel.** -/
theorem runHiK_true : runHiK = true := by decide +kernel

/-- **`"hi!"` is accepted on REF over the `KMem` engine** by the decoded binary. -/
theorem acceptedK_hi : ∃ a : RefAcceptor first.prof,
    decodeValid acceptHiBytes = some a ∧
      Accepted (E := core3K Silmaril.Wasm.SingleThreaded.neverFail) firstK.prof a.comp hi := by
  have h := runHiK_true
  unfold runHiK at h
  split at h
  · cases h
  · rename_i a ha
    split at h
    · cases h
    · rename_i st hst
      obtain ⟨args, hmem, heq⟩ := List.any_eq_true.mp h
      rw [(Value.Val.beqList_iff _ _).mp heq] at hmem
      exact ⟨a, ha, acceptRun_sound _ firstK hst hmem⟩

end Silmaril.Wasi.Accept.Ref.Examples
