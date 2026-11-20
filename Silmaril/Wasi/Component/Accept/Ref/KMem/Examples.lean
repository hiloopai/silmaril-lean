module

public import Silmaril.Wasi.Component.Accept.Ref.Examples
public import Silmaril.Wasm.Component.Engine.Core3K.Thms
public import Silmaril.Wasi.Component.Accept.Ref.Transfer.Thms

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
`core3 neverFail`. The REF machine simulation (`Machine.Transfer`) carries the run over:

* `hi_mem_of_progRel`: `"hi!"` is in `refBytesSystem` over `core3 neverFail`, if the acceptor's
  dispatcher and its linked instantiation programs over `core3K neverFail` and `core3 neverFail`
  are related (`DispatchRel`, `ProgRel` for `core3Sim neverFail KMem`).
* `hi_mem`: both hypotheses hold (`Ref.Transfer.accepted_of_storeSim`), so **`"hi!"` is in
  `refBytesSystem` over `core3 neverFail`** with no hypothesis. The only computation is the
  kernel run `runHiK_true` over `KMem` memories. This supersedes `Ref.Examples.hi_mem_of_runHi`,
  whose hypothesis is the native `#guard runHi` over `ByteArray` memories.
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

open Silmaril.Wasm.Component.Machine.Transfer in
/-- **`"hi!"` is in `refBytesSystem` over `core3 neverFail`, given related programs**: the
kernel-checked run on `KMem` (`acceptedK_hi`) carried over by `accepted_of_withStore`. Both
hypotheses hold (`hi_mem`). -/
theorem hi_mem_of_progRel
    (hd : DispatchRel (core3Sim Silmaril.Wasm.SingleThreaded.neverFail Silmaril.Wasm.Execution.KMem)
      (dispatch (E := core3K Silmaril.Wasm.SingleThreaded.neverFail)) (dispatch (E := Eng)))
    (hp : ∀ c, ProgRel (core3Sim Silmaril.Wasm.SingleThreaded.neverFail Silmaril.Wasm.Execution.KMem)
      (acceptLinkedProg (E := core3K Silmaril.Wasm.SingleThreaded.neverFail) c)
      (acceptLinkedProg (E := Eng) c)) :
    refBytesSystem first.prof acceptHiBytes hi :=
  let ⟨_, ha, hacc⟩ := acceptedK_hi
  (refBytesSystem_of_decode ha).2 (accepted_of_withStore _ hd (hp _) hacc)

/-- **`"hi!"` is in `refBytesSystem` over `core3 neverFail`**: the kernel-checked run on the
`KMem` engine (`runHiK_true`, `acceptedK_hi`) carried to the `ByteArray` engine by the REF
machine simulation for `core3Sim neverFail KMem` (`accepted_of_storeSim`). -/
theorem hi_mem : refBytesSystem first.prof acceptHiBytes hi :=
  let ⟨_, ha, hacc⟩ := acceptedK_hi
  (refBytesSystem_of_decode ha).2
    (accepted_of_storeSim (core3Sim Silmaril.Wasm.SingleThreaded.neverFail
      Silmaril.Wasm.Execution.KMem) hacc)

end Silmaril.Wasi.Accept.Ref.Examples
