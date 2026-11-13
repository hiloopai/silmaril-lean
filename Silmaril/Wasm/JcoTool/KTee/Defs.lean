module

public import Silmaril.Wasm.JcoTool.KDrop.Defs

/-!
# A generated tee: a core module with one input and two output streams

`KDrop.genD` generates the module of a byte kernel: one input stream, one output stream. The tee
of the stream tests (`wasm-streams-gen tee`, `KernelWat.teeWat`) was a text template with a
byte-level certificate and no semantics. This module gives a **generated tee**, `genT N`, in the
same fragment as `genD` (`KCore.S`, run by `KDrop.dexec` over the drop-faithful built-ins of
`Streams.Drop`, under the callback runtime `KDrop.DRStep`), and the relation `RelT` with the state
of a `Net` node with one input and **two** outputs (`teeNode`), the node whose transformer is
`trB` (every item as the `u8` of its byte: on a byte stream, the identity).

## The module

The lift (`entryT`) creates two streams (`stream.new` twice), a waitable set, returns the two
readable ends with one `task.return` of two values, and joins the input and both writable ends
to the set. The callback (`cbT`) keeps the state of the `Net` node in memory and globals:

* the bytes `RS` (input: `0` idle, `1` read pending, `2` ended, `3` dropped) and `O j` (output
  `j`: `0` idle, `1` write pending, `2` dead, `3` dropped) at addresses `0x10`, `0x11`, `0x12`;
* `LEN`: the bytes of the current batch in the input buffer at `IN = 0x100`; `OFF j`: how many of
  them output `j` has written;
* the handles: `INSR`, `W0` (global `OUTSW`), `W1`, and the waitable set `WS`.

An invocation with an event updates that state and returns `YIELD`; an invocation after `YIELD`
performs **at most one built-in**, the first of: write the rest of the batch to output `0`, to
output `1`; read the next batch (when neither output has a pending write and not both are dead);
drop the input (it ended, or both outputs are dead); drop an output (the input is dropped and the
output is written or dead); `EXIT` when everything is dropped; otherwise `WAIT`. So every step of
the runtime is one step of the node program `Net.NStep` of `teeNode`, or changes neither the store
nor the node (`KTee.Thms`, `step_sim`).

What is modelled, as for `genD`: the fragment's semantics `dexec` stands for WebAssembly's; the
runtime delivers well-formed events (`KDrop.wfD`); the lift's prologue is the network's setup
store (`Net.initStore`), not run.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node rh wh)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop (isE andE)

/-! ## Layout -/

/-- Globals: the batch length, the two offsets, the second output's writable end. The input's
readable end is `KCore.INSR`, the first output's writable end `KCore.OUTSW`, the set `KCore.WS`. -/
def LENg : Nat := 0
def OFF0 : Nat := 1
def OFF1 : Nat := 2
def W1g : Nat := 3

/-- The offset of output `j`. -/
def OFFg (j : Nat) : Nat := if j = 0 then OFF0 else OFF1

/-- The writable end of output `j`. -/
def WHg (j : Nat) : Nat := if j = 0 then OUTSW else W1g

/-- Memory: the input's state byte and the outputs' state bytes. -/
def aRS : Nat := 0x10
def aO (j : Nat) : Nat := 0x11 + j

/-! ## The code -/

/-- A state byte. -/
def ldA (a : Nat) : E := .ld8 (.c a)

/-- `a ∨ b` on `0/1` values. -/
def orE (a b : E) : E := .bin .ne (.bin .add a b) (.c 0)

/-- `2` when the packed result `p` is `DROPPED`, else `0`: the input state after a read. -/
def endedOf (p : E) : E :=
  .bin .add (.bin .ne (.bin .remu p (.c 16)) (.c 0)) (.bin .ne (.bin .remu p (.c 16)) (.c 0))

/-- After a read with packed result `p`: the batch is the bytes received; the input is idle, or
ended on `DROPPED`. -/
def onR (p : E) : S :=
  seqs [.gset LENg (.bin .divu p (.c 16)), .gset OFF0 (.c 0), .gset OFF1 (.c 0),
    .st8 (.c aRS) (endedOf p)]

/-- After a write of output `j` with packed result `p`: `DROPPED` makes it dead; `COMPLETED`
advances its offset (at most to the batch's end) and makes it idle. -/
def onW (j : Nat) (p : E) : S :=
  .ite (.bin .remu p (.c 16)) (.st8 (.c (aO j)) (.c 2))
    (.seq
      (.ite (.bin .geu (.bin .divu p (.c 16)) (.bin .sub (.g LENg) (.g (OFFg j))))
        (.gset (OFFg j) (.g LENg))
        (.gset (OFFg j) (.bin .add (.g (OFFg j)) (.bin .divu p (.c 16)))))
      (.st8 (.c (aO j)) (.c 0)))

/-- Output `j` is idle with bytes of the batch left to write. -/
def wrG (j : Nat) : E := andE (isE (ldA (aO j)) 0) (.bin .ltu (.g (OFFg j)) (.g LENg))

/-- Write the rest of the batch to output `j`. -/
def actW (j : Nat) : S :=
  seqs [.call .streamWrite [.g (WHg j), .bin .add (.c IN) (.g (OFFg j)),
      .bin .sub (.g LENg) (.g (OFFg j))] [LR],
    .ite (isE (.l LR) blocked) (.st8 (.c (aO j)) (.c 1)) (onW j (.l LR)), yield_]

/-- The input is idle, no output has a pending write, and not both are dead. -/
def rdG : E :=
  andE (isE (ldA aRS) 0) (andE (.bin .ne (ldA (aO 0)) (.c 1))
    (andE (.bin .ne (ldA (aO 1)) (.c 1)) (.eqz (andE (isE (ldA (aO 0)) 2) (isE (ldA (aO 1)) 2)))))

/-- Read the next batch of up to `N` bytes. -/
def actR (N : Nat) : S :=
  seqs [.gset LENg (.c 0), .gset OFF0 (.c 0), .gset OFF1 (.c 0),
    .call .streamRead [.g INSR, .c IN, .c N] [LR],
    .ite (isE (.l LR) blocked) (.st8 (.c aRS) (.c 1)) (onR (.l LR)), yield_]

/-- The input has ended, or it is idle and both outputs are dead. -/
def stopG : E :=
  orE (isE (ldA aRS) 2) (andE (isE (ldA aRS) 0) (andE (isE (ldA (aO 0)) 2) (isE (ldA (aO 1)) 2)))

/-- Drop the input. -/
def actStop : S := seqs [.call .dropR [.g INSR] [], .st8 (.c aRS) (.c 3), yield_]

/-- The input is dropped and output `j` is written or dead. -/
def closeG (j : Nat) : E :=
  andE (isE (ldA aRS) 3)
    (orE (andE (isE (ldA (aO j)) 0) (.bin .geu (.g (OFFg j)) (.g LENg))) (isE (ldA (aO j)) 2))

/-- Drop output `j`. -/
def actClose (j : Nat) : S := seqs [.call .dropW [.g (WHg j)] [], .st8 (.c (aO j)) (.c 3), yield_]

/-- Everything is dropped. -/
def exitG : E := andE (isE (ldA aRS) 3) (andE (isE (ldA (aO 0)) 3) (isE (ldA (aO 1)) 3))

/-- **An invocation after `YIELD`**: at most one built-in, then `YIELD`; or `EXIT`; or `WAIT`. -/
def readyT (N : Nat) : S :=
  .ite (wrG 0) (actW 0) <| .ite (wrG 1) (actW 1) <| .ite rdG (actR N) <| .ite stopG actStop <|
    .ite (closeG 0) (actClose 0) <| .ite (closeG 1) (actClose 1) <|
    .ite exitG (.ret (.c 0)) (.ret waitCode)

/-- A read event of the input: the batch received (`DROPPED` ends the input), or `DROPPED`
(count `0`) on the idle input. -/
def evR : S :=
  .ite (isE (ldA aRS) 1) (.seq (onR (.l 2)) yield_)
    (.ite (andE (isE (ldA aRS) 0) (isE (.bin .divu (.l 2) (.c 16)) 0))
      (.seq (.st8 (.c aRS) (endedOf (.l 2))) yield_) .unreachable)

/-- A write event of output `j`: the pending write's result, or `DROPPED` on the idle output. -/
def evW (j : Nat) : S :=
  .ite (isE (ldA (aO j)) 1) (.seq (onW j (.l 2)) yield_)
    (.ite (isE (ldA (aO j)) 0)
      (.seq (.ite (.bin .remu (.l 2) (.c 16)) (.st8 (.c (aO j)) (.c 2)) .nop) yield_) yield_)

/-- **The callback**: dispatch on the event's code and handle. -/
def cbT (N : Nat) : S :=
  .ite (andE (isE (.l 0) 2) (.bin .eq (.l 1) (.g INSR))) evR <|
    .ite (andE (isE (.l 0) 3) (.bin .eq (.l 1) (.g (WHg 0)))) (evW 0) <|
    .ite (andE (isE (.l 0) 3) (.bin .eq (.l 1) (.g (WHg 1)))) (evW 1) <|
    .ite (isE (.l 0) 0) (readyT N) .unreachable

/-- **The lift** `[async-lift]name (in) -> code`: two result streams, the waitable set,
`task.return` of both readable ends, the three joins; then `YIELD`. -/
def entryT : S :=
  seqs [.call .streamNew [] [1, 2], .call .streamNew [] [3, 4], .gset INSR (.l 0),
    .gset OUTSW (.l 2), .gset W1g (.l 4), .call .wsNew [] [5], .gset WS (.l 5),
    .call .taskReturn [.l 1, .l 3] [],
    .call .join [.g INSR, .g WS] [], .call .join [.g OUTSW, .g WS] [], .call .join [.g W1g, .g WS] [],
    yield_]

/-- **The generated tee**, reading up to `N` bytes at a time. -/
def genT (N : Nat) : Prog := ⟨entryT, cbT N, fun _ => 0⟩

/-- The machine after the lift, in a network: input `r`, outputs `w₀`, `w₁`, set `s`. -/
def initMST (r w₀ w₁ s : Nat) : MS :=
  ⟨upd (upd (upd (upd (fun _ => 0) INSR r) OUTSW w₀) W1g w₁) WS s, fun _ => 0, none, .ready⟩

/-! ## The node it runs -/

/-- An item as the `u8` of its byte (the canonical ABI's view of a `u8` stream). -/
def nrm (v : Val) : Val := u8v (byteOf v)

/-- **The tee's transformer**: every item as the `u8` of its byte (the identity on `u8`s). -/
def trB : Tr Unit Val Val := Tr.map nrm

/-- **The tee node**: input `a`, outputs `b` and `c`. -/
def teeNode (a b c : Nat) : Node := ⟨Unit, trB, some a, [b, c]⟩

/-! ## The relation with the node -/

/-- The bytes output `j` still has to write: bytes `OFF j .. LEN` of the batch. -/
def qOf (ms : MS) (j : Nat) : List Val := ((slice ms.m IN (ms.g LENg)).drop (ms.g (OFFg j))).map u8v

/-- Output `j`'s state byte against the node's output (a pending write has bytes to write). -/
def ORel (ms : MS) (j : Nat) (o : Silmaril.Wasm.Component.Streams.Net.Out) : Prop :=
  (ms.m (aO j) = 0 ∧ o.st = .idle (qOf ms j)) ∨
    (ms.m (aO j) = 1 ∧ o.st = .busy (qOf ms j) [] ∧ qOf ms j ≠ []) ∨
    (ms.m (aO j) = 2 ∧ o.st = .dead) ∨ (ms.m (aO j) = 3 ∧ ∃ d, o.st = .closed d)

/-- The input's state byte against the node's input side. -/
def IRel (r : Nat) (ms : MS) (x : NSt Unit) : Prop :=
  (ms.m aRS = 0 ∧ x.rd = .idle ∧ ms.rp = none) ∨
    (ms.m aRS = 1 ∧ x.rd = .busy ∧ ms.rp = some (r, IN) ∧ ms.g LENg = 0) ∨
    (ms.m aRS = 2 ∧ x.rd = .ended ∧ ms.rp = none) ∨
    (ms.m aRS = 3 ∧ (∃ b, x.rd = .gone b) ∧ ms.rp = none)

/-- The handles and the bounds of the batch. -/
def okT (ms : MS) (r w₀ w₁ s : Nat) : Prop :=
  ms.g INSR = r ∧ ms.g OUTSW = w₀ ∧ ms.g W1g = w₁ ∧ ms.g WS = s ∧ ms.g LENg ≤ 256 ∧
    ms.g OFF0 ≤ ms.g LENg ∧ ms.g OFF1 ≤ ms.g LENg

/-- **The simulation relation** between the tee's machine and the state of `teeNode a b c`
(readable end `r`, writable ends `w₀`, `w₁`, waitable set `s`). -/
def RelT (r w₀ w₁ s : Nat) (ms : MS) (x : NSt Unit) : Prop :=
  x.outs.length = 2 ∧
  if ms.mode = .exited then
    (∃ b, x.rd = .gone b) ∧ ∀ j, j ≤ 1 → ∃ o d, x.outs[j]? = some o ∧ o.st = .closed d
  else
    (ms.mode = .ready ∨ ms.mode = .waiting s) ∧ okT ms r w₀ w₁ s ∧ IRel r ms x ∧
      ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ ORel ms j o

end Silmaril.Wasm.JcoTool.KTee
