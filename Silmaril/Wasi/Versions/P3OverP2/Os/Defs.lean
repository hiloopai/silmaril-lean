module

public import Silmaril.Wasi.Versions.P3OverP2.Impl.Defs
public import Silmaril.Wasi.Versions.P2.Os.Defs

@[expose] public section

/-!
# WASI 0.3 over 0.2: the OS image of the composite

The composite `link η p3OverP2` answers the 0.3 calls of a guest; its 0.3 stdout bytes are
`P3.osTrace3 ch` of its answers (the bytes a stdout stream accepted, at once or through a
`stream-write` event). The 0.2 host below it sees the component's 0.2 calls; their OS image is
`P2.osTrace2 ch` of the host's answers (`write` and `blocking-write-and-flush` that succeeded),
the 0.2 side of the IoSpec bridge. `Silmaril.Wasi.Versions.P3OverP2.Os.Thms` relates the
two.

* `osImg2 ch`: the 0.2 image as a theory of the 0.2 host: it accepts what `pointwise P2.p2Ok`
  accepts (so `get-stdout` answers a handle), and its state is the 0.2 image so far.
* `osG3 ch`: the 0.3 image as a guarantee: its state is the state of `osStep3`, the 0.3 image
  so far, the number of answers, and whether the run has left the class `PollDone`.
* **`PollDone t`**: runs where the poll loop finishes: no `stream.write` was answered
  `BLOCKED` (every stdout write got a budget within `rounds` polls, or failed), and fewer than
  `2^29` answers (so that the component always has handles to allocate).
* `settled x`: no export call is running at the end of the export events `x`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Process.LPS (Word Event)

/-- **The 0.2 OS image as a theory of the 0.2 host.** -/
def osImg2 (ch : Word) : Protocol (List Event) WEv :=
  ⟨[], fun q e => if P2.p2Ok e then some (q ++ P2.osEv2 ch e) else none⟩

/-- A `stream.write` answered `BLOCKED`. -/
def blockedW : WEv → Bool
  | .imp f _ (some [pv]) => decide (f = cStreamWrite) && decide (natOf pv = some blocked)
  | _ => false

/-- The bound on the number of 0.3 answers. -/
def osBound : Nat := 2 ^ 29

/-- **Runs where the poll loop finishes.** -/
def PollDone (t : List WEv) : Prop := t.length < osBound ∧ ∀ e ∈ t, blockedW e = false

/-- The state of the 0.3 image guarantee. -/
structure Os3St where
  os : OsSt := {}
  img : List Event := []
  n : Nat := 0
  bad : Bool := false

/-- **The 0.3 OS image as a guarantee** (it accepts every run). -/
def osG3 (ch : Word) : Protocol Os3St WEv :=
  ⟨{}, fun q e => some ⟨(osStep3 ch q.os e).1, q.img ++ (osStep3 ch q.os e).2, q.n + 1,
    q.bad || blockedW e || decide (osBound ≤ q.n + 1)⟩⟩

/-- No export call is running at the end of the export events `x`. -/
def settled (x : List WEv) : Bool :=
  match x.getLast? with
  | some (.call _ _) => false
  | _ => true

end Silmaril.Wasi.Versions.P3OverP2
