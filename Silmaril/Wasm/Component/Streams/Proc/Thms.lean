module

public import Silmaril.Wasm.Component.Streams.Proc.Defs
public import Silmaril.Wasm.Component.Streams.Chunks.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Proc.Main

/-!
# Stream transformer components: results

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Proc.{Store,Chan,Inv,Main}`.

The pipeline `producer → transformer T → consumer` of `Silmaril.Wasm.Component.Streams.Proc`, run
over the Component Model stream built-ins (`Async.step`) in **any interleaving** of the three
components, with **any** chunking of the input by the producer, **any** batch size `N` of the
transformer and **any** read sizes of the consumer:

* **`pipeline_correct`**: when the three components have finished, the consumer holds exactly
  `T.run cs.flatten`. The result depends on the input chunks only through their concatenation:
  the free reassociation of byte chunks holds at the component level, whatever the rendezvous of
  the built-ins does to the batches.
* **`pipeline_safe`**: at every reachable point, what the consumer has received is a prefix of
  `T.run cs.flatten` (the components never emit anything wrong, even before they finish, even if
  they never finish).
* `pipeline_no_fault`: the transformer never finds its reader gone.

Instances (`T` any transformer of `Silmaril.Wasm.Component.Streams.Spec`, including composites):

* `pipeline_map`, `pipeline_filter`, `pipeline_take` (`take n` stops reading after `n` items and
  drops its readable end; the producer's next write reports `DROPPED`; the consumer still gets
  `F.take n`), `pipeline_comp` (a fused composite component behaves as the composite).
* **Lines and uniform chunks of a byte stream**: `linesV sep` (`stream<u8>` to a stream of lines,
  each a `record` of bytes) and `rechunkV n` (to records of `n` bytes, the last shorter), built as
  composites of the chunk-level rechunkers; `pipeline_lines`, `pipeline_rechunk`.

**Not covered here**: liveness (that a fair schedule finishes; only safety and correctness at
the end are proved), `tee` with two output streams as a component (`tee` is proved at the
specification level, `Tr.chan_run_tee`), chains of several transformer components (a fused
composite is covered by `pipeline_comp`), and the link to core modules through the jco adaptor.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Proofs.Wasm.Component.Streams.Proc
open scoped Silmaril.Wasm.Component.Streams.Tr

variable {σ τ : Type}

/-- **Correctness of the pipeline**: when all three components have finished, the consumer holds
exactly `T.run` of the concatenated input. -/
theorem pipeline_correct (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) (s : Sys σ)
    (h : Reach T N cs s) (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val)
    (hc : s.c = .fin acc) : acc = T.run cs.flatten :=
  fin_correct T _ s (reach_inv T N cs h) hp ht acc hc

/-- **Safety of the pipeline**: at every reachable point, the consumer's items are a prefix of
`T.run` of the concatenated input. -/
theorem pipeline_safe (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) (s : Sys σ)
    (h : Reach T N cs s) (acc : List Val)
    (hc : s.c = .recv acc ∨ s.c = .wait acc ∨ s.c = .close acc ∨ s.c = .fin acc) :
    acc <+: T.run cs.flatten :=
  prefix_safe T _ s (reach_inv T N cs h) acc hc

/-- The transformer never finds its reader gone. -/
theorem pipeline_no_fault (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) (s : Sys σ)
    (h : Reach T N cs s) : s.t ≠ .fault :=
  no_fault T _ s (reach_inv T N cs h)

/-- The chunking of the input does not matter. -/
theorem pipeline_rechunk_invariant (T : Tr σ Val Val) (N : Nat) (cs ds : List (List Val))
    (hcd : ChunkEq cs ds) (s s' : Sys σ) (h : Reach T N cs s) (h' : Reach T N ds s')
    (hp : s.p = .fin) (ht : s.t = .fin) (hp' : s'.p = .fin) (ht' : s'.t = .fin)
    (acc acc' : List Val) (hc : s.c = .fin acc) (hc' : s'.c = .fin acc') : acc = acc' := by
  rw [pipeline_correct T N cs s h hp ht acc hc, pipeline_correct T N ds s' h' hp' ht' acc' hc', hcd]

/-! ## Instances -/

theorem pipeline_map (f : Val → Val) (N : Nat) (cs : List (List Val)) (s : Sys Unit)
    (h : Reach (Tr.map f) N cs s) (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val)
    (hc : s.c = .fin acc) : acc = cs.flatten.map f := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, Tr.run_map]

theorem pipeline_filter (q : Val → Bool) (N : Nat) (cs : List (List Val)) (s : Sys Unit)
    (h : Reach (Tr.filter q) N cs s) (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val)
    (hc : s.c = .fin acc) : acc = cs.flatten.filter q := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, Tr.run_filter]

/-- **Take**: the consumer gets the first `n` items, although the transformer stops reading
after them. -/
theorem pipeline_take (n N : Nat) (cs : List (List Val)) (s : Sys Nat)
    (h : Reach (Tr.take n) N cs s) (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val)
    (hc : s.c = .fin acc) : acc = cs.flatten.take n := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, Tr.run_take]

/-- A fused composite component behaves as the composite. -/
theorem pipeline_comp (T : Tr σ Val Val) (U : Tr τ Val Val) (N : Nat) (cs : List (List Val))
    (s : Sys (σ × τ)) (h : Reach (T ⟫ U) N cs s) (hp : s.p = .fin) (ht : s.t = .fin)
    (acc : List Val) (hc : s.c = .fin acc) : acc = U.run (T.run cs.flatten) := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, Tr.run_comp']

/-! ## Lines and uniform chunks of a byte stream

The transformers `linesV` and `rechunkV` are defined in `Silmaril.Wasm.Component.Streams.Proc.Defs`.
-/

theorem flatten_singletons (xs : List Val) : (xs.map fun x => [x]).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem run_linesV (sep : Val → Bool) (xs : List Val) :
    (linesV sep).run xs = (lines sep xs).map Val.record := by
  rw [linesV, Tr.run_comp', Tr.run_comp', Tr.run_map (fun x => [x]), Tr.run_linesT,
    flatten_singletons, Tr.run_map]

theorem run_rechunkV (n : Nat) (xs : List Val) :
    (rechunkV n).run xs = (chunksOf n xs).map Val.record := by
  rw [rechunkV, Tr.run_comp', Tr.run_comp', Tr.run_map (fun x => [x]), Tr.run_rechunk,
    flatten_singletons, Tr.run_map]

/-- **The line splitter component**: the consumer gets the lines of the concatenated input,
whatever the chunking and the read sizes. -/
theorem pipeline_lines (sep : Val → Bool) (N : Nat) (cs : List (List Val))
    (s : Sys ((Unit × List Val) × Unit)) (h : Reach (linesV sep) N cs s) (hp : s.p = .fin)
    (ht : s.t = .fin) (acc : List Val) (hc : s.c = .fin acc) :
    acc = (lines sep cs.flatten).map Val.record := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, run_linesV]

/-- **The uniform rechunker component.** -/
theorem pipeline_rechunk (n N : Nat) (cs : List (List Val)) (s : Sys ((Unit × List Val) × Unit))
    (h : Reach (rechunkV n) N cs s) (hp : s.p = .fin) (ht : s.t = .fin) (acc : List Val)
    (hc : s.c = .fin acc) : acc = (chunksOf n cs.flatten).map Val.record := by
  rw [pipeline_correct _ N cs s h hp ht acc hc, run_rechunkV]

end Silmaril.Wasm.Component.Streams.Proc
