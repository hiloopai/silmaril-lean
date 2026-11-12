module

public import Silmaril.Wasm.Component.Streams.Pipes.Defs
public import Silmaril.Proofs.Wasm.Component.Streams.Net.Final
public import Silmaril.Proofs.Wasm.Component.Streams.Net.Check

/-!
# Pipelines, chains and tees over the drop-faithful built-ins: correctness

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Net.{Chan,Node,Store,Main,Final,Check}` (an earlier step:
moved out of `Silmaril/Raw` and restyled to the Isar conventions). Liveness (every maximal execution
finishes) is in `Silmaril.Wasm.Component.Streams.Live`.

The networks of `Silmaril.Wasm.Component.Streams.Pipes` run over the stream built-ins of
`Silmaril.Wasm.Component.Streams.Drop`, which have the Component Model's drop behaviour (`DROPPED`
with a count; `DROPPED` notifications on idle ends). Every component dispatches on the handle of
each event it receives. The theorems quantify over **every interleaving** of the components and
**every policy** of each component: how many items each `stream.read` asks for, how many each
`stream.write` offers (so every chunking of every stream, the source's included), and the order in
which it issues reads, writes and drops; and over every choice of `waitable-set.wait` among ready
members.

* **`pipe_correct`** (the pass-1 `Proc.pipeline_correct`, carried over to the drop semantics): when
  the sink has dropped its input, it holds `T.run xs`; `pipe_safe`: at every point, a prefix.
* **`chain_correct`**: two separate transformer components in a chain: `U.run (T.run xs)`.
* **`tee_correct`**: a tee with two output streams feeding `T` and `U`: the sinks hold `T.run xs`
  and `U.run xs`. If one branch stops early (`take`), the other still gets everything.

`net_spec` is the general statement for any well-formed network: each node's input is a prefix of
the specification propagated along its stream from a source, and all of it once it saw the end.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Pipes

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Net

variable {σ τ : Type}

/-- The network is well formed (checked by evaluation). -/
theorem pipe_wf (xs : List Val) (T : Tr σ Val Val) : (pipe xs T).WF :=
  Network.WF.of_check rfl

/-- The network is well formed (checked by evaluation). -/
theorem chain_wf (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : (chain xs T U).WF :=
  Network.WF.of_check rfl

/-- The network is well formed (checked by evaluation). -/
theorem teeNet_wf (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : (teeNet xs T U).WF :=
  Network.WF.of_check rfl

/-! ## The general statement -/

/-- **Any well-formed network**: if the writer of a node's input stream has read a prefix of `L`
(all of it once its input ended), the node has read a prefix of the writer's `T.run L` (all of it
once its own input ended). Sources start the induction with `L = []`. -/
theorem net_spec {net : Network} (hwf : net.WF) {s : Sys net} (h : Reach net s) (i : Fin net.k)
    {c : Nat} (hinp : (net.node i).inp = some c) (L : List Val) (hU : SpecOK s (net.wr c).1 L) :
    SpecOK s i ((net.node (net.wr c).1).T.run L) :=
  node_spec hwf (reach_inv hwf h) i hinp L hU

/-- Sources: nothing read, end seen. -/
theorem net_src {net : Network} (hwf : net.WF) {s : Sys net} (h : Reach net s) (i : Fin net.k)
    (hinp : (net.node i).inp = none) : SpecOK s i [] :=
  src_spec (reach_inv hwf h) i hinp

/-- A sink drops its input only after the end. -/
theorem net_sink_eof {net : Network} (hwf : net.WF) {s : Sys net} (h : Reach net s) (i : Fin net.k)
    (hout : (net.node i).outs = []) (hnd : ∀ q, (net.node i).T.done q = false) {b : Bool}
    (hb : (s.ns i).rd = .gone b) : b = true :=
  sink_eof (reach_inv hwf h) i hout hnd hb

/-! ## Source → `T` → sink -/

theorem pipe_spec (xs : List Val) (T : Tr σ Val Val) {s : Sys (pipe xs T)}
    (h : Reach (pipe xs T) s) : SpecOK s 2 (T.run xs) := by
  have hwf := pipe_wf xs T
  have h0 : SpecOK s 0 [] := net_src hwf h 0 rfl
  have h1 : SpecOK s 1 xs := net_spec hwf h 1 (c := 0) rfl [] h0
  exact net_spec hwf h 2 (c := 1) rfl xs h1

/-- **Correctness of a transformer component under the drop semantics**: once the sink has
dropped its input, it holds `T.run xs`, whatever the interleaving, the chunkings, the read sizes,
and the `DROPPED` notifications (including `DROPPED` with a count when `T` stops early). -/
theorem pipe_correct (xs : List Val) (T : Tr σ Val Val) {s : Sys (pipe xs T)}
    (h : Reach (pipe xs T) s) {b : Bool} (hC : (s.ns 2).rd = .gone b) :
    (s.ns 2).got = T.run xs := by
  have hb := net_sink_eof (pipe_wf xs T) h 2 rfl (fun _ => rfl) hC
  subst hb
  exact (pipe_spec xs T h).2 hC

/-- **Safety**: at every point the sink holds a prefix of `T.run xs`. -/
theorem pipe_safe (xs : List Val) (T : Tr σ Val Val) {s : Sys (pipe xs T)}
    (h : Reach (pipe xs T) s) : (s.ns 2).got <+: T.run xs :=
  (pipe_spec xs T h).1

/-! ## Source → `T` → `U` → sink -/

theorem chain_spec (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) {s : Sys (chain xs T U)}
    (h : Reach (chain xs T U) s) : SpecOK s 3 (U.run (T.run xs)) := by
  have hwf := chain_wf xs T U
  have h0 : SpecOK s 0 [] := net_src hwf h 0 rfl
  have h1 : SpecOK s 1 xs := net_spec hwf h 1 (c := 0) rfl [] h0
  have h2 : SpecOK s 2 (T.run xs) := net_spec hwf h 2 (c := 1) rfl xs h1
  exact net_spec hwf h 3 (c := 2) rfl _ h2

/-- **A chain of two separate transformer components**: the sink gets `U.run (T.run xs)`. -/
theorem chain_correct (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {s : Sys (chain xs T U)} (h : Reach (chain xs T U) s) {b : Bool} (hC : (s.ns 3).rd = .gone b) :
    (s.ns 3).got = U.run (T.run xs) := by
  have hb := net_sink_eof (chain_wf xs T U) h 3 rfl (fun _ => rfl) hC
  subst hb
  exact (chain_spec xs T U h).2 hC

theorem chain_safe (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {s : Sys (chain xs T U)} (h : Reach (chain xs T U) s) : (s.ns 3).got <+: U.run (T.run xs) :=
  (chain_spec xs T U h).1

/-- The chain of separate components computes the fused composite `T ⟫ U`. -/
theorem chain_eq_comp (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {s : Sys (chain xs T U)} (h : Reach (chain xs T U) s) {b : Bool} (hC : (s.ns 3).rd = .gone b) :
    (s.ns 3).got = (T.comp U).run xs := by
  rw [chain_correct xs T U h hC, Tr.run_comp']

/-! ## Tee -/

theorem tee_spec (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) {s : Sys (teeNet xs T U)}
    (h : Reach (teeNet xs T U) s) : SpecOK s 4 (T.run xs) ∧ SpecOK s 5 (U.run xs) := by
  have hwf := teeNet_wf xs T U
  have h0 : SpecOK s 0 [] := net_src hwf h 0 rfl
  have h1 : SpecOK s 1 xs := net_spec hwf h 1 (c := 0) rfl [] h0
  have h2 : SpecOK s 2 xs := by
    have := net_spec hwf h 2 (c := 1) rfl xs h1
    simpa [teeNet, tee, Tr.run_id] using this
  have h3 : SpecOK s 3 xs := by
    have := net_spec hwf h 3 (c := 2) rfl xs h1
    simpa [teeNet, tee, Tr.run_id] using this
  exact ⟨net_spec hwf h 4 (c := 3) rfl xs h2, net_spec hwf h 5 (c := 4) rfl xs h3⟩

/-- **A tee with two output streams**: each sink, once it has dropped its input, holds its
branch's transformer applied to the whole input, even if the other branch stopped early. -/
theorem tee_correct (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {s : Sys (teeNet xs T U)} (h : Reach (teeNet xs T U) s) :
    (∀ b, (s.ns 4).rd = .gone b → (s.ns 4).got = T.run xs) ∧
      (∀ b, (s.ns 5).rd = .gone b → (s.ns 5).got = U.run xs) := by
  have hwf := teeNet_wf xs T U
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have := net_sink_eof hwf h 4 rfl (fun _ => rfl) hb
    subst this
    exact (tee_spec xs T U h).1.2 hb
  · have := net_sink_eof hwf h 5 rfl (fun _ => rfl) hb
    subst this
    exact (tee_spec xs T U h).2.2 hb

theorem tee_safe (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {s : Sys (teeNet xs T U)} (h : Reach (teeNet xs T U) s) :
    (s.ns 4).got <+: T.run xs ∧ (s.ns 5).got <+: U.run xs :=
  ⟨(tee_spec xs T U h).1.1, (tee_spec xs T U h).2.1⟩

/-- Instance: `take n` on one branch, `map f` on the other. The `take` branch stops after `n` items
(its reader drops, the tee's writes on it report `DROPPED`), the other gets everything. -/
theorem tee_take_map (xs : List Val) (n : Nat) (f : Val → Val) {s : Sys (teeNet xs (Tr.take n) (Tr.map f))}
    (h : Reach (teeNet xs (Tr.take n) (Tr.map f)) s) :
    (∀ b, (s.ns 4).rd = .gone b → (s.ns 4).got = xs.take n) ∧
      (∀ b, (s.ns 5).rd = .gone b → (s.ns 5).got = xs.map f) := by
  obtain ⟨h1, h2⟩ := tee_correct xs _ _ h
  exact ⟨fun b hb => by rw [h1 b hb, Tr.run_take], fun b hb => by rw [h2 b hb, Tr.run_map]⟩

end Silmaril.Wasm.Component.Streams.Pipes
