module

public import Silmaril.Wasm.Component.Streams.Live.Defs
public import Silmaril.Wasm.Component.Streams.Pipes.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Live.Main

/-!
# Liveness of stream networks

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Live.{Pos,Pot,Ready,Progress,Main}`.

For a well-formed network whose nodes are numbered along the streams (`Network.Topo`), with a
consistent assignment `L` of specifications to the nodes (`Consistent`: a source reads `[]`, a
node reads its writer's `T.run` of the writer's specification):

* **termination** (`reach_pot_lt`): every step of every node, from every reachable system,
  strictly decreases the natural number `pot`; so no execution is infinite, whatever the
  scheduler, the read sizes, the write sizes and the choices of `waitable-set.wait`;
* **progress** (`reach_progress`): a reachable system in which some node has not finished can
  step: no deadlock, even with the Component Model's drop behaviour (`DROPPED` with a count,
  `DROPPED` on idle ends);
* **liveness under every scheduler** (`exec_done`): every maximal execution reaches, within
  `pot (init net)` steps, a system where every node has dropped its readable end and closed its
  writable ends, and stays there (`done_stuck`). A fair scheduler is a special case: since every
  execution terminates, fairness is not needed.

Instances: `pipe_live` discharges the frozen `Pipes.PipeLive`; `pipe_exec_correct`,
`chain_exec_correct` and `tee_exec_correct`: every maximal execution ends with the sinks holding
`T.run xs`, `U.run (T.run xs)`, and `T.run xs` and `U.run xs`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Pipes
open Silmaril.Proofs.Wasm.Component.Streams.Live

variable {σ τ : Type}

theorem _root_.Silmaril.Wasm.Component.Streams.Net.Network.Topo.of_check {net : Network}
    (h : net.topoCheck = true) : net.Topo := by
  intro c hc
  have := List.all_eq_true.1 h c (List.mem_range.2 hc)
  simpa using this

/-! ## The general theorems -/

/-- **Termination**: every step from a reachable system decreases the potential. -/
theorem reach_pot_lt {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    {s s' : Sys net} (h : Reach net s) (hs : Step net s s') :
    pot (bB S) (bBo S) s' < pot (bB S) (bBo S) s :=
  Silmaril.Proofs.Wasm.Component.Streams.Live.reach_pot_lt S h hs

/-- **No infinite execution.** -/
theorem no_infinite_run {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    (r : Nat → Sys net) (h0 : Reach net (r 0)) : ¬ ∀ n, Step net (r n) (r (n + 1)) := by
  intro hs
  have hreach : ∀ n, Reach net (r n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact Steps.tail ih (hs n)
  have hdec : ∀ n, pot (bB S) (bBo S) (r n) + n ≤ pot (bB S) (bBo S) (r 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := reach_pot_lt S (hreach n) (hs n)
      omega
  have := hdec (pot (bB S) (bBo S) (r 0) + 1)
  omega

/-- **Progress**: no deadlock before every node has finished. -/
theorem reach_progress {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    {s : Sys net} (h : Reach net s) (hnd : ¬ s.AllDone) : Enabled net s :=
  Silmaril.Proofs.Wasm.Component.Streams.Live.reach_progress S h hnd

/-- **Liveness (possibility)**: from every reachable system some steps finish every node. -/
theorem reach_done {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    {s : Sys net} (h : Reach net s) : ∃ s', Steps net s s' ∧ s'.AllDone :=
  Silmaril.Proofs.Wasm.Component.Streams.Live.reach_done S _ s h rfl

/-- **Liveness under every scheduler**: every maximal execution finishes every node within
`pot (init net)` steps and stays there. -/
theorem exec_done {net : Network} {L : Fin net.k → List Val} (S : Setting net L)
    {r : Nat → Sys net} (hr : Exec net r) :
    ∃ n, n ≤ pot (bB S) (bBo S) (init net) ∧ ∀ m, n ≤ m → r m = r n ∧ (r m).AllDone :=
  Silmaril.Proofs.Wasm.Component.Streams.Live.exec_done S hr

/-! ## Pipes, chains and tees -/

/-- The specifications of the pipe's nodes. -/
def pipeL (xs : List Val) (T : Tr σ Val Val) : Fin 3 → List Val :=
  fun i => if i.val = 0 then [] else if i.val = 1 then xs else T.run xs

theorem pipe_setting (xs : List Val) (T : Tr σ Val Val) :
    Setting (pipe xs T) (pipeL xs T) where
  wf := pipe_wf xs T
  topo := Network.Topo.of_check rfl
  cons := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact ⟨fun _ => rfl, (fun c h => by cases h)⟩
    | 1, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | 2, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | n + 3, h => exact absurd (show n + 3 < 3 from h) (by omega)

/-- **`Pipes.PipeLive`, proved**: from every reachable system of a pipe, some steps lead to
the sink having dropped its input (and so holding `T.run xs`, by `pipe_correct`). -/
theorem pipe_live : Pipes.PipeLive := by
  intro σ xs T s h
  obtain ⟨s', hs, hd⟩ := reach_done (pipe_setting xs T) h
  exact ⟨s', hs, (hd 2).1⟩

/-- **Every maximal execution of a pipe ends with the sink holding `T.run xs`**, within
`pot (init _)` steps, whatever the scheduler. -/
theorem pipe_exec_correct (xs : List Val) (T : Tr σ Val Val) {r : Nat → Sys (pipe xs T)}
    (hr : Exec (pipe xs T) r) :
    ∃ n, n ≤ pot (bB (pipe_setting xs T)) (bBo (pipe_setting xs T)) (init (pipe xs T)) ∧
      ∀ m, n ≤ m → r m = r n ∧ (r m).AllDone ∧ ((r m).ns 2).got = T.run xs := by
  obtain ⟨n, hle, hst⟩ := exec_done (pipe_setting xs T) hr
  refine ⟨n, hle, fun m hm => ⟨(hst m hm).1, (hst m hm).2, ?_⟩⟩
  obtain ⟨b, hb⟩ := ((hst m hm).2 2).1
  exact pipe_correct xs T (exec_reach hr m) hb

/-- The specifications of the chain's nodes. -/
def chainL (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : Fin 4 → List Val :=
  fun i => if i.val = 0 then [] else if i.val = 1 then xs else if i.val = 2 then T.run xs
    else U.run (T.run xs)

theorem chain_setting (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) :
    Setting (chain xs T U) (chainL xs T U) where
  wf := chain_wf xs T U
  topo := Network.Topo.of_check rfl
  cons := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact ⟨fun _ => rfl, (fun c h => by cases h)⟩
    | 1, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | 2, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | 3, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | n + 4, h => exact absurd (show n + 4 < 4 from h) (by omega)

/-- From every reachable system of a chain, some steps lead to the sink having finished. -/
theorem chain_live (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) {s : Sys (chain xs T U)}
    (h : Reach (chain xs T U) s) : ∃ s', Steps (chain xs T U) s s' ∧ ∃ b, (s'.ns 3).rd = .gone b := by
  obtain ⟨s', hs, hd⟩ := reach_done (chain_setting xs T U) h
  exact ⟨s', hs, (hd 3).1⟩

/-- **Every maximal execution of a chain of two components** ends with the sink holding
`U.run (T.run xs)`. -/
theorem chain_exec_correct (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {r : Nat → Sys (chain xs T U)} (hr : Exec (chain xs T U) r) :
    ∃ n, ∀ m, n ≤ m → r m = r n ∧ ((r m).ns 3).got = U.run (T.run xs) := by
  obtain ⟨n, -, hst⟩ := exec_done (chain_setting xs T U) hr
  refine ⟨n, fun m hm => ⟨(hst m hm).1, ?_⟩⟩
  obtain ⟨b, hb⟩ := ((hst m hm).2 3).1
  exact chain_correct xs T U (exec_reach hr m) hb

/-- The specifications of the tee network's nodes. -/
def teeL (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : Fin 6 → List Val :=
  fun i => if i.val = 0 then [] else if i.val ≤ 3 then xs else if i.val = 4 then T.run xs
    else U.run xs

theorem tee_setting (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) :
    Setting (teeNet xs T U) (teeL xs T U) where
  wf := teeNet_wf xs T U
  topo := Network.Topo.of_check rfl
  cons := by
    intro ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact ⟨fun _ => rfl, (fun c h => by cases h)⟩
    | 1, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | 2, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; exact (Tr.run_id xs).symm)⟩
    | 3, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; exact (Tr.run_id xs).symm)⟩
    | 4, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | 5, _ => exact ⟨(fun h => by cases h), (fun c h => by cases h; rfl)⟩
    | n + 6, h => exact absurd (show n + 6 < 6 from h) (by omega)

/-- **Every maximal execution of the tee network** ends with the two sinks holding `T.run xs` and
`U.run xs`, even when one branch stops early. -/
theorem tee_exec_correct (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val)
    {r : Nat → Sys (teeNet xs T U)} (hr : Exec (teeNet xs T U) r) :
    ∃ n, ∀ m, n ≤ m → r m = r n ∧ ((r m).ns 4).got = T.run xs ∧ ((r m).ns 5).got = U.run xs := by
  obtain ⟨n, -, hst⟩ := exec_done (tee_setting xs T U) hr
  refine ⟨n, fun m hm => ⟨(hst m hm).1, ?_, ?_⟩⟩
  · obtain ⟨b, hb⟩ := ((hst m hm).2 4).1
    exact (tee_correct xs T U (exec_reach hr m)).1 b hb
  · obtain ⟨b, hb⟩ := ((hst m hm).2 5).1
    exact (tee_correct xs T U (exec_reach hr m)).2 b hb

end Silmaril.Wasm.Component.Streams.Live
