module

public import Silmaril.Games.Abstract.SigBridge.Defs
public import Silmaril.Games.Abstract.Machine.Thms
public import Silmaril.Games.LTS.Thms
public import Mathlib.Order.Hom.Basic

/-!
# The game `E ↠ F` as an abstract game: proofs

Proofs for `Silmaril.Games.Abstract.SigBridge.Thms`: the receptivity conditions
of strategies and of trace models agree, so strategies and trace models of
`sigGame E F` are order-isomorphic; transition systems and their machines have
the same runs, so the two state-erasure maps agree.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SigBridge

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SigBridge

universe u

variable {E F : Sig.{u}}

theorem run_ofLTS_iff {L : LTS E F} {x y : (Machine.ofLTS L).State} {s : List (Move E F)} :
    (Machine.ofLTS L).Run x s y ↔ L.Run x s y := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil _
    | tau h _ ih => exact .tau h ih
    | vis h _ ih => exact .vis h ih
  · intro h
    induction h with
    | nil => exact .nil _
    | tau h _ ih => exact .tau h ih
    | vis h _ ih => exact .vis h ih

theorem traces_ofLTS (L : LTS E F) : (Machine.ofLTS L).traces = L.Traces :=
  Set.ext fun _ => exists_congr fun _ => run_ofLTS_iff

theorem strategyIso_ofLTS (L : LTS E F) :
    strategyIso (Strategy.ofLTS L) = (Machine.ofLTS L).denote := by
  apply le_antisymm
  · rw [← strategyIso.le_symm_apply]
    refine Strategy.ofLTS_le_iff.2 fun s hs hl => ?_
    exact Machine.mem_denote_of_mem_traces (by rw [traces_ofLTS]; exact hs) hl
  · refine TraceModel.generate_le_iff.2 fun s hs hl => ?_
    rw [traces_ofLTS] at hs
    exact Strategy.mem_ofLTS_of_mem_traces hs hl

end Silmaril.Proofs.Games.Abstract.SigBridge
