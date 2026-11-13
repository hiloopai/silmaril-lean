module

public import Silmaril.Servers.Reuse.Defs
public import Silmaril.Servers.Http.Defs

@[expose] public section

/-!
# Proofs: instance reuse as core machine runs

`seq_iff`: the logs of one reused instance are the histories of the origin read as a core
machine.
-/

namespace Silmaril.Proofs.Servers.PerRequest

open Silmaril.Servers Silmaril.Servers.Reuse Silmaril.Net.Http

variable {σ : Type} {O : Origin σ}

theorem seq_of_run {s s' : σ} {l : History Http.sig} (h : Machine.Run (Http.machine O) s l s') :
    Seq O s l := by
  induction h with
  | nil => exact .nil _
  | cons hq _ ih => exact .cons hq ih

theorem run_of_seq {s : σ} {l : Log} (h : Seq O s l) : ∃ s', Machine.Run (Http.machine O) s l s' := by
  induction h with
  | nil s => exact ⟨s, .nil s⟩
  | cons hq _ ih => obtain ⟨s', h⟩ := ih; exact ⟨s', .cons hq h⟩

theorem seq_iff {s : σ} {l : Log} : Seq O s l ↔ (Http.machine O).Hist s l :=
  ⟨run_of_seq, fun ⟨_, h⟩ => seq_of_run h⟩

end Silmaril.Proofs.Servers.PerRequest
