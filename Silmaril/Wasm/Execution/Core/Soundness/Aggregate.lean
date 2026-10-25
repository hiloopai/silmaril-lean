module

public import Silmaril.Wasm.Execution.Core.Soundness.AggregatePres
public import Silmaril.Wasm.Execution.Core.Soundness.AggregateProgress

@[expose] public section

/-! # Soundness, aggregate family

Preservation of `AggregateStep` (the frame is unchanged; the store is extended and
stays valid) and progress for `RefInstrOk` restricted to the instructions it reduces.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- **Preservation (aggregate).** The unit's extra invariant `StoreDefsOkAgg` is
exactly `StoreOk.structsClosed`/`arraysClosed`, so it is derived from `hst`. -/
theorem AggregateStep.preservation {c c' : Config H} {C : Context} {it : InstrType}
    (hst : StateOk c.store c.frame C) (hty : AdminsOk c.store C c.code it)
    (h : AggregateStep c c') :
    c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
      AdminsOk c'.store C c'.code it := by
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    AggregateStep.preservationAgg hst ⟨hst.1.structsClosed, hst.1.arraysClosed⟩ hty h
  exact ⟨h1, h2, h3, h4⟩

/-- **Progress (aggregate).** The extra hypotheses of `progress_aggregate'` are
`StoreOk.structsClosed`/`arraysClosed`. -/
theorem RefInstrOk.progress_aggregate {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C) (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩) (ha : i.IsAggregate)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  exact RefInstrOk.progress_aggregate' hst hst.1.structsClosed hst.1.arraysClosed hi ha hvs

end Silmaril.Wasm.Execution.Core
