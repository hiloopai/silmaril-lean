module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs

open Execution.Runtime (FuncAddr)

theorem runs_iff {A : Type} {p : Program} {f : Function} {addr : FuncAddr}
    (checked : p.Checked) (found : p.lookup addr = some f)
    (render : State → A) (native : A → A → Prop)
    (sound : ∀ {x y}, Ready p f x.phase → Step p f x y → native (render x) (render y))
    (readback : ∀ {x y}, Ready p f x.phase → native (render x) y →
      ∃ out, Step p f x out ∧ y = render out)
    {src : State} {dst : A} (ready : Ready p f src.phase) :
    Relation.ReflTransGen native (render src) dst ↔
      ∃ out, Runs p f src out ∧ Ready p f out.phase ∧ out.bytes.size = src.bytes.size ∧ dst = render out := by
  constructor
  · intro trace
    induction trace with
    | refl => exact ⟨src, .refl, ready, rfl, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, run, typed, size, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback typed step
      exact ⟨out, run.tail edge, preserve checked found edge typed, (bytes_preserved edge).trans size, rfl⟩
  · rintro ⟨out, run, _, _, rfl⟩
    have lift {y : State} (r : Runs p f src y) :
        Ready p f y.phase ∧ Relation.ReflTransGen native (render src) (render y) := by
      induction r with
      | refl => exact ⟨ready, .refl⟩
      | tail _ edge ih =>
        exact ⟨preserve checked found edge ih.1, ih.2.tail (sound ih.1 edge)⟩
    exact (lift run).2

end Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs
