module

public import Silmaril.Net.Http1.Connection.Defs

/-! Proofs for `Silmaril.Net.Http1.Connection.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Connection

open Silmaril.Net.Http1
open Silmaril.Parse.ByteParse (Bytes)

theorem stripHopByHop_mem {fs : List FieldLine} {f : FieldLine} (hf : f ∈ stripHopByHop fs) :
    f ∈ fs ∧ lower f.name ∉ hopByHopNames ∧ lower f.name ∉ connectionOptions fs := by
  simp only [stripHopByHop, isHopByHop, List.mem_filter, Bool.not_or, Bool.and_eq_true,
    Bool.not_eq_true'] at hf
  simpa using hf

theorem fieldValues_stripHopByHop {fs : List FieldLine} {n : Bytes}
    (hn : lower n ∈ hopByHopNames) : fieldValues (stripHopByHop fs) n = [] := by
  unfold fieldValues
  rw [List.filterMap_eq_nil_iff]
  intro f hf
  have := (stripHopByHop_mem hf).2.1
  split
  · next h => exact absurd (h ▸ hn) this
  · rfl

end Silmaril.Net.Http1.Proofs.Connection
