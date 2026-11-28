module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

public theorem openRequired_exact {limits : Snapshot.Limits} {input : Bytes} {source : Source limits input}
    (accepted : openRequired limits input = .ok source) :
    openFile limits input = .ok source ∧ source.schema.plan.element.nullable = false := by
  cases original : openFile limits input with
  | error => simp [openRequired, original] at accepted
  | ok opened =>
    cases nullable : opened.schema.plan.element.nullable <;>
      simp [openRequired, original, nullable] at accepted
    subst source
    exact ⟨rfl, nullable⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct
