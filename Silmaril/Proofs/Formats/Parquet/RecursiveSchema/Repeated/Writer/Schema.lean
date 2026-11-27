module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema

open Silmaril.Formats
open Parquet.RecursiveSchema.Repeated
open Parquet.RecursiveSchema.Repeated.Writer.Schema

public theorem equal_exact {depth : Nat} {left right : Arrow.RecursiveSchema.Schema}
    (checked : equal depth left right = true) : left = right :=
  Arrow.RecursiveSchema.Writer.equalSchema_exact checked

public theorem emit_wire {limits : Limits} {schema : Arrow.RecursiveSchema.Schema}
    {output : Checked limits} (written : emit limits schema = .ok output) :
    Wire limits schema output := by
  unfold emit at written
  cases planned : plan limits schema with
  | error cause => simp [planned, bind, Except.bind] at written
  | ok shape =>
    simp only [planned, bind, Except.bind] at written
    cases framed : wrap limits Bytes.empty shape [] with
    | error cause => simp [framed] at written
    | ok envelope =>
      simp only [framed] at written
      cases opened : openFile limits.snapshot envelope.bytes with
      | error cause => simp [opened, Except.mapError] at written
      | ok source =>
        simp only [opened, Except.mapError] at written
        split at written
        · rename_i exacts
          cases Except.ok.inj written
          simp only [Bool.and_eq_true, decide_eq_true_eq] at exacts
          exact ⟨planned, framed, opened, (equal_exact exacts.1).symm, exacts.2.1,
            exacts.2.2.1, exacts.2.2.2⟩
        · contradiction

public theorem wrap_bytes {limits : Limits} {payload : Bytes} {plan : Plan}
    {groups : List GroupIndex} {out : Envelope} (built : wrap limits payload plan groups = .ok out) :
    ∃ footer, out.footer = ⟨4 + payload.length, 4 + payload.length + footer.length⟩ ∧
      out.bytes = (((Parquet.Footer.magic.append payload).append footer).append
        (Bytes.ofList (KBytes.unpack 4 footer.length))).append Parquet.Footer.magic := by
  unfold wrap at built
  dsimp only at built
  split at built
  · contradiction
  · cases encoded : Compact.encode (footerCap limits (4 + payload.length)) plan groups with
    | error cause => simp [encoded, Except.mapError, bind, Except.bind] at built
    | ok suffix =>
      simp [encoded, Except.mapError, bind, Except.bind, Pure.pure, Except.pure] at built
      cases built
      exact ⟨suffix, rfl, rfl⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema
