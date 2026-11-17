module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs

/-!
# `sysvScalar`: the by-value struct is the one the declaring header defines

Proofs for `Silmaril.Machine.Abi.Conformance.SysvScalar.Thms`: `long f(struct s)` declares
`sseProto` (`struct s` SSE, SSE) in the header where `s` is two `double`s (`tagHdrB`), and not
in the one where `s` is two `long`s (`tagHdrA`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.SystemV.Scalar (Proto Arg)

theorem declares_sse : Declares sysvScalar tagHdrB "f" sseProto := by
  refine ⟨_, (by decide +kernel :
    tagHdrB.proto? "f" = some ⟨.int .long .signed, [.struct "s"], false⟩), ?_⟩
  show lowerScalar Silmaril.Data.Layout.sysvX86_64 tagHdrB.env
    ⟨.int .long .signed, [.struct "s"], false⟩ = .ok sseProto
  have h : (lowerScalar Silmaril.Data.Layout.sysvX86_64 tagHdrB.env
      ⟨.int .long .signed, [.struct "s"], false⟩).toOption = some sseProto := by
    decide +kernel
  revert h
  cases lowerScalar Silmaril.Data.Layout.sysvX86_64 tagHdrB.env
    ⟨.int .long .signed, [.struct "s"], false⟩ <;> simp [Except.toOption]

theorem not_declares_mismatch : ¬ Declares sysvScalar tagHdrA "f" sseProto := by
  rintro ⟨cp, hcp, hl⟩
  have h : tagHdrA.proto? "f" = some ⟨.int .long .signed, [.struct "s"], false⟩ := by
    decide +kernel
  rw [h] at hcp
  cases hcp
  have := congrArg (fun e : Except String Proto =>
    e.toOption.map (·.args.map Arg.eights)) hl
  exact absurd this (by decide +kernel)

end Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar

end
