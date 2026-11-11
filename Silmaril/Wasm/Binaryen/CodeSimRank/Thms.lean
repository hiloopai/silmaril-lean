module

public import Silmaril.Wasm.Binaryen.CodeSimClosed
import Silmaril.Proofs.Wasm.Binaryen.CodeSimRank.Closed

@[expose] public section

/-! # Closed-host export equivalence from one simulation, at any lawful rank

Silmaril's `CodeSimClosed.exportEquiv_of_baseSim` (one `BaseSim` plus no host-call redex
on its left side gives export equivalence at every deterministic profile, under the closed
host) generalised from the `codeSize` rank to any `LawfulCodeRank`, as
`CodeSimRank.exportEquiv_of_baseSim_rank` (proof in
`Silmaril.Proofs.Wasm.Binaryen.CodeSimRank.Closed`). The proof is silmaril's, copied with only
the rank parameter added; an upstreaming candidate. No verified stage uses it any more:
`tee-form`, its former user, is now proved at every numerical profile through
`Silmaril.Wasm.Binaryen.Deferred`.
-/

namespace Silmaril.Wasm.Binaryen.CodeSimRank

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.CodeSimClosed
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics Silmaril

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {BI : List Instr → List Instr → Prop}
  {B : List Admin → List Admin → Prop} {rank : List Admin → Nat} [LawfulCodeRank rank]
local notation "PD" => Profile.deterministic o

/-- **Export equivalence from one simulation at any lawful rank**, under the closed host:
modules with related bodies whose left code has no host-call redex are export-equivalent
at every deterministic profile. -/
theorem exportEquiv_of_baseSim_rank (hB : BaseSim PD (closedHost (H := H)) (FuncRel BI) BI B rank)
    (hnr : NoRedexB H B) {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) PD (closedHost (H := H)) m m' :=
  Silmaril.Proofs.Wasm.Binaryen.CodeSimRank.exportEquiv_of_baseSim_rank hB hnr hrel hm hm'

end Silmaril.Wasm.Binaryen.CodeSimRank
