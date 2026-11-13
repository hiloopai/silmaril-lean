module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.Basic
public import Silmaril.Proofs.Wasm.LimeCompile.SimLift.Basic

/-!
# The passive-data store relation: sessions

The session relation `SRelI K` (and its converse) has the export and invocation parts of
`SessTransport` (`sessTransport_fwd`, `sessTransport_back`): the two instances export the same
function addresses, and related stores accept the same invocations. The run and divergence
parts are hypotheses.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc?)
open Silmaril.Wasm.LimeCompile.SimLift Silmaril.Wasm.LimeCompile.PassiveEquiv

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Sessions from source to target, given run and divergence transport. -/
theorem sessTransport_fwd {K : Ctx}
    (hrun : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, SRelI K s t →
      exportFunc? K.mi x = some a → InvokeOk s a vs →
      RunTransport P host (SRelI K) (invoke s a vs) (invoke t a vs))
    (hdiv : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, SRelI K s t →
      exportFunc? K.mi x = some a → InvokeOk s a vs → Diverges P host (invoke s a vs) →
      Diverges P host (invoke t a vs)) :
    SessTransport P host (SRelI K) K.mi K.mi' :=
  ⟨exportFunc?_mi' K, fun h hx => SRel.invokeOk_iff h.1 hx _, hrun, hdiv⟩

/-- Sessions from target to source, given run and divergence transport. -/
theorem sessTransport_back {K : Ctx}
    (hrun : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, SRelI K s t →
      exportFunc? K.mi x = some a → InvokeOk t a vs →
      RunTransport P host (fun t s => SRelI K s t) (invoke t a vs) (invoke s a vs))
    (hdiv : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, SRelI K s t →
      exportFunc? K.mi x = some a → InvokeOk t a vs → Diverges P host (invoke t a vs) →
      Diverges P host (invoke s a vs)) :
    SessTransport P host (fun t s => SRelI K s t) K.mi' K.mi :=
  ⟨fun x => (exportFunc?_mi' K x).symm,
    fun h hx => (SRel.invokeOk_iff h.1 (by rw [← exportFunc?_mi']; exact hx) _).symm,
    fun h hx hok => hrun h (by rw [← exportFunc?_mi']; exact hx) hok,
    fun h hx hok hd => hdiv h (by rw [← exportFunc?_mi']; exact hx) hok hd⟩

end Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv
