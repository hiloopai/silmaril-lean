module

public import Silmaril.Process.Mt.Drf.Defs
import Silmaril.Proofs.Process.Mt.Drf.Bridge

/-!
# The memory-model bridge: results

Everything here is proved (standard axioms only). Proofs are in
`Silmaril/Proofs/Process/Mt/Drf/Bridge.lean`.

* **`drf_sc`** (the bridge): for a system with an ownership certificate (race free modulo
  synchronisation, `Cert`), every configuration that the store-buffer machine reaches under
  TSO or XL abstracts (buffered values installed) to a configuration that the SC machine with
  atomic synchronisation reaches, and the certificate still holds there.
* **`drf_sc_drained`**: a drained buffered configuration *is* an SC-reachable configuration.
* **`drf_sc_safety`**: so every safety property proved of the SC machine with atomic
  primitives (for example by decomposing it into single-threaded problems) holds of every
  drained TSO and XL configuration.
* `tso_le_xl`, `tso_reach_xl`: the TSO machine's runs are XL runs.

The litmus tests in `Silmaril.Process.Mt.Drf.Litmus.Thms` show that the certificate is
needed. The connection from the axiomatic x86 models (`Exec.Tso`, `Exec.Xl`) to the
store-buffer machines, and the correctness of primitive implementations, are stated in
`Silmaril.Process.Mt.Drf.Prim.Defs` and `Silmaril.Process.Mt.Drf.Prim.Thms`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf

variable {S : Sys} {N : Nat} {R : Cfg S → Own → Prop}

/-- **DRF modulo synchronisation ⇒ SC, under x86-TSO and XL.** If an ownership certificate
`R` holds at the start `C0`, every configuration `C` that the store-buffer machine reaches from
`C0` (empty buffers) abstracts to a configuration the SC machine with atomic synchronisation
reaches from `C0`. The certificate holds of the abstraction, and every buffered cell is owned
by its thread. -/
theorem drf_sc (hc : Cert S N R) {M : Model} {C0 : Cfg S} {o : Own} (h0 : R C0 o)
    {C : BCfg S} (h : BReach M S N C0.toB C) :
    ScReach S N C0 (C.abs N) ∧ ∃ o', R (C.abs N) o' ∧ BufOwned N C o' :=
  Silmaril.Proofs.Process.Mt.Drf.drf_reach hc h0 h

/-- The abstraction of a drained configuration is the configuration itself. -/
theorem abs_drained {C : BCfg S} (hd : C.Drained) : C.abs N = ⟨C.ts, C.mem⟩ :=
  Silmaril.Proofs.Process.Mt.Drf.abs_drained hd

/-- **Drained TSO/XL configurations are SC configurations.** -/
theorem drf_sc_drained (hc : Cert S N R) {M : Model} {C0 : Cfg S} {o : Own} (h0 : R C0 o)
    {C : BCfg S} (h : BReach M S N C0.toB C) (hd : C.Drained) :
    ScReach S N C0 ⟨C.ts, C.mem⟩ :=
  abs_drained (N := N) hd ▸ (drf_sc hc h0 h).1

/-- **Safety transfers.** A property of every SC-reachable configuration (with atomic
primitives) holds of every drained TSO or XL configuration. -/
theorem drf_sc_safety (hc : Cert S N R) {M : Model} {C0 : Cfg S} {o : Own} (h0 : R C0 o)
    {P : Cfg S → Prop} (hP : ∀ C, ScReach S N C0 C → P C) {C : BCfg S}
    (h : BReach M S N C0.toB C) (hd : C.Drained) : P ⟨C.ts, C.mem⟩ :=
  hP _ (drf_sc_drained hc h0 h hd)

/-- The TSO machine's steps are XL steps. -/
theorem tso_le_xl {C C' : BCfg S} (h : BStep .tso S N C C') : BStep .xl S N C C' :=
  Silmaril.Proofs.Process.Mt.Drf.tso_le_xl h

/-- The TSO machine's runs are XL runs. -/
theorem tso_reach_xl {C C' : BCfg S} (h : BReach .tso S N C C') : BReach .xl S N C C' :=
  Silmaril.Proofs.Process.Mt.Drf.tso_reach_xl h

end Silmaril.Process.Mt.Drf
