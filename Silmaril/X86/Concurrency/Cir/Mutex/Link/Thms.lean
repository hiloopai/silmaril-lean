module

public import Silmaril.X86.Concurrency.Cir.Mutex.Link.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Link

/-! # Linking any mutex at the object level: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Link`, namespace
`Silmaril.X86.Concurrency.Cir.Mutex.Link`), copied from `Link/AllocLink` with the interface
type and the spec type generalised:

* `importsClosed_iface`: in a link whose slot `ic` is an `IfaceClient` at the abstraction of
  the `IfaceUnit` at slot `ia`, the client's imports named in `names` are closed by the
  provider's exports (provided it `provides` each such name); every other import is a
  hypothesis (`AllocLink.ResolvedIn`).
* **`link_any_iface_env`**: `link_compose_env` with the client at the provider's abstraction:
  from the client's contract **for every** abstraction, the provider's family contract at the
  link point and the other units' contracts at the link point, every client export is
  `L.Safe n` for every `n`, and `Γ` is safe.
* `link_any_iface`: the `Γ = ∅` case with plain `TU.Sat` / `UnitFam.SatAt` contracts.
* **`link_any_mutex_obj`**: `link_any_iface` at `Ab := Mutex.Iface`, specs rendered by any
  `ρ : Render Spec`.

Not here: a `Render` into x86 `FnSpec` (call-level translation validation of CIR specs), and an
instance on real objects; the CIR-level theorem `Mutex.link_any_mutex` is the one used.
-/
