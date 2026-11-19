module

public import Silmaril.Containers.Adapter.Defs
public import Silmaril.Containers.Runtime.Defs

/-! # Experimental higher-order executor certificates

The parameters may be synchronous component strategies, hosts and contexts. A certificate
quantifies universally over the declared supported guests and admitted environments. It
requires validation/loading, simulation, source noUB and nonvacuity separately. It is not a
claim about Wasmtime, x86 hosting Wasm, every WIT interface, or termination. -/

@[expose] public section
namespace Silmaril.Containers

structure Executor (Guest Host Context Program E F : Type) where
  runtime : Runtime (Guest × Host × Context) Program E
  supported : Guest → Prop
  valid : Guest → Prop
  admits : Guest → Host → Context → Prop
  linked : Guest → Host → Context → Model F
  observe : Adapter E F

namespace Executor
variable {G H C P E F : Type}

/-- All supported guests, and **all** admitted hosts/contexts. `covered` prevents empty host
assumptions; `nonempty` prevents an executor with no runs from proving everything. -/
structure Certificate (x : Executor G H C P E F) : Prop where
  supported_exists : ∃ g, x.supported g
  covered : ∀ g, x.supported g → ∃ h c, x.admits g h c
  validates : ∀ g, x.supported g → x.valid g
  loads : ∀ g h c, x.supported g → x.admits g h c →
    ∃ p, x.runtime.load (g, h, c) = .ok p
  nonempty : ∀ g h c, x.supported g → x.admits g h c → ∃ b, x.runtime.beh (g, h, c) b
  noHostUB : ∀ g h c, x.supported g → x.admits g h c → (x.runtime.beh (g, h, c)).Sat Spec.noUB
  simulates : ∀ g h c, x.supported g → x.admits g h c →
    ∀ b, x.runtime.beh (g, h, c) b → x.linked g h c (x.observe.run b)

/-- A separate, model-relative progress obligation. A safety certificate does not imply it. -/
def Progress (x : Executor G H C P E F) (assumption : G → H → C → Spec E)
    (goal : Spec E) : Prop :=
  ∀ g h c, x.supported g → x.admits g h c →
    (x.runtime.beh (g, h, c)).Sat (Spec.under (assumption g h c) goal)

end Executor
end Silmaril.Containers
