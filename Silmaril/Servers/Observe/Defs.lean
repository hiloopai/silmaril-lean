module

public import Silmaril.Servers.Core.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Setoid.Basic

/-!
# Observations after initialization: behaviours, refinement and equivalence

The core (`Silmaril.Servers.Core`) reads a server as the set of request/response traces it can
be observed doing (`Model`). That reading assumes the server is up. This module adds the two
things a test harness sees besides traces, and fixes the orientation of refinement.

## Observations

An **observation** (`Obs A`) of a server from its start is one of:

* `initFail`: initialization failed (instantiation trapped, the process exited before
  accepting), so no request was accepted;
* `run t`: the server initialized and was observed doing the finite trace `t`; it may continue;
* `stop t`: the server initialized, did `t`, and then stopped (it exited or crashed and accepts
  no further event).

A **behaviour** (`Beh A`) is a set of observations. It is *healthy* (`Beh.Healthy`) when its
running traces are prefix closed and a server that stopped after `t` was running after `t`.

## What is and is not observed

All observations are finite. **Divergence** of a handler (it never answers) shows up only as
running traces with a pending request; such traces are also those of a slow server, so finite
observations do not distinguish divergence from slowness, and a timeout in a test records a
bound, not divergence. Properties over finite observations are **safety** properties
(`Beh.Must`, read universally). Eventual answers are **liveness** properties: they need infinite
runs and fairness (`Silmaril.Servers.Live`) and are not sentences here. Refinement
(`Beh.Refines`) preserves every universal property, including "initialization never fails"
(`Beh.InitSafe`), but not existential ones (`Beh.May`): the empty behaviour refines
everything (`Thms.empty_refines`), so a refinement may lose the ability to initialize.

## Orientation, preorder and quotient

`Beh.Refines I S` (implementation `I` first, specification `S` second) is `I ⊆ S`: every
observation of the implementation is allowed by the specification. **Observational
equivalence** (`Beh.Equiv`) is equality of observation sets, which is refinement both ways
(antisymmetry of `⊆`). Implementations of any kind, given a denotation `d : ι → Beh A`, are
preordered by refinement of their denotations (`implPreorder d`); the antisymmetric quotient is
`Quotient (obsSetoid d)` (same denotation), ordered by refinement (`Norm.partialOrder`), and its
elements are identified with their normalized trace languages (`norm d`, injective: `Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Observe

open Silmaril.Servers

/-- **An observation** of a server from its start. -/
inductive Obs (A : Sig) : Type where
  /-- Initialization failed: no request was accepted. -/
  | initFail
  /-- The server initialized and was observed doing `t`; it may continue. -/
  | run (t : Trace A)
  /-- The server initialized, did `t`, and stopped (exited or crashed). -/
  | stop (t : Trace A)

/-- **A behaviour**: the observations a server can produce. -/
abbrev Beh (A : Sig) : Type := Set (Obs A)

namespace Beh

variable {A : Sig}

/-- **Refinement**, implementation first: every observation of `I` is one of `S`. -/
def Refines (I S : Beh A) : Prop := I ⊆ S

/-- **Observational equivalence**: the same observations. -/
def Equiv (I S : Beh A) : Prop := ∀ o, o ∈ I ↔ o ∈ S

/-- The running traces of a behaviour, as a core model. -/
def traces (B : Beh A) : Model A := ⟨fun t => Obs.run t ∈ B⟩

/-- The behaviour of a core model that always initializes and never stops. -/
def ofModel (M : Model A) : Beh A := {o | ∃ t, o = .run t ∧ M.Tr t}

/-- The behaviour of a core model whose initialization may fail (when `canFail`). -/
def withInit (canFail : Prop) (M : Model A) : Beh A :=
  {o | (o = .initFail ∧ canFail) ∨ ∃ t, o = .run t ∧ M.Tr t}

/-- **Healthy**: running traces are prefix closed, and a stopped server was running. -/
def Healthy (B : Beh A) : Prop :=
  (∀ t t', Obs.run (t ++ t') ∈ B → Obs.run t ∈ B) ∧ (∀ t, Obs.stop t ∈ B → Obs.run t ∈ B)

/-- **Must**: every observation satisfies `φ` (a universal, safety reading). -/
def Must (B : Beh A) (φ : Obs A → Prop) : Prop := ∀ o ∈ B, φ o

/-- **May**: some observation satisfies `φ` (an existential reading). -/
def May (B : Beh A) (φ : Obs A → Prop) : Prop := ∃ o ∈ B, φ o

/-- Initialization never fails. -/
def InitSafe (B : Beh A) : Prop := Must B fun o => o ≠ .initFail

/-- The server never stops. -/
def NoStop (B : Beh A) : Prop := Must B fun o => ∀ t, o ≠ .stop t

/-- The server can initialize. -/
def CanInit (B : Beh A) : Prop := May B fun o => ∃ t, o = .run t

end Beh

/-- A trace sentence read on observations: failed initialization satisfies it vacuously, and a
running or stopped observation satisfies it when its trace does. -/
def Obs.sen {A : Sig} (φ : Sen A) : Obs A → Prop
  | .initFail => True
  | .run t => φ t
  | .stop t => φ t

/-- **A safety sentence**: closed under prefixes. -/
def Sen.Safety {A : Sig} (φ : Sen A) : Prop := ∀ t t', φ (t ++ t') → φ t

/-! ## Implementations: the refinement preorder and its quotient -/

section Impl

variable {A : Sig} {ι : Type} (d : ι → Beh A)

/-- **The refinement preorder** of implementations with denotation `d`. -/
@[instance_reducible]
def implPreorder : Preorder ι := Preorder.lift d

/-- **Observational equivalence** of implementations: the same denotation. -/
def obsSetoid : Setoid ι := Setoid.ker d

/-- **The normalized behaviour** of an equivalence class. -/
def norm : Quotient (obsSetoid d) → Beh A := Setoid.kerLift d

end Impl

end Silmaril.Servers.Observe
