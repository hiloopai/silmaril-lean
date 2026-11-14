module

public import Silmaril.Servers.Hosts.Defs

/-!
# HTTP obligations of abstract servers: problem shapes and evidence kinds

**Shapes.** The obligations Silmaril problems ask of a server, over the abstract observation
interface (`Silmaril.Servers.Observe`) that components, processes and specifications share:

| shape | statement | reading |
| --- | --- | --- |
| `Shape.Satisfies M φ` | `M.Sat φ` | every trace of the core model meets the trace sentence |
| `Shape.Refines I S` | `I ⊆ S` | implementation `I` refines specification `S` (orientation fixed) |
| `Shape.Equivalent I S` | `I = S` | observational equivalence (refinement both ways) |
| `Shape.InitSafe B` | `initFail ∉ B` | initialization never fails |
| `Shape.MustUnder Hs C φ` | `MustAll Hs C (Obs.sen φ)` | `φ` whatever the hosts of `Hs` answer |
| `Shape.MayUnder Hs C P` | `MaySome Hs C P` | some host of `Hs` lets some run show `P` |
| `Shape.RefinesUnder Hs C D` | `RefinesAt Hs C D` | refinement, the same host on both sides |

**Evidence.** What backs a claim, kept apart because they mean different things
(`Evidence`, with the badge shown for it):

* `proof` ("proved"): a Lean theorem, checked by the kernel, standard axioms only;
* `refutation` ("refuted"): a Lean theorem of the negation;
* `validatorCheck` ("validated"): a tool accepted or rejected an artifact (`wasm-tools
  validate` checks well-formedness of a component; `wasm-tools component targets` checks its
  type against a world). Not a theorem;
* `runtimeTest` ("tested"): runs of an artifact under named, recorded host policies, within
  stated bounds (`tests/servers/policies`). Finitely many runs: a failure under a host in the
  quantified set is a counterexample, a pass is not a proof;
* `nameMatch` ("names match"): the artifact exports a function of the expected *name*. Says
  nothing about its type or behaviour.

A component being "well typed with the right server interface" is thus three different claims:
the runtime/validator accepts it against the `wasi:http/proxy` world (`validatorCheck`), a
Lean theorem about its denotation over typed hosts (`proof`, `WasiCore.RunsTy`), or a matching
export name (`nameMatch`). `Silmaril.Servers.Problems.Thms` registers problems of each kind.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Problems

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts

/-- **What backs a claim.** -/
inductive Evidence where
  | proof
  | refutation
  | validatorCheck
  | runtimeTest
  | nameMatch
  deriving DecidableEq, Repr

/-- The badge shown for a kind of evidence. -/
def Evidence.badge : Evidence → String
  | .proof => "proved"
  | .refutation => "refuted"
  | .validatorCheck => "validated"
  | .runtimeTest => "tested"
  | .nameMatch => "names match"

/-- Whether the evidence is a Lean theorem. -/
def Evidence.isLean : Evidence → Bool
  | .proof | .refutation => true
  | _ => false

namespace Shape

variable {A : Sig} {H : Type}

/-- Every trace of the model meets the sentence. -/
def Satisfies (M : Model A) (φ : Sen A) : Prop := M.Sat φ

/-- The implementation refines the specification. -/
def Refines (I S : Beh A) : Prop := I.Refines S

/-- Observational equivalence. -/
def Equivalent (I S : Beh A) : Prop := I = S

/-- Initialization never fails. -/
def InitSafe (B : Beh A) : Prop := B.InitSafe

/-- The sentence holds under every host of `Hs`. -/
def MustUnder (Hs : Set H) (C : Open H A) (φ : Sen A) : Prop := MustAll Hs C (Obs.sen φ)

/-- Some host of `Hs` lets some observation satisfy `P`. -/
def MayUnder (Hs : Set H) (C : Open H A) (P : Obs A → Prop) : Prop := MaySome Hs C P

/-- Refinement under every host of `Hs`, the same host on both sides. -/
def RefinesUnder (Hs : Set H) (C D : Open H A) : Prop := RefinesAt Hs C D

end Shape

end Silmaril.Servers.Problems
