module

public import Silmaril.Wasm.Component.Reference.HLinkedSep.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.Main

/-!
# A concrete pair separating the open session object from the reference equivalence: theorems

**Scope.** The two concrete linked components with one host import of `HLinkedSep.Defs`:
`forgetL = sepL 0` and `rememberL = sepL 1` (exporter `setGetS` wired to nothing; importer
`f() -> u32` reading a global `g`, writing `g := c`, calling the host import `h()`, writing
`g := 0` and answering what it read). The session objects are those of `HLinkedSessionObj`: the
host-realizable `HLinked2.compSession` and the open `HLinked2.compSessionO`.

**Hypotheses.** Deterministic profiles `profile o` (every grow oracle `o`) for the objects and
the reference equivalence; every component choice profile `prof`. Nothing else: the components
are concrete. Their core modules are validated and instantiated by `decide +kernel` on a Boolean
summary (`sepSummary`), as for #697's fixtures.

## Proved

* **Both components are adequate and have the same types** (`HLinkedSep.forgetL_adequate`,
  `HLinkedSep.rememberL_adequate`, `HLinkedSep.sameTypes`).
* **Equal host-realizable objects** (`HLinkedSep.compSession_eq`):

  `compSession (profile o) forgetL = compSession (profile o) rememberL`.

  One call of `f` from the importer's store with the global `v`: the host call `h()` refused
  is a trap leaving `g = c`, `h()` answered (with no results, the only legal answer) is the answer
  `v` leaving `g = 0`, an untyped question traps at once, and nothing else happens (no
  divergence, no host chatter; uniqueness by `round_detH` and the importer's Proponent
  determinism). While nothing is refused both components have `g = 0` and answer `0`; once `h()`
  is refused it is refused again by every deterministic host (`HLinked2.Forced`), the
  realizable triple hides the forced refusal and both components trap, so `g` is never read again.
  The relation "same refusals, `g = 0` on both sides while nothing is refused" is a bisimulation
  of the host-realizable triples.
* **Reference equivalence** (`HLinkedSep.refSessEquivFull`): `RefSessEquivFull (profile o) prof
  forgetL rememberL`, from the equal objects by `HLinked2.refSessEquivFull_of_compSession`
  (equivalently `HLinked2.compSession_inj_full`).
* **Different open objects** (`HLinkedSep.compSessionO_ne`):

  `compSessionO (profile o) forgetL ≠ compSessionO (profile o) rememberL`.

  On the open interface the play "`f()`; `h()` refused; trap; `f()`; `h()` answered" is legal;
  `rememberL` answers it `1` (its trapped first call left `g = 1`), `forgetL` answers `0`. Equal
  open objects would give a bisimulation of the open triples (`StratSession.threadS_eq_iff`,
  store determinism and no plain traps), and it would have to match these two rounds. No
  deterministic host produces the play (`HLinked2.not_hostRun_refuse_answer`).
* **Hence the open object is not determined by the reference equivalence**
  (`HLinkedSep.not_compSessionO_of_refSessEquivFull`): it is not true that `RefSessEquivFull` of
  two adequate components gives `HEq` open objects.

## Not claimed

* Soundness of the open object (equal open objects implying `RefSessEquivFull`).
* Nondeterministic profiles.
* A characterisation of the components whose open and host-realizable objects agree.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.{Inst, Core, Round, Triple, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference.HLinkedSep

open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle}

/-- **The forgetful component is adequate** (proved). -/
theorem forgetL_adequate : forgetL.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.forgetL_adequate

/-- **The remembering component is adequate** (proved). -/
theorem rememberL_adequate : rememberL.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.rememberL_adequate

/-- **The pair has the same export and host-import types** (proved). -/
theorem sameTypes : HLinked2.SameTypes forgetL rememberL :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.sep_sameTypes

/-- **The host-realizable session objects of the pair are equal** (proved, `profile o`). -/
theorem compSession_eq :
    HLinked2.compSession (profile o) forgetL = HLinked2.compSession (profile o) rememberL :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.sep_compSession_eq

/-- **The pair is equivalent on the reference machine** under every typed deterministic stateful
host (proved, `profile o`, every component choice profile). -/
theorem refSessEquivFull (prof : ProfileKind) :
    HLinked2.RefSessEquivFull (profile o) prof forgetL rememberL :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.sep_refSessEquivFull prof

/-- **The open session objects of the pair differ** (proved, `profile o`). -/
theorem compSessionO_ne :
    HLinked2.compSessionO (profile o) forgetL ≠ HLinked2.compSessionO (profile o) rememberL :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.sep_compSessionO_ne

/-- **The reference equivalence does not determine the open object** (proved, `profile o`, every
component choice profile). -/
theorem not_compSessionO_of_refSessEquivFull (prof : ProfileKind) :
    ¬ ∀ l l' : HLinked2, l.Adequate → l'.Adequate → HLinked2.RefSessEquivFull (profile o) prof l l' →
      HEq (HLinked2.compSessionO (profile o) l) (HLinked2.compSessionO (profile o) l') :=
  fun h => compSessionO_ne (eq_of_heq (h _ _ forgetL_adequate rememberL_adequate
    (refSessEquivFull prof)))

end Silmaril.Wasm.Component.Reference.HLinkedSep
