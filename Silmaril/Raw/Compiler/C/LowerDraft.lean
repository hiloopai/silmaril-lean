module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.Compiler.Contract.Defs
public import Silmaril.Compiler.Mir.Syntax.Defs
public import Mathlib.Data.Set.Basic

/-!
# Draft interface for per-program C-to-Mir validation

This file defines no C semantics or interpreter. The permitted source instances
are csem's frozen `C0.sem` through `C5.sem`, or Cerberus Core through csem's
`Core.elabSem` and a reviewed elaborator. Their modules are absent on this ccomp
base, so the interface takes the source semantics, validity
relation and target behaviours as parameters. No csem module is imported here.

The parameters must be fixed together, using csem's actual definitions:

* `S := C5.sem` (or the chosen frozen rung / Core semantics);
* `valid := fun S => Category.Valid (Core.cAM S mirConfig ctlAddress)`;
* `targetBeh := Mir.beh mirConfig`;
* `lower := ccompMirRt`.

Then `lowerDraft S valid targetBeh lower p` unfolds to **exactly** the conclusion
of `Targets.ccomp_rt_tv_sound_c5` on a program accepted by `checkC5`. The existing
`Targets.Proofs.ccomp_rt_tv_sound_c5` supplies the certificate directly. The same
substitution works for C0 through C4 with their corresponding TV theorems. No
source-fragment proof is attempted on this trunk.

## Source references

An earlier read-only C semantics candidate:

* `Compile/C/Sem/Basic.lean:38-47`: `Obs`, `cSyntax`, `Semantics`;
* `Compile/Core/Semantics.lean:192-193,223-232,247-248`: `elabSem`, `readBack`, `cAM`;
* `Compile/Category/Valid.lean:42-57`: `Valid`, `valid_iff_beh`,
  `valid_iff_readBack` (these category definitions are also on this trunk);
* `Compile/Mir/Semantics.lean:106-113`: `Mir.beh`, `Mir.lang`;
* `Compile/C/Sem/Runtime.lean:45-55`: `ccompMirRt`;
* `Compile/C/Sem/Triangle.lean:35-38`: `mirConfig`, `ctlAddress`.

A later revision of it adds the C5 validation theorem:
`Compile/C/Sem/TargetsC5.lean:27-30`,
`Compile/C/Sem/TargetProofs.lean:138-139`, and
its `Compile/C/Sem/Validator.lean`. The candidate has the C5 semantics but no
`TargetsC5.lean`; the newer citation is necessary for that instantiation.
All paths above are below `Silmaril/` in the csem checkout.

## Observation boundary and backward refinement

Csem's `Obs` observes stdout bytes, an exit status modulo 256, a signal, or
divergence. `Core.cAM` relates source observations to `Core.readBack ctlAddress`
of target outcomes. `Category.Valid` is backward refinement: every target
behaviour is a realisation of a source behaviour (`valid_iff_beh`), equivalently
its read-back belongs to the source behaviour set (`valid_iff_readBack`). Source
UB is handled by the existing rung / Core semantics; unsupported/error is not
silently changed into UB. The draft imposes no new read-back or UB rule.

Target behaviour is **csem's link-defined `Mir.beh mirConfig`**, not ccomp's
independent `Contract.MirSem.Behaves`. The target-behaviour parameter makes this
choice explicit. Instantiating with the TV theorem needs no bridge. Relating the
result to `MirSem.start` / `MirSem.Behaves` later requires the named open
obligation `LowerDraft.MirSemBridge` below. It covers linking, entry, initial
memory, placements, outcome conversion and UB closure. It is a proposition
definition, with no proof supplied or assumed. The forward checked-link contract
alone does not discharge it. Landing csem's semantics byte-identically and
proving this bridge are separate later ideas.

Successful compilation and nonempty target behaviour are both required, so a
compiler that rejects or produces no behaviour cannot pass per-program validation.
The full stage contract and any identification of `ccompMirRt` with a configured
`Registry.Stage.lower` adapter remain open. Multi-TU linking and
strict `-c` need their own source composition / open-module interfaces.
-/

@[expose] public section

namespace Silmaril.Compile.Contract

/-- **Per-program lower draft.** `S`, `valid`, and `targetBeh` stand for csem's
frozen source semantics, its exact `Valid (Core.cAM S mirConfig ctlAddress)`
relation, and its exact `Mir.beh mirConfig`. See the module docstring for the
required simultaneous instantiation. This proposition is a certificate interface,
not a claim that any compiler or newly chosen semantic model is correct. -/
def lowerDraft {SourceObs TargetObs : Type}
    (S : Cerberus.Ail.TypedProgram → Set SourceObs)
    (valid : (Cerberus.Ail.TypedProgram → Set SourceObs) →
      Cerberus.Ail.TypedProgram → Array Mir.Unit → Prop)
    (targetBeh : Array Mir.Unit → Set TargetObs)
    (lower : Cerberus.Ail.TypedProgram → Option (Array Mir.Unit))
    (p : Cerberus.Ail.TypedProgram) : Prop :=
  ∃ us, lower p = some us ∧ valid S p us ∧ (targetBeh us).Nonempty

namespace LowerDraft

open Silmaril.Machine

/-- **Open obligation: csem Mir / independent Mir adequacy.** Instantiate
`targetBeh := Mir.beh mirConfig`, `linked := Mir.link mirConfig.layout`, and
`memSize := mirConfig.memSize` after csem's semantics are landed byte-identically.
`admissible` must be fixed explicitly by that later integration (including the
memory/address bounds needed for a valid placement); it must cover the compiler
outputs to which the bridge will be applied. Choosing an empty domain supplies
no bridge for those outputs.

For a successful link, one placement must simultaneously be valid, reproduce the
link's initial memory, agree on whether the no-argument entry starts, and give
exactly the target outcomes. This is an existential placement for that link,
not equivalence at every arbitrary valid placement. Failure to link gives no
behaviour. Failure to start also gives none, by the final equivalence.
`Behavior.toOutcome` preserves returned values/memory, traps and divergence;
its `.stuck` case is `.undefined`. The second disjunct closes the independent
behaviours under UB, exactly as csem's `Mir.ubClose` does, including outcomes
outside the image of `Behavior.toOutcome`.

This definition states work for a later idea. It is neither an axiom nor a
theorem, and `lowerDraft` and its direct TV instantiation do not require it. -/
def MirSemBridge
    (targetBeh : Array Mir.Unit →
      Set (Behaviour.Outcome (List Lir.Word × Lir.Memory) Lir.Memory Empty))
    (linked : Array Mir.Unit → Except String Mir.Linked)
    (memSize : Nat) (admissible : Array Mir.Unit → Prop) : Prop :=
  ∀ us, admissible us →
    match linked us with
    | .error _ => targetBeh us = ∅
    | .ok l => ∃ P : MirSem.Placement,
        P.Valid us memSize ∧
        MirSem.initMem us P memSize = linkedMem l memSize ∧
        ((∃ s, MirSem.start us P memSize = some s) ↔
          ∃ t, l.prog.start 0 [] (linkedMem l memSize) = some t) ∧
        ∀ o, o ∈ targetBeh us ↔
          ∃ s, MirSem.start us P memSize = some s ∧
            ((∃ b, MirSem.Behaves us P s b ∧ b.toOutcome = o) ∨
              MirSem.Behaves us P s .stuck)

variable {SourceObs TargetObs : Type}
variable {S : Cerberus.Ail.TypedProgram → Set SourceObs}
variable {valid : (Cerberus.Ail.TypedProgram → Set SourceObs) →
  Cerberus.Ail.TypedProgram → Array Mir.Unit → Prop}
variable {targetBeh : Array Mir.Unit → Set TargetObs}
variable {lower : Cerberus.Ail.TypedProgram → Option (Array Mir.Unit)}
variable {p : Cerberus.Ail.TypedProgram} {us : Array Mir.Unit}

/-- Direct adapter from csem's translation-validation theorem shape. This theorem
only transports the supplied certificate; it proves no new source semantics. -/
theorem of_translationValidation {check : Cerberus.Ail.TypedProgram → Bool}
    (sound : ∀ p, check p = true →
      ∃ us, lower p = some us ∧ valid S p us ∧ (targetBeh us).Nonempty)
    (accepted : check p = true) : lowerDraft S valid targetBeh lower p :=
  sound p accepted

/-- At the actual compiler output the per-program obligation is precisely csem's
validity relation together with its non-vacuity requirement. -/
theorem iff_of_output (output : lower p = some us) :
    lowerDraft S valid targetBeh lower p ↔
      valid S p us ∧ (targetBeh us).Nonempty := by
  constructor
  · rintro ⟨other, hother, hv, hne⟩
    have heq : other = us := Option.some.inj (hother.symm.trans output)
    subst other
    exact ⟨hv, hne⟩
  · rintro ⟨hv, hne⟩
    exact ⟨us, output, hv, hne⟩

/-- Rejection cannot satisfy a per-program certificate. -/
theorem not_of_reject (rejected : lower p = none) :
    ¬ lowerDraft S valid targetBeh lower p := by
  rintro ⟨_, output, _, _⟩
  rw [rejected] at output
  cases output

/-- A deliberately invalid output cannot satisfy the draft even if it has
behaviours. This checks the validity clause without defining another C semantics. -/
theorem not_of_invalid (output : lower p = some us) (invalid : ¬ valid S p us) :
    ¬ lowerDraft S valid targetBeh lower p := by
  intro h
  exact invalid ((iff_of_output output).mp h).1

/-- A target with no behaviours cannot pass by vacuous refinement. -/
theorem not_of_empty (output : lower p = some us) (empty : targetBeh us = ∅) :
    ¬ lowerDraft S valid targetBeh lower p := by
  intro h
  obtain ⟨b, hb⟩ := ((iff_of_output output).mp h).2
  rw [empty] at hb
  exact hb

end LowerDraft
end Silmaril.Compile.Contract
