module

public import Silmaril.Machine.Vex.Validate.Semantics.Defs
public import Silmaril.Machine.Translation.Soundness.Thms
import Silmaril.Proofs.Machine.Vex.Validate.Sound

public section

namespace Silmaril.Machine.Vex.AMD64Scalar

/-- Checker acceptance attests artifact provenance and the artifact relation. -/
theorem validate_certifies {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    Certificate pc bytes raw pair := Proofs.validateCertifies accepted

theorem boundary_beh {input output : Type} (run : input → Option output) (entry : input)
    (outcome : Behaviour.Outcome output Empty Empty) :
    (boundarySem run).Beh entry outcome ↔ ∃ value, run entry = some value ∧ outcome = .returned value :=
  Proofs.boundaryBeh run entry outcome

theorem Term.selectBit_sound (input : Input) (index : Nat) (term : Term) :
    (term.selectBit index).eval input = flagWord ((term.eval input).getLsbD index) :=
  Proofs.selectBit input index term

theorem X86.Block.lower_sound (block : X86.Block) (input : Input) :
    (block.lower input.rip).eval input = block.run input := Proofs.x86Lower block input

/-- All register values and both incoming ZF values, at the common entry PC. -/
theorem translation_runs {pc : Word} {source : X86.Block} {target : Block}
    (related : Translates pc source target) (input : Input) (entry : input.rip = pc) :
    target.run input = .ok (source.run input) := Proofs.translationRuns related input entry

/-- A related target has exactly one behavior at each related entry. -/
theorem translation_beh {pc : Word} {source : X86.Block} {target : Block}
    (related : Translates pc source target) {srcInput tgtInput : Input}
    (initial : Initial pc srcInput tgtInput) (outcome : Behaviour.Outcome Input Empty Empty) :
    (targetSem target).Beh tgtInput outcome ↔ outcome = .returned (source.run srcInput) :=
  Proofs.translationBeh related initial outcome

/-- Semantic soundness applies to any related artifacts, however produced. -/
theorem translation_sound (pc : Word) :
    Translation.Sound (Translates pc) .targetRefinesSource .strict sourceSem targetSem
      (fun _ _ => Initial pc) (fun _ _ _ _ => observations) := Proofs.translationSound pc

theorem translates_le_largestSoundAt (pc : Word) : Translates pc ≤ largestSoundAt pc :=
  Translation.sound_iff_le_largestSound.mp (translation_sound pc)

theorem validate_in_largestSoundAt {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) : largestSoundAt pc pair.source pair.target :=
  translates_le_largestSoundAt pc pair.source pair.target (validate_certifies accepted).translates

theorem check_word_erase {ctx : Scope} (value : Word) :
    checkExpr ctx ((Expr.word (ctx := ctx) value).erase) = .ok ⟨.i64, Expr.word value⟩ :=
  Proofs.wordErasure value

end Silmaril.Machine.Vex.AMD64Scalar
