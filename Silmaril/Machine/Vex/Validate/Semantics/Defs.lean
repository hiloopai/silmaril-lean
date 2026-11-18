module

public import Silmaril.Machine.Vex.Validate.Defs
public import Silmaril.Machine.Translation.Soundness.Defs

/-! # Boundary observations for the AMD64Scalar translation relation -/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar

/-- A successful boundary evaluation has a returned outcome and no steps.
An out-of-domain evaluation has no admitted outcome, not a UB outcome. -/
def boundarySem {input output : Type} (run : input → Option output) :
    Behaviour.Semantics input output Empty Empty where
  step := fun _ _ => False
  final := fun state outcome => ∃ value, run state = some value ∧ outcome = .returned value

def sourceSem (source : X86.Block) : Behaviour.Semantics Input Input Empty Empty :=
  boundarySem fun state => some (source.run state)

def targetSem (target : Block) : Behaviour.Semantics Input Input Empty Empty :=
  boundarySem fun state => (target.run state).toOption

def Initial (pc : Word) (source target : Input) : Prop := source = target ∧ source.rip = pc

def Final (source target : Input) : Prop := source.rip = target.rip

def observe (state : Input) : Word × Word × Word × Bool :=
  (state.rax, state.rdi, state.rsi, state.zf)

def observations : Behaviour.Obs Input Input Empty Empty Empty Empty where
  ret := fun source target => Final source target ∧ observe source = observe target
  trap := fun source _ => nomatch source
  fault := fun source _ => nomatch source

/-- The semantic upper bound at this entry, without syntactic restrictions
such as marker agreement or exact residual plans. -/
def largestSoundAt (pc : Word) : Translation.Relation X86.Block Block :=
  Translation.largestSound .targetRefinesSource .strict sourceSem targetSem
    (fun _ _ => Initial pc) (fun _ _ _ _ => observations)

end Silmaril.Machine.Vex.AMD64Scalar
