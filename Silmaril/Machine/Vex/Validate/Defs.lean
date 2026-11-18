module

public import Silmaril.Machine.Vex.X86.Defs
public import Silmaril.Machine.Translation.Defs

/-! # One-boundary translation validation -/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar

/-- The artifact relation on decoded x86 and checked VEX blocks. The common
residual plan is a syntactic witness, not an equality of executions. -/
structure Translates (pc : Word) (source : X86.Block) (target : Block) : Prop where
  address : target.address = pc
  marks : target.code.marks = source.marks
  plan : target.lower = .ok (source.lower pc)

inductive ValidationError where
  | vex (error : Error)
  | x86 (error : X86.DecodeError)
  | observation (error : ObservationError)
  | address
  | marks
  | differentPlan
  deriving DecidableEq, Repr

structure Pair where
  source : X86.Block
  target : Block

structure Certificate (pc : Word) (bytes : List UInt8) (raw : Raw.Block) (pair : Pair) : Prop where
  decoded : X86.decode pc bytes = .ok pair.source
  checked : check raw = .ok pair.target
  translates : Translates pc pair.source pair.target

/-- A deliberately incomplete test: both artifacts must produce the
same residual observation plan. No input enumeration or UB assumption. -/
def validate (pc : Word) (bytes : List UInt8) (raw : Raw.Block) : Except ValidationError Pair :=
  match X86.decode pc bytes with
  | .error error => .error (.x86 error)
  | .ok source => match check raw with
    | .error error => .error (.vex error)
    | .ok target =>
      if target.address ≠ pc then .error .address
      else if source.marks ≠ target.code.marks then .error .marks
      else match target.lower with
        | .error error => .error (.observation error)
        | .ok plan =>
          if source.lower pc ≠ plan then .error .differentPlan else .ok ⟨source, target⟩

end Silmaril.Machine.Vex.AMD64Scalar
