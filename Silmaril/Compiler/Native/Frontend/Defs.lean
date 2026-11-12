module

public import Silmaril.Cerberus.Frontend.Defs

/-! Native frontend input retains the actual desugaring state alongside the
same typed Ail program used by the imported frontend. In particular, enum
implementation registrations are preserved rather than inferred from uses. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Frontend

open Silmaril.Cerberus

/-- Match the parser input used by the imported frontend: remove only its final
newline, while the digest continues to use the untrimmed translation text. -/
def parserText (text : ByteArray) : ByteArray :=
  if text.size > 0 && text[text.size - 1]! == '\n'.toUInt8 then text.extract 0 (text.size - 1) else text

/-- The complete returned desugaring state, after final marker bookkeeping. -/
structure Result where
  program : Ail.TypedProgram
  state : Silmaril.Cerberus.Frontend.Desugar.DesugState

/-- The exact implementation registry returned by this frontend run. -/
def Result.enumBindings (result : Result) : List (Sym × IntegerType) :=
  result.state.registeredEnums

/-- Native input may come from C with its full desugaring state, or from saved
typed Ail with no such state. Missing registrations remain explicitly absent. -/
structure Input where
  program : Ail.TypedProgram
  state : Option Silmaril.Cerberus.Frontend.Desugar.DesugState := none

def Result.input (result : Result) : Input :=
  ⟨result.program, some result.state⟩

/-- Saved-Ail and oracle routes do not invent an implementation enum registry. -/
def Input.ofTyped (program : Ail.TypedProgram) : Input := ⟨program, none⟩

def Input.enumBindings (input : Input) : List (Sym × IntegerType) :=
  input.state.map (·.registeredEnums) |>.getD []

/-- Run the same desugaring action and final marker step as `Frontend.desugar`,
retaining its state. This does not change the imported frontend or its defaults. -/
def desugarState (digest : Digest) (unit : Cabs.TranslationUnit) :
    Except Ail.Reject (Ail.Program Unit × Silmaril.Cerberus.Frontend.Desugar.DesugState) :=
  let action := Silmaril.Cerberus.Frontend.Desugar.underScope .file do
    unit.declarations.forM (Silmaril.Cerberus.Frontend.Desugar.desugarAndRegisterExternalDeclaration
      (Silmaril.Cerberus.Frontend.Desugar.knot Silmaril.Cerberus.Frontend.Desugar.depth))
    Silmaril.Cerberus.Frontend.Desugar.extractProgram "main"
  (do
    let program ← action
    let _ ← Silmaril.Cerberus.Frontend.Desugar.finMarkersEnv
    pure program).run (Silmaril.Cerberus.Frontend.Desugar.initialState digest)

/-- Parse and typecheck exactly the extracted Ail while retaining its complete
desugaring state. Error stages and parser input match `Registry.Stage.frontend`. -/
def run (text : ByteArray) : Except String Result :=
  let action : Except Ail.Reject Result := do
    let unit ← (Silmaril.Cerberus.Frontend.parse (parserText text)).mapError
      Ail.Reject.ofCabs
    let (program, state) ← desugarState (Ail.fileDigest text) unit
    let typed ← Silmaril.Cerberus.Frontend.typecheck program
    pure ⟨typed, state⟩
  action.mapError fun reject => s!"{reject.stage}: {reject.message}"

end Silmaril.Compiler.Native.Frontend
