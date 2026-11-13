module

public import Silmaril.Compiler.Native.Frontend.Defs
public import Silmaril.Compiler.Registry.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Frontend

open Silmaril.Cerberus

theorem parserText_eq (text : ByteArray) : parserText text = Silmaril.Compile.Registry.cppText text := by
  rfl

/-- Retaining the final state preserves the imported desugarer's exact program. -/
theorem desugarState_program (digest : Digest) (unit : Cabs.TranslationUnit) :
    (desugarState digest unit).map Prod.fst =
      Silmaril.Cerberus.Frontend.desugar digest unit := by
  rfl

/-- Parsing, desugaring and typing produce exactly the existing frontend result
when the retained metadata is projected away, including every rejection. -/
theorem run_program (text : ByteArray) :
    (run text).map Result.program = Silmaril.Compile.Registry.Stage.frontend text := by
  unfold run Silmaril.Compile.Registry.Stage.frontend
  rw [parserText_eq]
  cases parsed : (Silmaril.Cerberus.Frontend.parse (Silmaril.Compile.Registry.cppText text)).mapError
      Ail.Reject.ofCabs with
  | error reject => rfl
  | ok unit =>
    simp only [bind, Except.bind]
    cases desugared : desugarState (Ail.fileDigest text) unit with
    | error reject =>
      have erased := desugarState_program (Ail.fileDigest text) unit
      simp only [desugared, Except.map] at erased
      rw [← erased]
      rfl
    | ok pair =>
      have erased := desugarState_program (Ail.fileDigest text) unit
      simp only [desugared, Except.map] at erased
      rw [← erased]
      dsimp only
      cases typed : Silmaril.Cerberus.Frontend.typecheck pair.1 <;> rfl

end Silmaril.Compiler.Native.Frontend
