module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Codiagonal
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Naturality
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Uniformity
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Codiagonal
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Naturality
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Uniformity
import Batteries.Tactic.Alias

/-!
# Complete Elgot laws for persistent output: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

noncomputable instance _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.instLawfulElgotMonadOfContinuousLog {W : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W] :
    LawfulElgotMonad (PartialWriter W) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity f g h comm := uniformity f g h comm

end Silmaril.Elgot.PartialWriter
