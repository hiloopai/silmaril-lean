module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Dispatch.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Dispatch

variable {Body Continuation : Layout → Type} {table : CodeTable Body}

theorem resolve_iff {ref : CodeRef} {definition : Definition Body ref.layout} :
    resolve table ref = .ok definition ↔ Resolves table ref definition :=
  Proofs.Languages.Python.Core.Closure.Dispatch.resolve_iff

theorem resolve_missing {ref : CodeRef} (missing : table ref.key = none) :
    resolve table ref = .error (.missingCode ref.key) := by
  simp [resolve, missing]

theorem resolve_layout_mismatch {ref : CodeRef} {entry : Entry Body}
    (found : table ref.key = some entry) (different : entry.layout ≠ ref.layout) :
    resolve table ref = .error (.layoutMismatch ref.layout entry.layout) := by
  simp [resolve, found, different]

theorem Definition.prepare_length {layout : Layout} {definition : Definition Body layout}
    {arguments bound : List Value} (prepared : definition.prepare arguments = .ok bound) :
    bound.length = definition.parameters.slots.length :=
  Proofs.Languages.Python.Core.Closure.Dispatch.prepare_length prepared

theorem dispatch_iff {callee : Value} {arguments : List Value} {heap : Heap}
    {caller : Call.Saved Continuation} {stack : List (Call.Saved Continuation)}
    {active : Active Body Continuation} :
    dispatch table callee arguments heap caller stack = .ok active ↔
      Dispatches table arguments heap caller stack callee active :=
  ⟨Proofs.Languages.Python.Core.Closure.Dispatch.dispatch_sound,
    Proofs.Languages.Python.Core.Closure.Dispatch.dispatch_complete⟩

end Silmaril.Languages.Python.Core.Closure.Dispatch
