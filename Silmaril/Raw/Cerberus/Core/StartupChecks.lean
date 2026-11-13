module

public import Silmaril.Cerberus.Core.ExecutionChecks.Defs

/-! Kernel checks for startup pointer order, terminators and calling conventions.
The C fixtures independently check the linked executions against the oracle. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Startup.Checks
open Mem.Concrete Dynamics

/-- Each supplied string pointer retains its own allocation provenance. -/
theorem pointer_order (ps : List Pointer) :
    contents ps .pointers = .ok (.array
      (ps.map (.pointer charType) ++ [.pointer charType (.null charType)])) := rfl

/-- Even an empty driver argument list has its mandatory null element. -/
theorem empty_argv : contents [] .pointers =
    .ok (.array [.pointer charType (.null charType)]) := rfl

def mainSym : Sym := ⟨⟨[]⟩, 700, .id "main"⟩
def argcSym : Sym := ⟨⟨[]⟩, 701, .id "argc"⟩
def argvSym : Sym := ⟨⟨[]⟩, 702, .id "argv"⟩

/-- Normal callconv allocates the array, argc, and argv even for argc zero. -/
theorem normal_empty_objects : objects [] false .unknown mainSym argcSym argvSym = .ok
    [⟨.mk [] (.array charPointer (some 1)), .pointers, .source .unknown [mainSym, argvSym]⟩,
     ⟨intType, .literal (.integer (.signed .int) 0), .source .unknown [mainSym, argcSym]⟩,
     ⟨argvType, .arrayPointer 0, .source .unknown [mainSym, argvSym]⟩] := rfl

/-- Inner callconv passes loaded values, without allocating parameter objects. -/
theorem inner_empty_objects : objects [] true .unknown mainSym argcSym argvSym = .ok
    [⟨.mk [] (.array charPointer (some 1)), .pointers, .source .unknown [mainSym, argvSym]⟩] := rfl

/-- The normal environment receives addresses of the two parameter objects. -/
theorem normal_bindings :
    let c := Control.pureExpr (Dynamics.Checks.pe (.sym argcSym)) ∅
    let ps := [Pointer.allocated 0 80, .allocated 1 64, .allocated 2 60, .allocated 3 48]
    requestAux Dynamics.Checks.emptyFile ∅ {} (.mainArgs [] ps [argcSym, argvSym] c) [] =
      .next (.startup (.pureExpr (Dynamics.Checks.pe (.sym argcSym))
        (extendEnv [(argcSym, .object (.pointer (.allocated 2 60))),
          (argvSym, .object (.pointer (.allocated 3 48)))] ∅))) [] := by
  simp [requestAux, awaitsScheduling, Dynamics.Checks.emptyFile]

/-- One string and its array produce argc one and the array pointer directly. -/
theorem inner_bindings :
    let c := Control.pureExpr (Dynamics.Checks.pe (.sym argcSym)) ∅
    let ps := [Pointer.allocated 0 80, .allocated 1 64]
    requestAux {Dynamics.Checks.emptyFile with callingConvention := .innerArg} ∅ {}
      (.mainArgs [] ps [argcSym, argvSym] c) [] =
      .next (.startup (.pureExpr (Dynamics.Checks.pe (.sym argcSym))
        (extendEnv [(argcSym, .loaded (.specified (.integer 1))),
          (argvSym, .loaded (.specified (.pointer (.allocated 1 64))))] ∅))) [] := by
  simp [requestAux, awaitsScheduling, Dynamics.Checks.emptyFile]

end Silmaril.Cerberus.Core.Startup.Checks
