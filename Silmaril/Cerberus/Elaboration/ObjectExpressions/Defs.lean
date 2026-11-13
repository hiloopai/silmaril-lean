module

public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.MemoryActions.Defs

/-! Object identifier and lvalue-conversion branches from pinned
`translation.lem:1840-1860,3145-3160`. The context is explicitly ECTX_other and
non-CHERI; global-initializer renaming and CHERI const aliases are not supplied.
Outer expression annotations belong to the recursive dispatcher. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ObjectExpressions
open Silmaril.Cerberus
open Construction

def identifier (config : Target.Config) (symbol : Sym) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI object identifier aliases")
  return pureEffect (symbolPure symbol)

/-- Only a direct atomic wrapper requests sequential consistency upstream. -/
def loadOrder : Ctype → MemoryOrder
  | .mk _ (.atomic _) => .seqCst
  | _ => .na

/-- Translate the child first, then allocate its object-pointer binder and load
using the child's exact CType, rather than its interpreted result type. -/
def rvalue (config : Target.Config) (location : Loc) (childType : Ctype)
    (child : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI object rvalue conversion")
  let core ← child
  let pointer ← State.wrappedFreshSymbol (.object .pointer)
  return weakSequence pointer.pattern core
    (MemoryActions.load location (ailCtype childType) pointer.expression (loadOrder childType))

end Silmaril.Cerberus.Elaboration.ObjectExpressions
