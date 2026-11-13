module

public import Silmaril.Wasm.Jco.Async.Defs
public import Silmaril.Wasm.Jco.Styles.Unified.Defs

/-!
# Async lifts in the unified wrapper

`awrapU md enc` is the unified wrapper `wrapU md.sync enc` (spilled parameters, wide results,
string encodings) with the async styles of `md`. A synchronous lift is the unified
`canon lift` (`canonCallU`). An async lift is `canon lift async` (`asyncCall`) of the async
shim over the unified wrapper's export shim, as in `awrap`.

**Where the styles are compatible.** The async layer of `Silmaril/Wasm/Jco/Async` lowers
parameters at `utf8` and returns results through `task.return` of the flat values. So an async
function must use the plain path of the unified wrapper: no spilled parameters and no wide
result (`AMeta.AsyncPlain`). Its string parameters are then lowered at `utf8`, whatever `enc`
is. The encoding `enc` applies to the synchronous functions.

`aspecU M md enc` is the specification: the unified convention for synchronous functions and
`aspecCall` for async ones.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

open Silmaril.Wasm.Component (Flat)

/-- A lift of an `XComp` with an optional async style. -/
structure AXLift where
  lift : XLift
  async : Option Style := none
  deriving Repr, Inhabited

/-- A unified wrapper whose lifts may be async. -/
structure AXComp where
  adaptor : XMod := ⟨[]⟩
  lifts : List AXLift
  deriving Repr, Inhabited

namespace AXComp

variable (M : CoreInst)

/-- The synchronous component underneath. -/
def base (c : AXComp) : XComp := { adaptor := c.adaptor, lifts := c.lifts.map (·.lift) }

/-- The behaviour of export `name`. -/
def callExport (c : AXComp) (name : String) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match c.lifts.find? (·.lift.sig.name == name) with
  | some ⟨l, none⟩ =>
    canonCallU M.withStore l.enc (c.base.callRef M.withStore l.realloc)
      (c.base.callRef M.withStore l.callee) l.sig vs
  | some ⟨l, some st⟩ =>
    asyncCall M (c.base.callRef M.withStore l.realloc)
      (shimRun M (c.base.callRef M.withStore l.callee) l.sig.result st) (AComp.noCallback M) st
      l.sig vs
  | none => RM.fail

end AXComp

/-- **The unified wrapper with async lifts.** -/
def awrapU (md : AMeta) (enc : StrEnc) : AXComp :=
  { adaptor := adaptorUOf md.sync
    lifts := ((liftsFrom 0 md.sync.world).map (Lift.withEnc enc)).zipWith
      (fun l s => ⟨l, s.async⟩) md.world }

/-- Every async function takes the plain path of the unified wrapper. -/
def AMeta.AsyncPlain (md : AMeta) : Prop :=
  ∀ s ∈ md.world, s.async.isSome = true →
    spillOf s.sig.params = none ∧ wideOf s.sig.result = none

variable (M : CoreInst)

/-- **The specification**: the unified convention, and `aspecCall` for async functions. -/
def aspecU (md : AMeta) (enc : StrEnc) (name : String) (vs : List PVal) :
    RM M.withStore.St (Option PVal) :=
  match md.world.find? (·.sig.name == name) with
  | some ⟨sig, none⟩ => md.sync.specCallU M.withStore enc sig vs
  | some ⟨sig, some st⟩ => aspecCall M md ⟨sig, some st⟩ vs
  | none => RM.fail

end Silmaril.Wasm.Jco.Async
