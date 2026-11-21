module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}

/-- The reference uses the public reply words without recording a checked
completion. The lowering body is the same canonical program as `Site.reference`. -/
noncomputable def Site.referenceWords (site : Site grow sig route) : Session grow sig (List FlatValue) :=
  site.referenceProgram >>= fun value => pure (route.reply site.destination site.start.host.nextTicket (.ok value)).2

def Site.EntryRequest (site : Site grow sig route) (call : Call (core3 grow)) : Prop :=
  match call with
  | .hostCallout (.embedder name kind) args =>
    name = site.name ∧ kind = site.functionType ∧ args = route.args site.handle
  | _ => False

/-- Install the reference implementation at this public request and keep all
other handlers. This is a fixed binding, not a one-shot change of dispatcher. -/
noncomputable def Site.referenceHost (site : Site grow sig route) (base : HostImpl (core3 grow) (HostState sig)) :
    HostImpl (core3 grow) (HostState sig) := by
  classical
  exact { base with embedder := fun name kind args =>
    if site.EntryRequest (.hostCallout (.embedder name kind) args) then site.referenceWords else base.embedder name kind args }

/-- A proper cut of a replay must not install this replacement again. The
test is on actual focused dispatch sites, not on unused imports or saved code. -/
structure Site.NoEntryAt (site : Site grow sig route) (state : Config (core3 grow) (HostState sig)) : Prop where
  direct : ∀ {thread request next frames rest}, state.ctl = ⟨thread, .prog (.op (.call request) next), frames⟩ :: rest →
    ¬ site.EntryRequest request
  core : ∀ {thread core next frames rest callee args}, state.ctl = ⟨thread, .core core next, frames⟩ :: rest →
    (core3 grow).status state.store.core core = .callout callee args → ¬ site.EntryRequest (.hostCallout callee args)

def Site.NoEntryThrough (site : Site grow sig route) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (start : Config (core3 grow) (HostState sig))
    (labels : List (Label (core3 grow) (HostState sig))) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {leading cut label trailing}, labels = leading ++ label :: trailing →
    Steps profile ready (specDispatch ready base) start leading cut →
    Steps profile ready (specDispatch ready base) cut (label :: trailing) finish → site.NoEntryAt cut

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot
