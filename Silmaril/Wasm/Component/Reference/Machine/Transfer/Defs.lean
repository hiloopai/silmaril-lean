module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Engine.Sim.Defs

/-!
# Relating the component machine over two engines with the same static part

`E.withStore I` (`Engine.Sim`) has the static part of `E` and the stores of `I`, and a
`StoreSim S : E.StoreSim I` maps its stores to those of `E` (`S.φ`). The component-level data of
the reference machine (REF) is indexed by the static part only (`CoreEngine.Static`), and so are
the component store `CStore` (which does not hold the core store) and the specification
programs `Canon.P`: programs over `E.withStore I` and over `E` have the same type, and they
reach the core store only through the core operations `readCore`, `memWrite`, `allocHost` and
`prepare`, which the machine answers from its own core store (`Machine.Config.core`).

* `ProgRel S p' p`: a relation between programs over `E.withStore I` and over `E`: the same
  operations with the same data and related continuations. Every program is related to itself
  (`Transfer.Thms`, `ProgRel.refl`).
* `FocusRel`, `SegRel`, `ActRel`, `CfgRel`: the relation lifted to machine configurations. Core
  activations, the component store and every other field are equal, except that the core
  stores are related by `S.φ`.
* `EventRel`, `LabelRel`: transition labels; `HostEvent.run` carries related programs.
* `DispatchRel S d' d`: two dispatchers return related programs on every call.
* `labelOf`: a label of `E.withStore I` as a label of `E`, for traces without `run` events.

`Machine.Transfer.Thms` proves that `Machine.Step` and `Steps` of `E.withStore I` are matched
by steps of `E` from related configurations, given related dispatchers (`step_sim`,
`steps_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.Transfer

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {I : E.StoreImpl} {σ : Type}

/-- **Related programs** over `E.withStore I` and `E` (which have the same type): the same
operations with the same data and related continuations. The relation does not depend on the
store map; `S` fixes the two engines. -/
inductive ProgRel (S : E.StoreSim I) {α : Type} : P (E.withStore I) σ α → P E σ α → Prop where
  | pure (a : α) : ProgRel S (.pure a) (.pure a)
  | get {k : CStore E → P (E.withStore I) σ α} {k' : CStore E → P E σ α} :
      (∀ s, ProgRel S (k s) (k' s)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) .get k) (.op (S := Eff E σ) .get k')
  | modify (f : CStore E → CStore E) {k : Unit → P (E.withStore I) σ α} {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.modify f) k) (.op (S := Eff E σ) (.modify f) k')
  | trap (r : TrapReason) (k : Empty → P (E.withStore I) σ α) (k' : Empty → P E σ α) :
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.trap r) k) (.op (S := Eff E σ) (.trap r) k')
  | choose (ck : ChoiceKind) {k : ck.Resp → P (E.withStore I) σ α} {k' : ck.Resp → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.choose ck) k) (.op (S := Eff E σ) (.choose ck) k')
  | callCore (f : E.FuncAddr) (args : List FlatValue)
      {k : List FlatValue → P (E.withStore I) σ α} {k' : List FlatValue → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.callCore f args) k)
        (.op (S := Eff E σ) (.callCore f args) k')
  | call (c : Call E) {k : Ret E → P (E.withStore I) σ α} {k' : Ret E → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.call c) k) (.op (S := Eff E σ) (.call c) k')
  | currentThread {k : Option ThreadId → P (E.withStore I) σ α} {k' : Option ThreadId → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) .currentThread k)
        (.op (S := Eff E σ) .currentThread k')
  | newThread (b : ThreadBody E) {k : ThreadId → P (E.withStore I) σ α} {k' : ThreadId → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.newThread b) k)
        (.op (S := Eff E σ) (.newThread b) k')
  | block (sw : Option ThreadId) {k : Unit → P (E.withStore I) σ α} {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.block sw) k) (.op (S := Eff E σ) (.block sw) k')
  | resumeThread (t : ThreadId) {k : Unit → P (E.withStore I) σ α} {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.resumeThread t) k)
        (.op (S := Eff E σ) (.resumeThread t) k')
  | hostGet {k : σ → P (E.withStore I) σ α} {k' : σ → P E σ α} :
      (∀ r, ProgRel S (k r) (k' r)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) .hostGet k) (.op (S := Eff E σ) .hostGet k')
  | hostSet (h : σ) {k : Unit → P (E.withStore I) σ α} {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.hostSet h) k) (.op (S := Eff E σ) (.hostSet h) k')
  | emit (o : HostObs) {k : Unit → P (E.withStore I) σ α} {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.emit o) k) (.op (S := Eff E σ) (.emit o) k')
  | readCore {k : CoreEngine.CoreView E (CanonHost E) → P (E.withStore I) σ α}
      {k' : CoreEngine.CoreView E (CanonHost E) → P E σ α} :
      (∀ v, ProgRel S (k v) (k' v)) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) .readCore k) (.op (S := Eff E σ) .readCore k')
  | memWrite (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray) {k : Unit → P (E.withStore I) σ α}
      {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.memWrite m ptr bytes) k)
        (.op (S := Eff E σ) (.memWrite m ptr bytes) k')
  | allocHost (ty : V1.FuncType) (h : CanonHost E) {k : Unit → P (E.withStore I) σ α}
      {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.allocHost ty h) k)
        (.op (S := Eff E σ) (.allocHost ty h) k')
  | prepare (md : E.Module) (imports : List E.ExternVal) {k : Unit → P (E.withStore I) σ α}
      {k' : Unit → P E σ α} :
      ProgRel S (k ()) (k' ()) →
      ProgRel S (.op (S := Eff (E.withStore I) σ) (.prepare md imports) k)
        (.op (S := Eff E σ) (.prepare md imports) k')

variable (S : E.StoreSim I)

/-- Related dispatchers: related programs on every late-bound call. -/
def DispatchRel (d' : Call (E.withStore I) → P (E.withStore I) σ (Ret (E.withStore I)))
    (d : Call E → P E σ (Ret E)) : Prop :=
  ∀ c : Call E, ProgRel S (d' c) (d c)

/-- Related foci: related programs, or the same core activation with related continuations. -/
def FocusRel : Focus (E.withStore I) σ → Focus E σ → Prop
  | .prog p', .prog p => ProgRel S p' p
  | .core t' k', .core t k => t' = t ∧ ∀ vs, ProgRel S (k' vs) (k vs)
  | _, _ => False

/-- Related segments. -/
def SegRel : Seg (E.withStore I) σ → Seg E σ → Prop
  | .prog k', .prog k => ∀ r : Ret E, ProgRel S (k' r) (k r)
  | .core t' k', .core t k => t' = t ∧ ∀ vs, ProgRel S (k' vs) (k vs)
  | _, _ => False

/-- Related activations: the same thread, related foci and segment stacks. -/
def ActRel (a' : Activation (E.withStore I) σ) (a : Activation E σ) : Prop :=
  a'.thread = a.thread ∧ FocusRel S a'.focus a.focus ∧ List.Forall₂ (SegRel S) a'.segs a.segs

/-- **Related configurations**: equal component stores, core stores related by `S.φ`, related
activations, saved continuations and control chains, and equal host state and host-call
records. -/
structure CfgRel (m' : Config (E.withStore I) σ) (m : Config E σ) : Prop where
  store : m.store = m'.store
  core : m.core = S.φ m'.core
  host : m'.host = m.host
  conts : List.Forall₂ (Option.Rel (ActRel S)) m'.conts m.conts
  ctl : List.Forall₂ (ActRel S) m'.ctl m.ctl
  pending : m'.pending = m.pending
  results : m'.results = m.results
  cancels : m'.cancels = m.cancels

/-- Related host events: equal, except that `run` carries related programs. -/
def EventRel : HostEvent (E.withStore I) σ → HostEvent E σ → Prop
  | .invoke c f args, .invoke c' f' args' => c = c' ∧ f = f' ∧ args = args'
  | .tick, .tick => True
  | .cancel c, .cancel c' => c = c'
  | .run p', .run p => ProgRel S p' p
  | _, _ => False

/-- Related labels: equal, except that host events are related by `EventRel`. -/
def LabelRel : Label (E.withStore I) σ → Label E σ → Prop
  | .tau, .tau => True
  | .choice k r, .choice k' r' => (⟨k, r⟩ : ChoiceRecord) = ⟨k', r'⟩
  | .host ev', .host ev => EventRel S ev' ev
  | .obs o, .obs o' => o = o'
  | .trap r, .trap r' => r = r'
  | .core, .core => True
  | _, _ => False

/-- A label of `E.withStore I` as a label of `E`: the same label, except that a `run` event is
replaced by `run (pure .unit)`. On traces without `run` events, `LabelRel S l (labelOf l)`
holds (`Transfer.Thms`). -/
def labelOf : Label (E.withStore I) σ → Label E σ
  | .tau => .tau
  | .choice k r => .choice k r
  | .host (.invoke c f args) => .host (.invoke c f args)
  | .host .tick => .host .tick
  | .host (.cancel c) => .host (.cancel c)
  | .host (.run _) => .host (.run (pure .unit))
  | .obs o => .obs o
  | .trap r => .trap r
  | .core => .core

end Silmaril.Wasm.Component.Machine.Transfer
