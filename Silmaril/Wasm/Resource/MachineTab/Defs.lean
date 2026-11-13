module

public import Silmaril.Wasm.Resource.CompTable.Defs

@[expose] public section

/-!
# Handle tables along whole runs of the reference machine

`Silmaril.Wasm.Resource.CompTable` reads successful runs of the resource built-in **cores** as
table histories. This file sets up the frame argument for **whole machine runs**: every store
update of every program the machine runs moves each handle table by a successful table history.

* `vtab s j`: the handle table of instance `j` in store `s`, `Table.empty` when `j` is not
  (yet) an instance (instances are allocated with an empty table).
* `TabMove j s s'`: the table of `j` goes from `vtab s j` to `vtab s' j` through a successful
  table history (`Table.Steps`); `TabFrom j s₀`: the stores reachable from `s₀` in this sense.
* `TabProg j p`: every store update `p` can issue preserves `TabFrom j s₀`, for every `s₀`
  (`P.Inv`, the program logic of the reference programs). Equivalently every `modify f`
  issued by `p` is a table move on `j` from every store.
* `FocusTab`, `SegTab`, `ActTab`, `CfgTab j m`: every program in configuration `m` (running
  activations, their pending continuations, and the saved activations of blocked threads) is a
  `TabProg j`, for every argument of its continuations.
* `TabDispatch j dispatch`: every program of the dispatcher is a `TabProg j`;
  `TabHost j host`: so are the host's programs (host functions, embedder imports, host thread
  bodies, buffers and cancellation hooks).
* `RunTab j tr`: the host-frame programs `HostEvent.run p` of a trace are `TabProg j`.

The frame theorems are in `Silmaril.Wasm.Resource.MachineTab.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type}

/-- The handle table of instance `j`, empty if `j` is not an instance. -/
def vtab (s : CStore E) (j : InstId) : Silmaril.Wasm.Component.Runtime.Table HandleEntry := (handles? s j).getD Table.empty

/-- The handle table of `j` moves from `s` to `s'` through a successful table history. -/
def TabMove (j : InstId) (s s' : CStore E) : Prop :=
  ∃ evs, Table.Steps (vtab s j) evs (vtab s' j)

/-- The stores whose table of `j` is reached from that of `s₀` by a successful history. -/
def TabFrom (j : InstId) (s₀ : CStore E) (s : CStore E) : Prop := TabMove j s₀ s

/-- Every store update of `p` moves the table of `j` by a successful history. -/
def TabProg {α : Type} (j : InstId) (p : P E σ α) : Prop :=
  ∀ s₀, P.Inv (TabFrom j s₀) p

/-- The programs of a focus are table-moving. -/
def FocusTab (j : InstId) : Focus E σ → Prop
  | .prog p => TabProg j p
  | .core _ k => ∀ vs, TabProg j (k vs)

/-- The programs of a pending continuation are table-moving. -/
def SegTab (j : InstId) : Seg E σ → Prop
  | .prog k => ∀ r, TabProg j (k r)
  | .core _ k => ∀ vs, TabProg j (k vs)

/-- The programs of an activation are table-moving. -/
def ActTab (j : InstId) (a : Activation E σ) : Prop :=
  FocusTab j a.focus ∧ ∀ g ∈ a.segs, SegTab j g

/-- Every program of a configuration is table-moving. -/
def CfgTab (j : InstId) (m : Config E σ) : Prop :=
  (∀ a ∈ m.ctl, ActTab j a) ∧ ∀ t a, m.cont? t = some a → ActTab j a

/-- Every program of a dispatcher is table-moving. -/
def TabDispatch (j : InstId) (dispatch : Call E → P E σ (Ret E)) : Prop :=
  ∀ c, TabProg j (dispatch c)

/-- Every program of a host is table-moving. -/
structure TabHost (j : InstId) (host : HostImpl E σ) : Prop where
  funcs : ∀ fn c, TabProg j (host.funcs fn c)
  embedder : ∀ n ft args, TabProg j (host.embedder n ft args)
  threadBody : ∀ fn t, TabProg j (host.threadBody fn t)
  buffer : ∀ op, TabProg j (host.buffer op)
  cancel : ∀ n, TabProg j (host.cancel n)

/-- The host-frame programs of a trace are table-moving. -/
def RunTab (j : InstId) (tr : List (Label E σ)) : Prop :=
  ∀ p, Label.host (.run p) ∈ tr → TabProg j p

end Silmaril.Wasm.Resource
