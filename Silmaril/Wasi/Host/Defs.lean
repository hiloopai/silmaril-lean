module

public import Silmaril.Wasi.World.Defs
public import Silmaril.Games.Composition.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

@[expose] public section

/-!
# WASI hosts: loose and concrete models of the imports

A **host** of the imports `I` is a strategy `Host Y I = Strategy Y (nsig I)`: it serves the
import calls of the component above it, possibly calling a lower interface `Y` (the operating
system; `Silmaril.Games.Sig.empty` for a closed host). It is the model of the dual game of a
world, in the same institution `Silmaril.Games.GInst` as the components.

* `hev`, `htrace`: the host's answers, as `WEv.imp` events (the host view of
  `Silmaril.Wasi.World`).
* `hostSat P`: the host's answers always satisfy `P` (a WASI theory, e.g. a protocol's
  acceptance).
* `ofPred P`: the host whose plays are the legal plays whose answers satisfy the prefix-closed
  `P`. It is the **loose** host of `P` (`loose T` for a protocol `T`): the largest host
  satisfying `P` (`Silmaril.Wasi.Host.Thms`), which answers in any way `P` allows.
* `Impl`, `Follows`, `concrete impl`: a **concrete** host, answering every call by a
  function of the answers given so far.
* `link η σ`: the component `σ` linked over the host `η` (`Strategy.comp`), with the export
  view `xtrace`.

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

variable {Y : Sig.{0}} {I X : Set FnName}

/-- Hosts of the imports `I` over the lower interface `Y`. -/
abbrev Host (Y : Sig.{0}) (I : Set FnName) : Type := Strategy Y (nsig I)

/-- The event of a host's move: its answers. -/
def hev : Move Y (nsig I) → Option WEv
  | .inr (.ans m n) => some (.imp m.1.1 m.2 n)
  | _ => none

/-- The answers of a host's play. -/
def htrace (s : List (Move Y (nsig I))) : List WEv := s.filterMap hev

/-- **The host satisfies the theory `P`**: its answers always satisfy `P`. -/
def hostSat (P : List WEv → Prop) : GSen Y (nsig I) := ⟨fun η => ∀ s ∈ η, P (htrace s)⟩

/-- Prefix-closed predicates on events (safety properties). -/
def PrefixClosed (P : List WEv → Prop) : Prop := P [] ∧ ∀ ⦃a b⦄, a <+: b → P b → P a

/-- Opponent moves of a host carry no answer. -/
theorem hev_of_isO {o : Move Y (nsig I)} (ho : o.IsO) : hev o = none := by
  rcases o with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩)
  · exact False.elim ho
  · rfl
  · rfl
  · exact False.elim ho

/-- An Opponent move does not change the answers. -/
theorem htrace_concat_of_isO (s : List (Move Y (nsig I))) {o : Move Y (nsig I)} (ho : o.IsO) :
    htrace (s ++ [o]) = htrace s := by
  rw [htrace, List.filterMap_append, List.filterMap_cons, hev_of_isO ho]
  exact List.append_nil _

/-- **The host of a prefix-closed theory**: every legal play whose answers satisfy `P`. -/
def ofPred (P : List WEv → Prop) (hP : PrefixClosed P) : Host Y I where
  plays := {s | Legal s ∧ P (htrace s)}
  nil_mem := ⟨Legal.nil, hP.1⟩
  legal h := h.1
  of_prefix := fun ⟨hl, hp⟩ hst => ⟨hl.of_prefix hst, hP.2 (hst.filterMap hev) hp⟩
  receptive := fun {s _ y _} ⟨_, hp⟩ hx hxy ho =>
    ⟨⟨y, hx.append (Path.single hxy)⟩, (htrace_concat_of_isO s ho).symm ▸ hp⟩

/-- Protocol acceptance is prefix-closed. -/
theorem prefixClosed_accepts {S : Type} (T : Protocol S WEv) : PrefixClosed T.Accepts :=
  ⟨Protocol.accepts_nil T, fun _ _ h hb => hb.of_prefix h⟩

/-- **The loose host of a theory**: it answers in every way the protocol `T` allows. -/
def loose {S : Type} (T : Protocol S WEv) : Host Y I := ofPred T.Accepts (prefixClosed_accepts T)

/-- A host implementation: the answer to `f args` after the answers so far. -/
abbrev Impl : Type := List WEv → FnName → List Val → Option (List Val)

/-- The answers follow the implementation. -/
def Follows (impl : Impl) (t : List WEv) : Prop :=
  ∀ p f a r, p ++ [WEv.imp f a r] <+: t → r = impl p f a

/-- Following an implementation is prefix-closed. -/
theorem prefixClosed_follows (impl : Impl) : PrefixClosed (Follows impl) := by
  refine ⟨fun p f a r hp => ?_, fun _ _ hab hb p f a r hp => hb p f a r (hp.trans hab)⟩
  exact absurd (List.prefix_nil.1 hp) (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _))

/-- **The concrete host of an implementation.** -/
def concrete (impl : Impl) : Host Y I := ofPred (Follows impl) (prefixClosed_follows impl)

/-! ## Linking -/

/-- The component `σ` linked over the host `η`: the imports are served by the host and hidden. -/
def link (η : Host Y I) (σ : Strategy (nsig I) (nsig X)) : Strategy Y (nsig X) := η.comp σ

/-- The event of a move of a linked system: its export calls and returns. -/
def xev : Move Y (nsig X) → Option WEv
  | .inr (.ask q) => some (.call q.1.1 q.2)
  | .inr (.ans q n) => some (.ret q.1.1 q.2 n)
  | .inl _ => none

/-- The export events of a play of a linked system. -/
def xtrace (p : List (Move Y (nsig X))) : List WEv := p.filterMap xev

/-- A protocol on the export events only (the other events are skipped): a guarantee
observable by the client of a linked system. -/
def onExp {S : Type} (G : Protocol S WEv) : Protocol S WEv :=
  ⟨G.init, fun q e => if e.isExp then G.step q e else some q⟩

end Silmaril.Wasi
