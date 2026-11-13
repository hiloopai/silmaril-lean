module

public import Silmaril.Servers.Calls.Defs
import Silmaril.Proofs.Servers.Calls.Shape

@[expose] public section

/-!
# Export calls of a WASI component: the shape theorem and per-call reasoning

* `calls_of_mem`: the completed calls of a play of `ofBody h` are complete runs of `h`
  (`Done`), whose events occur in the play.
* `sat_each`: to show that a component read as a server (`model`) satisfies `each R`, it is
  enough to show `R` of the exchanges of every complete run of one export call on which the
  host satisfies `T`. Proofs in `Silmaril.Proofs.Servers.Calls.Shape`.
-/

namespace Silmaril.Servers.Calls

open Silmaril.Games Silmaril.Wasi

variable {I X : Set FnName} {h : Body I X}

/-- **The completed calls of a play** are complete runs whose events occur in the play. -/
theorem calls_of_mem {s : List (Move (nsig I) (nsig X))} (hs : s ∈ ofBody h) :
    ∃ cs : List ((nsig X).Op × Call), (∀ x ∈ cs, Done h x.1 x.2) ∧
      (∀ x ∈ cs, ∀ e ∈ x.2.inner, e ∈ wtrace s) ∧ calls (wtrace s) = cs.map Prod.snd :=
  Proofs.Servers.Calls.calls_of_mem hs

/-- **Per-call reasoning** for components read as servers. -/
theorem sat_each {J : Iface} {T : WEv → Prop} {ans : Call → Bool} {obs : Call → Exch J → Prop}
    {R : J.Req → J.Resp → Prop}
    (hR : ∀ q c, Done h q c → (∀ e ∈ c.inner, T e) → ans c = true → ∀ x, obs c x → R x.1 x.2) :
    Sat (model T ans obs (ofBody h)) (each R) :=
  Proofs.Servers.Calls.sat_each hR

end Silmaril.Servers.Calls
