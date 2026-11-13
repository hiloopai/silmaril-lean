module

public import Silmaril.Servers.Calls.Defs
import Silmaril.Proofs.Servers.Calls.Shape

@[expose] public section

/-!
# Export calls of a WASI component: the shape theorem and per-call reasoning

* `calls_of_mem`: the completed calls of a play of `ofBody h` are complete runs of `h`
  (`Done`), whose events occur in the play.
* `mem_model_single`: a complete run of one export call, on which the host satisfies `T`, that
  `ans` counts as answered and `obs` reads as the exchange `x`, makes `[x]` a trace of the
  component read as a server (so that specifications proved with `sat_each` are not vacuous).
* `leads_runP`: a run over a concrete host is a run; `leads_call_pure`, `leads_pure`: the
  shape of a complete run.
* `sat_each`: to show that a component read as a server (`model`) satisfies `each R`, it is
  enough to show `R` of the exchanges of every complete run of one export call on which the
  host satisfies `T`. Proofs in `Silmaril.Proofs.Servers.Calls.Shape`.
-/

namespace Silmaril.Servers.Calls

open Silmaril.Servers.Exchange
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

/-- **A single answered call is a trace** of the component read as a server. -/
theorem mem_model_single {J : Iface} {T : WEv → Prop} {ans : Call → Bool}
    {obs : Call → Exch J → Prop} {q : (nsig X).Op} {u : List WEv}
    {r : Option (List Silmaril.Wasm.Component.Val)}
    (hl : Leads (h q) u (.pure r)) (hT : ∀ e ∈ Call.events ⟨q.1.1, q.2, u, r⟩, T e)
    (ha : ans ⟨q.1.1, q.2, u, r⟩ = true) {x : Exch J} (hx : obs ⟨q.1.1, q.2, u, r⟩ x) :
    [x] ∈ model T ans obs (ofBody h) :=
  Proofs.Servers.Calls.mem_model_single hl hT ha hx

/-- **A complete run is a play** of `ofBody h`, whose only completed call is the run. -/
theorem exists_play {q : (nsig X).Op} {u : List WEv} {r : Option (List Silmaril.Wasm.Component.Val)}
    (hl : Leads (h q) u (.pure r)) :
    ∃ s ∈ ofBody h, calls (wtrace s) = [⟨q.1.1, q.2, u, r⟩] ∧
      wtrace s = Call.events ⟨q.1.1, q.2, u, r⟩ :=
  Proofs.Servers.Calls.exists_play hl

/-- A complete run of a call starts with the call and its answer. -/
theorem leads_call_pure {m : (nsig I).Op} {k : Option (List Silmaril.Wasm.Component.Val) → BProg I}
    {u : List WEv} {r : Option (List Silmaril.Wasm.Component.Val)}
    (hl : Leads (.call m k) u (.pure r)) :
    ∃ n u', u = .req m.1.1 m.2 :: .imp m.1.1 m.2 n :: u' ∧ Leads (k n) u' (.pure r) := by
  cases hl with
  | call _ _ n h => exact ⟨n, _, rfl, h⟩

/-- A run of a returning program is empty. -/
theorem leads_pure {a : Option (List Silmaril.Wasm.Component.Val)} {u : List WEv} {p : BProg I}
    (hl : Leads (.pure a) u p) : u = [] := by
  cases hl
  rfl

/-- A run over a concrete host is a run. -/
theorem leads_runP (impl : Impl) (past : List WEv) (p : BProg I) :
    Leads p (runP impl past p).1 (.pure (runP impl past p).2) := by
  induction p generalizing past with
  | pure r => exact .refl _
  | call m k ih => exact .call m k _ (ih _ _)

/-- Answering one more call by the implementation keeps following it. -/
theorem follows_snoc {impl : Impl} {past : List WEv} (hp : Follows impl past) (f : FnName)
    (a : List Silmaril.Wasm.Component.Val) :
    Follows impl (past ++ [.imp f a (impl past f a)]) := by
  intro p g b r hpr
  rcases List.prefix_concat_iff.1 hpr with he | hp'
  · obtain ⟨rfl, he⟩ := List.append_inj' he rfl
    obtain ⟨rfl, rfl, rfl⟩ := WEv.imp.inj (List.cons.inj he).1
    rfl
  · exact hp p g b r hp'

/-- **The answers of a run over a concrete host follow its implementation.** -/
theorem follows_runP (impl : Impl) (p : BProg I) :
    ∀ past, Follows impl past → Follows impl (past ++ hostView (runP impl past p).1) := by
  induction p with
  | pure r => intro past hp; simpa [runP, hostView] using hp
  | call m k ih =>
    intro past hp
    have h := ih (impl past m.1.1 m.2) _ (follows_snoc hp m.1.1 m.2)
    simpa [runP, hostView, WEv.isImp, List.filter_cons] using h

/-- The host view of a completed call is that of its inner events. -/
theorem hostView_events (c : Call) : hostView c.events = hostView c.inner := by
  simp [hostView, Call.events, List.filter_append, WEv.isImp]

end Silmaril.Servers.Calls
