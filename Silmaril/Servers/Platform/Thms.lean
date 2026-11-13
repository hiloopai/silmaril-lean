module

public import Silmaril.Servers.Platform.Defs
import Silmaril.Servers.Reuse.Thms
import Silmaril.Proofs.Servers.Platform.Basic

/-!
# Platforms: theorems

PROVED (standard axioms):

* `Refines.refl`, `Refines.trans`, **`Refines.sat`**: refinement across platforms is a preorder
  and transports satisfaction of trace specifications from the refined implementation.
* `Refines.map`: refinement is preserved by a change of observation (`Platform.map`).
* `seq_refines_host`, `fresh_refines_host`: a handler on one reused instance, or on fresh
  instances, refines the same handler under a pooling host.
* `host_sat_of_inv`: an invariant that makes every step answer within `H` gives the pointwise
  specification of `H` under every host.
* **`web_host_iff`**, **`cgi_hello_iff`**, **`cgi_hello_equiv_host`**: the hello CGI script on
  any files and a stateless component answering the constant web under any `wasi:http` host
  have the same traces (each exchange answers `helloResponse`, `HEAD` without content): a
  cross-platform equivalence, refinement both ways.
* `cgi_view`, `container_view`: a CGI script is the sequential handler of its origin; a
  container is its entry point's process at the launch invocation (by definition).
* `merge_single`: one connection's log is a sequential log.
-/

@[expose] public section

namespace Silmaril.Servers.Platform

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers Silmaril.Servers.Reuse

variable {T U σ : Type}

namespace Refines

variable {P Q R : Platform T}

theorem refl (i : P.Impl) : Refines P P i i := fun _ h => h

theorem trans {i : P.Impl} {j : Q.Impl} {k : R.Impl} (h₁ : Refines P Q i j)
    (h₂ : Refines Q R j k) : Refines P R i k := fun t h => h₂ t (h₁ t h)

/-- **Refinement transports specifications.** -/
theorem sat {i : P.Impl} {j : Q.Impl} {φ : T → Prop} (h : Refines P Q i j) (hj : Q.Sat j φ) :
    P.Sat i φ := fun t ht => hj t (h t ht)

theorem map (f : T → U → Prop) {i : P.Impl} {j : Q.Impl} (h : Refines P Q i j) :
    Refines (Platform.map f P) (Platform.map f Q) i j := fun _ ⟨o, ho, t, hr, hf⟩ =>
  let ⟨o', ho', hr'⟩ := h t ⟨o, ho, hr⟩
  ⟨o', ho', t, hr', hf⟩

end Refines

theorem seq_refines_host (i : Origin σ × σ) :
    Refines (seq σ) (host σ) i i :=
  fun _ ⟨_, ho, hr⟩ => ⟨_, seq_hostRuns ho, hr⟩

theorem fresh_refines_host (i : Origin σ × σ) :
    Refines (fresh σ) (host σ) i i :=
  fun _ ⟨_, ho, hr⟩ => ⟨_, fresh_hostRuns ho, hr⟩

theorem host_sat_of_inv {O : Origin σ} {s₀ : σ} (Inv : σ → Prop)
    (H : Request → Response → Prop) (h0 : Inv s₀)
    (hstep : ∀ s r resp s', Inv s → O s r resp s' → Inv s')
    (hH : ∀ s r resp s', Inv s → O s r resp s' → H r resp) :
    (host σ).Sat (O, s₀) (fun l => ∀ p ∈ l, H p.1 p.2) :=
  fun _ ⟨_, ho, hr⟩ => hr ▸ hostRuns_of_inv Inv H h0 hstep hH ho

theorem cgi_view (g : Cgi.Gateway) (S : Spec) (fs : Fs) :
    (cgi g).view (S, fs) = (seq Fs).view (Cgi.origin g S, fs) := rfl

theorem container_view (fr : Framing) (P : SockSem) (c : Container) :
    (container fr).view (P, c) = (linux fr).view (P, c.launch) := rfl

/-- A stateless component of a web under any host: each exchange answers the web. -/
theorem web_host_iff (W : Origin.Web) (l : Log) :
    (host Unit).view (Origin.ofTargets W, ()) l ↔
      ∀ p ∈ l, p.2 = Origin.webAnswer W p.1 :=
  ⟨fun ⟨_, ho, hr⟩ => hr ▸ (Proofs.Servers.Platform.web_host_iff W _).mp ho,
    fun h => ⟨l, (Proofs.Servers.Platform.web_host_iff W l).mpr h, rfl⟩⟩

/-- The hello CGI script on any files: each exchange answers `helloResponse`. -/
theorem cgi_hello_iff (g : Cgi.Gateway) (fs : Fs) (l : Log) :
    (cgi g).view (Cgi.hello, fs) l ↔
      ∀ p ∈ l, p.2 = Origin.webAnswer (fun _ => Cgi.helloResponse) p.1 :=
  ⟨fun ⟨_, ho, hr⟩ => hr ▸ (Proofs.Servers.Platform.cgi_hello_iff g fs _).mp ho,
    fun h => ⟨l, (Proofs.Servers.Platform.cgi_hello_iff g fs l).mpr h, rfl⟩⟩

/-- **The hello CGI script and the hello component under any host are equivalent.** -/
theorem cgi_hello_equiv_host (g : Cgi.Gateway) (fs : Fs) :
    Refines (cgi g) (host Unit) (Cgi.hello, fs)
        (Origin.ofTargets fun _ => Cgi.helloResponse, ()) ∧
      Refines (host Unit) (cgi g)
        (Origin.ofTargets fun _ => Cgi.helloResponse, ()) (Cgi.hello, fs) :=
  ⟨fun l h => (web_host_iff _ l).mpr ((cgi_hello_iff g fs l).mp h),
    fun l h => (cgi_hello_iff g fs l).mpr ((web_host_iff _ l).mp h)⟩

theorem merge_single (l : Log) : Merge [l] l :=
  .cons .nil (Proofs.Servers.Platform.interleave_nil_right l)

end Silmaril.Servers.Platform
