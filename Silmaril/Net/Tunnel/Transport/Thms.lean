module

public import Silmaril.Net.Tunnel.Transport.Defs

@[expose] public section

/-!
# Connection setups: theorems

PROVED (standard axioms; the TLS guarantee itself is the assumption described in
`Transport.Defs`):

* `endToEnd_protects`: a setup that is end to end TLS (direct TLS, the `OPTIONS`-first mandatory
  RFC 2817 upgrade, and either of these inside any CONNECT tunnels) keeps every request inside
  TLS with the origin on every attacker trace;
* `protects_iff_endToEnd`: for setups without a tunnel, that description is exact;
* `optional_upgrade_downgrade`: an optional RFC 2817 upgrade has an attacker trace with no TLS
  handshake at all (the downgrade);
* `https_setups_protect`: the setups RFC 9110 allows for `https` protect every request;
* `tlsUpgrade_not_https`: no RFC 2817 upgrade is an `https` setup.
-/

namespace Silmaril.Net.Tunnel

theorem protectsTrace_underProxy {o p : Authority} {b : Bool} {tr : List Phase}
    (h : protectsTrace o tr = true) : protectsTrace o (tr.map (Phase.underProxy p b)) = true := by
  simp only [protectsTrace, List.all_eq_true, List.mem_map] at *
  rintro x ⟨y, hy, rfl⟩
  have := h y hy
  match y with
  | .request (some q) => simpa [Phase.underProxy] using this
  | .request none => simp at this
  | .control (some _) | .control none | .tlsHandshake _ =>
    cases b <;> simp [Phase.underProxy]

theorem endToEnd_protects (s : Setup) (h : s.endToEnd = true) : s.protects = true := by
  induction s with
  | directTls o a => simp [Setup.protects, Setup.traces, protectsTrace, Setup.origin]
  | tlsUpgrade o m =>
    cases m <;> simp_all [Setup.endToEnd, Setup.protects, Setup.traces, protectsTrace,
      Setup.origin]
  | connectTunnel p b inner ih =>
    simp only [Setup.endToEnd] at h
    have hi := ih h
    simp only [Setup.protects, Setup.origin, List.all_eq_true, Setup.traces,
      List.mem_map] at hi ⊢
    rintro _ ⟨tr, htr, rfl⟩
    have := protectsTrace_underProxy (p := p) (b := b) (hi tr htr)
    cases b <;> simp_all [protectsTrace]
  | cleartext _ | h2cPriorKnowledge _ | h2cUpgrade _ => simp [Setup.endToEnd] at h

theorem protects_iff_endToEnd (s : Setup) (hs : ∀ p b i, s ≠ .connectTunnel p b i) :
    s.protects = true ↔ s.endToEnd = true := by
  refine ⟨fun h => ?_, endToEnd_protects s⟩
  cases s with
  | connectTunnel p b i => exact absurd rfl (hs p b i)
  | tlsUpgrade o m =>
    cases m <;> simp_all [Setup.endToEnd, Setup.protects, Setup.traces, protectsTrace,
      Setup.origin]
  | _ => simp_all [Setup.endToEnd, Setup.protects, Setup.traces, protectsTrace, Setup.origin]

theorem optional_upgrade_downgrade (o : Authority) :
    ∃ tr ∈ (Setup.tlsUpgrade o .optional).traces, ∀ peer, Phase.tlsHandshake peer ∉ tr :=
  ⟨[.request none], by simp [Setup.traces], by simp⟩

theorem httpsAllowed_endToEnd (s : Setup) (h : s.httpsAllowed = true) : s.endToEnd = true := by
  induction s with
  | directTls => rfl
  | connectTunnel p b inner ih => exact ih h
  | _ => simp [Setup.httpsAllowed] at h

theorem https_setups_protect (s : Setup) (h : s.httpsAllowed = true) : s.protects = true :=
  endToEnd_protects s (httpsAllowed_endToEnd s h)

theorem tlsUpgrade_not_https (o : Authority) (m : TlsUpgradeMode) :
    (Setup.tlsUpgrade o m).httpsAllowed = false := rfl

/-! ## Examples -/

/-- An `https` request through a cleartext proxy: protected end to end. -/
example : (Setup.connectTunnel [0x70] false (.directTls [0x6f] (some .h2))).protects = true := by
  decide

/-- A cleartext `http` request through a TLS proxy: protected on the network hop, but the proxy
is the TLS peer, not the origin. -/
example : (Setup.connectTunnel [0x70] true (.cleartext [0x6f])).protects = false := by decide

/-- RFC 2817 with the upgrade on the real request exposes it. -/
example : (Setup.tlsUpgrade [0x6f] .mandatorySameRequest).protects = false := by decide

end Silmaril.Net.Tunnel
