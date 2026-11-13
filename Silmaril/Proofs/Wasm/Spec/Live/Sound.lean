module

public import Silmaril.Proofs.Wasm.Spec.Live.Ground

@[expose] public section

/-!
# Liveness sentences over `wasmDivSem` are sound for Core 3.0 behaviours

Every profile `P`, every total environment `K`:

* `not_diverges_of_terminates`: **termination**: if `p` satisfies `terminates j` in
  `inst ltlMax (wasmDivSem P)`, no Core invocation of `j` diverges under the host induced by
  `K`; `behaviours_ne_diverges` restates it on `behaviours`.
* `ltlMax_closed_world_div`: every `ltlMax` sentence verified over `wasmDivSem P` holds of a
  maximal behaviour representing each Core divergence (`DivWitness`).
* `ltlMax_closed_world`: every `ltlMax` sentence verified over `wasmDivSem P` holds of a
  maximal behaviour (finite, or an infinite limit) extending a trace of each terminating Core
  behaviour.
-/

namespace Silmaril.Wasm.Spec.Live

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **Termination is sound** (every profile, total environments). -/
theorem not_diverges_of_terminates {P : Profile} {X : WIface} (p : WasmProg X)
    (f : (ifaceSig X.exports).Op)
    (hM : Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p (terminates f.1))
    {K : Env (ifaceSig X.imports)} (htot : Total K) :
    ¬ Diverges P (hostOf X.imports K) (invoke p.store (p.inst.addr f.1) f.2.1) := by
  intro hdiv
  have hsat : (ltlMax FnType (List Val) (Behaviour Val)).Sat ((wasmDivSem P).traces p)
      (terminates f.1) := (models_iff (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p _).1 hM
  exact not_sat_responds_of_witness (fun r hr hne => hne hr) (diverges_witness p htot f hdiv) hsat

/-- Termination on the Core behaviours: `diverges` is not among them. -/
theorem behaviours_ne_diverges {P : Profile} {X : WIface} (p : WasmProg X)
    (f : (ifaceSig X.exports).Op)
    (hM : Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p (terminates f.1))
    {K : Env (ifaceSig X.imports)} (htot : Total K) :
    Behaviour.diverges ∉ behaviours P (hostOf X.imports K) p.store (p.inst.addr f.1) f.2.1 := by
  rintro (⟨c', r, -, -, hr⟩ | ⟨-, hdiv⟩)
  · cases r <;> cases hr
  · exact not_diverges_of_terminates p f hM htot hdiv

/-- **`ltlMax` sentences hold of Core divergence** (every profile, total environments). -/
theorem ltlMax_closed_world_div {P : Profile} {X : WIface} (p : WasmProg X)
    {φ : LTLFm (List Val) (Behaviour Val) X}
    (hM : Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p φ)
    {K : Env (ifaceSig X.imports)} (htot : Total K) (f : (ifaceSig X.exports).Op)
    (hdiv : Diverges P (hostOf X.imports K) (invoke p.store (p.inst.addr f.1) f.2.1)) :
    (∃ t, Maximal ((wasmDivSem P).traces p) t ∧ Event.call f.1 f.2.1 ∈ t ∧
        (∀ j r, Event.ret j r ∈ t → r = .diverges) ∧ LTL.HoldsFin t 0 φ) ∨
      (∃ w ∈ limits ((wasmDivSem P).traces p), (∃ k, w k = Event.call f.1 f.2.1) ∧
        (∀ k j r, w k ≠ Event.ret j r) ∧ LTL.HoldsInf w 0 φ) :=
  sat_of_witness ((models_iff (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p _).1 hM) (diverges_witness p htot f hdiv)

/-- **`ltlMax` sentences hold of terminating Core behaviours** (every profile): a trace of the
behaviour, agreeing with `K`, extends to a maximal behaviour satisfying the sentence. -/
theorem ltlMax_closed_world {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) {φ : LTLFm (List Val) (Behaviour Val) X}
    (hM : Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p φ)
    (K : Env (ifaceSig X.imports)) (hK : ThrowsBelow K p.store.exns.length)
    (f : (ifaceSig X.exports).Op) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ behaviours P (hostOf X.imports K) p.store (p.inst.addr f.1) f.2.1) :
    ∃ t ∈ (wasmDivSem P).traces p, exportEvents t = [.ask f.1 f.2.1, .ans f.1 b] ∧
      (∃ u : List (Ev (ifaceSig X.imports)), K.Agrees u ∧ importEvents t = u.map evOf) ∧
      ((∃ u, t <+: u ∧ Maximal ((wasmDivSem P).traces p) u ∧ LTL.HoldsFin u 0 φ) ∨
        ∃ w ∈ limits ((wasmDivSem P).traces p), prefixList w t.length = t ∧
          LTL.HoldsInf w 0 φ) := by
  have hsat : (ltlMax FnType (List Val) (Behaviour Val)).Sat ((wasmDivSem P).traces p) φ :=
    (models_iff (ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p _).1 hM
  obtain ⟨t, ht, hex, hag⟩ := exists_trace_of_behaviour p hw K hK f hb h
  refine ⟨t, ht, hex, hag, ?_⟩
  rcases exists_maximal_or_limit ((wasmDivSem P).good p) ht with ⟨u, htu, hu⟩ | ⟨w, hw', hwt⟩
  · exact .inl ⟨u, htu, hu, hsat.2 u hu⟩
  · exact .inr ⟨w, hw', hwt, hsat.1 w hw'⟩

end Silmaril.Wasm.Spec.Live
