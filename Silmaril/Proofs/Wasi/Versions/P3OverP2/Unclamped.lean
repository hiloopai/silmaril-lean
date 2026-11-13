module

public import Silmaril.Wasi.Versions.P3OverP2.Bounds.Defs
public import Silmaril.Wasi.Versions.P2OverP3.Sep.Thms

/-!
# Proofs: an unclamped `now` is not correct over the loose 0.2 theory

`latePlay` is the play of `p3OverP2u` (the component with `now` not clamped) on `lateCalls`:
`now` answers `5`, `wait-for 10` returns, `now` answers `6`. Its 0.2 answers are accepted by the
loose 0.2 theory `p2ThF F` (for every `F`): the 0.2 theory does not relate the readiness of
`subscribe-duration` to `now`. Its 0.3 answers are rejected by `clockTh3s`, which owes
`now ≥ 15`. The play is computed by `Silmaril.Wasi.Versions.P2OverP3.session`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2 (p2Command)
open Silmaril.Wasi.Versions.P2OverP3 (session session_mem)

/-- The session of `lateCalls` runs to its end. -/
theorem lateSession_isSome : (session bodyU init lateCalls).isSome = true := by decide +kernel

/-- **The late play** of the unclamped variant. -/
def latePlay : List (Move (nsig p2Command.imports) (nsig p3World.imports)) :=
  ((session bodyU init lateCalls).get lateSession_isSome).1

/-- `latePlay` is a play of `p3OverP2u`. -/
theorem latePlay_mem : latePlay ∈ p3OverP2u := by
  obtain ⟨⟨ms, s'⟩, hs⟩ := Option.isSome_iff_exists.1 lateSession_isSome
  have hp : latePlay = ms := by simp [latePlay, hs]
  rw [hp]
  exact session_mem hs

/-- The loose 0.2 theory accepts its 0.2 answers. -/
theorem latePlay_p2 : (P2.p2Th .loose).Accepts (hostView (wtrace latePlay)) :=
  (Protocol.acceptsB_iff _ _).1 (by decide +kernel)

/-- The saturated 0.3 clock theory rejects its 0.3 answers. -/
theorem latePlay_not_clock : ¬ clockTh3s.Accepts (retAsImp (wtrace latePlay)) := by
  intro h
  have hb := (Protocol.acceptsB_iff _ _).2 h
  revert hb
  decide +kernel

/-- `fsRead2 F` accepts every run without 0.2 reads and keeps its state. -/
theorem fsRead2_run_noRd (F : BitVec 32 → List (BitVec 8)) :
    ∀ (t : List WEv) (q : RdSt), t.all noRd2 = true → (fsRead2 F).run q t = some q
  | [], _, _ => rfl
  | e :: t, q, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have hstep : (fsRead2 F).step q e = some q := by
      have he : noRd2 e = true := h.1
      cases e with
      | imp f a r =>
        simp only [noRd2, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at he
        simp [fsRead2, rd2Step, he.1.1, he.1.2, he.2]
      | _ => rfl
    rw [Protocol.run_cons, hstep, Option.bind_some]
    exact fsRead2_run_noRd F t q h.2

/-- The loose 0.2 theory with any file contents accepts the 0.2 answers of `latePlay`. -/
theorem latePlay_p2F (F : BitVec 32 → List (BitVec 8)) :
    (p2ThF F).Accepts (hostView (wtrace latePlay)) := by
  rw [p2ThF, Protocol.accepts_prod_iff]
  refine ⟨latePlay_p2, ?_⟩
  unfold Protocol.Accepts
  rw [fsRead2_run_noRd F _ _ (by decide +kernel)]
  rfl

/-- **REFUTED: an unclamped `now`.** The variant of `p3OverP2` that answers the 0.2 instant is
not a model of the saturated 0.3 clock theory over the loose 0.2 theory `p2ThF F`: the loose
host of `p2ThF F` can give the answers of `latePlay`. -/
theorem p3OverP2u_not_clock (F : BitVec 32 → List (BitVec 8)) :
    ¬ (agP (p2ThF F) (retG clockTh3s)).holds p3OverP2u :=
  fun h => latePlay_not_clock ((accepts_retG _ _).1 (h _ latePlay_mem (latePlay_p2F F)))

end Silmaril.Wasi.Versions.P3OverP2
