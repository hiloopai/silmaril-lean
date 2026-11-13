module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Core

/-!
# Proofs: the stdout theory on the component's answers

How `stdoutTh3w` steps on each answer of the component: `stream.new` records the pair,
`write-via-stream` records the future of a known pair, `stream.write` is accepted
(`wcode` is admissible), `stream.drop-writable` records the end, `future.read` is accepted
unless it reports `ok`, and the other functions leave the state.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3

/-- The step of the corrected stdout theory. -/
theorem stdoutTh3w_step (q : OutSt) (e : WEv) :
    stdoutTh3w.step q e = if outShaped e then outStep q e else some q := rfl

/-- The step of the corrected stdout theory on a well-shaped call. -/
theorem stdoutTh3w_step_of {q : OutSt} {e : WEv} (h : outShaped e = true) :
    stdoutTh3w.step q e = outStep q e := by
  simp [stdoutTh3w_step, h]

/-- A pair found by `wOf` is a recorded pair. -/
theorem wOf_mem {q : OutSt} {r w : Nat} (h : q.wOf r = some w) : (r, w) ∈ q.pairs := by
  unfold OutSt.wOf at h
  cases hf : q.pairs.find? (·.1 = r) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hp := List.mem_of_find?_eq_some hf
    have h1 : p.1 = r := by simpa using List.find?_some hf
    exact h ▸ h1 ▸ hp

/-- `stream.new`. -/
theorem out_new (q : OutSt) (a : List Val) {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    stdoutTh3w.step q (.imp cStreamNew a (some [natV x, natV y])) =
      some { q with pairs := (x, y) :: q.pairs } := by
  rw [stdoutTh3w_step_of rfl]
  unfold outStep
  simp (config := { decide := true }) only [↓reduceIte, natOf_natV hx, natOf_natV hy]

/-- `write-via-stream` with one argument. -/
theorem out_wvs1 (q : OutSt) (v : Val) {f : Nat} (hf : f < 2 ^ 32) :
    stdoutTh3w.step q (.imp stdoutWrite3 [v] (some [natV f])) =
      match natOf v >>= q.wOf with
      | some w => some { q with futs := (f, w) :: q.futs }
      | none => some q := by
  rw [stdoutTh3w_step_of rfl]
  unfold outStep
  simp (config := { decide := true }) only [↓reduceIte, natOf_natV hf]
  rcases h : (natOf v).bind q.wOf with _ | w <;> simp only [Option.bind_eq_bind, h]

/-- `write-via-stream` with another argument list. -/
theorem out_wvs_ne (q : OutSt) {a : List Val} (ha : ∀ v, a ≠ [v]) (f : Nat) :
    stdoutTh3w.step q (.imp stdoutWrite3 a (some [natV f])) = some q := by
  rcases a with _ | ⟨v, _ | ⟨u, rest⟩⟩
  · rfl
  · exact absurd rfl (ha v)
  · rfl

/-- `copyOk` is monotone in the length. -/
theorem copyOk_mono {len len' : Nat} (h : len ≤ len') :
    ∀ {c}, copyOk len c = true → copyOk len' c = true
  | none, _ => rfl
  | some (.completed, k), hc => by simp only [copyOk, decide_eq_true_eq] at hc ⊢; omega
  | some (.dropped, k), hc => hc
  | some (.cancelled, _), hc => hc

/-- `stream.write` of two arguments. -/
theorem out_sw2 (q : OutSt) (wv buf : Val) (n : Nat) :
    stdoutTh3w.step q (.imp cStreamWrite [wv, buf]
      (some [natV (wcode ((swArgs [wv, buf]).elim 0 fun x => x.2.length) n)])) = some q := by
  obtain ⟨c, hc, hok⟩ := wcode_ok ((swArgs [wv, buf]).elim 0 fun x => x.2.length) n
  have hlen : (swArgs [wv, buf]).elim 0 (fun x => x.2.length) ≤ (bytesOf buf).length := by
    simp only [swArgs]
    cases natOf wv <;> simp [List.length_take]
  rw [stdoutTh3w_step_of rfl]
  unfold outStep
  simp (config := { decide := true }) only [↓reduceIte]
  rw [hc]
  simp [copyOk_mono hlen hok]

/-- `stream.write`: the code is accepted. -/
theorem out_sw (q : OutSt) (a : List Val) (n : Nat) :
    stdoutTh3w.step q (.imp cStreamWrite a
      (some [natV (wcode ((swArgs a).elim 0 fun x => x.2.length) n)])) = some q := by
  rcases a with _ | ⟨wv, _ | ⟨buf, _ | ⟨u, rest⟩⟩⟩
  · rfl
  · rfl
  · exact out_sw2 q wv buf n
  · rfl

/-- `stream.drop-writable`: the dropped end is recorded. -/
theorem out_dw (q : OutSt) (a : List Val) :
    ∃ q', stdoutTh3w.step q (.imp cStreamDropW a (some [])) = some q' ∧
      q'.pairs = q.pairs ∧ q'.futs = q.futs ∧ (∀ w ∈ q.dropped, w ∈ q'.dropped) ∧
      ∀ w, arg1 a = some w → w ∈ q'.dropped := by
  rcases a with _ | ⟨v, _ | ⟨u, rest⟩⟩
  · exact ⟨q, rfl, rfl, rfl, fun w hw => hw, fun w hw => by simp [arg1] at hw⟩
  · refine ⟨_, rfl, rfl, rfl, fun w hw => List.mem_append_right _ hw, fun w hw => ?_⟩
    simp only [arg1] at hw
    simp [hw]
  · exact ⟨q, rfl, rfl, rfl, fun w hw => hw, fun w hw => by simp [arg1] at hw⟩

/-- `future.read` answering `BLOCKED` or an error is accepted. -/
theorem out_fr_notok (q : OutSt) (a : List Val) {x : FAns} (hx : x ≠ .ok) :
    stdoutTh3w.step q (.imp cFutureRead a x.enc) = some q := by
  cases x
  · rcases a with _ | ⟨v, _ | ⟨u, rest⟩⟩ <;> rfl
  · exact absurd rfl hx
  · rcases a with _ | ⟨v, _ | ⟨u, rest⟩⟩ <;> rfl

/-- `future.read` answering `ok` is accepted when the future's end has been dropped. -/
theorem out_fr_ok (q : OutSt) (a : List Val)
    (h : ∀ v f w, a = [v] → natOf v = some f → (q.futs.find? (·.1 = f)).map (·.2) = some w →
      w ∈ q.dropped) :
    stdoutTh3w.step q (.imp cFutureRead a FAns.ok.enc) = some q := by
  rcases a with _ | ⟨v, _ | ⟨u, rest⟩⟩
  · rfl
  · show (match natOf v >>= fun f' => (q.futs.find? (·.1 = f')).map (·.2) with
        | some w' => if w' ∈ q.dropped then some q else none
        | none => some q) = some q
    cases hv : natOf v with
    | none => rfl
    | some f =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hw : (q.futs.find? (·.1 = f)).map (·.2) with
      | none => rfl
      | some w => simp [h v f w rfl hv hw]
  · rfl

end Silmaril.Wasi.Versions.P3OverP2
