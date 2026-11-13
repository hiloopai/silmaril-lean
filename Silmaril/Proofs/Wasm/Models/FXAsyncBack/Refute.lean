module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UExit

/-!
# `StepFX'` is not deterministic at `suspend`

The `suspend` rule of `StepFX'` captures the context `E` between the handler and the `suspend`,
and passes the values `vs` just before it as the payload. Nothing fixes where `E` ends and `vs`
begins: any suffix of the values in front of `suspend` can be the payload (the rule is untyped).
So the converse of `kernel_in_fx` cannot be proved by determinism of `StepFX'` alone:

* **`suspend_split`**: with a non-empty payload `v :: vs`, a `suspend` under a handling handler
  has two different successors, one passing `v :: vs` and one passing `vs` (and capturing `v`
  in the continuation);
* **`br_short_stuck`** (deterministic profile, no host calls): after the short split, the branch
  to the handler's label is stuck when it carries fewer values than the label's arity. In the
  encoding of a kernel `suspend t (ar t)` whose frame holds exactly the payload, every short
  split is such a dead end; a longer split (a frame with more operands than the payload) instead
  captures a continuation that is missing operands.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (plug_comp frameAt_comp handles_comp)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

/-- **Two different successors of one `suspend`.** -/
theorem suspend_split {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} {E : CtxV}
    {v : FVal} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    let c : ConfigFX H := ⟨s, K, f, [.handler hs (E.plug (fvals (v :: vs) ++ [.fx (.suspend x)]))]⟩
    let d₁ : ConfigFX H :=
      ⟨s, K ++ [some ⟨E.plug⟩], f, fvals (v :: vs) ++ [.contRef K.length, .core (.plain (.br l))]⟩
    let d₂ : ConfigFX H := ⟨s, K ++ [some ⟨(comp E (.seq [v] .hole [])).plug⟩], f,
      fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
    StepFX' P host fx c d₁ ∧ StepFX' P host fx c d₂ ∧ d₁ ≠ d₂ := by
  intro c d₁ d₂
  have hE' : ¬ (comp E (.seq [v] .hole [])).Handles ta := by
    rw [handles_comp]
    rintro (h | h)
    · exact hE h
    · exact h
  have ht' : s.tag? ((comp E (.seq [v] .hole [])).frameAt f) x = some (ta, ti) := by
    rw [frameAt_comp]
    exact ht
  have h₁ : StepFX' P host fx c d₁ := StepFX'.suspend ht hE hc
  have hplug : (comp E (.seq [v] .hole [])).plug (fvals vs ++ [.fx (.suspend x)]) =
      E.plug (fvals (v :: vs) ++ [.fx (.suspend x)]) := by
    simp [plug_comp, CtxV.plug]
  have h₂ : StepFX' P host fx c d₂ := by
    have h := StepFX'.suspend (P := P) (host := host) (fx := fx) (K := K) (vs := vs) ht' hE' hc
    rw [hplug] at h
    exact h
  have hne : d₁ ≠ d₂ := by
    intro h
    have hl := congrArg (fun d : ConfigFX H => d.code.length) h
    simp [d₁, d₂] at hl
  exact ⟨h₁, h₂, hne⟩

/-- **A branch carrying too few values to its label is stuck.** -/
theorem br_short_stuck {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {F : Frame} {A : List FVal} {n : Nat}
    {k : List InstrFX} {l : LabelIdx} {rest : List AdminFX} (hl : l.toNat = 0)
    (hn : A.length < n) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, [.label n k (fvals A ++ .core (.plain (.br l)) :: rest)]⟩ d) : False := by
  obtain ⟨V₁, V₂, d₀, -, hh, -⟩ :=
    local_inv (V := []) (T := []) (e := .label n k (fvals A ++ .core (.plain (.br l)) :: rest))
      rfl (by simp) (by simp) h
  obtain ⟨-, hout⟩ := fhead_br_label hh
  rcases hout with ⟨-, vs', vs, hA, hvs, -⟩ | ⟨hl', -⟩
  · have hlen : A.length = vs'.length + vs.length := by rw [hA, List.length_append]
    omega
  · omega

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
