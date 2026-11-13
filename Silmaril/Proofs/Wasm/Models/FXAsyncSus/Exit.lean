module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.SusStep

/-!
# After a `suspend`: the branch out of the handler's `block`

The `suspend` rule leaves `fvals A ++ [ref.cont k, br l]` where the handler frame was, inside the
`block btH` label of arity `n` of the encoding. Under an isolated context `E` (the frames below):

* **`exit_unique`**: when `A ++ [cont k]` has exactly `n` values, the `br 0` is the only step:
  it leaves the label with them (`UStepT`);
* **`exit_dead`**: when it has fewer, there is no step at all (`br_short_stuck'`), and the
  configuration is not a result; so it is a dead end of every run.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap Deep Quiet Iso SD UStepT TermFX Inev
  deep_unique_here deep_label_inner local_inv fhead_br_label uniq_brZero ustepT_plug
  step_plug_inv quiet_plug quiet_not_term)
open Silmaril.Wasm.Numerics (GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-- A label around a branch, followed by code, is quiet. -/
theorem quiet_brLabel {n : Nat} {k : List InstrFX} {A : List FVal} {l : LabelIdx}
    {rest T : List AdminFX} :
    Quiet ([.label n k (fvals A ++ .core (.plain (.br l)) :: rest)] ++ T) := by
  refine ⟨⟨[], _, T, rfl, rfl, trivial⟩, fun e hd => ?_⟩
  have hin : Deep e (fvals A ++ .core (.plain (.br l)) :: rest) :=
    deep_label_inner (V := []) hd
  have he : AdminFX.core (.plain (.br l)) = e := deep_unique_here rfl id hin
  rw [← he]
  trivial

/-- **A branch carrying too few values to its label is stuck**, with code after the label. -/
theorem br_short_stuck' {s : Store H} {K : List (Option ContFX)} {F : Frame} {A : List FVal}
    {n : Nat} {k : List InstrFX} {l : LabelIdx} {rest T : List AdminFX} (hl : l.toNat = 0)
    (hn : A.length < n) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, [.label n k (fvals A ++ .core (.plain (.br l)) :: rest)] ++ T⟩ d) :
    False := by
  obtain ⟨V₁, V₂, d₀, -, hh, -⟩ :=
    local_inv (V := []) (T := T) (e := .label n k (fvals A ++ .core (.plain (.br l)) :: rest))
      rfl (by simp) (by simp) h
  obtain ⟨-, hout⟩ := fhead_br_label hh
  rcases hout with ⟨-, vs', vs, hA, hvs, -⟩ | ⟨hl', -⟩
  · have hlen : A.length = vs'.length + vs.length := by rw [hA, List.length_append]
    omega
  · omega

/-- **A dead end**: the short branch under an isolated context has no step and is no result. -/
theorem exit_dead {E : CtxV} (hE : Iso E) {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {A : List FVal} {n : Nat} {k : List InstrFX} {l : LabelIdx} {rest T : List AdminFX}
    (hl : l.toNat = 0) (hn : A.length < n) (G : ConfigFX H → Prop) :
    Inev (SD o fx) TermFX G
      ⟨s, K, f, E.plug ([.label n k (fvals A ++ .core (.plain (.br l)) :: rest)] ++ T)⟩ := by
  have hq : Quiet ([.label n k (fvals A ++ .core (.plain (.br l)) :: rest)] ++ T) := quiet_brLabel
  refine .step (quiet_not_term (quiet_plug hq E hE)) fun d hd => ?_
  obtain ⟨c', hc', -⟩ := step_plug_inv hq E hE s K f d hd
  have hc'' : SD o fx ⟨s, K, E.frameAt f,
      [.label n k (fvals A ++ .core (.plain (.br l)) :: rest)] ++ T⟩ c' := hc'
  exact (br_short_stuck' hl hn hc'').elim

/-- **The unique exit**: the branch carrying the label's arity leaves it, and nothing else
steps. -/
theorem exit_unique {E : CtxV} (hE : Iso E) {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {vs : List FVal} {n : Nat} {l : LabelIdx} {rest T : List AdminFX}
    (hl : l.toNat = 0) (hn : vs.length = n) :
    UStepT o fx ⟨s, K, f, E.plug ([.label n [] (fvals vs ++ .core (.plain (.br l)) :: rest)] ++ T)⟩
      ⟨s, K, f, E.plug (fvals vs ++ T)⟩ := by
  have hq : Quiet ([.label n [] (fvals vs ++ .core (.plain (.br l)) :: rest)] ++ T) :=
    quiet_brLabel
  have h₀ : SD o fx ⟨s, K, E.frameAt f, [.label n [] (fvals [] ++ fvals vs ++
      [.core (.plain (.br l))] ++ rest)]⟩ ⟨s, K, E.frameAt f, fvals vs ++ []⟩ :=
    StepFX'.brLabelZero hl hn
  have h₁ : SD o fx ⟨s, K, E.frameAt f,
      [.label n [] (fvals vs ++ .core (.plain (.br l)) :: rest)] ++ T⟩
      ⟨s, K, E.frameAt f, fvals vs ++ T⟩ := by
    have h := Silmaril.Proofs.Wasm.Models.FXAsyncFX.step_seq [] T h₀
    simpa using h
  have hu : ∀ d, SD o fx ⟨s, K, E.frameAt f,
      [.label n [] (fvals vs ++ .core (.plain (.br l)) :: rest)] ++ T⟩ d →
      d = ⟨s, K, E.frameAt f, fvals vs ++ T⟩ := by
    intro d hd
    have h := uniq_brZero (U := []) (A := []) (T := T) hl hn (by simpa using hd)
    simpa using h
  exact ustepT_plug hE hq h₁ hu

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
