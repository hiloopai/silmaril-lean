module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLink
public import Silmaril.Proofs.Wasm.Component.Reference.Basic
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Two sequential calls of the linked litmus `dblFwdL` in the reference machine

`dblFwd_seq_ref`: over `core3 neverFail` (the embedder `emb`, no host function), instantiating
`dblFwdL.toRef` once and calling `f(3)` then `f(5)` on that one instance returns `6` then `10`.
Each call goes through the importer's `canon lower` of `g` into the exporter's `canon lift` and
core code, inside the machine. Closed computation of the copied drivers (`decide +kernel`) on the
summary `seqSummary`, read back as a behaviour of `seqBehaviours` (`seq_of_summary`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

/-- Closed instantiation, then two calls of `name` (top-level calls `0` and `1`) under `emb`,
summarised: the outcomes of the two calls. -/
def seqSummary (c : Core3Component) (name : String) (vs vs' : List Value.Val) :
    Option ((Machine.Outcome × Option (Option (List Value.Val))) ×
      (Machine.Outcome × Option (Option (List Value.Val)))) :=
  (emb.instantiateRun first 400 c [] (initConfig ())).bind fun (r, _, es) =>
    (es.lookup name).bind fun f =>
      (emb.callTop first 400 ⟨0⟩ f vs r.config).bind fun r₁ =>
        (emb.callTop first 400 ⟨1⟩ f vs' r₁.config).map fun r₂ =>
          ((r₁.outcome, r₁.config.result? ⟨0⟩), (r₂.outcome, r₂.config.result? ⟨1⟩))

/-- Two resolved calls in a summary are a behaviour of the sequence. -/
theorem seq_of_summary {c : Core3Component} {name : String} {vs vs' rs rs' : List Value.Val}
    (h : seqSummary c name vs vs' =
      some ((.resolved, some (some rs)), (.resolved, some (some rs')))) :
    ([rs], Outcome.returns (some rs')) ∈
      seqBehaviours first.prof (Host.ofEmbedder emb) () c [(name, vs)] name vs' := by
  unfold seqSummary at h
  obtain ⟨⟨r₁, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f, hf, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨ra, ha, h₃⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨rb, hb, h₄⟩ := Option.map_eq_some_iff.mp h₃
  have hr : (ra.outcome = .resolved ∧ ra.config.result? ⟨0⟩ = some (some rs)) ∧
      (rb.outcome = .resolved ∧ rb.config.result? ⟨1⟩ = some (some rs')) := by
    simpa only [Prod.mk.injEq] using h₄
  have hoa : callOutcome? ⟨0⟩ ra = some (.resolved (some rs)) := by
    simp only [callOutcome?, hr.1.1, hr.1.2, Option.map_some]
  have hob : callOutcome? ⟨1⟩ rb = some (.resolved (some rs')) := by
    simp only [callOutcome?, hr.2.1, hr.2.2, Option.map_some]
  have hm : [(name, vs)].mapM (fun q => es.lookup q.1) = some [f] := by
    simp only [List.mapM_cons, List.mapM_nil, hf]
    rfl
  exact Or.inl ⟨r₁.config, inst, es, [f], ra.config, f, instantiateRun_mem emb first hi, hm,
    .cons (emb.callTop_sound first ha hoa) (.nil _ _), hf, callTop_mem emb first hb hob⟩

/-- **Two sequential calls of the linked components** in the reference machine: on one instance
of `dblFwdL`, `f(3)` returns `6`, then `f(5)` returns `10`. -/
theorem dblFwd_seq_ref : ([[toRefVal (.u32 6)]], Outcome.returns (some [toRefVal (.u32 10)])) ∈
    seqBehaviours first.prof (Host.ofEmbedder emb) () dblFwdL.toRef [("f", [toRefVal (.u32 3)])]
      "f" [toRefVal (.u32 5)] :=
  seq_of_summary (by decide +kernel)

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
