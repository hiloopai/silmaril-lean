module

public import Silmaril.Proofs.Wasm.Component.Reference.SoundSeqI
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusSoundI
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Sequences of calls with imports on the litmus component `fwdS`

`fwd_seq_ir` (every profile, all `x`, `y`, `x'`, `y'`): the IR denotation of `fwdS` over
`impSem P` plays two calls of `f` on one instance, `f(x)` forwarded to the import `g` answered
`y` and returning `y`, then `f(x')` forwarded to `g` answered `y'` and returning `y'`: the two
instance plays `fwd_path` (from the instance's store back to it) are one play of the instance's
strategy, which `seqI_den` turns into a play of the IR.

`fwd_seq_sound` (every profile and component choice profile, all `x`, `y`): an instance of
`SimpleI.sound_seq` for the calls `f(x)` then `f(y)` under the host `g(n) = n + 1` (`fwdG`,
stateless).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- The instance round of `f(x)` forwarded to `g` answered `y`. -/
def fwdRound (x y : BitVec 32) : CRound fwdInst.E fwdInst.F :=
  ⟨fwdQ x, [⟨fwdE x, fwdAI x y⟩], fwdAO x y⟩

/-- The IR round of `f(x)` forwarded to `g` answered `y`. -/
def fwdIRRound (x y : BitVec 32) :
    CRound (sigN fwdS.imports.length) (sigN fwdS.toComp.exports.length) :=
  ⟨(⟨0, by decide⟩, .vals [.u32 x]), [⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩],
    some (.vals [.u32 y])⟩

theorem fwd_irRound (x y : BitVec 32) :
    ∃ j vs, IRRoundI fwdS fwdInst j vs (fwdRound x y) (fwdIRRound x y) :=
  ⟨⟨0, by decide⟩, [.u32 x], [Flat.i32 x],
    [[⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩]], rfl, rfl, rfl,
    .cons (fwd_impRel x y) .nil, rfl⟩

/-- **Two calls of `f` on one instance of `fwdS` are one IR play**, each forwarded to the
import `g` (every profile, all arguments and answers). -/
theorem fwd_seq_ir (P : Profile) (x y x' y' : BitVec 32) :
    seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x]), (⟨0, by decide⟩, [.u32 x'])]
      [[⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩],
        [⟨(⟨0, by decide⟩, .vals [.u32 x']), some (.vals [.u32 y'])⟩]]
      [[.u32 y], [.u32 y']] ∈ fwdS.toComp.den (impSem P) := by
  have hpath : fwdInst.Path P (.idle fwdInst.store)
      (cplay ([fwdRound x y] ++ [fwdRound x' y'])) (.idle fwdStore) := by
    rw [cplay_append]
    exact path_append (fwd_path P x y) (fwd_path P x' y')
  have hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI fwdS fwdInst j vs r u)
      [fwdRound x y, fwdRound x' y'] [fwdIRRound x y, fwdIRRound x' y'] :=
    .cons (fwd_irRound x y) (.cons (fwd_irRound x' y') .nil)
  have h := seqI_den fwdS_good fwd_isInst hrel (cplay_mem_strategy hpath)
  rw [seqMovesI_eq]
  exact h

theorem fwd_typedCalls (x : BitVec 32) :
    fwdS.TypedCalls [(⟨0, by decide⟩, [.u32 x])] := by
  intro q hq
  rw [List.mem_singleton.mp hq]
  rfl

/-- **Soundness for two calls with imports on `fwdS`** (every profile and component choice
profile, all `x`, `y`): every reference behaviour of `f(x)` then `f(y)` on one instance, under
the host `g(n) = n + 1`, is matched by the IR denotation (`SimpleI.sound_seq`). -/
theorem fwd_seq_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x y : BitVec 32) :
    ∀ p ∈ seqBehavioursI prof (answerHost P fwdG) () fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 x)])] "f" [toRefVal (.u32 y)],
      ∃ (wss : List (List Silmaril.Wasm.Component.Val))
        (dss : List (List (Σ _ : (sigN fwdS.imports.length).Op, Option Payload))),
        p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers fwdG d) ∧
        seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x])] dss wss ∈ fwdS.toComp.den (impSem P) ∧
        SeqIRObsI fwdS (fwdS.toComp.den (impSem P)) [(⟨0, by decide⟩, [.u32 x])] dss wss
          ⟨0, by decide⟩ [.u32 y] fwdG p.2 :=
  fun p hp => simpleI_sound_seq P prof fwdS fwdS_good fwdS_inst fwdS_floatFree fwdS_arity fwdG
    fwdG_ok [(⟨0, by decide⟩, [.u32 x])] ⟨0, by decide⟩ [.u32 y] (fwd_typedCalls x) rfl p hp

/-! ## A stateful host -/

/-- The stateful host `g(n) = n + s` in state `s` answers in the IR's types. -/
theorem fwdC_ok : fwdS.HostOkS fwdC := by
  intro s k hk ws rs s' h
  have hk0 : k = 0 := by simpa [fwdS] using hk
  subst hk0
  match ws, h with
  | [.u32 x], h =>
    have hrs : rs = [toRefVal (.u32 (BitVec.ofNat 32 (x.toNat + s)))] := by
      simp only [fwdC, toRefVal, List.map_cons, List.map_nil, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]
      simp only [toRefVal, BitVec.toNat_ofNat]
      congr 2
    exact ⟨[.u32 (BitVec.ofNat 32 (x.toNat + s))], hrs, rfl⟩

/-- **Soundness with imports answered by a stateful host on `fwdS`** (every profile and
component choice profile, all `x` and initial states `s₀`): every reference behaviour of `f(x)`
under the counter host `fwdC` from state `s₀` is matched by the IR denotation (`IRObsIS`). -/
theorem fwd_soundS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (x : BitVec 32)
    (s₀ : Nat) :
    ∀ b ∈ exportBehavioursI prof (answerHostS P fwdC) s₀ fwdS.toRef fwdS.imports "f"
        [toRefVal (.u32 x)],
      IRObsIS (fwdS.toComp.den (impSem P)) ⟨0, by decide⟩ [.u32 x] fwdC s₀ b :=
  simpleI_soundS P prof fwdS fwdS_good fwdS_inst fwdS_floatFree fwdS_arity fwdC fwdC_ok s₀
    ⟨0, by decide⟩ [.u32 x] rfl

/-- **Sequences with a stateful host on `fwdS`**: an instance of `SimpleI.sound_seqS` for the
calls `f(x)` then `f(y)` under the counter host `fwdC` from state `s₀`; the import calls of both
calls are answered with the host state threaded from `s₀`. -/
theorem fwd_seq_soundS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x y : BitVec 32) (s₀ : Nat) :
    ∀ p ∈ seqBehavioursI prof (answerHostS P fwdC) s₀ fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 x)])] "f" [toRefVal (.u32 y)],
      ∃ (wss : List (List Silmaril.Wasm.Component.Val))
        (dss : List (List (Σ _ : (sigN fwdS.imports.length).Op, Option Payload))) (s₁ : Nat),
        p.1 = wss.map (·.map toRefVal) ∧ HostRun fwdC s₀ dss.flatten s₁ ∧
        seqMovesI fwdS [(⟨0, by decide⟩, [.u32 x])] dss wss ∈ fwdS.toComp.den (impSem P) ∧
        SeqIRObsIS fwdS (fwdS.toComp.den (impSem P)) [(⟨0, by decide⟩, [.u32 x])] dss wss
          ⟨0, by decide⟩ [.u32 y] fwdC s₁ p.2 :=
  fun p hp => simpleI_sound_seqS P prof fwdS fwdS_good fwdS_inst fwdS_floatFree fwdS_arity fwdC
    fwdC_ok s₀ [(⟨0, by decide⟩, [.u32 x])] ⟨0, by decide⟩ [.u32 y] (fwd_typedCalls x) rfl p hp

section RefS

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- Instantiation from the host functions' store in host state `s₀`, then two calls of `name`
(top-level calls `0` and `1`), under the stateful embedder `embC`, summarised: the outcomes of
the two calls. -/
def seqSummaryC (c : Core3Component) (ims : Iface) (name : String) (vs vs' : List Value.Val)
    (s₀ : Nat) :
    Option ((Machine.Outcome × Option (Option (List Value.Val))) ×
      (Machine.Outcome × Option (Option (List Value.Val)))) :=
  (embC.instantiateRun first 400 c (importArgs ims)
      (Config.init (hostFuncs 0 ims CStore.empty) s₀)).bind fun (r, _, es) =>
    (es.lookup name).bind fun f =>
      (embC.callTop first 400 ⟨0⟩ f vs r.config).bind fun r₁ =>
        (embC.callTop first 400 ⟨1⟩ f vs' r₁.config).map fun r₂ =>
          ((r₁.outcome, r₁.config.result? ⟨0⟩), (r₂.outcome, r₂.config.result? ⟨1⟩))

/-- Two resolved calls in a summary are a behaviour of the sequence. -/
theorem seq_of_summaryC {c : Core3Component} {ims : Iface} {name : String}
    {vs vs' rs rs' : List Value.Val} {s₀ : Nat}
    (h : seqSummaryC c ims name vs vs' s₀ =
      some ((.resolved, some (some rs)), (.resolved, some (some rs')))) :
    ([rs], Outcome.returns (some rs')) ∈
      seqBehavioursI first.prof (Host.ofEmbedder embC) s₀ c ims [(name, vs)] name vs' := by
  unfold seqSummaryC at h
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
  refine Or.inl ⟨r₁.config, inst, es, [f], ra.config, f, instantiateRun_mem embC first hi, ?_,
    .cons (embC.callTop_sound first ha hoa) (.nil _ _), hf, ?_⟩
  · simp only [List.mapM_cons, List.mapM_nil, hf]
    rfl
  · exact callTop_mem embC first hb hob

/-- **The reference machine threads the host state between calls**: from host state `10`, the
counter host answers the first `f(3)` with `3 + 10 = 13` and the second with `3 + 11 = 14`. -/
theorem fwd_seq_refS : ([[toRefVal (.u32 13)]], Outcome.returns (some [toRefVal (.u32 14)])) ∈
    seqBehavioursI first.prof (Host.ofEmbedder embC) 10 fwdS.toRef fwdS.imports
      [("f", [toRefVal (.u32 3)])] "f" [toRefVal (.u32 3)] :=
  seq_of_summaryC (by decide +kernel)

end RefS

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
