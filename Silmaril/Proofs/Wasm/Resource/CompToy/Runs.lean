module

public import Silmaril.Wasm.Resource.CompToy.Defs
public import Silmaril.Wasm.Resource.CompProvider.Thms
public import Silmaril.Wasm.Component.Reference.Thms
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The toy resource component: executable runs and the refutation of the buggy variant

* `toyComp_valid`, `bugComp_valid`: the reference validator accepts both components;
* `callSeq_runCalls`, `session_runCalls`: a successful executable session is an instantiation
  and a multi-call run (`RunCalls`) of `refMultiSem`;
* `session_toy`, `session_toyTwo`, `session_bug` (kernel evaluation of the copied drivers over
  `core3 neverFail`): the toy's session `make`, `make`, `get(borrow 0)`, `drop(own 0)`, `make`
  answers `own 0`, `own 1`, `u32 0`, `[]`, `own 2`; two `make` calls of the buggy component
  both answer `own 7`; `sessionCtrs_toy`, `sessionCtrs_bug`: the counter `toyCtr` along them;
* **`bug_not_compProvider`**: the buggy component violates `compProviderSpec makeE dropE` in
  `refMultiSem` (through `compProvider_refuted_of_reuse`);
* `toySession_trace`, `toySession_accepted`: the toy's session is a multi-call trace of the toy,
  accepted by the sentence.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Core3Adder
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-! ## Validity -/

theorem exists_of_accepts {c : Core3Component} (h : accepts c = true) :
    ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c = .ok ct := by
  unfold accepts at h
  split at h
  next ct hc => exact ⟨ct, hc⟩
  next => cases h

/-- The reference validator accepts the toy. -/
theorem toyComp_valid : ∃ ct, Valid Silmaril.Wasm.Component.Features.p2 toyComp ct :=
  (exists_of_accepts (c := toyComp) (by decide +kernel)).imp fun _ => check?_sound

/-- … and the buggy component. -/
theorem bugComp_valid : ∃ ct, Valid Silmaril.Wasm.Component.Features.p2 bugComp ct :=
  (exists_of_accepts (c := bugComp) (by decide +kernel)).imp fun _ => check?_sound

/-! ## Sessions -/

/-- The host of the executable runs. -/
abbrev H0 : Host E0 Unit := Host.ofEmbedder emb

/-- A resolved executable top-level call is a `Calls` fact of the embedder's host. -/
theorem calls_of_callTop {fuel k : ℕ} {f : FuncId} {args : List Silmaril.Wasm.Component.Reference.Val} {m : Config E0 Unit}
    {r : RunResult E0 Unit first.State} {res : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (h : emb.callTop first fuel ⟨k⟩ f args m = some r) (ho : r.outcome = .resolved)
    (hr : r.config.result? ⟨k⟩ = some res) :
    Calls first.prof H0.hr H0.dispatch m ⟨k⟩ f args r.config (.resolved res) := by
  have hc : callOutcome? ⟨k⟩ r = some (.resolved res) := by
    simp only [callOutcome?, ho, hr, Option.map_some]
  exact emb.callTop_sound first h hc

/-- One resolved call of `callSeq`. -/
theorem callSeq_cons {es : List (String × FuncId)} {k : ℕ} {j : Xt.Exp} {a : List Silmaril.Wasm.Component.Reference.Val}
    {cs : List (Xt.Exp × List Silmaril.Wasm.Component.Reference.Val)} {m m' : Config E0 Unit} {ds : List (DoneCall Xt)}
    (h : callSeq es k ((j, a) :: cs) m = some (ds, m')) :
    ∃ f r res ds', es.lookup (names j) = some f ∧
      Calls first.prof H0.hr H0.dispatch m ⟨k⟩ f a r (.resolved res) ∧
      callSeq es (k + 1) cs r = some (ds', m') ∧ ds = ⟨j, a, res⟩ :: ds' := by
  obtain ⟨f, hf, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hc, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  revert h₂
  split
  · rename_i res ho hres
    intro h₃
    obtain ⟨⟨ds', m''⟩, hs, he⟩ := Option.map_eq_some_iff.mp h₃
    have he' : ds = ⟨j, a, res⟩ :: ds' ∧ m' = m'' := by
      simpa only [Prod.mk.injEq, eq_comm] using he
    have hs' : callSeq es (k + 1) cs r.config = some (ds', m') := he'.2 ▸ hs
    exact ⟨f, r.config, res, ds', hf, calls_of_callTop hc ho hres, hs', he'.1⟩
  · intro h₃
    cases h₃

/-- **A successful `callSeq` is a multi-call run.** -/
theorem callSeq_runCalls {es : List (String × FuncId)} :
    ∀ {k : ℕ} {cs : List (Xt.Exp × List Silmaril.Wasm.Component.Reference.Val)} {m m' : Config E0 Unit} {ds : List (DoneCall Xt)},
      callSeq es k cs m = some (ds, m') → RunCalls first.prof H0 names es m k ds m'
  | k, [], m, m', ds, h => by
    have he : ([], m) = (ds, m') := Option.some.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact .nil m k
  | k, (j, a) :: cs, m, m', ds, h => by
    obtain ⟨f, r, res, ds', hf, hc, hs, rfl⟩ := callSeq_cons h
    exact .cons hf hc (callSeq_runCalls hs)

/-- **A successful session is an instantiation and a multi-call run.** -/
theorem session_runCalls {c : Core3Component} {cs : List (Xt.Exp × List Silmaril.Wasm.Component.Reference.Val)}
    {l : List (Xt.Exp × List Silmaril.Wasm.Component.Reference.Val × Option (List Silmaril.Wasm.Component.Reference.Val))} (h : session c cs = some l) :
    ∃ m₀ inst es ds mₙ,
      InstResult.instance m₀ inst es ∈ instBehaviours first.prof H0 (initConfig ()) c [] ∧
      RunCalls first.prof H0 names es m₀ 0 ds mₙ ∧ ds.map (fun d => (d.exp, d.args, d.res)) = l := by
  unfold session at h
  obtain ⟨⟨r, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨ds, mₙ⟩, hs, hl⟩ := Option.map_eq_some_iff.mp h₁
  exact ⟨r.config, inst, es, ds, mₙ, emb.instantiateRun_sound first hi, callSeq_runCalls hs, hl⟩

theorem session_toy :
    session toyComp toySession = some [(makeE, [], some [.own 0]), (makeE, [], some [.own 1]),
      (getE, [.borrow 0], some [Value.Val.u32 0]), (dropE, [.own 0], some []),
      (makeE, [], some [.own 2])] := by
  decide +kernel

theorem session_toyTwo :
    session toyComp twoMakes = some [(makeE, [], some [.own 0]), (makeE, [], some [.own 1])] := by
  decide +kernel

theorem session_bug :
    session bugComp twoMakes = some [(makeE, [], some [.own 7]), (makeE, [], some [.own 7])] := by
  decide +kernel

/-- The toy's counter (`toyCtr`) along its session: `0` after instantiation, then `1`, `2`, `2`,
`2`, `3`; each `make` returning `own n` goes from counter `n` to `n + 1`, as `CtrVCOn.fresh`
asks. -/
theorem sessionCtrs_toy : sessionCtrs toyComp toySession = some [0, 1, 2, 2, 2, 3] := by
  decide +kernel

/-- The buggy component's counter never moves. -/
theorem sessionCtrs_bug : sessionCtrs bugComp twoMakes = some [0, 0, 0] := by
  decide +kernel

/-- The resolved calls of a session, read back. -/
theorem doneCalls_eq {ds : List (DoneCall Xt)} {l : List (Xt.Exp × List Silmaril.Wasm.Component.Reference.Val × Option (List Silmaril.Wasm.Component.Reference.Val))}
    (h : ds.map (fun d => (d.exp, d.args, d.res)) = l) :
    ds = l.map fun (j, a, r) => ⟨j, a, r⟩ := by
  subst h
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, ← ih]

/-- **The buggy component is refuted**: its `make` returns the live representation `7` again, so
it violates the provider sentence over several calls (Core 3.0 with the never-failing grow
oracle, the first-alternative oracle's choice profile, no host functions). -/
theorem bug_not_compProvider :
    ¬ Models (protoLogic CFn (List RVal) Component.Outcome (Option (List ℕ)))
      (refMultiSem first.prof H0 ()) bugProg (compProviderSpec makeE dropE) := by
  obtain ⟨m₀, inst, es, ds, mₙ, hi, hr, hl⟩ := session_runCalls session_bug
  have hds : ds = [⟨makeE, [], some [.own 7]⟩, ⟨makeE, [], some [.own 7]⟩] := doneCalls_eq hl
  exact compProvider_refuted_of_reuse (p := bugProg) hi (hds ▸ hr)

/-- The calls of the toy's session. -/
def toySessionCalls : List (DoneCall Xt) :=
  [⟨makeE, [], some [.own 0]⟩, ⟨makeE, [], some [.own 1]⟩,
    ⟨getE, [.borrow 0], some [Value.Val.u32 0]⟩, ⟨dropE, [.own 0], some []⟩,
    ⟨makeE, [], some [.own 2]⟩]

/-- The toy's session is a multi-call trace of the toy. -/
theorem toySession_trace :
    doneEvents toySessionCalls ∈ refMultiTraces first.prof H0 () toyProg := by
  obtain ⟨m₀, inst, es, ds, mₙ, hi, hr, hl⟩ := session_runCalls session_toy
  have hds : ds = toySessionCalls := doneCalls_eq hl
  exact hds ▸ doneEvents_mem toyProg hi hr

/-- … accepted by the provider sentence. -/
theorem toySession_accepted :
    (compProviderSpec makeE dropE).acceptsB (doneEvents toySessionCalls) = true := by
  decide +kernel

end Silmaril.Wasm.Resource.CompToy
