module

public import Silmaril.Proofs.Wasm.Det.CompScratch.Seq
public import Silmaril.Wasm.Det.CompRef.Thms
public import Silmaril.Wasm.Det.CompRef.Litmus.Thms

/-!
# Simple components are stateless over sessions

A session configuration of a simple component (`SeqReach` with `SimpleAdm`) is the end of a
sequence of resolved typed calls `0, …, k-1` after instantiation (`reach_seq`), so the next call
is a behaviour of `seqBehaviours`. The reference-machine half for sequences
(`Silmaril.Wasm.Component.Reference.seq_refToSpec`) excludes deadlock and cancellation
(`ofCall_resolved`), and the IR's statelessness (`Silmaril.Wasm.Det.CompRef.simple_seq_returns_eq`)
gives equal results (`simple_compStatelessSeq`). The adder is an instance.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompScratch

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Det.Core.Component Silmaril.Wasm.Det.CompScratch
open Silmaril.Wasm.Numerics (Profile)

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

theorem mapM_length' {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨y, -, ys', hys, rfl⟩ := h
    simp [mapM_length' hys]

theorem mapM_snoc {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} {x : α} {y : β}
    (h : xs.mapM f = some ys) (hx : f x = some y) : (xs ++ [x]).mapM f = some (ys ++ [y]) := by
  rw [List.mapM_append, h]
  simp [hx]

theorem seqCalls_snoc {prof : ProfileKind} {h : Host E σ} {m m' m'' : Config E σ} {k : Nat}
    {cs : List (FuncId × List Value.Val)} {rss : List (List Value.Val)} {f : FuncId}
    {args rs : List Value.Val} (hs : SeqCalls prof h m k cs rss m')
    (hc : Calls prof h.hr h.dispatch m' ⟨k + cs.length⟩ f args m'' (.resolved (some rs))) :
    SeqCalls prof h m k (cs ++ [(f, args)]) (rss ++ [rs]) m'' := by
  induction hs with
  | nil => exact .cons hc (.nil _ _)
  | cons h₁ _ ih =>
    refine .cons h₁ (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1] using hc

variable {P : Profile} {prof : ProfileKind} {c : Simple}

/-- The names and reference arguments of IR calls. -/
abbrev callNames (c : Simple)
    (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (String × List Value.Val) :=
  cs.map fun q => (c.exports[q.1].name, q.2.map toRefVal)

theorem typedCalls_snoc {cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} (ht : TypedCalls c cs)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList c.exports[j].ty.params vs = true) :
    TypedCalls c (cs ++ [(j, vs)]) := by
  intro q hq
  rcases List.mem_append.1 hq with hq | hq
  · exact ht q hq
  · rw [List.mem_singleton] at hq
    subst hq
    exact hvs

theorem zip_snoc {cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {fs : List FuncId} {f : FuncId} {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val}
    (hl : fs.length = cs.length) :
    (fs ++ [f]).zip ((callNames c (cs ++ [(j, vs)])).map Prod.snd) =
      fs.zip ((callNames c cs).map Prod.snd) ++ [(f, vs.map toRefVal)] := by
  have hl' : fs.length = ((callNames c cs).map Prod.snd).length := by simpa [callNames] using hl
  simp only [callNames, List.map_append, List.map_cons, List.map_nil]
  rw [List.zip_append (by simpa [callNames] using hl')]
  rfl

/-- One more resolved typed call of a session. -/
theorem reach_seq_step {m₀ m m' : Config (core3P P) Unit} {es : List (String × FuncId)}
    {cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)} {fs : List FuncId}
    {rss : List (List Value.Val)} {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val}
    {f : FuncId} {rs : List Value.Val}
    (hfs : (callNames c cs).mapM (fun q => es.lookup q.1) = some fs)
    (hS : SeqCalls prof (refHost P) m₀ 0 (fs.zip ((callNames c cs).map Prod.snd)) rss m)
    (hf : es.lookup c.exports[j].name = some f)
    (hc : Calls prof (refHost P).hr (refHost P).dispatch m ⟨cs.length⟩ f (vs.map toRefVal) m'
      (.resolved (some rs))) :
    (callNames c (cs ++ [(j, vs)])).mapM (fun q => es.lookup q.1) = some (fs ++ [f]) ∧
      SeqCalls prof (refHost P) m₀ 0 ((fs ++ [f]).zip ((callNames c (cs ++ [(j, vs)])).map
        Prod.snd)) (rss ++ [rs]) m' := by
  have hl : fs.length = cs.length := by rw [mapM_length' hfs]; simp [callNames]
  have hm : (callNames c (cs ++ [(j, vs)])).mapM (fun q => es.lookup q.1) = some (fs ++ [f]) := by
    simp only [callNames, List.map_append, List.map_cons, List.map_nil]
    exact mapM_snoc hfs hf
  have hz : (fs.zip ((callNames c cs).map Prod.snd)).length = cs.length := by
    rw [List.length_zip, hl]
    simp [callNames]
  have hc' : Calls prof (refHost P).hr (refHost P).dispatch m
      ⟨0 + (fs.zip ((callNames c cs).map Prod.snd)).length⟩ f (vs.map toRefVal) m'
      (.resolved (some rs)) := by rw [hz, Nat.zero_add]; exact hc
  exact ⟨hm, (zip_snoc hl).symm ▸ seqCalls_snoc hS hc'⟩

/-- **A session configuration ends a sequence of resolved typed calls.** -/
theorem reach_seq {m : Config (core3P P) Unit} {es : List (String × FuncId)} {k : Nat}
    (hm : SeqReach prof (refHost P) () c.toRef [] (SimpleAdm c) m es k) :
    ∃ (m₀ : Config (core3P P) Unit) (inst : InstId)
      (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) (fs : List FuncId)
      (rss : List (List Value.Val)),
      InstResult.instance m₀ inst es ∈ instBehaviours prof (refHost P) (initConfig ()) c.toRef [] ∧
      TypedCalls c cs ∧ (callNames c cs).mapM (fun q => es.lookup q.1) = some fs ∧
      SeqCalls prof (refHost P) m₀ 0 (fs.zip ((callNames c cs).map Prod.snd)) rss m ∧
      k = cs.length := by
  induction hm with
  | inst hi => exact ⟨_, _, [], [], [], hi, (fun _ h => nomatch h), rfl, .nil _ _, rfl⟩
  | @call m m' es k name f vals rs _ hf ha hc ih =>
    obtain ⟨m₀, inst, cs, fs, rss, hi, ht, hfs, hS, rfl⟩ := ih
    obtain ⟨j, vs, rfl, rfl, hvs⟩ := ha
    obtain ⟨hm, hS'⟩ := reach_seq_step hfs hS hf hc
    exact ⟨m₀, inst, cs ++ [(j, vs)], fs ++ [f], rss ++ [rs], hi, typedCalls_snoc ht hvs, hm, hS',
      by simp⟩

/-- The specification never deadlocks and never cancels. -/
theorem specAt_ne {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
    {vs : List Silmaril.Wasm.Component.Val} {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {b : Silmaril.Wasm.Component.Reference.Outcome} (hb : b ∈ specAt P c I x vs s) :
    b ≠ .returns none ∧ b ≠ .deadlocks := by
  unfold specAt at hb
  split at hb
  · rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  · rcases hb with ⟨r, -, rfl⟩ | ⟨rfl, -⟩
    · unfold liftOutcome
      split
      · split <;> exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem ofCall_resolved {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
    {vs : List Silmaril.Wasm.Component.Val} {s : Silmaril.Wasm.Execution.Core.Store Nat}
    {out : CallOutcome} (hb : Outcome.ofCall out ∈ specAt P c I x vs s) (ht : out ≠ .trap) :
    ∃ rs, out = .resolved (some rs) := by
  obtain ⟨h₁, h₂⟩ := specAt_ne hb
  cases out with
  | resolved r =>
    cases r with
    | some rs => exact ⟨rs, rfl⟩
    | none => exact (h₁ rfl).elim
  | trap => exact (ht rfl).elim
  | deadlock => exact (h₂ rfl).elim

/-- The next call of a session is a sequence behaviour. -/
theorem mem_seqBehaviours {m m' : Config (core3P P) Unit} {es : List (String × FuncId)} {k : Nat}
    (hm : SeqReach prof (refHost P) () c.toRef [] (SimpleAdm c) m es k) {f : FuncId}
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hf : es.lookup c.exports[j].name = some f) {out : CallOutcome}
    (hc : Calls prof (refHost P).hr (refHost P).dispatch m ⟨k⟩ f (vs.map toRefVal) m' out) :
    ∃ (cs : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (rss : List (List Value.Val)), TypedCalls c cs ∧
      (rss, Outcome.ofCall out) ∈ seqBehaviours prof (refHost P) () c.toRef (callNames c cs)
        c.exports[j].name (vs.map toRefVal) := by
  obtain ⟨m₀, inst, cs, fs, rss, hi, ht, hfs, hS, rfl⟩ := reach_seq hm
  refine ⟨cs, rss, ht, .inl ⟨m₀, inst, es, fs, m, f, hi, hfs, hS, hf, .inl ⟨m', out, ?_, rfl⟩⟩⟩
  simpa [callNames] using hc

/-- **A simple component with a stateless module is stateless over sessions** (every profile,
every component choice profile). -/
theorem simple_compStatelessSeq (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (hD : Silmaril.Wasm.Det.CompRef.ModStateless P c.mod) :
    CompStatelessSeq prof (refHost P) () c.toRef [] (SimpleAdm c) := by
  intro m₁ es₁ k₁ m₂ es₂ k₂ hm₁ hm₂ name f₁ f₂ hf₁ hf₂ vals hadm m₁' m₂' out₁ out₂ hc₁ hc₂ ht₁ ht₂
  obtain ⟨j, vs, rfl, rfl, hvs⟩ := hadm
  obtain ⟨cs₁, rss₁, hty₁, hp₁⟩ := mem_seqBehaviours hm₁ j vs hf₁ hc₁
  obtain ⟨cs₂, rss₂, hty₂, hp₂⟩ := mem_seqBehaviours hm₂ j vs hf₂ hc₂
  obtain ⟨I₁, w₁, s₁, -, -, -, hs₁⟩ := seq_refToSpec P prof c hc hf hi ha cs₁ j vs hty₁ hvs _ hp₁
  obtain ⟨I₂, w₂, s₂, -, -, -, hs₂⟩ := seq_refToSpec P prof c hc hf hi ha cs₂ j vs hty₂ hvs _ hp₂
  obtain ⟨rs₁, rfl⟩ := ofCall_resolved hs₁ ht₁
  obtain ⟨rs₂, rfl⟩ := ofCall_resolved hs₂ ht₂
  have e := Silmaril.Wasm.Det.CompRef.simple_seq_returns_eq P prof c hc hf hi ha hD cs₁ cs₂ hty₁ hty₂
    j vs hvs hp₁ hp₂ rfl rfl
  rw [e]

theorem adderS_floatFree' : Silmaril.Wasm.Component.Reference.Litmus.adderS.FloatFree := by
  intro x hx
  simp only [Silmaril.Wasm.Component.Reference.Litmus.adderS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

end Silmaril.Proofs.Wasm.Det.CompScratch
