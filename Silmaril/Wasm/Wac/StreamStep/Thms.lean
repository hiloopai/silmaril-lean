module

public import Silmaril.Wasm.Wac.StreamStep.Defs
public import Silmaril.Wasm.Wac.StreamFn.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Play.Thms

/-!
# WAC: stream functions called step by step, the theorems

* `tr_run`: the whole output of a code's transformer is `TCode.run`;
* `session_traces`, **`session_mem`**: a whole stream (any chunks, then the end of the input)
  is a play of the module's strategy in `stepSem`;
* **`answers_session`**: its answers, concatenated, are `k.run` of the concatenated chunks:
  the stepwise reading delivers, chunk by chunk, exactly the batch output;
* `session_batch`: the one-chunk session answers what the batch call of `callSem` answers;
* `chunkL_traces_sub`, **`stepSem_congr`**: codes whose transformers are equivalent (`Tr.Equiv`)
  have the same strategy in `stepSem` (a weak simulation in each direction);
* `fnComp_equivS`, `runAgreeS_equiv`, **`composeText_step_equiv`**: the same WAC text with two
  sets of package bytes that decode to the same types and agree stepwise (`RunAgreeS`) gives two
  binaries whose components, each read off its own bytes by `readFn κ other`, are equivalent in
  the stepwise semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamStep

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamFn Silmaril.Wasm.Wac.StreamPkg
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Wac.SpliceX Silmaril.Wasm.Wac.Emit Silmaril.Wasm.Wac.EndToEnd

/-! ## The transformer of a code -/

/-- **The whole output of a code's transformer is `TCode.run`.** -/
theorem tr_run : ∀ k : TCode, (tr k).run = k.run
  | .id | .map _ | .filter _ | .take _ | .lines _ | .rechunk _ => rfl
  | .comp a b => by
    funext xs
    have h : ((tr a).comp (tr b)).run xs = (tr b).run ((tr a).run xs) := Tr.run_comp' _ _ xs
    show ((tr a).comp (tr b)).run xs = b.run (a.run xs)
    rw [h, tr_run a, tr_run b]

/-- Feeding a concatenation is feeding its parts in turn. -/
theorem feed_append {σ : Type} (T : Tr σ Val Val) (s : σ) (xs ys : List Val) :
    T.feed s (xs ++ ys) =
      ((T.feed (T.feed s xs).1 ys).1, (T.feed s xs).2 ++ (T.feed (T.feed s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : T.done s = true
    · have hs : ∀ zs, T.feed s zs = (s, []) := fun zs => by cases zs <;> simp [Tr.feed, h]
      rw [List.cons_append, hs, hs, hs]
      rfl
    · simp [Tr.feed, h, ih]

/-! ## Sessions -/

theorem chunks_run {σ : Type} (T : Tr σ Val Val) :
    ∀ (s : σ) (cs : List (List Val)),
      (chunkL T).Run (.idle s) (chunks T s cs).1 (.idle (chunks T s cs).2)
  | _, [] => .nil _
  | s, xs :: cs =>
    .vis (.ask s (qChunk xs)) (.vis (.chunk s (qChunk xs) xs rfl) (chunks_run T _ cs))

theorem chunks_path {σ : Type} (T : Tr σ Val Val) :
    ∀ (s : σ) (cs : List (List Val)), Path (.idle : Pos (sigN 0) SigF) (chunks T s cs).1 .idle
  | _, [] => .nil _
  | _, _ :: cs => .cons (.ask _) (.cons (.ret _ _) (chunks_path T _ cs))

theorem session_traces {σ : Type} (T : Tr σ Val Val) (s : σ) (cs : List (List Val)) :
    (chunkL T).Run (.idle s) (session T s cs) (.idle T.init) :=
  (chunks_run T s cs).append (.vis (.ask _ qEnd) (.vis (.close _ qEnd rfl) (.nil _)))

theorem session_legal {σ : Type} (T : Tr σ Val Val) (s : σ) (cs : List (List Val)) :
    Legal (session T s cs) := by
  refine ⟨.idle, ?_⟩
  have hp : Path (.idle : Pos (sigN 0) SigF) (chunks T s cs).1 .idle := chunks_path T s cs
  have he : Path (.idle : Pos (sigN 0) SigF)
      [.inr (.ask qEnd), .inr (.ans qEnd (some (.vals (T.flush (chunks T s cs).2))))] .idle :=
    .cons (.ask _) (.cons (.ret _ _) (.nil _))
  exact hp.append he

/-- **A whole stream is a play of the module's strategy in the stepwise semantics.** -/
theorem session_mem (n : String) (k : TCode) (cs : List (List Val)) :
    session (tr k) (tr k).init cs ∈ stepSem.sem (⟨n, k⟩ : FCode) :=
  Strategy.mem_ofLTS_of_mem_traces ⟨_, session_traces (tr k) (tr k).init cs⟩
    (session_legal (tr k) (tr k).init cs)

theorem chunks_feed {σ : Type} (T : Tr σ Val Val) :
    ∀ (s : σ) (cs : List (List Val)),
      (chunks T s cs).2 = (T.feed s cs.flatten).1 ∧
        answers (chunks T s cs).1 = (T.feed s cs.flatten).2
  | s, [] => ⟨rfl, rfl⟩
  | s, xs :: cs => by
    obtain ⟨h1, h2⟩ := chunks_feed T (T.feed s xs).1 cs
    have he : T.feed s (xs ++ cs.flatten) =
        ((T.feed (T.feed s xs).1 cs.flatten).1, (T.feed s xs).2 ++ (T.feed (T.feed s xs).1 cs.flatten).2) :=
      feed_append T s xs cs.flatten
    rw [List.flatten_cons, he]
    exact ⟨h1, by simp [chunks, answers, h2]⟩

theorem answers_append (p q : List MoveF) : answers (p ++ q) = answers p ++ answers q := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    match m with
    | .inr (.ans _ (some (.vals ys))) => simp [answers, ih]
    | .inr (.ans _ (some (.flat _))) | .inr (.ans _ none) | .inr (.ask _) | .inl _ =>
      simpa [answers] using ih

/-- **The stepwise answers of a whole stream are its batch output.** -/
theorem answers_session (k : TCode) (cs : List (List Val)) :
    answers (session (tr k) (tr k).init cs) = k.run cs.flatten := by
  obtain ⟨h1, h2⟩ := chunks_feed (tr k) (tr k).init cs
  have hr : (tr k).run cs.flatten = k.run cs.flatten := by rw [tr_run]
  rw [← hr, session, answers_append, h2, h1]
  simp [answers, Tr.run]

/-- **The one-chunk session answers what the batch call answers.** -/
theorem session_batch (k : TCode) (xs : List Val) :
    callAns k.run (.vals xs) = some (.vals (answers (session (tr k) (tr k).init [xs]))) := by
  rw [answers_session]
  simp [callAns]

/-! ## Equivalent transformers give equal strategies -/

theorem equiv_symm {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U) :
    Tr.Equiv U T := fun xs => ⟨(h xs).1.symm, (h xs).2.symm⟩

/-- What two equivalent transformers emit on a chunk after the same history. -/
theorem out_eq {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U)
    (hs xs : List Val) :
    (T.feed (T.feed T.init hs).1 xs).2 = (U.feed (U.feed U.init hs).1 xs).2 := by
  have h1 : T.runP (hs ++ xs) = U.runP (hs ++ xs) := (h (hs ++ xs)).1
  have h2 : T.runP hs = U.runP hs := (h hs).1
  rw [Tr.runP, Tr.runP, feed_append, feed_append] at h1
  rw [Tr.runP, Tr.runP] at h2
  rw [h2] at h1
  exact List.append_cancel_left h1

/-- What two equivalent transformers flush after the same history. -/
theorem flush_eq {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U)
    (hs : List Val) : T.flush (T.feed T.init hs).1 = U.flush (U.feed U.init hs).1 := by
  have h1 : T.run hs = U.run hs := (h hs).2
  have h2 : (T.feed T.init hs).2 = (U.feed U.init hs).2 := (h hs).1
  simp only [Tr.run, h2] at h1
  exact List.append_cancel_left h1

/-- The relation of the simulation: the same history since the stream was opened. -/
def SimR {σ τ : Type} (T : Tr σ Val Val) (U : Tr τ Val Val) (x : CState σ) (y : CState τ) : Prop :=
  (∃ hs, x = .idle (T.feed T.init hs).1 ∧ y = .idle (U.feed U.init hs).1) ∨
    ∃ hs q, x = .run (T.feed T.init hs).1 q ∧ y = .run (U.feed U.init hs).1 q

theorem simR_init {σ τ : Type} (T : Tr σ Val Val) (U : Tr τ Val Val) :
    SimR T U (.idle T.init) (.idle U.init) := .inl ⟨[], rfl, rfl⟩

theorem simR_idle {σ τ : Type} (T : Tr σ Val Val) (U : Tr τ Val Val) (hs : List Val) :
    SimR T U (.idle (T.feed T.init hs).1) (.idle (U.feed U.init hs).1) := .inl ⟨hs, rfl, rfl⟩

/-- One step of the run state, matched. -/
theorem sim_run {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U)
    (hs : List Val) (q : SigF.Op) {x' : CState σ} {l : Option MoveF}
    (hx : CStep T (.run (T.feed T.init hs).1 q) l x') :
    ∃ y', (chunkL U).Run (.run (U.feed U.init hs).1 q) l.toList y' ∧ SimR T U x' y' := by
  cases hx with
  | chunk _ _ xs hq =>
    rw [out_eq h hs xs]
    refine ⟨_, .vis (.chunk _ q xs hq) (.nil _), ?_⟩
    have e1 : (T.feed (T.feed T.init hs).1 xs).1 = (T.feed T.init (hs ++ xs)).1 := by
      rw [feed_append]
    have e2 : (U.feed (U.feed U.init hs).1 xs).1 = (U.feed U.init (hs ++ xs)).1 := by
      rw [feed_append]
    rw [e1, e2]
    exact simR_idle T U _
  | close _ _ hq =>
    rw [flush_eq h hs]
    exact ⟨_, .vis (.close _ q hq) (.nil _), simR_init T U⟩
  | bad _ _ fs hq hne => exact ⟨_, .vis (.bad _ q fs hq hne) (.nil _), simR_idle T U hs⟩

/-- **A weak simulation of the chunk game of `T` by that of an equivalent `U`.** -/
def chunkSim {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U) :
    (chunkL T).Simulation (chunkL U) where
  R := SimR T U
  init := simR_init T U
  step := by
    intro x x' y l hR hx
    rcases hR with ⟨hs, rfl, rfl⟩ | ⟨hs, q, rfl, rfl⟩
    · cases hx with
      | ask _ q => exact ⟨_, .vis (.ask _ q) (.nil _), .inr ⟨hs, q, rfl, rfl⟩⟩
    · exact sim_run h hs q hx

theorem chunkL_traces_sub {σ τ : Type} {T : Tr σ Val Val} {U : Tr τ Val Val} (h : Tr.Equiv T U) :
    (chunkL T).Traces ⊆ (chunkL U).Traces :=
  (chunkSim h).traces_subset

/-- **Codes whose transformers are equivalent have the same strategy in `stepSem`.** -/
theorem stepSem_congr {n : String} {k k' : TCode} (h : Tr.Equiv (tr k) (tr k')) :
    stepSem.sem (⟨n, k⟩ : FCode) = stepSem.sem (⟨n, k'⟩ : FCode) := by
  have ht : (chunkL (tr k)).Traces = (chunkL (tr k')).Traces :=
    Set.Subset.antisymm (chunkL_traces_sub h) (chunkL_traces_sub (equiv_symm h))
  show Strategy.generate (chunkL (tr k)).Traces = Strategy.generate (chunkL (tr k')).Traces
  rw [ht]

/-- **Codes with equivalent transformers give equivalent function components** (stepwise). -/
theorem fnComp_equivS {n : String} {k k' : TCode} (h : Tr.Equiv (tr k) (tr k')) :
    CompEquiv stepSem (fnComp n k) (fnComp n k') := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  simp only [fnComp, Comp.denU, denNodes, Node.den, coreNode, stepSem_congr h]
  rfl

theorem runAgreeS_equiv {κ : Interp} {other : AstX → Option (Comp FCode)} {dflt : Comp FCode}
    {tbl tbl' : PkgTableX} (h : RunAgreeS κ tbl tbl') (n : String) :
    CompEquiv stepSem (pkgMeaning (readFn κ other) dflt (tbl.lookup n))
      (pkgMeaning (readFn κ other) dflt (tbl'.lookup n)) := by
  rcases h n with he | ⟨a, a', s, s', k, k', ha, ha', hs, hk, hs', hk', hn, hq⟩
  · rw [he]; exact CompEquiv.refl _ _
  · simp only [ha, ha', pkgMeaning, Option.bind_some, readFn_lowerFn hs hk, readFn_lowerFn hs' hk',
      Option.getD_some, hn]
    exact fnComp_equivS hq

/-- **Stream packages that agree stepwise give equivalent compositions in the stepwise
semantics, from the WAC text and the bytes.** -/
theorem composeText_step_equiv {src : String} {raw raw' : List (String × ByteArray)}
    {b b' : ByteArray} {tbl tbl' : PkgTableX}
    (h : composeText src raw = .ok (b, some tbl, true))
    (h' : composeText src raw' = .ok (b', some tbl', true))
    (hT : ∀ k, (raw.lookup k).map TypeOf.decodeAnyX = (raw'.lookup k).map TypeOf.decodeAnyX)
    (S : Nat → PkgSig) (κ : Interp) (other : AstX → Option (Comp FCode)) (dflt : Comp FCode)
    (hr : RunAgreeS κ tbl tbl') :
    ∃ X X', binCompX S (readFn κ other) dflt b = .ok X ∧
      binCompX S (readFn κ other) dflt b' = .ok X' ∧ CompEquiv stepSem X X' :=
  composeText_equiv h h' hT S (readFn κ other) dflt (runAgreeS_equiv hr)

end Silmaril.Wasm.Wac.StreamStep
