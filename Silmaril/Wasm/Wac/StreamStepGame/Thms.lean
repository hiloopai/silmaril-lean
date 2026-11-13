module

public import Silmaril.Wasm.Wac.StreamStepGame.Defs
public import Silmaril.Wasm.Wac.StreamStep.Thms
public import Silmaril.Wasm.Component.Algebra.StreamGame.Thms

/-!
# WAC: the chunk game, the stream game and the async machine, the theorems

**The pull game** (`Algebra.StreamGame`):

* `feedA_items`, `ans_chunks`: fed the items of chunks, one answer each, the pull game's stream
  function produces the items the chunk game answered on them (the output so far);
* **`feedA_stream`**, **`ans_stream`**: fed a whole stream (the items, then an end answer `e`),
  it produces the items of the whole chunk-game session, then passes `e` on, and is back in its
  initial state;
* **`ans_streams`**: the same for any number of streams in a row (the next question of the chunk
  game opens a new stream, as the next item after an end does in the pull game);
* `ans_code`: for the transformer of a code, the items of `k.run` of the concatenated chunks.

So the two games compute the same stream function: `den (tr k) = kahn (ans (tr k))` is the
strategy whose answers to a whole stream are the chunk game's answers, item by item, for every
chunking of the stream.

**The async machine** (`Component.Async`):

* `rdv_open`: a rendezvous (`stream.read r n` then `stream.write w xs`, `n = xs.length`) on an
  open stream succeeds, transfers exactly `xs` (the ghost `sent` grows by `xs`), leaves the
  stream open and every other stream and the handle table unchanged;
* **`chunksM_ok`**, **`sessionM_ok`**: a whole stream of the chunk game played on the machine
  (each chunk written into the input stream, each answer into the output stream, the flush, then
  both writable ends dropped) runs without trapping; the input stream carries the concatenated
  chunks and the output stream carries exactly the answers of the chunk-game session;
* **`sessionM_code`**: for a code `k`, the output stream carries `k.run` of the concatenated
  chunks, whatever the chunking.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamStepGame

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Algebra.StreamGame Silmaril.Wasm.Component.Algebra.Kahn
open Silmaril.Wasm.Component.Async Silmaril.Wasm.Wac.StreamStep Silmaril.Wasm.Wac.StreamFn
open Silmaril.Wasm.Component.Streams.Alg

variable {σ : Type}

/-! ## The pull game -/

theorem react_item (T : Tr σ Val Val) (s : σ) (v : Val) :
    react T s (item v) = ((T.feed s [v]).1, (T.feed s [v]).2.map item) := rfl

theorem react_end (T : Tr σ Val Val) (s : σ) {e : Ans} (he : IsEnd e) :
    react T s e = (T.init, (T.flush s).map item ++ [e]) := by
  simp only [react, show ofItem e = none from he]

theorem feedA_append (T : Tr σ Val Val) :
    ∀ (s : σ) (h h' : List Ans), feedA T s (h ++ h') =
      ((feedA T (feedA T s h).1 h').1, (feedA T s h).2 ++ (feedA T (feedA T s h).1 h').2)
  | s, [], h' => by simp [feedA]
  | s, a :: h, h' => by
    have ih := feedA_append T (react T s a).1 h h'
    simp [feedA, ih]

/-- Fed items, the pull game feeds the transformer. -/
theorem feedA_items (T : Tr σ Val Val) :
    ∀ (s : σ) (xs : List Val),
      feedA T s (xs.map item) = ((T.feed s xs).1, (T.feed s xs).2.map item)
  | s, [] => rfl
  | s, x :: xs => by
    have ih := feedA_items T (T.feed s [x]).1 xs
    have hf : T.feed s ([x] ++ xs) = ((T.feed (T.feed s [x]).1 xs).1,
        (T.feed s [x]).2 ++ (T.feed (T.feed s [x]).1 xs).2) := feed_append T s [x] xs
    simp only [List.singleton_append] at hf
    simp [feedA, react_item, ih, hf]

/-- The answers of a session, split. -/
theorem answers_session_eq (T : Tr σ Val Val) (s : σ) (cs : List (List Val)) :
    answers (session T s cs) = (T.feed s cs.flatten).2 ++ T.flush (T.feed s cs.flatten).1 := by
  obtain ⟨h1, h2⟩ := chunks_feed T s cs
  rw [session, answers_append, h2, h1]
  simp [answers]

/-- **Output so far**: fed the items of chunks, the pull game answers the items the chunk game
answered. -/
theorem ans_chunks (T : Tr σ Val Val) (cs : List (List Val)) :
    ans T (cs.flatten.map item) = (answers (chunks T T.init cs).1).map item := by
  rw [ans, feedA_items, (chunks_feed T T.init cs).2]

/-- **A whole stream in the pull game is a session of the chunk game**, and the transformer is
back in its initial state. -/
theorem feedA_stream (T : Tr σ Val Val) (s : σ) (cs : List (List Val)) {e : Ans} (he : IsEnd e) :
    feedA T s (itemsOf cs e) = (T.init, (answers (session T s cs)).map item ++ [e]) := by
  rw [itemsOf, feedA_append, feedA_items, answers_session_eq]
  simp [feedA, react_end T _ he]

theorem ans_stream (T : Tr σ Val Val) (cs : List (List Val)) {e : Ans} (he : IsEnd e) :
    ans T (itemsOf cs e) = (answers (session T T.init cs)).map item ++ [e] := by
  rw [ans, feedA_stream T _ cs he]

/-- **Any number of streams**: the pull game answers each with the chunk game's session. -/
theorem ans_streams (T : Tr σ Val Val) (ss : List (List (List Val))) {e : Ans} (he : IsEnd e) :
    feedA T T.init (ss.flatMap fun cs => itemsOf cs e) =
      (T.init, ss.flatMap fun cs => (answers (session T T.init cs)).map item ++ [e]) := by
  induction ss with
  | nil => rfl
  | cons cs ss ih =>
    rw [List.flatMap_cons, feedA_append, feedA_stream T _ cs he, ih, List.flatMap_cons]

/-- For a code: the items of `k.run` of the concatenated chunks, then the end. -/
theorem ans_code (k : TCode) (cs : List (List Val)) {e : Ans} (he : IsEnd e) :
    ans (tr k) (itemsOf cs e) = (k.run cs.flatten).map item ++ [e] := by
  rw [ans_stream _ cs he, answers_session]

/-! ## The async machine -/

/-- The store after a rendezvous of `xs` on the stream `s` read by `r`. -/
def afterRdv (st : Store) (r s : Nat) (xs : List Val) : Store :=
  (st.setChan s { st.chans s with sent := (st.chans s).sent ++ xs }).post r
    ⟨.streamRead, r, packCopy .completed xs.length, xs⟩

theorem upd_upd {β : Type} (f : Nat → β) (k : Nat) (a b : β) : upd (upd f k a) k b = upd f k b := by
  funext j
  by_cases hj : j = k <;> simp [upd, hj]

theorem upd_same {β : Type} (f : Nat → β) (k : Nat) (v : β) : upd f k v k = v := by
  simp [upd]

theorem rdv_eq {st : Store} {r w s : Nat} (h : Open st r w s) (xs : List Val) :
    rdv st r w xs = some (afterRdv st r s xs) := by
  simp [rdv, step, streamRead, streamWrite, h.hw, h.hr, h.idle, h.live, Store.setChan,
    Store.post, upd_upd, upd_same, afterRdv]

/-- **One rendezvous on an open stream** transfers exactly `xs` and keeps the stream open. -/
theorem rdv_open {st : Store} {r w s : Nat} (h : Open st r w s) (xs : List Val) :
    ∃ st', rdv st r w xs = some st' ∧ st'.tbl = st.tbl ∧
      st'.chans s = { st.chans s with sent := (st.chans s).sent ++ xs } ∧
      ∀ t, t ≠ s → st'.chans t = st.chans t :=
  ⟨afterRdv st r s xs, rdv_eq h xs, rfl, by simp [afterRdv, Store.setChan, Store.post, upd],
    fun t ht => by simp [afterRdv, Store.setChan, Store.post, upd, ht]⟩

/-- `stream.drop-writable` with no copy pending. -/
theorem dropW_idle {st : Store} {w s : Nat} (hw : st.tbl w = some (.streamW s))
    (hp : (st.chans s).pend = .idle) :
    step st (.streamDropW w) =
      some ((st.setChan s { st.chans s with wDropped := true }).remove w, .unit) := by
  simp [step, streamDropW, hw, hp]

/-- Both streams open, on different channels. -/
structure Open2 (st : Store) (ri wi si ro wo so : Nat) : Prop where
  inp : Open st ri wi si
  out : Open st ro wo so
  ne : si ≠ so

theorem open_of {st st' : Store} {r w s : Nat} {xs : List Val} (h : Open st r w s) (ht : st'.tbl = st.tbl)
    (hc : st'.chans s = { st.chans s with sent := (st.chans s).sent ++ xs }) : Open st' r w s :=
  ⟨by rw [ht]; exact h.hw, by rw [ht]; exact h.hr, by rw [hc]; exact h.idle,
    by rw [hc]; exact h.live⟩

theorem open_keep {st st' : Store} {r w s : Nat} (h : Open st r w s) (ht : st'.tbl = st.tbl)
    (hc : st'.chans s = st.chans s) : Open st' r w s :=
  ⟨by rw [ht]; exact h.hw, by rw [ht]; exact h.hr, by rw [hc]; exact h.idle,
    by rw [hc]; exact h.live⟩

/-- **The chunks of the chunk game on the machine.** -/
theorem chunksM_ok (T : Tr σ Val Val) {ri wi si ro wo so : Nat} :
    ∀ (st : Store) (s : σ) (cs : List (List Val)), Open2 st ri wi si ro wo so →
      ∃ st', chunksM T ri wi ro wo st s cs = some (st', (chunks T s cs).2) ∧
        Open2 st' ri wi si ro wo so ∧ st'.tbl = st.tbl ∧
        (st'.chans si).sent = (st.chans si).sent ++ cs.flatten ∧
        (st'.chans so).sent = (st.chans so).sent ++ answers (chunks T s cs).1
  | st, s, [], h => ⟨st, rfl, h, rfl, by simp, by simp [chunks, answers]⟩
  | st, s, xs :: cs, h => by
    obtain ⟨st₁, h1, t1, ci1, co1⟩ := rdv_open h.inp xs
    have hco1 : st₁.chans so = st.chans so := co1 so (Ne.symm h.ne)
    have o1 : Open2 st₁ ri wi si ro wo so :=
      ⟨open_of h.inp t1 ci1, open_keep h.out t1 hco1, h.ne⟩
    obtain ⟨st₂, h2, t2, co2, ci2⟩ := rdv_open o1.out (T.feed s xs).2
    have hci2 : st₂.chans si = st₁.chans si := ci2 si h.ne
    have o2 : Open2 st₂ ri wi si ro wo so :=
      ⟨open_keep o1.inp t2 hci2, open_of o1.out t2 co2, h.ne⟩
    obtain ⟨st₃, h3, o3, t3, si3, so3⟩ := chunksM_ok T st₂ (T.feed s xs).1 cs o2
    refine ⟨st₃, ?_, o3, by rw [t3, t2, t1], ?_, ?_⟩
    · simp [chunksM, h1, h2, h3, chunks]
    · rw [si3, hci2, ci1]
      simp
    · rw [so3, co2, hco1]
      simp [chunks, answers]

/-- **A whole stream of the chunk game on the machine**: it runs without trapping, the input
stream carries the concatenated chunks, the output stream the session's answers, and both
writable ends are dropped. -/
theorem sessionM_ok (T : Tr σ Val Val) {ri wi si ro wo so : Nat} {st : Store}
    (cs : List (List Val)) (h : Open2 st ri wi si ro wo so) :
    ∃ st', sessionM T ri wi ro wo st cs = some st' ∧
      (st'.chans si).sent = (st.chans si).sent ++ cs.flatten ∧
      (st'.chans so).sent = (st.chans so).sent ++ answers (session T T.init cs) ∧
      (st'.chans si).wDropped = true ∧ (st'.chans so).wDropped = true := by
  obtain ⟨st₁, h1, o1, t1, si1, so1⟩ := chunksM_ok T st T.init cs h
  obtain ⟨st₂, h2, t2, co2, ci2⟩ := rdv_open o1.out (T.flush (chunks T T.init cs).2)
  have hci2 : st₂.chans si = st₁.chans si := ci2 si h.ne
  have hwi : st₂.tbl wi = some (.streamW si) := by rw [t2]; exact o1.inp.hw
  have hwo : st₂.tbl wo = some (.streamW so) := by rw [t2]; exact o1.out.hw
  have hpi : (st₂.chans si).pend = .idle := by rw [hci2]; exact o1.inp.idle
  have hpo : (st₂.chans so).pend = .idle := by rw [co2]; exact o1.out.idle
  have hne : wi ≠ wo := by
    rintro rfl
    rw [hwi] at hwo
    exact h.ne (Obj.streamW.inj (Option.some.inj hwo))
  have hd1 := dropW_idle hwi hpi
  let st₃ := (st₂.setChan si { st₂.chans si with wDropped := true }).remove wi
  have hwo3 : st₃.tbl wo = some (.streamW so) := by simp [st₃, Store.remove, Store.setChan, upd, Ne.symm hne, hwo]
  have hpo3 : (st₃.chans so).pend = .idle := by
    simp [st₃, Store.remove, Store.setChan, upd, Ne.symm h.ne, hpo]
  have hd2 := dropW_idle hwo3 hpo3
  refine ⟨(st₃.setChan so { st₃.chans so with wDropped := true }).remove wo, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sessionM, h1, h2, hd1, hd2, st₃]
  · simp [st₃, Store.setChan, Store.remove, upd, h.ne, hci2, si1]
  · simp [st₃, Store.setChan, Store.remove, upd, Ne.symm h.ne, co2, so1, session, answers_append,
      answers]
  · simp [st₃, Store.setChan, Store.remove, upd, h.ne]
  · simp [Store.setChan, Store.remove, upd]

/-- **For a code**: the output stream carries `k.run` of the concatenated chunks, for every
chunking. -/
theorem sessionM_code (k : TCode) {ri wi si ro wo so : Nat} {st : Store}
    (cs : List (List Val)) (h : Open2 st ri wi si ro wo so) :
    ∃ st', sessionM (tr k) ri wi ro wo st cs = some st' ∧
      (st'.chans si).sent = (st.chans si).sent ++ cs.flatten ∧
      (st'.chans so).sent = (st.chans so).sent ++ k.run cs.flatten := by
  obtain ⟨st', h1, h2, h3, -, -⟩ := sessionM_ok (tr k) cs h
  exact ⟨st', h1, h2, by rw [h3, answers_session]⟩

end Silmaril.Wasm.Wac.StreamStepGame
