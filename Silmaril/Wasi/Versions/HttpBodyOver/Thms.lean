module

public import Silmaril.Wasi.Versions.HttpBodyOver.Defs
public import Silmaril.Wasi.Versions.HttpOver.Thms
public import Silmaril.Wasi.Versions.HttpBody3.Thms

@[expose] public section

/-!
# HTTP with response bodies across versions: theorems

PROVED (standard axioms):

* `wp_liftP_body`: a program over the outgoing 0.2 imports, lifted to the imports with bodies,
  keeps its weakest precondition under `bodyTh B` (the body part of the state is framed).
* **`httpB3Over2_sat`, `httpB3Over2_model`**: for every body web `B`, every number of rounds
  and every host of the 0.2 theory with bodies `bodyTh B`, the buffering composite
  `httpB3Over2 rounds` is a model of the 0.3 theory with bodies `body3Th B`. Invariant `JB3`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## Framing the outgoing slice -/

/-- The outgoing 0.2 functions are not body functions. -/
theorem isBodyFn_of_http {f : FnName} (hf : f ∈ httpImports) : isBodyFn f = false := by
  simp only [httpImports_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Body functions keep the outgoing 0.2 state. -/
theorem httpNext_body (q : HttpSt) {f : FnName} (hb : isBodyFn f = true) (a : List Val)
    (r : Option (List Val)) : httpNext q (.imp f a r) = q := by
  have hne : f ≠ setAuthority ∧ f ≠ setPath ∧ f ≠ httpHandle ∧ f ≠ futGet := by
    simp only [isBodyFn, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;> decide
  unfold httpNext
  split <;> simp_all

/-- Other functions keep the body part of the 0.2 state. -/
theorem bodyStep_other (q : BodySt) {f : FnName} (hb : isBodyFn f = false) (a : List Val)
    (r : Option (List Val)) : bodyStep q (.imp f a r) = q := by
  have hr : isReadFn f = false := by
    simp only [isBodyFn, Bool.or_eq_false_iff] at hb
    simp [isReadFn, hb.2, hb.1.2]
  have hne : f ≠ consume2 ∧ f ≠ bodyStream2 ∧ f ≠ bodyFinish2 ∧ f ≠ trGet2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; simp [isBodyFn] at hb)
  unfold bodyStep
  split <;> simp_all

/-- The body part of the 0.2 state does not touch the outgoing part. -/
theorem bodyStep_base (q : BodySt) (e : WEv) : (bodyStep q e).base = q.base := by
  unfold bodyStep
  repeat' split
  all_goals rfl

/-- A step of the 0.2 theory with bodies on an outgoing function is a step of `httpTh`, and
keeps the body part. -/
theorem bodyTh_step_http {B : BWeb} {q q' : BodySt} {f : FnName} (hb : isBodyFn f = false)
    {a : List Val} {r : Option (List Val)} (h : (bodyTh B).step q (.imp f a r) = some q') :
    (httpTh B.web).step q.base (.imp f a r) = some q'.base ∧ q' = { q with base := q'.base } := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  have hok' : httpOk B.web q.base (.imp f a r) = true := by
    simp only [bodyOk, Bool.and_eq_true] at hok; exact hok.1
  subst hq
  refine ⟨gated_step_of hok', ?_⟩
  simp [bodyNext, bodyStep_other q hb]

/-- **Lifted outgoing programs**: the weakest precondition under `httpTh B.web` of the outgoing
state gives the one under `bodyTh B`, with the body part framed. -/
theorem wp_liftP_body (B : BWeb) {A : Type} (q0 : BodySt) (Q : A → HttpSt → Prop) :
    ∀ (p : Prog (nsig httpImports) A) (q : BodySt), q = { q0 with base := q.base } →
      Wp (httpTh B.web) p Q q.base →
      Wp (bodyTh B) (liftP httpImports_sub p) (fun a q' => ∃ b, q' = { q0 with base := b } ∧ Q a b) q
  | .pure a, q, hq, h => ⟨q.base, hq, h⟩
  | .call m k, q, hq, h => fun n q' hs => by
    obtain ⟨h2, hq'⟩ := bodyTh_step_http (isBodyFn_of_http m.1.2) hs
    exact wp_liftP_body B q0 Q (k n) q' (by rw [hq']; rw [hq]) (h n q'.base h2)

/-- Body functions of 0.3 keep the outgoing 0.3 state. -/
theorem http3Next_body (q : Http3St) {f : FnName} (hb : isBodyFn3 f = true) (a : List Val)
    (r : Option (List Val)) : http3Next q (.imp f a r) = q := by
  have hne : f ≠ setAuth3 ∧ f ≠ setPath3 ∧ f ≠ send3 := by
    simp only [isBodyFn3, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((rfl | rfl) | rfl) | rfl <;> decide
  unfold http3Next
  split <;> simp_all

/-- Other functions keep the body part of the 0.3 state. -/
theorem body3Step_other (q : Body3St) {f : FnName} (hb : isBodyFn3 f = false) (a : List Val)
    (r : Option (List Val)) : body3Step q (.imp f a r) = q := by
  simp only [isBodyFn3, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hb
  obtain ⟨⟨⟨h₁, -⟩, h₃⟩, h₄⟩ := hb
  unfold body3Step
  split <;> simp_all

/-- A step of the 0.3 outgoing theory on an outgoing function is a step of the 0.3 theory with
bodies, framing the body part. -/
theorem body3Th_step_http {B : BWeb} {q : Body3St} {b : Http3St} {f : FnName}
    (hb : isBodyFn3 f = false) {a : List Val} {r : Option (List Val)}
    (h : (httpTh3 B.web).step q.base (.imp f a r) = some b) :
    (body3Th B).step q (.imp f a r) = some { q with base := b } := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  subst hq
  refine gated_step_iff.2 ⟨?_, ?_⟩
  · simp [body3Ok, hok, body3Check_other B q hb]
  · simp [body3Next, body3Step_other q hb]

/-- A step of the 0.3 theory with bodies on a body function: the check and the body part. -/
theorem body3Th_step_body {B : BWeb} {q : Body3St} {f : FnName} (hb : isBodyFn3 f = true)
    {a : List Val} {r : Option (List Val)} (hc : body3Check B q (.imp f a r) = true) :
    (body3Th B).step q (.imp f a r) = some (body3Step q (.imp f a r)) := by
  obtain ⟨h₁, h₂⟩ := bodyFn3_ne hb
  refine gated_step_iff.2 ⟨by simp [body3Ok, http3Ok_other B.web _ h₁ h₂, hc], ?_⟩
  have hbase : (body3Step q (.imp f a r)).base = q.base := by
    unfold body3Step; repeat' split
    all_goals rfl
  simp only [body3Next, http3Next_body q.base hb]
  rw [← hbase]

/-! ## (b) with bodies: the outgoing slice -/

/-- **An outgoing export call** of `httpB3Over2` keeps `JB3`. -/
theorem base_call (B : BWeb) (rounds : Nat) {st : B3St} {q2 : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (q : (nsig httpBody3Fns).Op) (hb : isBodyFn3 q.1.1 = false) :
    Wp (bodyTh B) (httpB3Over2 rounds st q)
      (fun a q2' => ∃ q3', (body3Th B).step q3 (.imp q.1.1 q.2 a.2) = some q3' ∧ JB3 B a.1 q2' q3')
      q2 := by
  have h0 := (http3Over2_inv B.web rounds).call () q2.base q3.base (⟨q.1.1, mem_http3 q.1.2 hb⟩, q.2)
    hJ.1
  have h1 := wp_liftP_body B q2 _ _ q2 rfl h0
  show Wp (bodyTh B) (if hb : isBodyFn3 q.1.1 = false then _ else _) _ q2
  simp only [hb, ↓reduceDIte]
  rw [Wp.bind]
  refine Wp.mono (fun x q2' hx => ?_) h1
  obtain ⟨b, rfl, qG', hG, hJ'⟩ := hx
  exact ⟨{ q3 with base := qG' }, body3Th_step_http hb hG, hJ', hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩

/-! ## (b) with bodies: buffered answers -/

/-- `completed3` of a buffered read answer. -/
theorem completed3_read3Ans (rest : List (BitVec 8)) (n : Nat) :
    completed3 (read3Ans rest n) =
      if rest.isEmpty then none else some (rest.take (min n chunk3)).length := by
  unfold read3Ans
  by_cases he : rest.isEmpty = true
  · simp only [he, ↓reduceIte, completed3, P3.natV, copy3_dropped]
  · have hc : (rest.take (min n chunk3)).length ≤ chunk3 :=
      (List.length_take_le _ _).trans (Nat.min_le_right _ _)
    simp only [he, Bool.false_eq_true, ↓reduceIte, completed3, P3.natV, copy3_completed hc]

/-- `DROPPED 0` completes nothing. -/
theorem completed3_dropped0 : completed3 dropped0 = none := by
  simp [completed3, dropped0, P3.natV, copy3_dropped]

/-- Reading `c` buffered bytes keeps the buffer equal to the rest of the body. -/
theorem drop_buf (body : List (BitVec 8)) (off c : Nat) :
    (body.drop off).drop c = body.drop (off + c) := by
  rw [List.drop_drop]

/-- The 0.3 state after a read on a tracked stream. -/
theorem body3Step_read_tracked (q : Body3St) (h : BitVec 32) (a' : List Val) {k : Val × Val}
    {off : Nat} (hl : lookup h q.streams = some (some (k, off))) (r : Option (List Val)) :
    body3Step q (.imp P3.cStreamRead (.u32 h :: a') r) =
      match completed3 r with
      | some c => { q with streams := (h, some (k, off + c)) :: q.streams }
      | none => q := by
  cases hc : completed3 r <;> simp [body3Step, hl, hc, show P3.cStreamRead ≠ consumeBody3 by decide]

/-- The 0.3 state after a read on an untracked stream. -/
theorem body3Step_read_untracked (q : Body3St) (h : BitVec 32) (a' : List Val)
    (hl : ∀ k off, lookup h q.streams ≠ some (some (k, off))) (r : Option (List Val)) :
    body3Step q (.imp P3.cStreamRead (.u32 h :: a') r) = q := by
  unfold body3Step
  simp only [show P3.cStreamRead ≠ consumeBody3 by decide, ↓reduceIte]
  split
  · next k n c hl' _ => exact absurd hl' (hl k n)
  · rfl

/-- After a buffered read of a tracked stream, its buffer is the rest of the body. -/
theorem buf_read_tracked (B : BWeb) {q3 : Body3St} {h : BitVec 32} {a' : List Val}
    {rest : List (BitVec 8)} {k0 : Val × Val} {off : Nat}
    (hl : lookup h q3.streams = some (some (k0, off))) (hrest : rest = (B.body k0).drop off)
    {k : Val × Val} {n : Nat}
    (hr : lookup h (body3Step q3 (.imp P3.cStreamRead (.u32 h :: a')
        (read3Ans rest (count3 (.u32 h :: a'))))).streams = some (some (k, n))) :
    rest.drop (rest.take (min (count3 (.u32 h :: a')) chunk3)).length = (B.body k).drop n := by
  by_cases he : rest.isEmpty = true
  · have hkn : k0 = k ∧ off = n := by
      simpa [body3Step_read_tracked q3 h a' hl, completed3_read3Ans, he, hl] using hr
    obtain ⟨rfl, rfl⟩ := hkn
    simp [List.isEmpty_iff.1 he, ← hrest]
  · have hkn : k0 = k ∧ off + (rest.take (min (count3 (.u32 h :: a')) chunk3)).length = n := by
      simpa [body3Step_read_tracked q3 h a' hl, completed3_read3Ans, he, lookup_cons_self] using hr
    obtain ⟨rfl, rfl⟩ := hkn
    rw [hrest, drop_buf]

/-- After a buffered read of `h`, the buffer of `h` is the rest of the body it tracks. -/
theorem buf_read_self (B : BWeb) {st : B3St} {q3 : Body3St}
    (hS : ∀ r k n, lookup r q3.streams = some (some (k, n)) →
      lookup r st.bufs = some ((B.body k).drop n))
    {h : BitVec 32} {a' : List Val} {rest : List (BitVec 8)} (hb : lookup h st.bufs = some rest)
    {k : Val × Val} {n : Nat}
    (hr : lookup h (body3Step q3 (.imp P3.cStreamRead (.u32 h :: a')
        (read3Ans rest (count3 (.u32 h :: a'))))).streams = some (some (k, n))) :
    rest.drop (rest.take (min (count3 (.u32 h :: a')) chunk3)).length = (B.body k).drop n := by
  by_cases ht : ∃ k0 off, lookup h q3.streams = some (some (k0, off))
  · obtain ⟨k0, off, hl⟩ := ht
    have hrest : rest = (B.body k0).drop off := Option.some.inj (hb.symm.trans (hS h k0 off hl))
    exact buf_read_tracked B hl hrest hr
  · push Not at ht
    have hr' : lookup h q3.streams = some (some (k, n)) := by
      rwa [body3Step_read_untracked q3 h a' ht] at hr
    exact absurd hr' (ht k n)

/-- A read of `h` does not change what the 0.3 state tracks for another stream. -/
theorem streams_read_other {q3 : Body3St} {h r : BitVec 32} {a' : List Val}
    {res : Option (List Val)} (hrh : r ≠ h) {k : Val × Val} {n : Nat}
    (hr : lookup r (body3Step q3 (.imp P3.cStreamRead (.u32 h :: a') res)).streams =
      some (some (k, n))) :
    lookup r q3.streams = some (some (k, n)) := by
  by_cases ht : ∃ k0 off, lookup h q3.streams = some (some (k0, off))
  · obtain ⟨k0, off, hl⟩ := ht
    rw [body3Step_read_tracked q3 h a' hl] at hr
    split at hr
    · rwa [lookup_cons_ne hrh] at hr
    · exact hr
  · push Not at ht
    rwa [body3Step_read_untracked q3 h a' ht] at hr

/-- The streams clause of `JB3` after a buffered read of `h`. -/
theorem streams_after_read (B : BWeb) {st : B3St} {q3 : Body3St}
    (hS : ∀ r k n, lookup r q3.streams = some (some (k, n)) →
      lookup r st.bufs = some ((B.body k).drop n))
    (h : BitVec 32) (a' : List Val) (rest : List (BitVec 8)) (hb : lookup h st.bufs = some rest) :
    ∀ r k n, lookup r (body3Step q3 (.imp P3.cStreamRead (.u32 h :: a')
        (read3Ans rest (count3 (.u32 h :: a'))))).streams = some (some (k, n)) →
      lookup r ((h, rest.drop (rest.take (min (count3 (.u32 h :: a')) chunk3)).length) :: st.bufs) =
        some ((B.body k).drop n) := by
  intro r k n hr
  by_cases hrh : r = h
  · rw [hrh] at hr ⊢
    rw [lookup_cons_self]
    exact congrArg some (buf_read_self B hS hb hr)
  · rw [lookup_cons_ne hrh]
    exact hS r k n (streams_read_other hrh hr)

/-- A read keeps the trailer futures of the 0.3 state. -/
theorem body3Step_streams_futs (q : Body3St) (a : List Val) (r : Option (List Val)) :
    (body3Step q (.imp P3.cStreamRead a r)).futs = q.futs := by
  unfold body3Step
  repeat' split
  all_goals simp_all [P3.cStreamRead, P3.canon, consumeBody3]

/-- A read keeps the trailer resources of the 0.3 state. -/
theorem body3Step_read_trs (q : Body3St) (a : List Val) (r : Option (List Val)) :
    (body3Step q (.imp P3.cStreamRead a r)).trs = q.trs := by
  unfold body3Step
  repeat' split
  all_goals simp_all [P3.cStreamRead, P3.canon, consumeBody3]

/-- The body part of the 0.3 state does not touch the outgoing part. -/
theorem body3Step_base (q : Body3St) (e : WEv) : (body3Step q e).base = q.base := by
  unfold body3Step
  repeat' split
  all_goals rfl

/-- The read check on a buffered answer. -/
theorem bufRead_check (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (h : BitVec 32) (a' : List Val) {rest : List (BitVec 8)} (hb : lookup h st.bufs = some rest) :
    body3Check B q3 (.imp P3.cStreamRead (.u32 h :: a') (read3Ans rest (count3 (.u32 h :: a')))) =
      true := by
  simp only [body3Check, ↓reduceIte]
  split
  · next k n hl =>
    have hr : lookup h st.bufs = some ((B.body k).drop n) := hJ.2.1 h k n hl
    rw [hb] at hr
    rw [← Option.some.inj hr]
    exact read3Ans_ok rest _
  · rfl
where
  read3Ans_ok (rest : List (BitVec 8)) (n : Nat) : read3Ok rest n (read3Ans rest n) = true :=
    read3Ok_ans rest n

/-- `stream.read` of a stream with no buffer: `DROPPED 0` keeps `JB3`. -/
theorem bufRead_none (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (h : BitVec 32) (a' : List Val) (hn : lookup h st.bufs = none) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cStreamRead (.u32 h :: a') dropped0) = some q3' ∧
      JB3 B st q2 q3' := by
  have hu : ∀ k off, lookup h q3.streams ≠ some (some (k, off)) := fun k off hl => by
    have h' : lookup h st.bufs = some ((B.body k).drop off) := hJ.2.1 h k off hl
    rw [hn] at h'; exact absurd h' (by simp)
  have hc : body3Check B q3 (.imp P3.cStreamRead (.u32 h :: a') dropped0) = true := by
    simp only [body3Check, ↓reduceIte]
  refine ⟨_, body3Th_step_body (by decide) hc, ?_⟩
  rw [body3Step_read_untracked q3 h a' hu]
  exact hJ

/-- `stream.read` with ill-shaped arguments keeps `JB3`. -/
theorem bufRead_bad (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) (hne : ∀ h a', a = .u32 h :: a' → False) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cStreamRead a dropped0) = some q3' ∧ JB3 B st q2 q3' := by
  have hc : body3Check B q3 (.imp P3.cStreamRead a dropped0) = true := by
    unfold body3Check; split <;> simp_all
  have hs : body3Step q3 (.imp P3.cStreamRead a dropped0) = q3 := by
    unfold body3Step; split <;> simp_all
  exact ⟨_, body3Th_step_body (by decide) hc, by rw [hs]; exact hJ⟩

/-- **`stream.read` from the buffer** keeps `JB3`. -/
theorem bufRead_step (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cStreamRead a (bufRead st a).2) = some q3' ∧
      JB3 B (bufRead st a).1 q2 q3' := by
  unfold bufRead
  split
  · next h a' =>
    split
    · next rest hb =>
      refine ⟨_, body3Th_step_body (by decide) (bufRead_check B hJ h a' hb),
        by rw [body3Step_base]; exact hJ.1, streams_after_read B hJ.2.1 h a' rest hb, ?_, ?_⟩
      · exact fun f k hl => hJ.2.2.1 f k (by rwa [body3Step_streams_futs] at hl)
      · exact fun t k hl => hJ.2.2.2 t k (by rwa [body3Step_read_trs] at hl)
    · next hn => exact bufRead_none B hJ h a' hn
  · next hne => exact bufRead_bad B hJ a hne

/-- With no trailers, every `entries` answer passes. -/
theorem entriesOk_none (ans : Option (List Val)) : entriesOk none ans = true := by
  unfold entriesOk; split <;> rfl

/-- `copy-all` keeps the 0.3 state. -/
theorem body3Step_copy (q : Body3St) (a : List Val) (r : Option (List Val)) :
    body3Step q (.imp copyAll3 a r) = q := by
  unfold body3Step
  split <;> first
    | (rename_i h; obtain ⟨rfl, -⟩ := h; simp (config := {decide := true}))
    | rfl

/-- The trailer-resource clause of `JB3` after `future.read` hands out a fresh trailer handle. -/
theorem trs_after_fut (B : BWeb) {st : B3St} {q3 : Body3St}
    (hF : ∀ f k, lookup f q3.futs = some (some k) → (∃ r, B k.1 k.2 = .resp r) →
      ∃ i, lookup f st.futv = some i ∧ InfoOk B k i)
    (hT : ∀ t k, lookup t q3.trs = some (some k) →
      ∃ ans, lookup t st.trv = some ans ∧ entriesOk (B.trailers k) ans = true)
    {h : BitVec 32} {ans : Option (List Val)} (hi : lookup h st.futv = some (.tr ans)) :
    ∀ t k, lookup t ((BitVec.ofNat 32 (2 * st.next), (lookup h q3.futs).join) :: q3.trs) =
        some (some k) →
      ∃ ans', lookup t ((BitVec.ofNat 32 (2 * st.next), ans) :: st.trv) = some ans' ∧
        entriesOk (B.trailers k) ans' = true := by
  intro t k hl
  by_cases ht : t = BitVec.ofNat 32 (2 * st.next)
  · subst ht
    rw [lookup_cons_self] at hl ⊢
    have hk : lookup h q3.futs = some (some k) := by
      cases hj : lookup h q3.futs with
      | none => rw [hj] at hl; cases hl
      | some o => rw [hj] at hl; simp at hl; rw [hl]
    refine ⟨ans, rfl, ?_⟩
    cases hB : B k.1 k.2 with
    | resp x =>
      obtain ⟨i, hi', hok⟩ := hF h k hk ⟨x, hB⟩
      rw [hi] at hi'; cases hi'
      exact hok.2
    | error c => simp [BWeb.trailers, hB, entriesOk_none]
  · rw [lookup_cons_ne ht] at hl ⊢
    exact hT t k hl

/-- The 0.3 state after a `future.read` answer. -/
theorem body3Step_fut (q : Body3St) (h : BitVec 32) (a' : List Val) (r : Option (List Val)) :
    body3Step q (.imp P3.cFutureRead (.u32 h :: a') r) =
      match trHandle3 r with
      | some t => { q with trs := (t, (lookup h q.futs).join) :: q.trs }
      | none => q := by
  cases ht : trHandle3 r <;>
    simp [body3Step, ht, show P3.cFutureRead ≠ consumeBody3 by decide,
      show P3.cFutureRead ≠ P3.cStreamRead by decide]

/-- The future check on a tracked future with a buffered outcome. -/
theorem futCheck (B : BWeb) {q3 : Body3St} {h : BitVec 32} {a' : List Val} {r : Option (List Val)}
    (hk : ∀ k, lookup h q3.futs = some (some k) → (∃ x, B k.1 k.2 = .resp x) →
      fut3Ok (B.trailers k) r = true) :
    body3Check B q3 (.imp P3.cFutureRead (.u32 h :: a') r) = true := by
  simp only [body3Check, show P3.cFutureRead ≠ P3.cStreamRead by decide, ↓reduceIte]
  split
  · next k hl =>
    split
    · next x hx => exact hk k hl ⟨x, hx⟩
    · rfl
  · rfl

/-- A `future.read` answer that hands out no trailer handle and passes the check keeps `JB3`. -/
theorem futQuiet_step (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) (ans : Option (List Val)) (htr : trHandle3 ans = none)
    (hc : body3Check B q3 (.imp P3.cFutureRead a ans) = true) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cFutureRead a ans) = some q3' ∧ JB3 B st q2 q3' := by
  have hs : body3Step q3 (.imp P3.cFutureRead a ans) = q3 := by
    unfold body3Step
    split <;> first
      | (rename_i h; obtain ⟨rfl, -, rfl⟩ := h; simp (config := {decide := true}) [htr])
      | rfl
  exact ⟨_, body3Th_step_body (by decide) hc, by rw [hs]; exact hJ⟩

/-- The buffered outcome of a tracked future of a response. -/
theorem futInfo {B : BWeb} {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    {h : BitVec 32} {i : TrInfo} (hi : lookup h st.futv = some i) {k : Val × Val}
    (hl : lookup h q3.futs = some (some k)) (hr : ∃ x, B k.1 k.2 = .resp x) : InfoOk B k i := by
  obtain ⟨i', hi', hok⟩ := hJ.2.2.1 h k hl hr
  have hii : i' = i := Option.some.inj (hi'.symm.trans hi)
  exact hii ▸ hok

/-- `future.read` handing out a fresh trailer handle keeps `JB3`. -/
theorem futTr_step (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (h : BitVec 32) (a' : List Val) {ans : Option (List Val)} (hi : lookup h st.futv = some (.tr ans)) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cFutureRead (.u32 h :: a')
        (some [P3.natV 0, okV (some (.variant 1 (some (.u32 (BitVec.ofNat 32 (2 * st.next))))))])) =
        some q3' ∧
      JB3 B { st with trv := (BitVec.ofNat 32 (2 * st.next), ans) :: st.trv, next := st.next + 1 }
        q2 q3' := by
  have hc : body3Check B q3 (.imp P3.cFutureRead (.u32 h :: a')
      (some [P3.natV 0, okV (some (.variant 1 (some (.u32 (BitVec.ofNat 32 (2 * st.next))))))]))
      = true := futCheck B fun k hl hr => (futInfo hJ hi hl hr).1
  refine ⟨_, body3Th_step_body (by decide) hc, ?_⟩
  rw [body3Step_fut]
  exact ⟨hJ.1, hJ.2.1, hJ.2.2.1, trs_after_fut B hJ.2.2.1 hJ.2.2.2 hi⟩

/-- **`future.read` from the buffer** keeps `JB3`. -/
theorem bufFut_step (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) :
    ∃ q3', (body3Th B).step q3 (.imp P3.cFutureRead a (bufFut st a).2) = some q3' ∧
      JB3 B (bufFut st a).1 q2 q3' := by
  unfold bufFut
  split
  · next h a' =>
    split
    · next hi =>
      refine futQuiet_step B hJ _ _ rfl (futCheck B fun k hl hr => ?_)
      have hn : B.trailers k = none := futInfo hJ hi hl hr
      simp [fut3Ok, okV, noneV, hn]
    · next ans hi => exact futTr_step B hJ h a' hi
    · next v hi =>
      refine futQuiet_step B hJ _ _ rfl (futCheck B fun k hl hr => ?_)
      obtain ⟨c, p, hv⟩ : ∃ c p, v = .variant c p := futInfo hJ hi hl hr
      simp [fut3Ok, errV, hv]
    · next hi =>
      refine futQuiet_step B hJ _ _ rfl (futCheck B fun k hl hr => ?_)
      obtain ⟨i, hi', -⟩ := hJ.2.2.1 h k hl hr
      exact absurd (hi.symm.trans hi') (by simp)
  · next hne => exact futQuiet_step B hJ _ _ rfl (by unfold body3Check; split <;> simp_all)

/-- **`copy-all` from the buffer** keeps `JB3`. -/
theorem bufCopy_step (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) :
    ∃ q3', (body3Th B).step q3 (.imp copyAll3 a (bufCopy st a).2) = some q3' ∧
      JB3 B (bufCopy st a).1 q2 q3' := by
  have hb3 : isBodyFn3 copyAll3 = true := by decide
  have hs : ∀ r, body3Step q3 (.imp copyAll3 a r) = q3 := fun r =>
    body3Step_copy q3 a r
  refine ⟨_, body3Th_step_body hb3 ?_, by rw [hs]; exact hJ⟩
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    simp only [body3Check, bufCopy, selfH, show copyAll3 ≠ P3.cStreamRead by decide,
      show copyAll3 ≠ P3.cFutureRead by decide, ↓reduceIte]
    split
    · next k hl =>
      obtain ⟨ans, hans, hok⟩ := hJ.2.2.2 h k hl
      simp [hans, hok]
    · rfl
  all_goals rfl

/-! ## (b) with bodies: `consume-body` -/

/-- A step of the 0.2 theory with bodies on a body function: the check and the body part. -/
theorem bodyTh_step_body {B : BWeb} {q q' : BodySt} {f : FnName} (hb : isBodyFn f = true)
    {a : List Val} {r : Option (List Val)} (h : (bodyTh B).step q (.imp f a r) = some q') :
    bodyCheck B q (.imp f a r) = true ∧ q' = bodyStep q (.imp f a r) := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  refine ⟨by simp only [bodyOk, Bool.and_eq_true] at hok; exact hok.2, ?_⟩
  rw [hq, bodyNext, httpNext_body _ hb, ← bodyStep_base q]

/-- `JB3` reads only the outgoing part of the 0.2 state. -/
theorem jb3_base {B : BWeb} {st : B3St} {q2 q2' : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (hb : q2'.base = q2.base) : JB3 B st q2' q3 :=
  ⟨by rw [hb]; exact hJ.1, hJ.2⟩

/-- A trap of `consume-body` keeps `JB3`. -/
theorem consume_trap (B : BWeb) {st : B3St} {q2 q2' : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (hb : q2'.base = q2.base) (a : List Val) : PostC B q3 a (st, none) q2' := by
  have hc : body3Check B q3 (.imp consumeBody3 a none) = true := by
    unfold body3Check
    split <;> first
      | (rename_i h; obtain ⟨rfl, -, rfl⟩ := h; simp (config := {decide := true}))
      | rfl
  have hs : body3Step q3 (.imp consumeBody3 a none) = q3 := by
    unfold body3Step
    split <;> first
      | (rename_i h; obtain ⟨rfl, -, rfl⟩ := h; simp (config := {decide := true}))
      | rfl
  exact ⟨_, body3Th_step_body (by decide) hc, by rw [hs]; exact jb3_base hJ hb⟩

/-- The streams clause of `JB3` after storing a buffered body. -/
theorem store_streams (B : BWeb) {st : B3St} {q3 : Body3St}
    (hS : ∀ r k n, lookup r q3.streams = some (some (k, n)) →
      lookup r st.bufs = some ((B.body k).drop n))
    (o : Option (Val × Val)) (bytes : List (BitVec 8)) (hbytes : ∀ k, o = some k → bytes = B.body k) :
    ∀ r k n, lookup r ((BitVec.ofNat 32 (2 * st.next), o.map (·, 0)) :: q3.streams) =
        some (some (k, n)) →
      lookup r ((BitVec.ofNat 32 (2 * st.next), bytes) :: st.bufs) = some ((B.body k).drop n) := by
  intro r k n hl
  by_cases hrd : r = BitVec.ofNat 32 (2 * st.next)
  · rw [hrd, lookup_cons_self] at hl ⊢
    cases o with
    | none => cases hl
    | some k' =>
      have hkn : k' = k ∧ 0 = n := by simpa using hl
      obtain ⟨rfl, rfl⟩ := hkn
      rw [hbytes k' rfl]; rfl
  · rw [lookup_cons_ne hrd] at hl ⊢
    exact hS r k n hl

/-- The trailer-future clause of `JB3` after storing a buffered trailer outcome. -/
theorem store_futs (B : BWeb) {st : B3St} {q3 : Body3St}
    (hF : ∀ f k, lookup f q3.futs = some (some k) → (∃ r, B k.1 k.2 = .resp r) →
      ∃ i, lookup f st.futv = some i ∧ InfoOk B k i)
    (o : Option (Val × Val)) (i : TrInfo)
    (hinfo : ∀ k, o = some k → (∃ x, B k.1 k.2 = .resp x) → InfoOk B k i) :
    ∀ f k, lookup f ((BitVec.ofNat 32 (2 * st.next + 1), o) :: q3.futs) = some (some k) →
      (∃ r, B k.1 k.2 = .resp r) →
      ∃ i', lookup f ((BitVec.ofNat 32 (2 * st.next + 1), i) :: st.futv) = some i' ∧ InfoOk B k i' := by
  intro f k hl hx
  by_cases hfu : f = BitVec.ofNat 32 (2 * st.next + 1)
  · rw [hfu, lookup_cons_self] at hl ⊢
    exact ⟨i, rfl, hinfo k (Option.some.inj hl) hx⟩
  · rw [lookup_cons_ne hfu] at hl ⊢
    exact hF f k hl hx

/-- **Storing a buffered body** whose bytes and trailer outcome match the web keeps `JB3`. -/
theorem consume_store (B : BWeb) {st : B3St} {q2 q2' : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (hb : q2'.base = q2.base) (rs : BitVec 32) (rest : List Val)
    (bytes : List (BitVec 8)) (i : TrInfo)
    (hbytes : ∀ k, lookup rs q2.base.resps = some k → bytes = B.body k)
    (hinfo : ∀ k, lookup rs q2.base.resps = some k → (∃ x, B k.1 k.2 = .resp x) → InfoOk B k i) :
    PostC B q3 (.u32 rs :: rest) (storeBody st bytes i) q2' := by
  have hc : body3Check B q3 (.imp consumeBody3 (.u32 rs :: rest) (storeBody st bytes i).2) = true := by
    simp [body3Check, consumeBody3, P3.cStreamRead, P3.cFutureRead, copyAll3, P3.canon]
  refine ⟨_, body3Th_step_body (by decide) hc, ?_⟩
  have hr : lookup rs q3.base.resps = lookup rs q2.base.resps := by rw [hJ.1.2.2]
  simp only [body3Step, storeBody, P3.natV, ↓reduceIte, hr]
  exact ⟨by rw [hb]; exact hJ.1, store_streams B hJ.2.1 _ bytes hbytes,
    store_futs B hJ.2.2.1 _ i hinfo, hJ.2.2.2⟩

/-! ### 0.2 body steps -/

/-- `consume` answered `ok(b)`. -/
theorem bodyStep_consume (q : BodySt) (rs : BitVec 32) {r : Option (List Val)} {b : BitVec 32}
    (h : okHandle r = some b) :
    bodyStep q (.imp consume2 [.u32 rs] r) = { q with bodies := (b, lookup rs q.base.resps) :: q.bodies } := by
  simp [bodyStep, h]

/-- `stream` answered `ok(s)`. -/
theorem bodyStep_stream (q : BodySt) (b : BitVec 32) {r : Option (List Val)} {s : BitVec 32}
    (h : okHandle r = some s) :
    bodyStep q (.imp bodyStream2 [.u32 b] r) =
      { q with streams := (s, (lookup b q.bodies).join.map (·, 0)) :: q.streams } := by
  simp [bodyStep, h, show bodyStream2 ≠ consume2 by decide]

/-- `finish` answered `ft`. -/
theorem bodyStep_finish (q : BodySt) (b ft : BitVec 32) :
    bodyStep q (.imp bodyFinish2 [.u32 b] (some [.u32 ft])) =
      { q with ftr := (ft, (lookup b q.bodies).join) :: q.ftr } := by
  simp [bodyStep, show bodyFinish2 ≠ consume2 by decide, show bodyFinish2 ≠ bodyStream2 by decide,
    show isReadFn bodyFinish2 = false by decide]

/-- `future-trailers.get` with no trailer handle in the answer. -/
theorem bodyStep_trGet_none (q : BodySt) (ft : BitVec 32) {r : Option (List Val)}
    (h : trHandle r = none) : bodyStep q (.imp trGet2 [.u32 ft] r) = q := by
  simp [bodyStep, h, show trGet2 ≠ consume2 by decide, show trGet2 ≠ bodyStream2 by decide,
    show isReadFn trGet2 = false by decide, show trGet2 ≠ bodyFinish2 by decide]

/-- `future-trailers.get` handing out the trailer handle `t`. -/
theorem bodyStep_trGet_some (q : BodySt) (ft : BitVec 32) {r : Option (List Val)} {t : BitVec 32}
    (h : trHandle r = some t) :
    bodyStep q (.imp trGet2 [.u32 ft] r) = { q with trs := (t, (lookup ft q.ftr).join) :: q.trs } := by
  simp [bodyStep, h, show trGet2 ≠ consume2 by decide, show trGet2 ≠ bodyStream2 by decide,
    show isReadFn trGet2 = false by decide, show trGet2 ≠ bodyFinish2 by decide]

/-- `entries` keeps the body state. -/
theorem bodyStep_entries (q : BodySt) (a : List Val) (r : Option (List Val)) :
    bodyStep q (.imp entries2 a r) = q := by
  unfold bodyStep
  split <;> first
    | (rename_i h; obtain ⟨rfl, -⟩ := h; simp (config := {decide := true}))
    | rfl

/-- The trailer check on a trailer future of key `o`. -/
theorem trGet_check (B : BWeb) {q : BodySt} {ft : BitVec 32} {o : Option (Val × Val)}
    (hl : lookup ft q.ftr = some o) {r : Option (List Val)}
    (hc : bodyCheck B q (.imp trGet2 [.u32 ft] r) = true) :
    ∀ k, o = some k → (∃ x, B k.1 k.2 = .resp x) → trailerOk (B.trailers k) r = true := by
  rintro k rfl ⟨x, hx⟩
  simpa [bodyCheck, hl, hx, show isReadFn trGet2 = false by decide] using hc

/-- The `entries` check on a trailer resource of key `o`. -/
theorem entries_check (B : BWeb) {q : BodySt} {t : BitVec 32} {o : Option (Val × Val)}
    (hl : lookup t q.trs = some o) {r : Option (List Val)}
    (hc : bodyCheck B q (.imp entries2 [.u32 t] r) = true) :
    ∀ k, o = some k → entriesOk (B.trailers k) r = true := by
  rintro k rfl
  simpa [bodyCheck, hl, show isReadFn entries2 = false by decide,
    show entries2 ≠ trGet2 by decide] using hc

/-- After `future-trailers.get` handed out the trailer handle `t`: `entries(t)`. -/
theorem pollTr_entries (B : BWeb) {q2 : BodySt} {q3 : Body3St} (a : List Val) (ft : BitVec 32) (o : Option (Val × Val)) (kont : TrInfo → BProg3)
    (hk : ∀ i qx, qx.base = q2.base →
      (∀ k, o = some k → (∃ x, B k.1 k.2 = .resp x) → InfoOk B k i) →
      Wp (bodyTh B) (kont i) (PostC B q3 a) qx)
    (qa qb : BodySt) (hb : qa.base = q2.base) (hl : lookup ft qa.ftr = some o)
    {t : BitVec 32}
    (hq : qb = bodyStep qa (.imp trGet2 [.u32 ft]
      (some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 1 (some (.u32 t))))))))])))
    (htr : ∀ k, o = some k → (∃ x, B k.1 k.2 = .resp x) → trailerOk (B.trailers k)
      (some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 1 (some (.u32 t))))))))]) =
        true) :
    Wp (bodyTh B) (.call (iEntries, [.u32 t]) fun r₂ => kont (.tr r₂)) (PostC B q3 a) qb := by
  intro r₂ qc hs₂
  obtain ⟨hc₂, hq₂⟩ := bodyTh_step_body (f := entries2) (by decide) hs₂
  change bodyCheck B qb (.imp entries2 [.u32 t] r₂) = true at hc₂
  change qc = bodyStep qb (.imp entries2 [.u32 t] r₂) at hq₂
  have hqb : qb = { qa with trs := (t, o) :: qa.trs } := by
    rw [hq, bodyStep_trGet_some _ _ rfl, hl]; rfl
  have hlt : lookup t qb.trs = some o := by rw [hqb]; exact lookup_cons_self _ _ _
  have hent := entries_check B hlt hc₂
  have hbc : qc.base = q2.base := by rw [hq₂, bodyStep_entries, hqb]; exact hb
  exact hk (.tr r₂) qc hbc fun k ho hx => ⟨htr k ho hx, hent k ho⟩

/-- **Polling the trailers** gives the continuation an outcome that matches the web. -/
theorem wp_pollTr (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) (ft : BitVec 32) (o : Option (Val × Val)) (kont : TrInfo → BProg3)
    (hk : ∀ i qx, qx.base = q2.base →
      (∀ k, o = some k → (∃ x, B k.1 k.2 = .resp x) → InfoOk B k i) →
      Wp (bodyTh B) (kont i) (PostC B q3 a) qx) :
    ∀ n qa, qa.base = q2.base → lookup ft qa.ftr = some o →
      Wp (bodyTh B) (pollTr st ft kont n) (PostC B q3 a) qa
  | 0, _, hb, _ => consume_trap B hJ hb a
  | n + 1, qa, hb, hl => fun r qb hs => by
    obtain ⟨hc, hq⟩ := bodyTh_step_body (f := trGet2) (by decide) hs
    change bodyCheck B qa (.imp trGet2 [.u32 ft] r) = true at hc
    change qb = bodyStep qa (.imp trGet2 [.u32 ft] r) at hq
    have htr := trGet_check B hl hc
    have hbb : qb.base = q2.base := by rw [hq, bodyStep_base, hb]
    beta_reduce
    split
    · have hq' : qb = qa := by rw [hq, bodyStep_trGet_none _ _ rfl]
      exact wp_pollTr B hJ a ft o kont hk n qb hbb (hq' ▸ hl)
    · exact hk .noTr qb hbb fun k ho hx => Option.isNone_iff_eq_none.1 (htr k ho hx)
    · next t => exact pollTr_entries B a ft o kont hk qa qb hb hl hq htr
    · next c p => exact hk (.err _) qb hbb fun _ _ _ => ⟨c, p, rfl⟩
    · exact consume_trap B hJ hbb a

/-! ### Reading the body -/

/-- A `blocking-read` answered `ok(bytes)` advances a tracked stream by the bytes read. -/
theorem bodyStep_bread_ok (q : BodySt) (s : BitVec 32) (len : Val) {o : Option (Val × Val)} {m : Nat}
    (hl : lookup s q.streams = some (o.map (·, m))) {vs : List Val} {bs : List (BitVec 8)}
    (hbs : u8sOf vs = some bs) :
    lookup s (bodyStep q (.imp P2.isBread [.u32 s, len] (some [.variant 0 (some (.record vs))]))).streams =
        some (o.map (·, m + bs.length)) ∧
      (bodyStep q (.imp P2.isBread [.u32 s, len] (some [.variant 0 (some (.record vs))]))).bodies =
        q.bodies := by
  have hr : isReadFn P2.isBread = true := by decide
  cases o with
  | none =>
    simp only [Option.map_none] at hl ⊢
    simp [bodyStep, hl, hr, show P2.isBread ≠ consume2 by decide,
      show P2.isBread ≠ bodyStream2 by decide]
  | some k =>
    simp only [Option.map_some] at hl ⊢
    simp [bodyStep, hl, hr, readCount, hbs, show P2.isBread ≠ consume2 by decide,
      show P2.isBread ≠ bodyStream2 by decide, lookup_cons_self]

/-- A `blocking-read` answered `error(closed)` keeps the body state. -/
theorem bodyStep_bread_closed (q : BodySt) (s : BitVec 32) (len : Val) :
    bodyStep q (.imp P2.isBread [.u32 s, len] (some [.variant 1 (some (.variant 1 none))])) = q := by
  have hr : isReadFn P2.isBread = true := by decide
  simp only [bodyStep, hr, show P2.isBread ≠ consume2 by decide,
    show P2.isBread ≠ bodyStream2 by decide, ↓reduceIte, readCount, isFailed]
  split <;> simp_all

/-- The read check on a stream of key `o`. -/
theorem bread_check (B : BWeb) {q : BodySt} {s : BitVec 32} {len : Val} {o : Option (Val × Val)}
    {m : Nat} (hl : lookup s q.streams = some (o.map (·, m))) {r : Option (List Val)}
    (hc : bodyCheck B q (.imp P2.isBread [.u32 s, len] r) = true) :
    ∀ k, o = some k → readOk ((B.body k).drop m) (readLen [.u32 s, len]) r = true := by
  rintro k rfl
  simpa [bodyCheck, hl, show isReadFn P2.isBread = true by decide] using hc

/-- Bytes read after the first `m` are the next ones of the body. -/
theorem take_append_read {body acc bs : List (BitVec 8)} {m len : Nat} (hacc : acc = body.take m)
    (h : readOk (body.drop m) len (some [.variant 0 (some (.record (bs.map .u8)))]) = true) :
    acc ++ bs = body.take (m + bs.length) := by
  have h' : bs = (body.drop m).take bs.length := by
    simp only [readOk, u8sOf_map, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [hacc, List.take_add, ← h']

/-- `error(closed)` on a tracked stream: the bytes read are the whole body. -/
theorem closed_all {body acc : List (BitVec 8)} {m len : Nat} (hacc : acc = body.take m)
    (h : readOk (body.drop m) len (some [.variant 1 (some (.variant 1 none))]) = true) :
    acc = body := by
  have he : body.drop m = [] := List.isEmpty_iff.1 h
  rw [hacc, List.take_of_length_le (List.drop_eq_nil_iff.1 he)]

/-- `u8sOf` decodes only `u8` lists. -/
theorem u8sOf_eq {vs : List Val} {bs : List (BitVec 8)} (h : u8sOf vs = some bs) : vs = bs.map .u8 := by
  induction vs generalizing bs with
  | nil => simp [u8sOf] at h; simp [← h]
  | cons v t ih =>
    cases v <;> simp [u8sOf] at h
    obtain ⟨bs', hbs', rfl⟩ := h
    simp [ih hbs']

/-- **Reading the body to its end** gives the continuation the body bytes. -/
theorem wp_readAll (B : BWeb) {st : B3St} {q2 : BodySt} {q3 : Body3St} (hJ : JB3 B st q2 q3)
    (a : List Val) (s b : BitVec 32) (o : Option (Val × Val)) (kont : List (BitVec 8) → BProg3)
    (hk : ∀ bytes qx, qx.base = q2.base → lookup b qx.bodies = some o →
      (∀ k, o = some k → bytes = B.body k) → Wp (bodyTh B) (kont bytes) (PostC B q3 a) qx) :
    ∀ n acc qa, qa.base = q2.base → lookup b qa.bodies = some o → RdInv B s o acc qa →
      Wp (bodyTh B) (readAll st s kont n acc) (PostC B q3 a) qa
  | 0, _, _, hb, _, _ => consume_trap B hJ hb a
  | n + 1, acc, qa, hb, hbo, ⟨m, hl, hacc⟩ => fun r qb hs => by
    obtain ⟨hc, hq⟩ := bodyTh_step_body (f := P2.isBread) (by decide) hs
    change bodyCheck B qa (.imp P2.isBread [.u32 s, .u64 (BitVec.ofNat 64 readLen2)] r) = true at hc
    change qb = bodyStep qa (.imp P2.isBread [.u32 s, .u64 (BitVec.ofNat 64 readLen2)] r) at hq
    have hrd := bread_check B hl hc
    have hbb : qb.base = q2.base := by rw [hq, bodyStep_base, hb]
    beta_reduce
    split
    · next vs =>
      split
      · next bs hbs =>
        obtain ⟨hl', hbo'⟩ := bodyStep_bread_ok qa s _ hl hbs
        refine wp_readAll B hJ a s b o kont hk n (acc ++ bs) qb hbb (by rw [hq, hbo']; exact hbo)
          ⟨m + bs.length, by rw [hq]; exact hl', fun k ho => ?_⟩
        have h1 := hrd k ho
        rw [u8sOf_eq hbs] at h1
        exact take_append_read (hacc k ho) h1
      · exact consume_trap B hJ hbb a
    · have hq' : qb = qa := by rw [hq, bodyStep_bread_closed]
      exact hk acc qb hbb (hq' ▸ hbo) fun k ho => closed_all (hacc k ho) (hrd k ho)
    · exact consume_trap B hJ hbb a

/-! ### Finishing the body and the whole call -/

/-- After the body: `finish`, then the trailers, then the stored answer. -/
theorem wp_finish (B : BWeb) (rounds : Nat) {st : B3St} {q2 : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (rs : BitVec 32) (rest : List Val) (b : BitVec 32)
    (bytes : List (BitVec 8)) (qa : BodySt) (hb : qa.base = q2.base)
    (hbo : lookup b qa.bodies = some (lookup rs q2.base.resps))
    (hbytes : ∀ k, lookup rs q2.base.resps = some k → bytes = B.body k) :
    Wp (bodyTh B) (finishProg rounds st b bytes) (PostC B q3 (.u32 rs :: rest)) qa := by
  intro r qb hs
  obtain ⟨-, hq⟩ := bodyTh_step_body (f := bodyFinish2) (by decide) hs
  change qb = bodyStep qa (.imp bodyFinish2 [.u32 b] r) at hq
  have hbb : qb.base = q2.base := by rw [hq, bodyStep_base, hb]
  beta_reduce
  split
  · next ft =>
    have hl : lookup ft qb.ftr = some (lookup rs q2.base.resps) := by
      rw [hq, bodyStep_finish, lookup_cons_self, hbo]; rfl
    exact wp_pollTr B hJ (.u32 rs :: rest) ft _ (fun i => .pure (storeBody st bytes i))
      (fun i qx hbx hi => consume_store B hJ hbx rs rest bytes i hbytes hi) rounds qb hbb hl
  · exact consume_trap B hJ hbb _

/-- After `consume` gave the body `b` (recorded for the request of `rs`): the stream, the body
and the trailers. -/
theorem wp_streamProg (B : BWeb) (rounds : Nat) {st : B3St} {q2 : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (rs : BitVec 32) (rest : List Val) (b : BitVec 32) (qa : BodySt)
    (hba : qa.base = q2.base) (hbo : lookup b qa.bodies = some (lookup rs q2.base.resps)) :
    Wp (bodyTh B) (streamProg rounds st b) (PostC B q3 (.u32 rs :: rest)) qa := by
  intro r₂ qb hs₂
  obtain ⟨-, hq₂⟩ := bodyTh_step_body (f := bodyStream2) (by decide) hs₂
  change qb = bodyStep qa (.imp bodyStream2 [.u32 b] r₂) at hq₂
  have hbb : qb.base = q2.base := by rw [hq₂, bodyStep_base, hba]
  beta_reduce
  split
  · next s hs =>
    have hbo' : lookup b qb.bodies = some (lookup rs q2.base.resps) := by
      rw [hq₂, bodyStep_stream _ _ hs]; exact hbo
    have hsl : lookup s qb.streams = some ((lookup rs q2.base.resps).map (·, 0)) := by
      rw [hq₂, bodyStep_stream _ _ hs, lookup_cons_self, hbo]; rfl
    exact wp_readAll B hJ _ s b _ _
      (fun bytes qx hbx hbox hby => wp_finish B rounds hJ rs rest b bytes qx hbx hbox hby)
      rounds [] qb hbb hbo' ⟨0, hsl, fun _ _ => rfl⟩
  · exact consume_trap B hJ hbb _

/-- **The program of `consume-body`** answers as the 0.3 theory with bodies allows, keeping
`JB3`. -/
theorem wp_consume (B : BWeb) (rounds : Nat) {st : B3St} {q2 : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (a : List Val) :
    Wp (bodyTh B) (consumeProg rounds st a) (PostC B q3 a) q2 := by
  unfold consumeProg
  split
  · next rs rest =>
    intro r₁ qa hs₁
    obtain ⟨-, hq₁⟩ := bodyTh_step_body (f := consume2) (by decide) hs₁
    change qa = bodyStep q2 (.imp consume2 [.u32 rs] r₁) at hq₁
    have hba : qa.base = q2.base := by rw [hq₁, bodyStep_base]
    beta_reduce
    split
    · next b hb₁ =>
      have hbo : lookup b qa.bodies = some (lookup rs q2.base.resps) := by
        rw [hq₁, bodyStep_consume _ _ hb₁, lookup_cons_self]
      exact wp_streamProg B rounds hJ rs rest b qa hba hbo
    · exact consume_trap B hJ hba _
  · exact consume_trap B hJ rfl a

/-! ### The invariant and the model theorem -/

/-- The body functions of the 0.3 slice. -/
theorem bodyFn3_cases {f : FnName} (hb : isBodyFn3 f = true) :
    f = consumeBody3 ∨ f = copyAll3 ∨ f = P3.cStreamRead ∨ f = P3.cFutureRead := by
  simp only [isBodyFn3, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with ((h | h) | h) | h <;> simp [h]

/-- **A body export call** of `httpB3Over2` keeps `JB3`. -/
theorem body_call (B : BWeb) (rounds : Nat) {st : B3St} {q2 : BodySt} {q3 : Body3St}
    (hJ : JB3 B st q2 q3) (q : (nsig httpBody3Fns).Op) (hb : isBodyFn3 q.1.1 = true) :
    Wp (bodyTh B) (httpB3Over2 rounds st q)
      (fun a q2' => ∃ q3', (body3Th B).step q3 (.imp q.1.1 q.2 a.2) = some q3' ∧ JB3 B a.1 q2' q3')
      q2 := by
  show Wp (bodyTh B) (if hb : isBodyFn3 q.1.1 = false then _ else _) _ q2
  simp only [hb, Bool.true_eq_false, ↓reduceDIte, bodyProg3]
  rcases bodyFn3_cases hb with h | h | h | h <;> rw [h]
  · simp only [↓reduceIte]
    exact wp_consume B rounds hJ q.2
  · simp only [show copyAll3 ≠ consumeBody3 by decide, show copyAll3 ≠ P3.cStreamRead by decide,
      show copyAll3 ≠ P3.cFutureRead by decide, ↓reduceIte]
    exact bufCopy_step B hJ q.2
  · simp only [show P3.cStreamRead ≠ consumeBody3 by decide, ↓reduceIte]
    exact bufRead_step B hJ q.2
  · simp only [show P3.cFutureRead ≠ consumeBody3 by decide,
      show P3.cFutureRead ≠ P3.cStreamRead by decide, ↓reduceIte]
    exact bufFut_step B hJ q.2

/-- The invariant of `httpB3Over2`. -/
theorem httpB3Over2_inv (B : BWeb) (rounds : Nat) :
    WpInv (httpB3Over2 rounds) {} (bodyTh B) (body3Th B) (JB3 B) where
  init := ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ h => by simp [lookup, body3Th, gated] at h,
    fun _ _ h => by simp [lookup, body3Th, gated] at h,
    fun _ _ h => by simp [lookup, body3Th, gated] at h⟩
  call := by
    intro st q2 q3 q hJ
    by_cases hb : isBodyFn3 q.1.1 = false
    · exact base_call B rounds hJ q hb
    · exact body_call B rounds hJ q (by simpa using hb)

/-- **The component guarantee of HTTP with bodies, 0.3 over 0.2.** -/
theorem httpB3Over2_sat (B : BWeb) (rounds : Nat) :
    (agP (bodyTh B) (retG (body3Th B))).holds (ofSBody (httpB3Over2 rounds) {}) :=
  ag_of_wpInv (httpB3Over2_inv B rounds)

/-- **HTTP with response bodies, 0.3 over 0.2**: over every host of the 0.2 theory with
bodies of the body web `B`, the buffering composite is a model of the 0.3 theory with bodies of
the same web. -/
theorem httpB3Over2_model (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBodyImports}
    (hη : (hostSat (bodyTh B).Accepts).holds η) :
    (hostSat (body3Th B).Accepts).holds (link η (ofSBody (httpB3Over2 rounds) {})) :=
  link_model (httpB3Over2_sat B rounds) hη

end Silmaril.Wasi.Versions.Net
