module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.OsStore
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Typed
public import Silmaril.Wasi.Versions.P3OverP2.Os.Defs
public import Silmaril.Wasi.Os.Thms

/-!
# Proofs: the OS image of WASI 0.3 over 0.2, one call at a time

`OsInv c o n` relates the component's state `c` to the state `o` of the 0.3 image `osStep3` after
`n` answers, in runs where no `stream.write` was answered `BLOCKED`:

* the store invariant `SI`, and at most `1 + 4 n` handles used (so there is room while
  `n < 2^29`); no pending stdout write, in the component or in the image;
* every writable end of a guest stream `s` is the one the image recorded for `s`; a recorded
  pair `(r, r + 1)` has `r` still a live readable end, or bound to stdout, or a dead channel;
* a writable end bound to stdout is recorded as such by the image (`outW`), and a writable end
  the image records as stdout is bound, or its channel is dead (`outW'`), so a write to it never
  completes as a guest write.

`wp_os`: every call keeps the invariant (unless it answers `BLOCKED` or reaches `2^29` answers),
and the bytes its 0.2 program wrote (`osImg2`) are the bytes `osStep3` records for its answer:
`stream.write` on a stdout stream `write`s exactly the bytes it reports `COMPLETED`
(`os_sw`); every other call writes nothing and records nothing.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (Store Obj Res packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Process.LPS (Word Event)

/-- A 0.2 function that writes bytes in the OS image. -/
def isW (f : FnName) : Prop :=
  f = P2.osWrite ∨ f = streamWrite ∨ f = P2.osWriteZeroes ∨ f = P2.osBwzf

/-- A program that never calls a writing function. -/
def NoW {I : Set FnName} {A : Type} : Prog (nsig I) A → Prop
  | .pure _ => True
  | .call m k => ¬ isW m.1.1 ∧ ∀ n, NoW (k n)

/-- Calls of non-writing functions add nothing to the 0.2 image. -/
theorem osEv2_noW (ch : Word) {f : FnName} (hf : ¬ isW f) (a : List Val) (r : Option (List Val)) :
    P2.osEv2 ch (.imp f a r) = [] := by
  have h1 : ¬ (f = P2.osWrite ∨ f = streamWrite) := fun h => hf (h.elim Or.inl (Or.inr ∘ Or.inl))
  have h2 : ¬ (f = P2.osWriteZeroes ∨ f = P2.osBwzf) := fun h => hf (Or.inr (Or.inr h))
  unfold P2.osEv2
  split
  · rename_i f' a' heq
    cases heq
    simp only [h1, h2, ↓reduceIte]
  · rfl

/-- The 0.2 image is kept by an accepted answer of a non-writing function. -/
theorem img2_noW (ch : Word) {f : FnName} (hf : ¬ isW f) {a : List Val} {r : Option (List Val)}
    {q q' : List Event} (h : (osImg2 ch).step q (.imp f a r) = some q') : q' = q := by
  change (if P2.p2Ok (.imp f a r) then some (q ++ P2.osEv2 ch (.imp f a r)) else none) = some q' at h
  split at h
  · rw [osEv2_noW ch hf] at h
    simpa using h.symm
  · cases h

/-- **A program without writes keeps the 0.2 image.** -/
theorem wp_noW (ch : Word) {I : Set FnName} {A : Type} {Q : A → List Event → Prop} {qT : List Event}
    (hQ : ∀ a, Q a qT) : ∀ p : Prog (nsig I) A, NoW p → Wp (osImg2 ch) p Q qT
  | .pure a, _ => hQ a
  | .call m k, ⟨hm, hk⟩ => fun n qT' hn => by
    have hq := img2_noW ch hm hn
    subst hq
    exact wp_noW ch hQ (k n) (hk n)

/-- `emb` keeps the absence of writes. -/
theorem noW_emb {A : Type} : ∀ p : NProg A, NoW p → NoW (emb p)
  | .pure _, _ => trivial
  | .call _ k, ⟨hm, hk⟩ => ⟨hm, fun n => noW_emb (k n) (hk n)⟩

/-- `emb` of a sequence. -/
theorem emb_bind {A B : Type} (f : A → NProg B) : ∀ p : NProg A,
    emb (p.bind f) = (emb p).bind fun a => emb (f a)
  | .pure _ => rfl
  | .call m k => by
    show Prog.call _ _ = Prog.call _ _
    congr 1
    funext n
    exact emb_bind f (k n)

/-- A pure continuation by cases has no writes. -/
theorem noW_pure {I : Set FnName} {A : Type} (a : A) : NoW (.pure a : Prog (nsig I) A) := trivial


/-- The bytes a `writeOut` of `xs` put in the 0.2 image, by its result. -/
def imgW (ch : Word) (xs : List (BitVec 8)) : Option Nat → List Event
  | some m => (xs.take m).map (.writeEv ch)
  | none => []

theorem notW_checkWrite : ¬ isW P2.osCheckWrite := by unfold isW; decide
theorem notW_pollPoll : ¬ isW P2.pollPoll := by unfold isW; decide
theorem notW_pollDrop : ¬ isW P2.pollDrop := by unfold isW; decide
theorem notW_subscribe : ¬ isW P2.osSubscribe := by unfold isW; decide
theorem notW_bflush : ¬ isW P2.osBflush := by unfold isW; decide
theorem notW_getStdout : ¬ isW getStdout := by unfold isW; decide
theorem notW_getStdin : ¬ isW P2.getStdin := by unfold isW; decide
theorem notW_now : ¬ isW clockNow := by unfold isW; decide
theorem notW_subDur : ¬ isW P2.monoSubDuration := by unfold isW; decide
theorem notW_getDirs : ¬ isW getDirs := by unfold isW; decide
theorem notW_openAt : ¬ isW openAt := by unfold isW; decide
theorem notW_bread : ¬ isW P2.isBread := by unfold isW; decide
theorem notW_rvs : ¬ isW P2.fdReadStream := by unfold isW; decide

theorem noW_checkW (os : BitVec 32) : NoW (checkW os) := by
  refine ⟨notW_checkWrite, fun n => ?_⟩
  dsimp only
  split <;> trivial

theorem noW_pollOn (p : BitVec 32) : NoW (pollOn p) :=
  ⟨notW_pollPoll, fun _ => ⟨notW_pollDrop, fun _ => trivial⟩⟩

theorem noW_pollOut (os : BitVec 32) : NoW (pollOut os) := by
  refine ⟨notW_subscribe, fun n => ?_⟩
  dsimp only
  split
  · exact noW_pollOn _
  · trivial

theorem noW_bind {I : Set FnName} {A B : Type} {f : A → Prog (nsig I) B} (hf : ∀ a, NoW (f a)) :
    ∀ p : Prog (nsig I) A, NoW p → NoW (p.bind f)
  | .pure a, _ => hf a
  | .call _ k, ⟨hm, hk⟩ => ⟨hm, fun n => noW_bind hf (k n) (hk n)⟩

theorem noW_permit (os : BitVec 32) : ∀ fuel, NoW (permit os fuel)
  | 0 => noW_checkW os
  | fuel + 1 => by
    refine noW_bind (fun r => ?_) _ (noW_checkW os)
    split
    · exact noW_bind (fun _ => noW_permit os fuel) _ (noW_pollOut os)
    · trivial

/-- The bytes of `write`'s argument list. -/
theorem contentsOf_write (os : BitVec 32) (ys : List (BitVec 8)) :
    P2.contentsOf [.u32 os, bytesV ys] = ys := Silmaril.Wasi.Os.bytesOf_bytesV ys

/-- A `write` answer that is not `ok` adds nothing to the 0.2 image. -/
theorem osEv2_notOk (ch : Word) (f : FnName) (a : List Val) {r : Option (List Val)}
    (hr : r ≠ some [.variant 0 none]) : P2.osEv2 ch (.imp f a r) = [] := by
  unfold P2.osEv2
  split
  · rename_i f' a' heq
    cases heq
    exact absurd rfl hr
  · rfl

/-- `write` is always accepted by `p2Ok`. -/
theorem p2Ok_write (a : List Val) (r : Option (List Val)) : P2.p2Ok (.imp P2.osWrite a r) = true := by
  have h : P2.ioOp P2.osWrite = .write := by decide
  simp [P2.p2Ok, h]

/-- The step of the 0.2 image on a `write`. -/
theorem img2_write (ch : Word) (os : BitVec 32) (ys : List (BitVec 8)) (ans : Option (List Val))
    (qT qT' : List Event) (hs : (osImg2 ch).step qT (.imp P2.osWrite [.u32 os, bytesV ys] ans) = some qT') :
    qT' = qT ++ P2.osEv2 ch (.imp P2.osWrite [.u32 os, bytesV ys] ans) := by
  change (if P2.p2Ok (.imp P2.osWrite [.u32 os, bytesV ys] ans) then
    some (qT ++ P2.osEv2 ch (.imp P2.osWrite [.u32 os, bytesV ys] ans)) else none) = some qT' at hs
  rw [p2Ok_write] at hs
  exact (Option.some.inj hs).symm

/-- The `write` of `writeOut` and its answer. -/
theorem wp_write_ans (ch : Word) (xs : List (BitVec 8)) (m : Nat) (hm : m ≤ xs.length)
    (ans : Option (List Val)) (qT : List Event) (os : BitVec 32) :
    Wp (osImg2 ch) (emb (match ans with
        | some [.variant 0 none] => (Prog.pure (some m) : NProg (Option Nat))
        | _ => Prog.pure none))
      (fun d q => q = qT ++ imgW ch xs d ∧ ∀ m', d = some m' → m' ≤ xs.length)
      (qT ++ P2.osEv2 ch (.imp P2.osWrite [.u32 os, bytesV (xs.take m)] ans)) := by
  by_cases ha : ans = some [.variant 0 none]
  · subst ha
    refine ⟨?_, fun m' hm' => by cases hm'; exact hm⟩
    simp [P2.osEv2, contentsOf_write, imgW]
  · rw [osEv2_notOk ch _ _ ha, List.append_nil]
    revert ha
    split
    · intro ha
      exact absurd rfl ha
    · intro _
      exact ⟨by simp [imgW], fun m' hm' => by cases hm'⟩

/-- **`writeOut` writes what its result says.** -/
theorem wp_writeOut (ch : Word) (os : BitVec 32) (xs : List (BitVec 8)) (qT : List Event) :
    Wp (osImg2 ch) (emb (writeOut os xs))
      (fun d q => q = qT ++ imgW ch xs d ∧ ∀ m, d = some m → m ≤ xs.length) qT := by
  rw [writeOut, emb_bind, Wp.bind]
  refine wp_noW ch (fun r => ?_) _ (noW_emb _ (noW_permit os rounds))
  rcases r with _ | n
  · exact ⟨by simp [imgW], fun m hm => by cases hm⟩
  · by_cases hm : min n xs.length = 0
    · simp only [hm, ↓reduceIte]
      exact ⟨by simp [imgW], fun m hm' => by cases hm'; exact Nat.zero_le _⟩
    · simp only [hm, ↓reduceIte]
      intro ans qT' hs
      have hq : qT' = qT ++ P2.osEv2 ch
          (.imp P2.osWrite [.u32 os, bytesV (xs.take (min n xs.length))] ans) :=
        img2_write ch os _ ans qT qT' hs
      subst hq
      exact wp_write_ans ch xs _ (Nat.min_le_right _ _) ans qT os


/-- `p2Ok` makes `get-stdout` answer a handle. -/
theorem p2Ok_getStdout {a : List Val} {r : Option (List Val)}
    (h : P2.p2Ok (.imp getStdout a r) = true) : ∃ os, r = some [.u32 os] := by
  have hop : P2.ioOp getStdout = .other := by decide
  have h1 : (getStdout = P2.cliExit) = False := by decide
  have h2 : (getStdout = P2.getEnv) = False := by decide
  have h3 : (getStdout = P2.getArgs) = False := by decide
  have h4 : (getStdout = P2.initialCwd) = False := by decide
  simp only [P2.p2Ok, hop, ↓reduceIte, P2.cliOk_eq_hand, P2.cliOkH, h1, h2, h3, h4, true_or, or_true] at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- **`write-via-stream`'s 0.2 program**: it keeps the 0.2 image, and it gets an output stream
when the stream is a live guest stream and there is room. -/
theorem wp_ioWvs (ch : Word) (c : Core) (a : List Val) (qT : List Event) :
    Wp (osImg2 ch) (emb (ioWvs c a))
      (fun d q => q = qT ∧ (wvsSrc c a ≠ none → c.room = true → d ≠ none)) qT := by
  unfold ioWvs
  split
  · split
    · rename_i hroom
      intro ans qT' hs
      have hq := img2_noW ch notW_getStdout hs
      subst hq
      change (if P2.p2Ok (.imp getStdout [] ans) then some _ else none) = some _ at hs
      split at hs
      · rename_i hok
        obtain ⟨os, rfl⟩ := p2Ok_getStdout hok
        exact ⟨rfl, fun _ _ => by simp⟩
      · cases hs
    · rename_i hroom
      exact ⟨rfl, fun _ h => absurd h hroom⟩
  · rename_i hsrc
    exact ⟨rfl, fun h => absurd hsrc h⟩


/-! ## The invariant -/

/-- The writable end the OS image recorded for the readable end `r`. -/
def pairOf (o : OsSt) (r : Nat) : Option Nat := (o.pairs.find? (·.1 = r)).map (·.2)

/-- **The OS invariant**: the component's store and bindings against the state `o` of the 0.3
image after `n` answers. -/
structure OsInv (c : Core) (o : OsSt) (n : Nat) : Prop where
  si : SI c.st
  room : c.st.next ≤ 1 + 4 * n
  pend : c.pend = []
  opend : o.pend = []
  wEnd : ∀ w s, c.st.tbl w = some (.streamW s) → pairOf o s = some w
  pairs : ∀ r w, pairOf o r = some w → w = r + 1 ∧ 1 ≤ r ∧ r + 1 < c.st.next ∧
    (c.st.tbl r = some (.streamR r) ∨ c.outOf r ≠ none ∨ Dead c.st r)
  outW : ∀ w, outW c w ≠ none → w ∈ o.outW
  outW' : ∀ w s, w ∈ o.outW → c.st.tbl w = some (.streamW s) → c.outOf s ≠ none ∨ Dead c.st s
  outs : ∀ ch, c.outOf ch ≠ none → ch < c.st.next
  oOutW : ∀ w ∈ o.outW, w < c.st.next

theorem OsInv.init : OsInv ({} : Core) ({} : OsSt) 0 :=
  ⟨SI.init, Nat.le_refl _, rfl, rfl, (fun _ _ h => by cases h), (fun _ _ h => by cases h),
    (fun _ h => by simp [P3OverP2.outW] at h), (fun _ _ h => by cases h), (fun _ h => by simp [Core.outOf] at h),
    (fun _ h => by cases h)⟩

/-- `outW` through the table. -/
theorem outW_eq {c : Core} {w : Nat} (h : outW c w ≠ none) :
    ∃ s, c.st.tbl w = some (.streamW s) ∧ c.outOf s ≠ none := by
  unfold P3OverP2.outW at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · exact absurd rfl h

/-- The recorded pairs under a change that keeps live readable ends live or dead. -/
theorem OsInv.mono_pairs {c c' : Core} {o : OsSt} {n : Nat} (h : OsInv c o n)
    (hnx : c.st.next ≤ c'.st.next) (hout : c'.outs = c.outs)
    (hr : ∀ r, c.st.tbl r = some (.streamR r) → c'.st.tbl r = some (.streamR r) ∨ Dead c'.st r)
    (hdead : ∀ s, Dead c.st s → Dead c'.st s) (r w : Nat) (hrw : pairOf o r = some w) :
    w = r + 1 ∧ 1 ≤ r ∧ r + 1 < c'.st.next ∧
      (c'.st.tbl r = some (.streamR r) ∨ c'.outOf r ≠ none ∨ Dead c'.st r) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.pairs r w hrw
  have hof : c'.outOf r = c.outOf r := by simp [Core.outOf, hout]
  refine ⟨h1, h2, by omega, ?_⟩
  rw [hof]
  rcases h4 with h4 | h4 | h4
  · exact (hr r h4).elim Or.inl (Or.inr ∘ Or.inr)
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (hdead r h4))

/-- **The invariant under a change of the store** that adds no writable end, keeps live readable
ends live or dead, keeps dead channels dead, and keeps the bindings. -/
theorem OsInv.mono {c c' : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hsi : SI c'.st)
    (hroom : c'.st.next ≤ 1 + 4 * (n + 1)) (hnx : c.st.next ≤ c'.st.next)
    (hout : c'.outs = c.outs) (hp : c'.pend = [])
    (hw : ∀ w s, c'.st.tbl w = some (.streamW s) → c.st.tbl w = some (.streamW s))
    (hr : ∀ r, c.st.tbl r = some (.streamR r) → c'.st.tbl r = some (.streamR r) ∨ Dead c'.st r)
    (hdead : ∀ s, Dead c.st s → Dead c'.st s) : OsInv c' o (n + 1) := by
  have hof : ∀ ch, c'.outOf ch = c.outOf ch := fun ch => by simp [Core.outOf, hout]
  refine ⟨hsi, hroom, hp, h.opend, fun w s hw' => h.wEnd w s (hw w s hw'),
    h.mono_pairs hnx hout hr hdead, fun w hw' => ?_, fun w s hw1 hw2 => ?_,
    fun ch hc => Nat.lt_of_lt_of_le (h.outs ch (hof ch ▸ hc)) hnx,
    fun w hw' => Nat.lt_of_lt_of_le (h.oOutW w hw') hnx⟩
  · obtain ⟨s, hws, hs⟩ := outW_eq hw'
    refine h.outW w ?_
    unfold P3OverP2.outW
    rw [hw w s hws]
    rw [hof] at hs
    exact hs
  · rw [hof]
    exact (h.outW' w s hw1 (hw w s hw2)).imp id (hdead s)

/-- **A step of the async store keeps the invariant** (bindings and the image state unchanged). -/
theorem OsInv.astep {c : Core} {o : OsSt} {n : Nat} {st' : Store} (h : OsInv c o n)
    (ha : AOk c.st st') (c' : Core) (hst : c'.st = st') (hout : c'.outs = c.outs)
    (hp : c'.pend = []) : OsInv c' o (n + 1) := by
  subst hst
  have hn := ha.next
  have hroom := h.room
  refine h.mono ha.si (by omega) hn.1 hout hp (fun w s hw => ?_) (fun r hr => ?_) ha.dead
  · rcases ha.tbl w _ hw with hw' | ⟨-, hw'⟩
    · exact hw'
    · cases hw'
  · cases ht : c'.st.tbl r with
    | none => exact Or.inr (ha.rGone r r hr ht)
    | some o' =>
      rcases ha.tbl r o' ht with ht' | ⟨hr', -⟩
      · rw [hr] at ht'; cases ht'; exact Or.inl rfl
      · have := (h.si.lt r _ hr).2; omega


/-- The invariant for one more answer. -/
theorem OsInv.succ {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) : OsInv c o (n + 1) :=
  h.astep (AOk.refl h.si) c rfl rfl h.pend

/-! ## The 0.3 image, by function -/

/-- Functions the 0.3 image ignores. -/
theorem osStep3_other (ch : Word) (o : OsSt) {f : FnName} (h1 : f ≠ cStreamNew)
    (h2 : f ≠ stdoutWrite3) (h3 : f ≠ cStreamWrite) (h4 : f ≠ cWait) (a : List Val)
    (r : Option (List Val)) : osStep3 ch o (.imp f a r) = (o, []) := by
  delta osStep3
  dsimp only
  simp only [h1, h2, h3, h4, ↓reduceIte]

/-- `waitable-set.wait` with no pending write in the image. -/
theorem osStep3_wait (ch : Word) {o : OsSt} (ho : o.pend = []) (a : List Val)
    (r : Option (List Val)) : osStep3 ch o (.imp cWait a r) = (o, []) := by
  have h1 : cWait ≠ cStreamNew := by decide
  have h2 : cWait ≠ stdoutWrite3 := by decide
  have h3 : cWait ≠ cStreamWrite := by decide
  delta osStep3
  dsimp only
  simp only [h1, h2, h3, ↓reduceIte, ho]
  split
  · split
    · split
      · rename_i heq; simp at heq
      · rfl
    · rfl
  · rfl

/-- `stream.new` with handles below `2^32`. -/
theorem osStep3_new (ch : Word) (o : OsSt) (a : List Val) {x y : Nat} (hx : x < 2 ^ 32)
    (hy : y < 2 ^ 32) :
    osStep3 ch o (.imp cStreamNew a (some [natV x, natV y])) =
      ({ o with pairs := (x, y) :: o.pairs }, []) := by
  delta osStep3
  dsimp only
  simp [natOf_natV hx, natOf_natV hy]

/-- `write-via-stream`. -/
theorem osStep3_wvs (ch : Word) (o : OsSt) (a : List Val) (r : Option (List Val)) :
    osStep3 ch o (.imp stdoutWrite3 a r) =
      (match arg1 a >>= pairOf o with
       | some w => ({ o with outW := w :: o.outW }, [])
       | none => (o, [])) := by
  have h1 : stdoutWrite3 ≠ cStreamNew := by decide
  delta osStep3
  dsimp only
  simp only [h1, ↓reduceIte]
  match a with
  | [rv] =>
    simp only [arg1]
    rfl
  | [] => rfl
  | _ :: _ :: _ => rfl


/-- `stream.write` answered `COMPLETED k`. -/
theorem osStep3_sw_completed (ch : Word) (o : OsSt) {wv buf : Val} {w : Nat} (hw : natOf wv = some w)
    {code k : Nat} (hc : code < 2 ^ 32) (hk : copyOf code = some (some (.completed, k))) :
    osStep3 ch o (.imp cStreamWrite [wv, buf] (some [natV code])) =
      (o, if w ∈ o.outW then ((bytesOf buf).take k).map (.writeEv ch) else []) := by
  have h1 : cStreamWrite ≠ cStreamNew := by decide
  have h2 : cStreamWrite ≠ stdoutWrite3 := by decide
  delta osStep3
  dsimp only
  simp only [h1, h2, ↓reduceIte, hw, natOf_natV hc, Option.bind_eq_bind, Option.bind_some, hk]
  split <;> rfl

/-- `stream.write` answered neither `COMPLETED` nor `BLOCKED`. -/
theorem osStep3_sw_other (ch : Word) (o : OsSt) (a : List Val) {code : Nat}
    (hc : code < 2 ^ 32) (hk : ∀ k, copyOf code ≠ some (some (.completed, k)))
    (hb : copyOf code ≠ some none) :
    osStep3 ch o (.imp cStreamWrite a (some [natV code])) = (o, []) := by
  have h1 : cStreamWrite ≠ cStreamNew := by decide
  have h2 : cStreamWrite ≠ stdoutWrite3 := by decide
  delta osStep3
  dsimp only
  simp only [h1, h2, ↓reduceIte]
  split
  · rename_i wv buf pv heq
    cases heq
    simp only [natOf_natV hc, Option.bind_eq_bind, Option.bind_some]
    split
    · rename_i hk'
      exact absurd hk' (hk _)
    · rename_i hk'
      exact absurd hk' hb
    · rfl
  · rfl


/-! ## The invariant under the functions that allocate -/

theorem pairOf_cons (o : OsSt) (x y r : Nat) :
    pairOf { o with pairs := (x, y) :: o.pairs } r = if x = r then some y else pairOf o r := by
  by_cases h : x = r <;> simp [pairOf, h]

/-- The table after `alloc2`. -/
theorem alloc2_tbl (st : Store) (a b : Nat → Obj) (x : Nat) :
    (st.alloc2 a b).1.tbl x =
      if x = st.next + 1 then some (b st.next) else if x = st.next then some (a st.next)
      else st.tbl x := by
  simp only [Store.alloc2, Silmaril.Wasm.Component.Async.upd]

/-- **`stream.new`** keeps the invariant, with the new pair recorded. -/
theorem OsInv.new {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hr : c.room = true) :
    OsInv (finNew c).1 { o with pairs := (c.st.next, c.st.next + 1) :: o.pairs } (n + 1) := by
  have hst : (finNew c).1 = { c with st := (c.st.alloc2 .streamR .streamW).1 } := by
    simp [finNew, hr]
  rw [hst]
  have hsi := h.si.alloc2 .streamR .streamW (Or.inl fun _ => ⟨rfl, rfl⟩)
  have hroom := h.room
  have hnx : (c.st.alloc2 .streamR .streamW).1.next = c.st.next + 2 := rfl
  have hch : (c.st.alloc2 .streamR .streamW).1.chans = c.st.chans := rfl
  have hdead : ∀ s, Dead c.st s → Dead (c.st.alloc2 .streamR .streamW).1 s := fun s hd => by
    unfold Dead; rw [hch]; exact hd
  have hof : ∀ ch, ({ c with st := (c.st.alloc2 .streamR .streamW).1 } : Core).outOf ch = c.outOf ch :=
    fun _ => rfl
  have hold : ∀ x o', c.st.tbl x = some o' → x < c.st.next := fun x o' hx => (h.si.lt x o' hx).2
  refine ⟨hsi, by rw [hnx]; omega, h.pend, h.opend, fun w s hw => ?_, fun r w hr' => ?_,
    fun w hw => ?_, fun w s hw hw' => ?_, fun ch hch' => ?_, fun w hw => ?_⟩
  · simp only [alloc2_tbl] at hw
    rw [pairOf_cons]
    split at hw
    · cases hw; simp_all
    · split at hw
      · cases hw
      · have := hold w _ hw
        have hws := h.si.wEnd w s hw
        rw [ite_eq_right (by omega)]
        exact h.wEnd w s hw
  · rw [pairOf_cons] at hr'
    split at hr'
    · rename_i hx
      cases hr'
      subst hx
      refine ⟨rfl, h.si.pos, by rw [hnx]; omega, Or.inl ?_⟩
      simp [alloc2_tbl]
    · obtain ⟨h1, h2, h3, h4⟩ := h.pairs r w hr'
      refine ⟨h1, h2, by rw [hnx]; omega, ?_⟩
      rw [hof]
      rcases h4 with h4 | h4 | h4
      · refine Or.inl ?_
        rw [alloc2_tbl, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact h4
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr (hdead r h4))
  · obtain ⟨s, hws, hs⟩ := outW_eq hw
    rw [hof] at hs
    simp only [alloc2_tbl] at hws
    split at hws
    · cases hws; exact absurd (h.outs _ hs) (Nat.lt_irrefl _)
    · split at hws
      · cases hws
      · refine h.outW w ?_
        unfold P3OverP2.outW
        rw [hws]
        exact hs
  · have hlt := h.oOutW w hw
    simp only [alloc2_tbl, ite_eq_right (show w ≠ c.st.next + 1 by omega),
      ite_eq_right (show w ≠ c.st.next by omega)] at hw'
    rw [hof]
    rcases h.outW' w s hw hw' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hdead s h1)
  · rw [hof] at hch'
    have := h.outs ch hch'
    rw [hnx]; omega
  · have := h.oOutW w hw
    rw [hnx]; omega


/-- **Fresh handles that are not writable ends** keep the invariant. -/
theorem OsInv.extend {c c' : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hsi : SI c'.st)
    (hn1 : c.st.next ≤ c'.st.next) (hn2 : c'.st.next ≤ c.st.next + 4)
    (hch : c'.st.chans = c.st.chans) (hout : c'.outs = c.outs) (hp : c'.pend = [])
    (hold : ∀ x, x < c.st.next → c'.st.tbl x = c.st.tbl x)
    (hnew : ∀ x s, c.st.next ≤ x → c'.st.tbl x ≠ some (.streamW s)) : OsInv c' o (n + 1) := by
  have hroom := h.room
  have hdead : ∀ s, Dead c.st s → Dead c'.st s := fun s hd => by unfold Dead; rw [hch]; exact hd
  refine h.mono hsi (by omega) hn1 hout hp (fun w s hw => ?_) (fun r hr => ?_) hdead
  · by_cases hlt : w < c.st.next
    · rw [← hold w hlt]; exact hw
    · exact absurd hw (hnew w s (Nat.le_of_not_lt hlt))
  · exact Or.inl ((hold r (h.si.lt r _ hr).2).trans hr)

/-- **`finIn`** (a stream fed by the component) keeps the invariant. -/
theorem OsInv.finIn {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hr : c.room = true)
    (file : Bool) (d : Option (BitVec 32)) : OsInv (P3OverP2.finIn c file d).1 o (n + 1) := by
  obtain ⟨-, -, hnx, hout, -, -⟩ := finIn_room hr file d
  have hst : (P3OverP2.finIn c file d).1.st =
      (((c.st.alloc2 .streamR .streamW).1.alloc2 .futureR .futureW).1.remove (c.st.next + 1)) := by
    unfold P3OverP2.finIn
    simp only [hr, ↓reduceIte]
    cases d <;> rfl
  have hp : (P3OverP2.finIn c file d).1.pend = c.pend := by
    unfold P3OverP2.finIn
    simp only [hr, ↓reduceIte]
    cases d <;> rfl
  have hsi1 := h.si.alloc2 .streamR .streamW (Or.inl fun _ => ⟨rfl, rfl⟩)
  have hsi2 := hsi1.alloc2 .futureR .futureW (Or.inr fun _ => ⟨rfl, rfl⟩)
  refine h.extend (by rw [hst]; exact hsi2.remove _) (by omega) (by omega) (by rw [hst]; rfl) hout
    (by rw [hp]; exact h.pend) (fun x hx => ?_) (fun x s hx => ?_)
  · have h2 : (c.st.alloc2 .streamR .streamW).1.next = c.st.next + 2 := rfl
    rw [hst]
    simp only [remove_tbl, alloc2_tbl, h2]
    simp [show x ≠ c.st.next + 1 by omega, show x ≠ c.st.next by omega,
      show x ≠ c.st.next + 2 by omega, show x ≠ c.st.next + 2 + 1 by omega]
  · have h2 : (c.st.alloc2 .streamR .streamW).1.next = c.st.next + 2 := rfl
    rw [hst]
    simp only [remove_tbl, alloc2_tbl, h2]
    split_ifs <;> first | (intro hx'; have := (h.si.lt x _ hx').2; omega) | simp


/-- The stdout binding after a new binding. -/
theorem outOf_cons (c : Core) (st : Store) (r : Nat) (ob : OutB) (ch : Nat) :
    ({ c with st := st, outs := (r, ob) :: c.outs } : Core).outOf ch =
      if r = ch then some ob else c.outOf ch := by
  by_cases h : r = ch <;> simp [Core.outOf, h]

/-- **Binding the readable end `r` to stdout** keeps the invariant, with `r + 1` recorded. -/
theorem OsInv.bind {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {r : Nat}
    (hr : c.st.tbl r = some (.streamR r)) (hp : pairOf o r = some (r + 1)) (ob : OutB) :
    OsInv { c with st := c.st.remove r, outs := (r, ob) :: c.outs }
      { o with outW := (r + 1) :: o.outW } n := by
  have hrl := (h.si.lt r _ hr).2
  have hpr := h.pairs r (r + 1) hp
  have htb : ∀ x, x ≠ r → (c.st.remove r).tbl x = c.st.tbl x := fun x hx => by simp [hx]
  have hdead : ∀ s, Dead c.st s → Dead (c.st.remove r) s := fun s hd => hd
  have hw : ∀ w s, (c.st.remove r).tbl w = some (.streamW s) → c.st.tbl w = some (.streamW s) := by
    intro w s hw
    by_cases hwr : w = r
    · subst hwr; simp at hw
    · rwa [htb w hwr] at hw
  refine ⟨h.si.remove r, h.room, h.pend, h.opend, fun w s hw' => h.wEnd w s (hw w s hw'),
    fun r' w hr' => ?_, fun w hw' => ?_, fun w s hw1 hw2 => ?_, fun ch hc => ?_, fun w hw' => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.pairs r' w hr'
    refine ⟨h1, h2, h3, ?_⟩
    simp only [outOf_cons]
    by_cases hrr : r = r'
    · exact Or.inr (Or.inl (by simp [hrr]))
    · simp only [hrr, ↓reduceIte]
      rw [htb r' (Ne.symm hrr)]
      exact h4.imp id (Or.imp id (hdead r'))
  · obtain ⟨s, hws, hs⟩ := outW_eq hw'
    simp only [outOf_cons] at hs
    have hws' := hw w s hws
    by_cases hrs : r = s
    · subst hrs
      have := h.si.wEnd w r hws'
      subst this
      exact List.mem_cons_self
    · simp only [hrs, ↓reduceIte] at hs
      refine List.mem_cons_of_mem _ (h.outW w ?_)
      unfold P3OverP2.outW
      rw [hws']
      exact hs
  · simp only [outOf_cons]
    have hws' := hw w s hw2
    have hws := h.si.wEnd w s hws'
    rcases List.mem_cons.1 hw1 with hw1 | hw1
    · subst hw1
      have : s = r := by omega
      subst this
      exact Or.inl (by simp)
    · by_cases hrs : r = s
      · exact Or.inl (by simp [hrs])
      · simp only [hrs, ↓reduceIte]
        exact (h.outW' w s hw1 hws').imp id (hdead s)
  · simp only [outOf_cons] at hc
    split at hc
    · rename_i hrc; subst hrc; exact hrl
    · exact h.outs ch hc
  · rcases List.mem_cons.1 hw' with hw' | hw'
    · subst hw'; exact hpr.2.2.1
    · exact h.oOutW w hw'

/-- **Recording a stdout writable end whose readable end is bound or dead** keeps the invariant. -/
theorem OsInv.addOut {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {r w : Nat}
    (hp : pairOf o r = some w) (hr : c.st.tbl r = some (.streamR r) → c.outOf r ≠ none) :
    OsInv c { o with outW := w :: o.outW } n := by
  obtain ⟨h1, h2, h3, h4⟩ := h.pairs r w hp
  refine ⟨h.si, h.room, h.pend, h.opend, h.wEnd, h.pairs, fun w' hw' => List.mem_cons_of_mem _ (h.outW w' hw'),
    fun w' s hw1 hw2 => ?_, h.outs, fun w' hw' => ?_⟩
  · rcases List.mem_cons.1 hw1 with hw1 | hw1
    · subst hw1
      have hws := h.si.wEnd _ s hw2
      have : s = r := by omega
      subst this
      rcases h4 with h4 | h4 | h4
      · exact Or.inl (hr h4)
      · exact Or.inl h4
      · exact Or.inr h4
    · exact h.outW' w' s hw1 hw2
  · rcases List.mem_cons.1 hw' with hw' | hw'
    · subst hw'; omega
    · exact h.oOutW w' hw'


/-- **Binding a readable end without a recorded pair** keeps the invariant. -/
theorem OsInv.bind0 {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {r : Nat}
    (hr : c.st.tbl r = some (.streamR r)) (hp : pairOf o r = none) (ob : OutB) :
    OsInv { c with st := c.st.remove r, outs := (r, ob) :: c.outs } o n := by
  have hrl := (h.si.lt r _ hr).2
  have htb : ∀ x, x ≠ r → (c.st.remove r).tbl x = c.st.tbl x := fun x hx => by simp [hx]
  have hdead : ∀ s, Dead c.st s → Dead (c.st.remove r) s := fun s hd => hd
  have hw : ∀ w s, (c.st.remove r).tbl w = some (.streamW s) → c.st.tbl w = some (.streamW s) := by
    intro w s hw
    by_cases hwr : w = r
    · subst hwr; simp at hw
    · rwa [htb w hwr] at hw
  have hnr : ∀ w, c.st.tbl w ≠ some (.streamW r) := fun w hw' => by
    rw [h.wEnd w r hw'] at hp; cases hp
  refine ⟨h.si.remove r, h.room, h.pend, h.opend, fun w s hw' => h.wEnd w s (hw w s hw'),
    fun r' w hr' => ?_, fun w hw' => ?_, fun w s hw1 hw2 => ?_, fun ch hc => ?_, h.oOutW⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.pairs r' w hr'
    refine ⟨h1, h2, h3, ?_⟩
    simp only [outOf_cons]
    by_cases hrr : r = r'
    · exact Or.inr (Or.inl (by simp [hrr]))
    · simp only [hrr, ↓reduceIte]
      rw [htb r' (Ne.symm hrr)]
      exact h4.imp id (Or.imp id (hdead r'))
  · obtain ⟨s, hws, hs⟩ := outW_eq hw'
    simp only [outOf_cons] at hs
    have hws' := hw w s hws
    by_cases hrs : r = s
    · subst hrs; exact absurd hws' (hnr w)
    · simp only [hrs, ↓reduceIte] at hs
      refine h.outW w ?_
      unfold P3OverP2.outW
      rw [hws']
      exact hs
  · simp only [outOf_cons]
    have hws' := hw w s hw2
    by_cases hrs : r = s
    · subst hrs; exact absurd hws' (hnr w)
    · simp only [hrs, ↓reduceIte]
      exact (h.outW' w s hw1 hws').imp id (hdead s)
  · simp only [outOf_cons] at hc
    split at hc
    · rename_i hrc; subst hrc; exact hrl
    · exact h.outs ch hc

/-- `wvsSrc` gives a live readable end. -/
theorem wvsSrc_spec {c : Core} {a : List Val} {r : Nat} (h : wvsSrc c a = some r) :
    arg1 a = some r ∧ r ≠ 0 ∧ c.st.tbl r = some (.streamR r) := by
  unfold wvsSrc at h
  split at h
  · rename_i r' hr'
    split at h
    · rename_i hc
      cases h
      exact ⟨hr', hc.1, hc.2⟩
    · cases h
  · cases h

/-- A readable end recorded by the image and live is a source of `write-via-stream`. -/
theorem wvsSrc_of {c : Core} {a : List Val} {r : Nat} (ha : arg1 a = some r) (h0 : r ≠ 0)
    (hr : c.st.tbl r = some (.streamR r)) : wvsSrc c a = some r := by
  unfold wvsSrc
  rw [ha]
  simp [h0, hr]

/-- The core after the future of `write-via-stream` is allocated. -/
def wvsCore (c : Core) : Core := { c with st := (c.st.alloc2 .futureR .futureW).1 }

/-- Old handles after the future is allocated. -/
theorem wvsCore_tbl (c : Core) (x : Nat) (hx : x < c.st.next) : (wvsCore c).st.tbl x = c.st.tbl x := by
  simp only [wvsCore, alloc2_tbl]
  simp [show x ≠ c.st.next + 1 by omega, show x ≠ c.st.next by omega]

/-- Allocating the future keeps the invariant. -/
theorem OsInv.alloc_fut {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) :
    OsInv (wvsCore c) o (n + 1) := by
  refine h.extend (h.si.alloc2 .futureR .futureW (Or.inr fun _ => ⟨rfl, rfl⟩))
    (by simp [wvsCore, Store.alloc2]) (by simp [wvsCore, Store.alloc2]) rfl rfl h.pend
    (wvsCore_tbl c) (fun x s hx => ?_)
  simp only [wvsCore, alloc2_tbl]
  split_ifs <;> first | (intro hx'; have := (h.si.lt x _ hx').2; omega) | simp

/-- `write-via-stream` of a live guest stream `r`: it is bound. -/
theorem OsInv.wvs_bound (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n)
    (hroom : c.room = true) {a : List Val} {r : Nat} (hsrc : wvsSrc c a = some r) (os : BitVec 32)
    (ans : Option (List Val)) :
    OsInv (finWvs c a (some os)).1 (osStep3 ch o (.imp stdoutWrite3 a ans)).1 (n + 1) := by
  obtain ⟨ha, -, hr⟩ := wvsSrc_spec hsrc
  have hfin : (finWvs c a (some os)).1 =
      { wvsCore c with st := (wvsCore c).st.remove r, outs := (r, ⟨os, c.st.next⟩) :: c.outs } := by
    simp [finWvs, hroom, hsrc, wvsCore, Store.alloc2]
  have hr1 : (wvsCore c).st.tbl r = some (.streamR r) := by
    rw [wvsCore_tbl c r (h.si.lt r _ hr).2]; exact hr
  rw [hfin, osStep3_wvs, ha, Option.bind_eq_bind, Option.bind_some]
  cases hp : pairOf o r with
  | none => exact h.alloc_fut.bind0 hr1 hp _
  | some w =>
    obtain ⟨hw, -⟩ := h.pairs r w hp
    subst hw
    exact h.alloc_fut.bind hr1 hp _

/-- `write-via-stream` of anything else: the stream recorded by the image, if any, is bound or
dead already. -/
theorem OsInv.wvs_unbound (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n)
    (hroom : c.room = true) {a : List Val} (hsrc : wvsSrc c a = none) (d : Option (BitVec 32))
    (ans : Option (List Val)) :
    OsInv (finWvs c a d).1 (osStep3 ch o (.imp stdoutWrite3 a ans)).1 (n + 1) := by
  have hfin : (finWvs c a d).1 = { wvsCore c with errF := c.st.next :: c.errF } := by
    simp only [finWvs, hroom, ↓reduceIte, hsrc]
    rfl
  have h1 := h.alloc_fut
  have h2 : OsInv { wvsCore c with errF := c.st.next :: c.errF } o (n + 1) :=
    ⟨h1.si, h1.room, h1.pend, h1.opend, h1.wEnd, h1.pairs, h1.outW, h1.outW', h1.outs, h1.oOutW⟩
  rw [hfin, osStep3_wvs]
  cases ha : arg1 a >>= pairOf o with
  | none => exact h2
  | some w =>
    obtain ⟨r', ha', hp⟩ := Option.bind_eq_some_iff.1 ha
    refine h2.addOut hp fun hr' => ?_
    have hpr := h.pairs r' w hp
    rw [wvsCore_tbl c r' (by omega)] at hr'
    rw [wvsSrc_of ha' (by omega) hr'] at hsrc
    cases hsrc

/-- **`write-via-stream`** keeps the invariant (the image records the writable end). -/
theorem OsInv.wvs (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hroom : c.room = true)
    (a : List Val) (d : Option (BitVec 32)) (hd : wvsSrc c a ≠ none → d ≠ none)
    (ans : Option (List Val)) :
    OsInv (finWvs c a d).1 (osStep3 ch o (.imp stdoutWrite3 a ans)).1 (n + 1) := by
  cases hsrc : wvsSrc c a with
  | some r =>
    obtain ⟨os, rfl⟩ := Option.ne_none_iff_exists'.1 (hd (by simp [hsrc]))
    exact h.wvs_bound ch hroom hsrc os ans
  | none => exact h.wvs_unbound ch hroom hsrc d ans


/-! ## `stream.write` -/

/-- The bytes `stream.write`'s 0.2 program put in the 0.2 image, by its result. -/
def imgSw (ch : Word) (c : Core) (a : List Val) (d : Option Nat) : List Event :=
  match swArgs a with
  | some (w, xs) =>
    match P3OverP2.outW c w with
    | some _ => if xs = [] then [] else imgW ch xs d
    | none => []
  | none => []

/-- The length of the bytes of `stream.write` (at most `cap`). -/
def swLen (a : List Val) : Nat := (swArgs a).elim 0 fun x => x.2.length

/-- **`stream.write`'s 0.2 program.** -/
theorem wp_ioSw (ch : Word) (c : Core) (a : List Val) (qT : List Event) :
    Wp (osImg2 ch) (emb (ioSw c a))
      (fun d q => q = qT ++ imgSw ch c a d ∧ ∀ m, d = some m → m ≤ swLen a) qT := by
  unfold ioSw
  rcases hsw : swArgs a with _ | ⟨w, xs⟩
  · exact ⟨by simp [imgSw, hsw], fun m hm => by cases hm⟩
  · dsimp only
    rcases hob : P3OverP2.outW c w with _ | ob
    · exact ⟨by simp [imgSw, hsw, hob], fun m hm => by cases hm⟩
    · dsimp only
      by_cases hx : xs = []
      · simp only [hx, ↓reduceIte]
        exact ⟨by simp [imgSw, hsw, hob, hx], fun m hm => by cases hm⟩
      · simp only [hx, ↓reduceIte]
        exact Wp.mono (fun d q hq => ⟨by simp [imgSw, hsw, hob, hx, hq.1],
          fun m hm => by simpa [swLen, hsw] using hq.2 m hm⟩) (wp_writeOut ch ob.os xs qT)

/-- A write to a dead channel reports `DROPPED 0`. -/
theorem sw_dead {st st' : Store} {w s : Nat} {ys : List Val} {res : Res} (hd : Dead st s)
    (hw : st.tbl w = some (.streamW s))
    (hs : Silmaril.Wasm.Component.Async.step st (.streamWrite w ys) = some (st', res)) :
    res = .nat (packCopy .dropped 0) := by
  simp only [Silmaril.Wasm.Component.Async.step, Silmaril.Wasm.Component.Async.streamWrite, hw] at hs
  split at hs
  · cases hs
  · rename_i hr k hp
    exact absurd hp (hd.2 hr k)
  · rw [hd.1] at hs
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
    exact hs.2.symm

/-- `swArgs` of a well-formed `stream.write`. -/
theorem swArgs_spec {a : List Val} {w : Nat} {xs : List (BitVec 8)} (h : swArgs a = some (w, xs)) :
    ∃ wv buf, a = [wv, buf] ∧ natOf wv = some w ∧ xs = (bytesOf buf).take cap := by
  unfold swArgs at h
  split at h
  · rename_i wv buf
    cases hw : natOf wv with
    | none => simp [hw] at h
    | some w' =>
      simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wv, buf, rfl, hw, rfl⟩
  · cases h

/-- A non-`BLOCKED` code of `wcode` is admissible. -/
theorem wcode_eq {len n : Nat} (h : wcode len n ≠ blocked) : wcode len n = n ∧ n < 2 ^ 32 := by
  unfold wcode at h ⊢
  by_cases hc : codeOk len n = true
  · have hc' := hc
    simp only [codeOk, Bool.and_eq_true, decide_eq_true_eq] at hc'
    exact ⟨by simp [hc], hc'.1⟩
  · simp only [hc] at h
    exact absurd rfl h

/-- `blockedW` of a `stream.write` answer. -/
theorem blockedW_sw (a : List Val) (x : Nat) (hx : x < 2 ^ 32) :
    blockedW (.imp cStreamWrite a (some [natV x])) = decide (x = blocked) := by
  simp [blockedW, natOf_natV hx]


/-- `wcode` is a `u32`. -/
theorem wcode_lt (len n : Nat) : wcode len n < 2 ^ 32 := by
  unfold wcode
  by_cases hc : codeOk len n = true
  · simp only [hc, ↓reduceIte]
    simp only [codeOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    decide

/-- `stream.write` to a guest stream: the store steps, and the image records no bytes. -/
theorem os_sw_guest (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {wv buf : Val}
    {w : Nat} (hwv : natOf wv = some w) (hob : P3OverP2.outW c w = none) (ys : List Val)
    {st' : Store} {code : Nat}
    (hs : Silmaril.Wasm.Component.Async.step c.st (.streamWrite w ys) = some (st', .nat code))
    (hc : code < 2 ^ 32) (hnb : code ≠ blocked) :
    OsInv { c with st := st' } o (n + 1) ∧
      osStep3 ch o (.imp cStreamWrite [wv, buf] (some [natV code])) = (o, []) := by
  have ha := AOk.step h.si (op := .streamWrite w ys) trivial hs
  refine ⟨h.astep ha _ rfl rfl h.pend, ?_⟩
  by_cases hcomp : ∃ k, copyOf code = some (some (.completed, k))
  · obtain ⟨k, hk⟩ := hcomp
    rw [osStep3_sw_completed ch o hwv hc hk]
    have hnw : w ∉ o.outW := by
      intro hw
      have hsw := hs
      simp only [Silmaril.Wasm.Component.Async.step, Silmaril.Wasm.Component.Async.streamWrite] at hsw
      split at hsw
      · rename_i s hws
        rcases h.outW' w s hw hws with h1 | h1
        · unfold P3OverP2.outW at hob
          rw [hws] at hob
          exact h1 hob
        · have hr := sw_dead h1 hws hs
          cases hr
          rw [show copyOf (packCopy .dropped 0) = some (some (.dropped, 0)) by decide] at hk
          cases hk
      · cases hsw
    simp [hnw]
  · refine osStep3_sw_other ch o _ hc (fun k hk => hcomp ⟨k, hk⟩) (fun hb => hnb ?_)
    unfold copyOf at hb
    split at hb
    · assumption
    · split at hb <;> (try split at hb) <;> (try split at hb) <;> cases hb


/-- `finSw` on a guest stream. -/
theorem finSw_guest {c : Core} {wv buf : Val} {w : Nat} {xs : List (BitVec 8)}
    (hsw : swArgs [wv, buf] = some (w, xs)) (hob : P3OverP2.outW c w = none) (d : Option Nat) :
    finSw c [wv, buf] d =
      match Silmaril.Wasm.Component.Async.step c.st (.streamWrite w (xs.map .u8)) with
      | some (st', .nat code) => ({ c with st := st' }, code)
      | _ => (c, blocked) := by
  simp only [finSw, hsw, hob]
  rfl

/-- `finSw` on a stdout stream with a non-empty buffer, by the result of the 0.2 program. -/
def swOut (c : Core) (w : Nat) (ob : OutB) (xs : List (BitVec 8)) : Option Nat → Core × Nat
  | none => (c, packCopy .dropped 0)
  | some k =>
    if min k xs.length = 0 then ({ c with pend := (w, ob.os, xs) :: c.pend }, blocked)
    else (c, packCopy .completed (min k xs.length))

/-- `finSw` on a stdout stream. -/
theorem finSw_out {c : Core} {wv buf : Val} {w : Nat} {xs : List (BitVec 8)} {ob : OutB}
    (hsw : swArgs [wv, buf] = some (w, xs)) (hob : P3OverP2.outW c w = some ob) (d : Option Nat) :
    finSw c [wv, buf] d = if xs = [] then (c, packCopy .completed 0) else swOut c w ob xs d := by
  simp only [finSw, hsw, hob]
  cases d <;> rfl

/-- The answer of `stream.write`, by `finSw`. -/
abbrev SwOk (ch : Word) (c : Core) (o : OsSt) (n : Nat) (a : List Val) (d : Option Nat) : Prop :=
  OsInv (finSw c a d).1 o (n + 1) ∧
    osStep3 ch o (.imp cStreamWrite a (some [natV (finSw c a d).2])) = (o, imgSw ch c a d)

/-- `stream.write` to a guest stream. -/
theorem os_sw_guest' (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {wv buf : Val}
    {w : Nat} {xs : List (BitVec 8)} (hsw : swArgs [wv, buf] = some (w, xs))
    (hwv : natOf wv = some w) (hob : P3OverP2.outW c w = none) (d : Option Nat)
    (hnb : (finSw c [wv, buf] d).2 ≠ blocked) (hclt : (finSw c [wv, buf] d).2 < 2 ^ 32) :
    SwOk ch c o n [wv, buf] d := by
  have himg : imgSw ch c [wv, buf] d = [] := by simp [imgSw, hsw, hob]
  rw [SwOk, himg]
  rw [finSw_guest hsw hob d] at hnb hclt ⊢
  rcases hs : Silmaril.Wasm.Component.Async.step c.st (.streamWrite w (xs.map .u8)) with _ | ⟨st', r⟩
  · simp [hs] at hnb
  · cases r with
    | nat code =>
      simp only [hs] at hnb hclt ⊢
      exact os_sw_guest ch h hwv hob _ hs hclt hnb
    | _ => simp [hs] at hnb

/-- `stream.write` of `k > 0` bytes to stdout. -/
theorem os_sw_completed (ch : Word) {o : OsSt} {wv buf : Val} {w : Nat} {xs : List (BitVec 8)}
    (hwv : natOf wv = some w) (hxs : xs = (bytesOf buf).take cap) (hw : w ∈ o.outW)
    {k : Nat} (hk : k ≤ xs.length) (hclt : packCopy .completed k < 2 ^ 32) :
    osStep3 ch o (.imp cStreamWrite [wv, buf] (some [natV (packCopy .completed k)])) =
      (o, imgW ch xs (some k)) := by
  have hcap : k ≤ cap := by
    have hl : xs.length ≤ cap := hxs ▸ List.length_take_le cap (bytesOf buf)
    omega
  rw [osStep3_sw_completed ch o hwv hclt (copyOf_completed hcap)]
  simp only [hw, ↓reduceIte, imgW, hxs, List.take_take, Nat.min_eq_left hcap]

/-- `stream.write` to a stdout stream, by the result of the 0.2 program. -/
theorem os_sw_out_ne (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {wv buf : Val}
    {w : Nat} {xs : List (BitVec 8)} (hwv : natOf wv = some w) (hxs : xs = (bytesOf buf).take cap)
    (hw : w ∈ o.outW) (ob : OutB) (d : Option Nat)
    (hd : ∀ m, d = some m → m ≤ xs.length) (hnb : (swOut c w ob xs d).2 ≠ blocked)
    (hclt : (swOut c w ob xs d).2 < 2 ^ 32) :
    OsInv (swOut c w ob xs d).1 o (n + 1) ∧
      osStep3 ch o (.imp cStreamWrite [wv, buf] (some [natV (swOut c w ob xs d).2])) =
        (o, imgW ch xs d) := by
  rcases d with _ | k
  · have hs0 : swOut c w ob xs none = (c, packCopy .dropped 0) := rfl
    rw [hs0] at hclt ⊢
    refine ⟨h.succ, ?_⟩
    rw [osStep3_sw_other ch o _ hclt (fun k hk => by rw [copyOf_dropped] at hk; cases hk)
      (by rw [copyOf_dropped]; simp)]
    rfl
  · have hmin : min k xs.length = k := Nat.min_eq_left (hd k rfl)
    have hk0 : k ≠ 0 := fun hk0 => hnb (by simp [swOut, hk0])
    have hsk : swOut c w ob xs (some k) = (c, packCopy .completed k) := by simp [swOut, hmin, hk0]
    rw [hsk] at hclt ⊢
    exact ⟨h.succ, os_sw_completed ch hwv hxs hw (hd k rfl) hclt⟩

/-- `stream.write` to a stdout stream. -/
theorem os_sw_out (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) {wv buf : Val}
    {w : Nat} {xs : List (BitVec 8)} {ob : OutB} (hsw : swArgs [wv, buf] = some (w, xs))
    (hwv : natOf wv = some w) (hxs : xs = (bytesOf buf).take cap) (hob : P3OverP2.outW c w = some ob)
    (d : Option Nat) (hd : ∀ m, d = some m → m ≤ xs.length)
    (hnb : (finSw c [wv, buf] d).2 ≠ blocked) (hclt : (finSw c [wv, buf] d).2 < 2 ^ 32) :
    SwOk ch c o n [wv, buf] d := by
  have hw : w ∈ o.outW := h.outW w (by simp [hob])
  have himg : imgSw ch c [wv, buf] d = if xs = [] then [] else imgW ch xs d := by simp [imgSw, hsw, hob]
  rw [SwOk, himg]
  rw [finSw_out hsw hob d] at hnb hclt ⊢
  by_cases hx : xs = []
  · simp only [hx, ↓reduceIte] at hnb hclt ⊢
    refine ⟨h.succ, ?_⟩
    rw [osStep3_sw_completed ch o hwv hclt (copyOf_completed (Nat.zero_le _))]
    simp
  · simp only [hx, ↓reduceIte] at hnb hclt ⊢
    exact os_sw_out_ne ch h hwv hxs hw ob d hd hnb hclt

/-- **`stream.write`**: the invariant is kept and the 0.3 image records the bytes of the 0.2
`write`. -/
theorem os_sw (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (a : List Val)
    (d : Option Nat) (hd : ∀ m, d = some m → m ≤ swLen a)
    (hnb : blockedW (.imp cStreamWrite a (some [natV (wcode (swLen a) (finSw c a d).2)])) = false) :
    OsInv (finSw c a d).1 o (n + 1) ∧
      osStep3 ch o (.imp cStreamWrite a (some [natV (wcode (swLen a) (finSw c a d).2)])) =
        (o, imgSw ch c a d) := by
  have hlt := wcode_lt (swLen a) (finSw c a d).2
  rw [blockedW_sw _ _ hlt, decide_eq_false_iff_not] at hnb
  obtain ⟨hweq, hclt⟩ := wcode_eq hnb
  rw [hweq] at hnb ⊢
  rcases hsw : swArgs a with _ | ⟨w, xs⟩
  · exact absurd (by simp [finSw, hsw]) hnb
  obtain ⟨wv, buf, rfl, hwv, hxs⟩ := swArgs_spec hsw
  rcases hob : P3OverP2.outW c w with _ | ob
  · exact os_sw_guest' ch h hsw hwv hob d hnb hclt
  · exact os_sw_out ch h hsw hwv hxs hob d (fun m hm => by simpa [swLen, hsw] using hd m hm) hnb hclt


/-! ## Functions that only step the store -/

/-- A change of the core by at most one step of the store, keeping the stdout bindings. -/
def OFrame (c c' : Core) : Prop :=
  AOk c.st c'.st ∧ c'.outs = c.outs ∧ (c.pend = [] → c'.pend = [])

theorem OsInv.oframe {c c' : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hf : OFrame c c') :
    OsInv c' o (n + 1) :=
  h.astep hf.1 c' rfl hf.2.1 (hf.2.2 h.pend)

theorem OFrame.refl {c : Core} (h : SI c.st) : OFrame c c := ⟨AOk.refl h, rfl, id⟩

theorem OFrame.astep {c : Core} (h : SI c.st) {op : Silmaril.Wasm.Component.Async.Op}
    {st' : Store} {r : Res} (hs : Silmaril.Wasm.Component.Async.step c.st op = some (st', r))
    (hop : UsedOp op) : OFrame c { c with st := st' } :=
  ⟨AOk.step h hop hs, rfl, id⟩

theorem finSr_oframe {c : Core} (h : SI c.st) (a : List Val) (d : Option (List Val)) :
    OFrame c (finSr c a d).1 := by
  unfold finSr
  repeat' split
  all_goals first
    | exact OFrame.refl h
    | exact OFrame.astep h ‹_› (by trivial)

theorem finDropR_oframe {c : Core} (h : SI c.st) (a : List Val) : OFrame c (finDropR c a) := by
  unfold finDropR
  split
  · dsimp only
    split <;> split
    all_goals first
      | exact OFrame.refl h
      | exact OFrame.astep h ‹_› (by trivial)
  · exact OFrame.refl h

theorem finFDropR_oframe {c : Core} (h : SI c.st) (a : List Val) : OFrame c (finFDropR c a) := by
  unfold finFDropR
  repeat' split
  all_goals first | exact OFrame.refl h | exact OFrame.astep h ‹_› (by trivial)

theorem finJoin_oframe {c : Core} (h : SI c.st) (a : List Val) : OFrame c (finJoin c a) := by
  unfold finJoin
  repeat' split
  all_goals first | exact OFrame.refl h | exact OFrame.astep h ‹_› (by trivial)

theorem finWsNew_oframe {c : Core} (h : SI c.st) : OFrame c (finWsNew c).1 := by
  unfold finWsNew
  repeat' split
  all_goals first | exact OFrame.refl h | exact OFrame.astep h ‹_› (by trivial)

theorem finWait_oframe {c : Core} (h : SI c.st) (a : List Val) (d : Option (Option Nat)) :
    OFrame c (finWait c a d).1 := by
  unfold finWait
  repeat' split
  all_goals first
    | exact OFrame.refl h
    | exact OFrame.astep h ‹_› (by trivial)
    | exact ⟨AOk.refl h, rfl, fun hp => by simp [hp]⟩

theorem finDropW_oframe {c : Core} (h : SI c.st) (a : List Val) : OFrame c (finDropW c a) := by
  unfold finDropW
  split
  · dsimp only
    split
    · rename_i hs
      exact ⟨AOk.step h (by trivial) hs, rfl, fun hp => by simp [hp]⟩
    · exact ⟨AOk.refl h, rfl, fun hp => by simp [hp]⟩
  · exact OFrame.refl h


/-! ## The programs without writes -/

theorem noW_ioDropW {c : Core} (hp : c.pend = []) (a : List Val) : NoW (ioDropW c a) := by
  unfold ioDropW
  split
  · rename_i w _
    have : c.pendOf w = none := by simp [Core.pendOf, hp]
    rw [this]
    trivial
  · trivial

theorem noW_ioFr (c : Core) (a : List Val) : NoW (ioFr c a) := by
  unfold ioFr
  repeat' split
  all_goals first | trivial | exact ⟨notW_bflush, fun _ => trivial⟩

theorem noW_ioWait {c : Core} (hp : c.pend = []) (a : List Val) : NoW (ioWait c a) := by
  unfold ioWait
  split
  · rename_i s _
    split
    · trivial
    · have : firstPend c s = none := by simp [firstPend, hp]
      rw [this]
      trivial
  · trivial

theorem noW_ioStdin (c : Core) : NoW (ioStdin c) := by
  unfold ioStdin
  split
  · refine ⟨notW_getStdin, fun n => ?_⟩
    dsimp only
    split <;> trivial
  · trivial

theorem noW_ioNow : NoW ioNow := by
  refine ⟨notW_now, fun n => ?_⟩
  dsimp only
  split <;> trivial

theorem noW_ioWaitFor (a : List Val) : NoW (ioWaitFor a) := by
  unfold ioWaitFor
  split
  · refine ⟨notW_subDur, fun n => ?_⟩
    dsimp only
    split
    · exact noW_pollOn _
    · trivial
  · trivial

theorem noW_ioSr (c : Core) (a : List Val) : NoW (ioSr c a) := by
  unfold ioSr
  repeat' split
  all_goals first | trivial | exact ⟨notW_bread, fun _ => trivial⟩

theorem noW_ioRv (c : Core) (a : List Val) : NoW (ioRv c a) := by
  unfold ioRv
  repeat' split
  all_goals first | trivial | exact ⟨notW_rvs, fun _ => trivial⟩

/-- Room for the next call, from the bound on the answers. -/
theorem OsInv.room_of {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (hn : n + 1 < osBound) :
    c.room = true := by
  have := h.room
  simp only [Core.room, decide_eq_true_eq]
  simp only [osBound] at hn
  omega

/-! ## Each call -/

/-- The postcondition of a call for the OS image. -/
def OsPost (ch : Word) (o : OsSt) (n : Nat) (qT : List Event) (f : FnName) (args : List Val)
    (a : St × Option (List Val)) (qT' : List Event) : Prop :=
  blockedW (.imp f args a.2) = false → n + 1 < osBound →
    OsInv a.1.core (osStep3 ch o (.imp f args a.2)).1 (n + 1) ∧
      qT' = qT ++ (osStep3 ch o (.imp f args a.2)).2

/-- A call the image ignores that keeps the invariant. -/
theorem osPost_same (ch : Word) {o : OsSt} {n : Nat} {qT : List Event} {f : FnName}
    (hf : (f != cStreamNew && f != stdoutWrite3 && f != cStreamWrite && f != cWait) = true)
    (args : List Val) (k : ClockSt) {c' : Core} (ans : Option (List Val))
    (hinv : n + 1 < osBound → OsInv c' o (n + 1)) :
    OsPost ch o n qT f args (⟨k, c'⟩, ans) qT := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
  intro _ hn
  rw [osStep3_other ch o hf.1.1.1 hf.1.1.2 hf.1.2 hf.2]
  exact ⟨hinv hn, by simp⟩


/-- `write-via-stream` records no bytes. -/
theorem osStep3_wvs_img (ch : Word) (o : OsSt) (a : List Val) (r : Option (List Val)) :
    (osStep3 ch o (.imp stdoutWrite3 a r)).2 = [] := by
  rw [osStep3_wvs]
  split <;> rfl

/-- `stream.new`. -/
theorem os_new (ch : Word) {c : Core} {o : OsSt} {n : Nat} (h : OsInv c o n) (k : ClockSt)
    (a : List Val) (qT : List Event) :
    OsPost ch o n qT cStreamNew a (done k ((finNew c).1, some [natV (finNew c).2.1,
      natV (finNew c).2.2])) qT := by
  intro _ hn
  have hroom : c.room = true := h.room_of hn
  have hl : c.st.next + 4 < 2 ^ 32 := room_lt hroom
  have h2 : (finNew c).2 = (c.st.next, c.st.next + 1) := (finNew_room hroom).1
  simp only [done, h2]
  rw [osStep3_new ch o a (by omega) (by omega)]
  exact ⟨h.new hroom, by simp⟩

/-- `stream.write`. -/
theorem os_write (ch : Word) {s : St} {o : OsSt} {n : Nat} (h : OsInv s.core o n) (a : List Val)
    (qT : List Event) :
    Wp (osImg2 ch) (emb (ioSw s.core a)) (fun d q => OsPost ch o n qT cStreamWrite a
      (done s.clk ((finSw s.core a d).1,
        some [natV (wcode ((swArgs a).elim 0 fun x => x.2.length) (finSw s.core a d).2)])) q) qT := by
  refine Wp.mono ?_ (wp_ioSw ch s.core a qT)
  intro d q hq hnb _
  obtain ⟨hinv, hos⟩ := os_sw ch h a d hq.2 hnb
  simp only [done, swLen] at hos ⊢
  rw [hos]
  exact ⟨hinv, hq.1⟩

/-- `waitable-set.wait`. -/
theorem os_wait (ch : Word) {s : St} {o : OsSt} {n : Nat} (h : OsInv s.core o n) (a : List Val)
    (d : Option (Option Nat)) (qT : List Event) :
    OsPost ch o n qT cWait a (done s.clk (let r := finWait s.core a d
      (r.1, some [natV r.2.1, natV r.2.2.1, natV r.2.2.2]))) qT := by
  intro _ _
  rw [osStep3_wait ch h.opend]
  exact ⟨h.oframe (finWait_oframe h.si a d), by simp⟩

/-- `write-via-stream`. -/
theorem os_wvs (ch : Word) {s : St} {o : OsSt} {n : Nat} (h : OsInv s.core o n) (a : List Val)
    (qT : List Event) :
    Wp (osImg2 ch) (emb (ioWvs s.core a)) (fun d q => OsPost ch o n qT stdoutWrite3 a
      (done s.clk (let r := finWvs s.core a d; (r.1, some [natV r.2]))) q) qT := by
  refine Wp.mono ?_ (wp_ioWvs ch s.core a qT)
  intro d q hq _ hn
  refine ⟨h.wvs ch (h.room_of hn) a d (fun hs => hq.2 hs (h.room_of hn)) _, ?_⟩
  rw [osStep3_wvs_img, hq.1]
  simp

/-- `read-via-stream`. -/
theorem os_readVia (ch : Word) {s : St} {o : OsSt} {n : Nat} (h : OsInv s.core o n) (a : List Val)
    (d : Option (List Val)) (qT : List Event) :
    OsPost ch o n qT readVia3 a (done s.clk (let r := finRv s.core a d
      (r.1, some [.record [natV r.2.1, natV r.2.2]]))) qT := by
  refine osPost_same ch (by decide) a _ _ fun hn => ?_
  simp only [finRv]
  split
  · exact h.finIn (h.room_of hn) true _
  · exact h.succ

set_option linter.unusedTactic false in
/-- **Every call keeps the OS invariant and adds the same bytes to both images**, by class. -/
theorem wp_os' (ch : Word) (s : St) (f : FnName) (hf : f ∈ p3World.imports) (a : List Val)
    (o : OsSt) (n : Nat) (qT : List Event) (h : OsInv s.core o n) :
    Wp (osImg2 ch) (body s (⟨f, hf⟩, a)) (OsPost ch o n qT f a) qT := by
  have hsi : SI s.core.st := h.si
  obtain ⟨cl, hc, hne, rfl⟩ := cls_cases hf
  cases cl <;> simp only [body, hc, thenFin] <;> try simp only [Fn3.name]
  case other => exact absurd rfl hne
  case streamNew => exact os_new ch h s.clk a qT
  case dropR => exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finDropR_oframe hsi a)
  case futDropR => exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finFDropR_oframe hsi a)
  case wsNew => exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finWsNew_oframe hsi)
  case join => exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finJoin_oframe hsi a)
  all_goals rw [Wp.bind]
  case streamWrite => exact os_write ch h a qT
  case wvs => exact os_wvs ch h a qT
  case streamRead =>
    refine wp_noW ch (fun d => ?_) _ (noW_ioSr _ _)
    exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finSr_oframe hsi a d)
  case dropW =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ (noW_ioDropW h.pend a))
    exact osPost_same ch (by decide) a _ _ fun _ => h.oframe (finDropW_oframe hsi a)
  case futRead =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ (noW_ioFr _ a))
    exact osPost_same ch (by decide) a _ _ fun _ => h.succ
  case wait =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ (noW_ioWait h.pend a))
    exact os_wait ch h a d qT
  case stdin =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ (noW_ioStdin _))
    exact osPost_same ch (by decide) a _ _ fun hn => h.finIn (h.room_of hn) false d
  case now =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ noW_ioNow)
    exact osPost_same ch (by decide) a _ _ fun _ => h.succ
  case waitFor =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ (noW_ioWaitFor a))
    exact osPost_same ch (by decide) a _ _ fun _ => h.succ
  case getDirs =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ ⟨notW_getDirs, fun _ => trivial⟩)
    exact osPost_same ch (by decide) a _ _ fun _ => h.succ
  case openAt =>
    refine wp_noW ch (fun d => ?_) _ (noW_emb _ ⟨notW_openAt, fun _ => trivial⟩)
    exact osPost_same ch (by decide) a _ _ fun _ => h.succ
  case readVia =>
    refine wp_noW ch (fun d => ?_) _ (noW_ioRv _ _)
    exact os_readVia ch h a d qT

/-- **Every call keeps the OS invariant and adds the same bytes to both images.** -/
theorem wp_os (ch : Word) (s : St) (q : (nsig p3World.imports).Op) (o : OsSt) (n : Nat)
    (qT : List Event) (h : OsInv s.core o n) :
    Wp (osImg2 ch) (body s q) (OsPost ch o n qT q.1.1 q.2) qT :=
  wp_os' ch s q.1.1 q.1.2 q.2 o n qT h

end Silmaril.Wasi.Versions.P3OverP2
