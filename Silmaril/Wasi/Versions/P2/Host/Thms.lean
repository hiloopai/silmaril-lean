module

public import Silmaril.Wasi.Versions.P2.Host.Defs
public import Silmaril.Wasi.Versions.P2.World.Thms

@[expose] public section

/-!
# WASI 0.2: the hosts are models

* `ioImpl_ok`, `p2Impl_io`: every `wasi:io` answer of the concrete host is admissible in the
  **strict** reading, in the theory state of the answers so far.
* `io_follows`: the concrete host's answer sequences are accepted by the strict `wasi:io` theory.
* `p2Impl_p2Ok`, `p2Impl_fsOk`, `clock_follows_of`: the other three components.
* **`p2Impl_sat`**: the concrete host satisfies the strict WASI 0.2 theory, hence the loose one
  (`p2Impl_sat_loose`). `p2Loose_sat`: the loose hosts satisfy their theories.
* **Agreement with the base WASI theory** (`p2Impl_getStdout`, `p2Impl_streamDrop`, `p2Impl_streamWrite`):
  on `get-stdout` and the stream drop the concrete host answers as the base WASI theory's `stdoutImpl`, and on
  `blocking-write-and-flush` as well while the stream is not closed; on `now` it is the base WASI theory's
  `clockImpl` and on the base WASI theory's filesystem functions the base WASI theory's `fsImpl` (`p2Impl_now`, `p2Impl_fs`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The `wasi:io` part -/

/-- The answer of `poll` is admissible. -/
theorem pollImpl_ok (a : List Val) : pollAns a (pollImpl a) = true := by
  unfold pollImpl pollAns
  split
  · rename_i ps
    by_cases he : ps.isEmpty = true
    · simp [he]
    · have hall : ((List.range ps.length).map hnd).all (idxOk ps.length) = true := by
        simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp]
        intro i hi
        have hlt : (BitVec.ofNat 32 i).toNat < ps.length :=
          lt_of_le_of_lt (by simp [Nat.mod_le]) hi
        simpa [idxOk, hnd] using hlt
      have hne : ((List.range ps.length).map hnd).isEmpty = false := by
        cases ps with
        | nil => exact absurd rfl he
        | cons _ _ => simp [List.range_succ]
      simp [he, hall, hne]
  · rfl

/-- `orClosed` answers are sticky. -/
theorem stickyOk_orClosed (s : IoSt) (h : BitVec 32) (v : Option (List Val)) :
    stickyOk s h (orClosed s h v) = true := by
  unfold stickyOk orClosed
  cases s.closed h <;> rfl

/-- `error(closed)` and the normal answers of `ioImpl` are well formed. -/
theorem orClosed_cases (s : IoSt) (h : BitVec 32) (v : Option (List Val)) :
    orClosed s h v = some [errClosed] ∨ orClosed s h v = v := by
  unfold orClosed
  cases s.closed h <;> simp

/-- A write-like call of the concrete host. -/
theorem ioImpl_write_ok (s : IoSt) (n : Nat) (o : IoOp) (a : List Val)
    (ho : o = .write ∨ o = .writeZeroes) : ansOk .strict s o a (ioImpl s n o a) = true := by
  have hans : ioImpl s n o a =
      if writeLen o a ≤ s.permit (selfOf a) then orClosed s (selfOf a) (some [okV none]) else none := by
    rcases ho with rfl | rfl <;> rfl
  have hok : ansOk .strict s o a (ioImpl s n o a) =
      if writeLen o a ≤ s.permit (selfOf a) then
        stickyOk s (selfOf a) (ioImpl s n o a) && unitAns (ioImpl s n o a)
      else (ioImpl s n o a).isNone := by
    rcases ho with rfl | rfl <;> rfl
  rw [hok, hans]
  by_cases hle : writeLen o a ≤ s.permit (selfOf a)
  · simp only [hle, ↓reduceIte, stickyOk_orClosed, Bool.true_and]
    cases hc : s.closed (selfOf a) <;> simp [orClosed, hc, unitAns_eq_hand, unitAnsH, errClosed, errV, okV, streamErrOk_eq_hand, streamErrOkH]
  · simp [hle]

/-- **Every `wasi:io` answer of the concrete host is admissible in the strict reading.** -/
theorem ioImpl_ok (s : IoSt) (n : Nat) (o : IoOp) (a : List Val) :
    ansOk .strict s o a (ioImpl s n o a) = true := by
  cases o
  case poll => exact pollImpl_ok a
  case write => exact ioImpl_write_ok s n _ a (.inl rfl)
  case writeZeroes => exact ioImpl_write_ok s n _ a (.inr rfl)
  all_goals
    cases hc : s.closed (selfOf a) <;>
      simp [ansOk, ioImpl, orClosed, hc, stickyOk, errClosed, errV, okV, unitAns_eq_hand, unitAnsH, natAns,
        streamErrOk_eq_hand, streamErrOkH, bytesAns, isClosedAns, isOkZero, handleAns_eq_hand, handleAnsH, readyAns_eq_hand,
        readyAnsH, blockAns_eq_hand, blockAnsH, hnd]

/-- The concrete host's `wasi:io` answers are admissible in the state of its answers so far. -/
theorem p2Impl_io (p : List WEv) (f : FnName) (a : List Val) :
    ansOk .strict (ioState p) (ioOp f) a (p2Impl p f a) = true := by
  by_cases ho : ioOp f = .other
  · rw [ho]
    rfl
  · have hi : p2Impl p f a = ioImpl (ioState p) p.length (ioOp f) a := by simp [p2Impl, ho]
    rw [hi]
    exact ioImpl_ok _ _ _ _

/-- One more answer of the concrete host. -/
theorem io_step_follows {p : List WEv} {e : WEv}
    (he : ∀ f a r, e = .imp f a r → r = p2Impl p f a) :
    ioStep .strict (ioState p) e = some (ioState (p ++ [e])) := by
  have hst : ioState (p ++ [e]) = ioNext (ioState p) e := by simp [ioState, List.foldl_append]
  rw [hst]
  cases e
  case imp f a r =>
    have hr : r = p2Impl p f a := he f a r rfl
    subst hr
    simp [ioStep, ioNext, p2Impl_io]
  all_goals rfl

/-- **The concrete host's answers are accepted by the strict `wasi:io` theory.** -/
theorem io_follows {t : List WEv} (ht : Follows p2Impl t) :
    ioStrict.run ioStrict.init t = some (ioState t) := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    have ht' : Follows p2Impl t := (prefixClosed_follows p2Impl).2 (List.prefix_append t [e]) ht
    have he : ∀ f a r, e = .imp f a r → r = p2Impl t f a :=
      fun f a r h => ht t f a r (h ▸ List.prefix_refl _)
    rw [Protocol.run_concat, ih ht']
    exact io_step_follows he

/-! ## The other parts -/

/-- `clockNow` is not a `wasi:io` function. -/
theorem ioOp_clockNow : ioOp clockNow = .other := by decide

/-- On `now` the concrete host is the base WASI theory's tick clock. -/
theorem p2Impl_now (p : List WEv) (a : List Val) : p2Impl p clockNow a = clockImpl p clockNow a :=
  rfl

/-- the base WASI theory's filesystem functions. -/
def Fs856 (f : FnName) : Prop := f = getDirs ∨ f = openAt ∨ f = fdWrite ∨ f = fdRead ∨ f = fdDrop

/-- On the base WASI theory's filesystem functions the concrete host is the base WASI theory's `fsImpl`. -/
theorem p2Impl_fs {f : FnName} (hf : Fs856 f) (p : List WEv) (a : List Val) :
    p2Impl p f a = fsImpl p f a := by
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The answers of `restImpl` satisfy `cliOk`. -/
theorem restImpl_cliOk (p : List WEv) (f : FnName) (a : List Val) :
    cliOk f (restImpl p f a) = true := by
  rw [cliOk_eq_hand]
  unfold cliOkH restImpl
  by_cases h1 : f = cliExit
  · simp [h1]
  simp only [h1, ↓reduceIte]
  by_cases h2 : f = getEnv
  · simp [h2]
  simp only [h2, ↓reduceIte]
  by_cases h3 : f = getArgs
  · simp [h3]
  simp only [h3, ↓reduceIte]
  by_cases h4 : f = initialCwd
  · simp [h4, optStrOk]
  simp only [h4, ↓reduceIte]
  by_cases h5 : f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration
  · simp [h5, hnd]
  simp only [h5, ↓reduceIte]
  by_cases h6 : f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr
  · simp [h6, optHandleOk]
  simp only [h6, ↓reduceIte]
  by_cases h7 : f = monoRes
  · simp [h7]
  simp only [h7, ↓reduceIte]
  by_cases h8 : f = wallNow ∨ f = wallRes
  · simp [h8, datetimeOk]
  simp only [h8, ↓reduceIte]
  by_cases h9 : f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream
  · simp [h9, handleResOk, okV, hnd]
  simp only [h9, ↓reduceIte]
  by_cases h10 : f = fdGetType
  · simp [h10, okV]
  simp only [h10, ↓reduceIte]
  by_cases h11 : f = streamDrop
  · simp [h11]
  simp only [h11, ↓reduceIte]

/-- **The concrete host's answers satisfy `p2Ok`.** -/
theorem p2Impl_p2Ok (p : List WEv) (f : FnName) (a : List Val) :
    p2Ok (.imp f a (p2Impl p f a)) = true := by
  by_cases ho : ioOp f = .other
  · have hr : p2Impl p f a = restImpl p f a := by simp [p2Impl, ho]
    rw [p2Ok_of_other ho, hr]
    exact restImpl_cliOk p f a
  · simp [p2Ok, ho]

/-- **The concrete host's answers satisfy the base WASI theory's filesystem typing.** -/
theorem p2Impl_fsOk (p : List WEv) (f : FnName) (a : List Val) :
    fsOk (.imp f a (p2Impl p f a)) = true := by
  by_cases hf : Fs856 f
  · rw [p2Impl_fs hf]
    exact fsImpl_ok p f a
  · have h5 : ¬ (f = getDirs ∨ f = openAt ∨ f = fdWrite ∨ f = fdRead ∨ f = fdDrop) := hf
    simp only [not_or] at h5
    simp [fsOk, h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2]

/-- The clock theory for every host answering `now` as the tick clock. -/
theorem clock_follows_of {impl : Impl} (hnow : ∀ p a, impl p clockNow a = clockImpl p clockNow a)
    {t : List WEv} (ht : Follows impl t) :
    ∃ q, clockTh.run clockTh.init t = some q ∧ ClockBound t q := by
  induction t using List.reverseRecOn with
  | nil => exact ⟨none, rfl, fun v hv => (Option.some_ne_none v hv.symm).elim⟩
  | append_singleton t e ih =>
    have ht' : Follows impl t := (prefixClosed_follows impl).2 (List.prefix_append t [e]) ht
    obtain ⟨q, hq, hb⟩ := ih ht'
    have he : ∀ a r, e = .imp clockNow a r → r = clockImpl t clockNow a :=
      fun a r h => (ht t clockNow a r (h ▸ List.prefix_refl _)).trans (hnow t a)
    obtain ⟨q', hq', hb'⟩ := clock_snoc hb he
    refine ⟨q', ?_, hb'⟩
    rw [Protocol.run_concat, hq]
    exact hq'

/-! ## Satisfaction -/

/-- The concrete host's answer sequences are accepted by the strict WASI 0.2 theory. -/
theorem p2Impl_accepts {t : List WEv} (ht : Follows p2Impl t) : (p2Th .strict).Accepts t := by
  have hio : ioStrict.Accepts t := (Protocol.accepts_iff_exists _ _).2 ⟨_, io_follows ht⟩
  have hcl : clockTh.Accepts t :=
    let ⟨q, hq, _⟩ := clock_follows_of p2Impl_now ht
    (Protocol.accepts_iff_exists _ _).2 ⟨q, hq⟩
  have hok : (pointwise p2Ok).Accepts t := follows_pointwise p2Impl_p2Ok (fun e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  have hfs : fsTyped.Accepts t := follows_pointwise p2Impl_fsOk (fun e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  exact (Protocol.accepts_prod_iff _ _ _).2 ⟨hio, (Protocol.accepts_prod_iff _ _ _).2
    ⟨hcl, (Protocol.accepts_prod_iff _ _ _).2 ⟨hok, hfs⟩⟩⟩

/-- **The concrete host satisfies the strict WASI 0.2 theory.** -/
theorem p2Impl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (p2Th .strict).Accepts).holds (concrete (Y := Y) (I := I) p2Impl) :=
  concrete_sat _ fun _ ht => p2Impl_accepts ht

/-- The concrete host satisfies the loose WASI 0.2 theory. -/
theorem p2Impl_sat_loose {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (p2Th .loose).Accepts).holds (concrete (Y := Y) (I := I) p2Impl) :=
  concrete_sat _ fun _ ht => p2_loose_of_strict (p2Impl_accepts ht)

/-- The loose hosts satisfy their theories. -/
theorem p2Loose_sat {Y : Sig.{0}} {I : Set FnName} (r : Reading) :
    (hostSat (p2Th r).Accepts).holds (p2Loose (Y := Y) (I := I) r) :=
  loose_sat _

/-! ## Agreement with the base WASI theory's stdout host -/

/-- `get-stdout` as the base WASI theory's `stdoutImpl`. -/
theorem p2Impl_getStdout (p : List WEv) (a : List Val) :
    p2Impl p getStdout a = stdoutImpl p getStdout a := by
  rfl

/-- The stream drop as the base WASI theory's `stdoutImpl`. -/
theorem p2Impl_streamDrop (p : List WEv) (a : List Val) :
    p2Impl p streamDrop a = stdoutImpl p streamDrop a :=
  rfl

/-- `blocking-write-and-flush` as the base WASI theory's `stdoutImpl`, on a stream that is not closed. -/
theorem p2Impl_streamWrite (p : List WEv) (a : List Val)
    (hc : (ioState p).closed (selfOf a) = false) :
    p2Impl p streamWrite a = stdoutImpl p streamWrite a := by
  have ho : ioOp streamWrite = .bwf := ioOp_bwf
  have hi : p2Impl p streamWrite a = ioImpl (ioState p) p.length .bwf a := by
    unfold p2Impl
    rw [ho]
    rfl
  rw [hi]
  simp only [ioImpl, orClosed, hc]
  rfl

end Silmaril.Wasi.Versions.P2
