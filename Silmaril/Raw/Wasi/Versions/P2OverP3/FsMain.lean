module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsReadInv

/-!
# Proofs (unrefined): the filesystem extension is a model of the loose 0.2 theory

* `neutral_good`, `fsStream_good`: the answers of the other methods of a file stream;
* `wp_progF`: every export call establishes `PostF`;
* `wpInvF`, `p2OverP3Fs_sat`: the invariant method.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step)

variable {F : BitVec 32 → List (BitVec 8)}

/-! ## Classification -/

theorem ioOp_read {f : FnName} (h : ioOp f = .read) : f = isRead := by
  unfold ioOp at h
  rw [ite_eq_right (fun h0 : f = osCheckWrite => by rw [ite_eq_left h0] at h; cases h)] at h
  rw [ite_eq_right (fun h1 : f = osWrite => by rw [ite_eq_left h1] at h; cases h)] at h
  rw [ite_eq_right (fun h2 : f = osBwf => by rw [ite_eq_left h2] at h; cases h)] at h
  rw [ite_eq_right (fun h3 : f = osFlush => by rw [ite_eq_left h3] at h; cases h)] at h
  rw [ite_eq_right (fun h4 : f = osBflush => by rw [ite_eq_left h4] at h; cases h)] at h
  rw [ite_eq_right (fun h5 : f = osSubscribe => by rw [ite_eq_left h5] at h; cases h)] at h
  rw [ite_eq_right (fun h6 : f = osWriteZeroes => by rw [ite_eq_left h6] at h; cases h)] at h
  rw [ite_eq_right (fun h7 : f = osBwzf => by rw [ite_eq_left h7] at h; cases h)] at h
  rw [ite_eq_right (fun h8 : f = osSplice => by rw [ite_eq_left h8] at h; cases h)] at h
  rw [ite_eq_right (fun h9 : f = osBsplice => by rw [ite_eq_left h9] at h; cases h)] at h
  by_cases h10 : f = isRead
  · exact h10
  rw [ite_eq_right h10] at h
  rw [ite_eq_right (fun h11 : f = isBread => by rw [ite_eq_left h11] at h; cases h)] at h
  rw [ite_eq_right (fun h12 : f = isSkip => by rw [ite_eq_left h12] at h; cases h)] at h
  rw [ite_eq_right (fun h13 : f = isBskip => by rw [ite_eq_left h13] at h; cases h)] at h
  rw [ite_eq_right (fun h14 : f = isSubscribe => by rw [ite_eq_left h14] at h; cases h)] at h
  rw [ite_eq_right (fun h15 : f = pollReady => by rw [ite_eq_left h15] at h; cases h)] at h
  rw [ite_eq_right (fun h16 : f = pollBlock => by rw [ite_eq_left h16] at h; cases h)] at h
  rw [ite_eq_right (fun h17 : f = pollPoll => by rw [ite_eq_left h17] at h; cases h)] at h
  rw [ite_eq_right (fun h18 : f = pollDrop => by rw [ite_eq_left h18] at h; cases h)] at h
  cases h

theorem ioOp_bread {f : FnName} (h : ioOp f = .bread) : f = isBread := by
  unfold ioOp at h
  rw [ite_eq_right (fun h0 : f = osCheckWrite => by rw [ite_eq_left h0] at h; cases h)] at h
  rw [ite_eq_right (fun h1 : f = osWrite => by rw [ite_eq_left h1] at h; cases h)] at h
  rw [ite_eq_right (fun h2 : f = osBwf => by rw [ite_eq_left h2] at h; cases h)] at h
  rw [ite_eq_right (fun h3 : f = osFlush => by rw [ite_eq_left h3] at h; cases h)] at h
  rw [ite_eq_right (fun h4 : f = osBflush => by rw [ite_eq_left h4] at h; cases h)] at h
  rw [ite_eq_right (fun h5 : f = osSubscribe => by rw [ite_eq_left h5] at h; cases h)] at h
  rw [ite_eq_right (fun h6 : f = osWriteZeroes => by rw [ite_eq_left h6] at h; cases h)] at h
  rw [ite_eq_right (fun h7 : f = osBwzf => by rw [ite_eq_left h7] at h; cases h)] at h
  rw [ite_eq_right (fun h8 : f = osSplice => by rw [ite_eq_left h8] at h; cases h)] at h
  rw [ite_eq_right (fun h9 : f = osBsplice => by rw [ite_eq_left h9] at h; cases h)] at h
  rw [ite_eq_right (fun h10 : f = isRead => by rw [ite_eq_left h10] at h; cases h)] at h
  by_cases h11 : f = isBread
  · exact h11
  rw [ite_eq_right h11] at h
  rw [ite_eq_right (fun h12 : f = isSkip => by rw [ite_eq_left h12] at h; cases h)] at h
  rw [ite_eq_right (fun h13 : f = isBskip => by rw [ite_eq_left h13] at h; cases h)] at h
  rw [ite_eq_right (fun h14 : f = isSubscribe => by rw [ite_eq_left h14] at h; cases h)] at h
  rw [ite_eq_right (fun h15 : f = pollReady => by rw [ite_eq_left h15] at h; cases h)] at h
  rw [ite_eq_right (fun h16 : f = pollBlock => by rw [ite_eq_left h16] at h; cases h)] at h
  rw [ite_eq_right (fun h17 : f = pollPoll => by rw [ite_eq_left h17] at h; cases h)] at h
  rw [ite_eq_right (fun h18 : f = pollDrop => by rw [ite_eq_left h18] at h; cases h)] at h
  cases h

theorem fsMethod_other {f : FnName} (hm : fsMethod f = true) (ho : ioOp f = .other) :
    f = osDrop ∨ f = isDrop := by
  unfold fsMethod at hm
  rw [ho] at hm
  simpa [IoOp.isStream] using hm

theorem fsMethod_stream {f : FnName} (hm : fsMethod f = false) : (ioOp f).isStream = false := by
  unfold fsMethod at hm
  simp only [Bool.or_eq_false_iff] at hm
  exact hm.1.1

/-! ## Answers of the other methods -/

theorem neutral_closed {s : IoSt} {o : IoOp} {a : List Val} (hc : s.closed (selfOf a) = true)
    (hw : o ≠ .write) (hz : o ≠ .writeZeroes) : neutral s o a = errAns := by
  cases o <;> simp_all [neutral]

theorem neutral_ans (s : IoSt) {o : IoOp} (a : List Val) (ho : o.isStream = true) :
    ansOk .loose s o a (neutral s o a) = true := by
  cases o <;> simp only [IoOp.isStream, Bool.false_eq_true] at ho
  · rw [ansOk_cw]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, nat_err]; rfl
  · rw [ansOk_write (.inl rfl)]; unfold neutral
    by_cases hp : s.permit (selfOf a) < writeLen .write a
    · rw [ite_eq_left hp, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right hp, ite_eq_left (by omega)]
      cases hc : s.closed (selfOf a)
      · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
      · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_bwf (.inl rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
    · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_flush (.inl rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
    · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_flush (.inr rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
    · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_write (.inr rfl)]; unfold neutral
    by_cases hp : s.permit (selfOf a) < writeLen .writeZeroes a
    · rw [ite_eq_left hp, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right hp, ite_eq_left (by omega)]
      cases hc : s.closed (selfOf a)
      · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
      · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_bwf (.inr rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, unit_ok]; rfl
    · simp only [ite_true, sticky_err, unit_err]; rfl
  · rw [ansOk_splice (.inl rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, nat_err]; rfl
  · rw [ansOk_splice (.inr rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, nat_err]; rfl
  · rw [ansOk_read (.inl rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, bytes_ok (bs := []) (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, bytes_err]; rfl
  · rw [ansOk_read (.inr rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, bytes_ok (bs := []) (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, bytes_err]; rfl
  · rw [ansOk_skip (.inl rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, nat_err]; rfl
  · rw [ansOk_skip (.inr rfl)]; unfold neutral
    cases hc : s.closed (selfOf a)
    · simp only [Bool.false_eq_true, ite_false, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
    · simp only [ite_true, sticky_err, nat_err]; rfl

theorem neutral_err {s : IoSt} {o : IoOp} {a : List Val} (h : isErrAns (neutral s o a) = true) :
    s.closed (selfOf a) = true := by
  cases hc : s.closed (selfOf a)
  · exfalso
    cases o <;> simp_all [neutral, isErrAns, okUnit, okN, okV, okBytes]
  · rfl

/-- The 0.2 read theory ignores a call whose first argument is not a handle. -/
theorem rd2_nohead (q : RdSt) {f : FnName} {a : List Val} (r : Option (List Val))
    (h1 : f ≠ fdReadStream) (hu : u32Head a = false) : rd2Step F q (.imp f a r) = some q := by
  unfold rd2Step
  dsimp only
  rw [ite_eq_right h1]
  split
  · split
    · simp [u32Head] at hu
    · rfl
  · rfl

/-! ## Filesystem functions -/

theorem cliOk_true {f : FnName} (h1 : f ≠ cliExit) (h2 : f ≠ getEnv) (h3 : f ≠ getArgs)
    (h4 : f ≠ initialCwd)
    (h5 : ¬ (f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration))
    (h6 : ¬ (f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr)) (h7 : f ≠ monoRes)
    (h8 : ¬ (f = wallNow ∨ f = wallRes))
    (h9 : ¬ (f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream)) (h10 : f ≠ fdGetType)
    (h11 : f ≠ streamDrop) (r : Option (List Val)) : cliOk f r = true := by
  rw [cliOk_eq_hand]
  unfold cliOkH
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
    ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10,
    ite_eq_right h11]

theorem cliOk_getDirs (r : Option (List Val)) : cliOk getDirs r = true :=
  cliOk_true (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r
theorem cliOk_openAt (r : Option (List Val)) : cliOk openAt r = true :=
  cliOk_true (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r
theorem cliOk_fdDrop (r : Option (List Val)) : cliOk fdDrop r = true :=
  cliOk_true (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r
theorem cliOk_isDrop (r : Option (List Val)) : cliOk isDrop r = true :=
  cliOk_true (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r
theorem cliOk_osDrop : cliOk osDrop (some []) = true := by decide +kernel

/-- An answer to a function that `wasi:io` classifies as `other`, other than `now` and
`read-via-stream`, well typed for `cliOk` and `fsOk`, is good. -/
theorem good_other {s : StF} {f : FnName} {a : List Val} {q2 : RdSt} {r : Option (List Val)}
    (ho : ioOp f = .other) (h1 : f ≠ fdReadStream) (hc : cliOk f r = true)
    (hfs : fsOk (.imp f a r) = true) : Good F s f a q2 r where
  ans := by rw [ho]; rfl
  p2 := by simp only [p2Ok, ho, ite_true]; exact hc
  fs := hfs
  rd := ⟨q2, rd2_other q2 a r h1 (fun h => by subst h; exact absurd ho (by decide))
    (fun h => by subst h; exact absurd ho (by decide)), fun _ => rfl⟩
  closed := fun h hx => by
    rcases ioUpd_closed hx with hx | ⟨-, hst, -⟩
    · exact .inl hx
    · rw [ho] at hst; exact absurd hst (by decide)

theorem fsOk_imp (f : FnName) (a : List Val) (r : Option (List Val)) :
    fsOk (.imp f a r) = fsOk (.imp f [] r) := rfl

theorem fsOk_getDirs (a : List Val) (r : Option (List Val)) :
    fsOk (.imp getDirs a (dirsFix r)) = true := by
  unfold dirsFix
  split
  · next h => rw [fsOk_imp]; exact h
  · rw [fsOk_imp]; decide +kernel

theorem fsOk_openAt (a : List Val) (r : Option (List Val)) :
    fsOk (.imp openAt a (openFix r)) = true := by
  unfold openFix
  split
  · next h => rw [fsOk_imp]; exact h
  · rw [fsOk_imp]; decide +kernel

theorem fsOk_fdDrop (a : List Val) : fsOk (.imp fdDrop a (some [])) = true := by
  rw [fsOk_imp]; decide +kernel

theorem fsOk_none {f : FnName} (hf : f ∈ exp2) (a : List Val) (r : Option (List Val)) :
    fsOk (.imp f a r) = true := fsOk_of_mem hf a r

theorem wp_getDirs {s : StF} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (getDirsP s) (PostF F s getDirs a g q2) qT :=
  wp_noread (by decide) hJ ⟨⟨(by decide : getDirs3 ≠ readVia3), (by decide : getDirs3 ≠ cStreamRead)⟩,
    fun r => ⟨shrinks_refl _, good_other (by decide) (by decide) (cliOk_getDirs _) (fsOk_getDirs a r)⟩⟩

theorem wp_openAt {s : StF} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (openAtP s a) (PostF F s openAt a g q2) qT :=
  wp_noread (by decide) hJ ⟨⟨(by decide : openAt3 ≠ readVia3), (by decide : openAt3 ≠ cStreamRead)⟩,
    fun r => ⟨shrinks_refl _, good_other (by decide) (by decide) (cliOk_openAt _) (fsOk_openAt a r)⟩⟩

theorem wp_fdDrop {s : StF} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (fdDropP s a) (PostF F s fdDrop a g q2) qT :=
  wp_noread (by decide) hJ ⟨⟨(by decide : fdDrop3 ≠ readVia3), (by decide : fdDrop3 ≠ cStreamRead)⟩,
    fun _ => ⟨shrinks_refl _, good_other (by decide) (by decide) (cliOk_fdDrop _) (fsOk_fdDrop a)⟩⟩

end Silmaril.Wasi.Versions.P2OverP3
