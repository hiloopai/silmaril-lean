module

public import Silmaril.Proofs.Wasi.Versions.Adapter.Helpers

/-!
# Proofs: the adapter's answers satisfy the preview1 theory (leaves)

`Good n a f r`: the answer `r.2` of `n a` is well typed and within bounds, and the descriptor
theory, from `f`, accepts it into a state related to the adapter's state `r.1` by `FdInv`.
One lemma per kind of answer of the adapter.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt fdStep fdOk typedOk boundsOk okAns errAns)

/-- The preview1 theory (but the clock) accepts the answer `r` of `n a`. -/
def Good (n : String) (a : List Val) (f : FdSt) (r : ASt × Option (List Val)) : Prop :=
  TB n a r.2 ∧ ∃ f', fdStep f (.imp (P1.fn n) a r.2) = some f' ∧ FdInv r.1 f'

/-! ## The descriptor theory on answers -/

theorem fdStep_err (f : FdSt) (g : FnName) (a : List Val) (e : Nat) :
    fdStep f (.imp g a (errAns e)) = some f := by
  unfold fdStep; split <;> simp_all [errAns, errV]

theorem fdStep_none (f : FdSt) (g : FnName) (a : List Val) : fdStep f (.imp g a none) = some f := by
  unfold fdStep; split <;> simp_all

theorem fdStep_nonfd {n : String} (hn : n ∉ P1.fdFns) (f : FdSt) (a : List Val)
    (r : Option (List Val)) : fdStep f (.imp (P1.fn n) a r) = some f := by
  unfold fdStep
  split
  · rename_i heq
    obtain ⟨rfl, -, -⟩ := heq
    simp [P1.fn, hn]
  · rfl

theorem fdStep_fd {n : String} (hn : n ∈ P1.fdFns) (f : FdSt) (fd : BitVec 32) (a : List Val)
    (v : Option Val) :
    fdStep f (.imp (P1.fn n) (.u32 fd :: a) (okAns v)) =
      if (n = "fd_write" ∨ n = "fd_read") ∧ P1.emptyIovs (.u32 fd :: a) = true then some f
      else if fd ∈ f.dead then none else fdOk f n fd a v := by
  simp only [fdStep, okAns, okV, P1.fn, hn, and_true, ite_true]

/-- An operation other than `fd_close`, `path_open`, `fd_renumber` marks its descriptor open. -/
theorem fdOk_plain {n : String} (h1 : n ≠ "fd_close") (h2 : n ≠ "path_open")
    (h3 : n ≠ "fd_renumber") (f : FdSt) (fd : BitVec 32) (a : List Val) (v : Option Val) :
    fdOk f n fd a v = some (touch f fd) := by
  simp only [fdOk, h1, h2, h3, ite_false]; rfl

/-! ## Leaves -/

theorem mem_fnNames {n : String}
    (h : n ∈ ["fd_write", "fd_read", "fd_close", "path_open", "clock_time_get", "clock_res_get",
      "random_get", "args_get", "args_sizes_get", "environ_get", "environ_sizes_get",
      "sched_yield", "proc_exit"]) : n ∈ P1.fnNames := by
  revert n h; decide

/-- An error answer, in an unchanged state. -/
theorem good_err {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") {e : Nat}
    (he : ValidErr e) {s : ASt} {f : FdSt} (hJ : FdInv s f) (a : List Val) :
    Good n a f (s, errAns e) :=
  ⟨tb_err hn hx he a, f, fdStep_err f _ a e, hJ⟩

/-- An `ok` answer of a function without descriptor, in an unchanged state. -/
theorem good_ok_nonfd {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit")
    (hfd : n ∉ P1.fdFns) {v : Option Val} (hv : P1.okShape n v = true)
    (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get") {s : ASt} {f : FdSt}
    (hJ : FdInv s f) (a : List Val) : Good n a f (s, okAns v) :=
  ⟨tb_ok hn hx hv hb a, f, fdStep_nonfd hfd f a _, hJ⟩

theorem firstBuf_le : ∀ {bufs : List Val} {bs : List (BitVec 8)}, firstBuf bufs = some bs →
    bs.length ≤ P1.bufTotal (.record bufs)
  | [], _, h => by cases h
  | [b], _, h => by
    simp only [firstBuf, Option.some.injEq] at h
    subst h; simp [P1.bufTotal]
  | b :: c :: t, bs, h => by
    simp only [firstBuf] at h
    split_ifs at h with hb
    · have := firstBuf_le h
      simp only [P1.bufTotal, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simp only [Option.some.injEq] at h
      subst h; simp only [P1.bufTotal, List.map_cons, List.sum_cons]; omega

theorem firstBuf_nil : ∀ {bufs : List Val}, firstBuf bufs = none → bufs = []
  | [], _ => rfl
  | [b], h => by simp [firstBuf] at h
  | b :: c :: t, h => by
    simp only [firstBuf] at h
    split_ifs at h
    exact absurd (firstBuf_nil h) (by simp)

theorem toNat_ofNat_le (k n : Nat) : (BitVec.ofNat k n).toNat ≤ n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _

/-- `fd_write` of an empty ciovec list. -/
theorem good_write_empty {s : ASt} {f : FdSt} (hJ : FdInv s f) (fd : BitVec 32) :
    Good "fd_write" [.u32 fd, .record []] f (s, okAns (sizeV 0)) := by
  refine ⟨⟨rfl, rfl⟩, f, ?_, hJ⟩
  rw [fdStep_fd (by decide)]
  simp [P1.emptyIovs]

/-- `fd_write` of the first buffer `bs` on an open descriptor. -/
theorem good_write_ok {bufs : List Val} {bs : List (BitVec 8)} (hfb : firstBuf bufs = some bs)
    {s : ASt} {f : FdSt} (hJ : FdInv s f) {fd : BitVec 32} (ho : IsOpen s fd) :
    Good "fd_write" [.u32 fd, .record bufs] f (s, okAns (sizeV bs.length)) := by
  have hne : bufs ≠ [] := by rintro rfl; cases hfb
  refine ⟨⟨?_, ?_⟩, touch f fd, ?_, fdInv_touch hJ ho⟩
  · rfl
  · simp only [P1.boundsOk, ite_true, okAns, okV, sizeV, decide_eq_true_eq]
    exact (toNat_ofNat_le 32 _).trans (firstBuf_le hfb)
  · rw [fdStep_fd (by decide)]
    have hemp : P1.emptyIovs [.u32 fd, .record bufs] = false := by
      rcases bufs with _ | ⟨b, t⟩
      · exact absurd rfl hne
      · rfl
    simp only [hemp, Bool.false_eq_true, and_false, ite_false, hJ.not_dead ho]
    exact fdOk_plain (by decide) (by decide) (by decide) f fd _ _

theorem isBytesV_of_allU8 : ∀ {bs : List Val}, allU8 bs = true → P1.isBytesV (.record bs) = true
  | [], _ => rfl
  | b :: t, h => by
    simp only [allU8, List.all_cons, Bool.and_eq_true] at h
    have ih := isBytesV_of_allU8 (bs := t) h.2
    simp only [P1.isBytesV, List.all_cons, Bool.and_eq_true] at ih ⊢
    refine ⟨?_, ih⟩
    have := h.1
    split at this <;> simp_all

theorem bytesOf_length_of_allU8 : ∀ {bs : List Val}, allU8 bs = true →
    (bytesOf (.record bs)).length = bs.length
  | [], _ => rfl
  | b :: t, h => by
    simp only [allU8, List.all_cons, Bool.and_eq_true] at h
    have ih := bytesOf_length_of_allU8 (bs := t) h.2
    simp only [bytesOf, List.filterMap_cons] at ih ⊢
    have := h.1
    split at this
    · simp [ih]
    · simp at this

theorem firstLen_le : ∀ {lens : List Val} {n : Nat}, firstLen lens = some n →
    n ≤ P1.lenTotal (.record lens)
  | [], _, h => by cases h
  | [l], _, h => by
    simp only [firstLen, Option.some.injEq] at h
    subst h; simp only [P1.lenTotal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      lenOf]; split <;> simp
  | l :: c :: t, n, h => by
    simp only [firstLen] at h
    split_ifs at h with hl
    · have := firstLen_le h
      simp only [P1.lenTotal, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simp only [Option.some.injEq] at h
      subst h; simp only [P1.lenTotal, List.map_cons, List.sum_cons, lenOf]; split <;> simp

theorem firstLen_lt : ∀ {lens : List Val} {n : Nat}, firstLen lens = some n → n < 2 ^ 64
  | [], _, h => by cases h
  | [l], _, h => by
    simp only [firstLen, Option.some.injEq] at h
    subst h; unfold lenOf; split
    · rename_i x; have := x.isLt; omega
    · omega
  | l :: c :: t, n, h => by
    simp only [firstLen] at h
    split_ifs at h with hl
    · exact firstLen_lt h
    · simp only [Option.some.injEq] at h
      subst h; unfold lenOf; split
      · rename_i x; have := x.isLt; omega
      · omega

theorem firstLen_nil : ∀ {lens : List Val}, firstLen lens = none → lens = []
  | [], _ => rfl
  | [b], h => by simp [firstLen] at h
  | b :: c :: t, h => by
    simp only [firstLen] at h
    split_ifs at h
    exact absurd (firstLen_nil h) (by simp)

/-- `fd_read` with an empty iovec list. -/
theorem good_read_empty {s : ASt} {f : FdSt} (hJ : FdInv s f) (fd : BitVec 32) :
    Good "fd_read" [.u32 fd, .record []] f (s, okAns (some (bytesV []))) := by
  refine ⟨⟨rfl, rfl⟩, f, ?_, hJ⟩
  rw [fdStep_fd (by decide)]
  simp [P1.emptyIovs]

/-- `fd_read` of at most `n` bytes on an open descriptor. -/
theorem good_read_ok {lens : List Val} {n : Nat} (hfl : firstLen lens = some n) {bs : List Val}
    (hu : allU8 bs = true) (hl : bs.length ≤ n) {s : ASt} {f : FdSt} (hJ : FdInv s f)
    {fd : BitVec 32} (ho : IsOpen s fd) :
    Good "fd_read" [.u32 fd, .record lens] f (s, okAns (some (.record bs))) := by
  have hne : lens ≠ [] := by rintro rfl; cases hfl
  refine ⟨⟨?_, ?_⟩, touch f fd, ?_, fdInv_touch hJ ho⟩
  · have hb := isBytesV_of_allU8 hu
    simp only [typedOk, P1.fn, P1.module, mem_fnNames (n := "fd_read") (by simp), and_self,
      ite_true, P1.ansOk, okAns, okV]
    simp [P1.okShape, P1.isBytes, hb]
  · simp only [P1.boundsOk, show P1.fn "fd_read" ≠ P1.fn "fd_write" by decide, ite_false,
      ite_true, okAns, okV, decide_eq_true_eq, bytesOf_length_of_allU8 hu]
    exact hl.trans (firstLen_le hfl)
  · rw [fdStep_fd (by decide)]
    have hemp : P1.emptyIovs [.u32 fd, .record lens] = false := by
      rcases lens with _ | ⟨b, t⟩
      · exact absurd rfl hne
      · rfl
    simp only [hemp, Bool.false_eq_true, and_false, ite_false, hJ.not_dead ho]
    exact fdOk_plain (by decide) (by decide) (by decide) f fd _ _

/-- `fd_close` of an open descriptor. -/
theorem good_close {s : ASt} {f : FdSt} (hJ : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {fd : BitVec 32} (ho : isOpenD (getD t fd) = true) :
    Good "fd_close" [.u32 fd] f (⟨some (t.set fd.toNat .closed), fd.toNat :: s.free⟩, okAns none) := by
  refine ⟨⟨rfl, rfl⟩, _, ?_, fdInv_close hJ ht ho⟩
  rw [fdStep_fd (by decide)]
  simp only [show ¬ ("fd_close" = "fd_write" ∨ "fd_close" = "fd_read") by decide, false_and,
    ite_false, hJ.not_dead ((isOpen_some ht fd).2 ho)]
  simp only [fdOk, ite_true]
  rfl

/-- `path_open` of a fresh descriptor. -/
theorem good_open {s : ASt} {f : FdSt} (hJ : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {fd : BitVec 32} (hdir : isOpenD (getD t fd) = true) {d : Desc} (hd : isOpenD d = true)
    {s' : ASt} {x : Nat} (hopen : openDesc s t d = some (s', x)) (a : List Val) :
    Good "path_open" (.u32 fd :: a) f (s', okAns (sizeV x)) := by
  obtain ⟨hfresh, hJ'⟩ := fdInv_open hJ ht hdir hd hopen
  refine ⟨⟨rfl, rfl⟩, _, ?_, hJ'⟩
  rw [fdStep_fd (by decide)]
  simp only [show ¬ ("path_open" = "fd_write" ∨ "path_open" = "fd_read") by decide, false_and,
    ite_false, hJ.not_dead ((isOpen_some ht fd).2 hdir)]
  simp only [fdOk, show "path_open" ≠ "fd_close" by decide, ite_false, ite_true, sizeV]
  show (if BitVec.ofNat 32 x ∈ (touch f fd).live then none else _) = _
  rw [ite_eq_right_iff.mpr (fun h => absurd h hfresh)]
  rfl

end Silmaril.Wasi.Versions.Adapter
