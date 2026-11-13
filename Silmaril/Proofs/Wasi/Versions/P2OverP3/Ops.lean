module

public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Leaves

/-!
# Proofs: every answer of a `wasi:io` export is admissible in the loose 0.2 theory

For each `wasi:io` function `o`, every result of its program in the state `s` (whatever the
WASI 0.3 host answers) is admissible for the loose `wasi:io` theory in the 0.2 stream state
`s.io` of the component's earlier answers: `prog_io`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3 (natV)

/-! ## Answer shapes -/

theorem sticky_err (s : IoSt) (h : BitVec 32) : stickyOk s h errAns = true := by
  simp [stickyOk, errAns, errClosed, isClosedAns, errV]

theorem sticky_open {s : IoSt} {h : BitVec 32} (hc : s.closed h = false) (r : Option (List Val)) :
    stickyOk s h r = true := by
  simp [stickyOk, hc]

theorem unit_err : unitAns errAns = true := by rw [unitAns_eq_hand]; rfl
theorem unit_ok : unitAns okUnit = true := by rw [unitAns_eq_hand]; rfl
theorem nat_err (b : Nat) : natAns b errAns = true := rfl
theorem bytes_err (b : Nat) : bytesAns b false errAns = true := rfl

theorem nat_okN {b n : Nat} (h : n ≤ b) : natAns b (okN n) = true := by
  simp only [natAns, okN, okV, BitVec.toNat_ofNat, decide_eq_true_eq]
  exact (Nat.mod_le _ _).trans h

theorem bytes_ok {b : Nat} {bs : List (BitVec 8)} (h : bs.length ≤ b) :
    bytesAns b false (okBytes bs) = true := by
  simp [bytesAns, okBytes, okV, bytesV, isU8, h]

/-- The predicate of an admissible answer of `o` to `a` in the stream state `s`. -/
abbrev Adm (s : IoSt) (o : IoOp) (a : List Val) (x : ISt × Option (List Val)) : Prop :=
  ansOk .loose s o a x.2 = true

/-! ## The loose `wasi:io` admissibility per function -/

theorem nat_top (n : Nat) : natAns (2 ^ 64) (okN n) = true := by
  simp only [natAns, okN, okV, BitVec.toNat_ofNat, decide_eq_true_eq]
  exact Nat.le_of_lt (Nat.mod_lt _ (by decide))

theorem ansOk_cw (s : IoSt) (a : List Val) (r : Option (List Val)) :
    ansOk .loose s .checkWrite a r = (stickyOk s (selfOf a) r && natAns (2 ^ 64) r) := by
  simp [ansOk]

theorem ansOk_write {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .write ∨ o = .writeZeroes)
    (r : Option (List Val)) : ansOk .loose s o a r =
      if writeLen o a ≤ s.permit (selfOf a) then stickyOk s (selfOf a) r && unitAns r
      else r.isNone := by
  rcases ho with rfl | rfl <;> rfl

theorem ansOk_bwf {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .bwf ∨ o = .bwzf)
    (r : Option (List Val)) : ansOk .loose s o a r =
      (stickyOk s (selfOf a) r && (unitAns r || (decide (4096 < writeLen o a) && r.isNone))) := by
  rcases ho with rfl | rfl <;> rfl

theorem ansOk_flush {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .flush ∨ o = .bflush)
    (r : Option (List Val)) : ansOk .loose s o a r = (stickyOk s (selfOf a) r && unitAns r) := by
  rcases ho with rfl | rfl <;> rfl

theorem ansOk_splice {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .splice ∨ o = .bsplice)
    (r : Option (List Val)) :
    ansOk .loose s o a r = (stickyOk s (selfOf a) r && natAns (spliceLenOf a) r) := by
  rcases ho with rfl | rfl <;> rfl

/-! ## Output streams -/

theorem cw_good (cap : Nat) (s : St) (a : List Val) :
    Leaves (cwP cap s a) (Adm s.io .checkWrite a) := by
  unfold cwP
  dsimp only
  cases hc : s.io.closed (selfOf a)
  · rw [ite_eq_right Bool.false_ne_true]
    split
    · exact leaves_pure (by rw [Adm, ansOk_cw, sticky_err, nat_err]; rfl)
    · refine leaves_bind_of (fun o' => leaves_pure ?_) _
      show ansOk .loose s.io .checkWrite a (if o'.err then errAns else okN _) = true
      rw [ansOk_cw, sticky_open hc]
      split
      · rfl
      · exact nat_top _
  · rw [ite_eq_left rfl]
    exact leaves_pure (by rw [Adm, ansOk_cw, sticky_err, nat_err]; rfl)

/-- `write` within the permit. -/
theorem write_good_open (s : St) (a : List Val) {o : IoOp} (bs : List (BitVec 8))
    (hans : ∀ st r, Adm s.io o a (st, r) ↔ (stickyOk s.io (selfOf a) r && unitAns r) = true)
    (hc : s.io.closed (selfOf a) = false) :
    Leaves (match look s.impl.outs (selfOf a) with
      | none => .pure (s.impl, errAns)
      | some o =>
        if o.err then .pure (s.impl, errAns)
        else (pump { o with buf := o.buf ++ bs }).bind fun o' =>
          .pure (s.impl.setOut (selfOf a) o', if o'.err then errAns else okUnit))
      (Adm s.io o a) := by
  have herr : Adm s.io o a (s.impl, errAns) := (hans _ _).2 (by rw [sticky_err, unit_err]; rfl)
  split
  · exact leaves_pure herr
  · split
    · exact leaves_pure herr
    · refine leaves_bind_of (fun o' => leaves_pure ((hans _ _).2 ?_)) _
      rw [sticky_open hc]
      split
      · rfl
      · rfl

theorem write_good (s : St) (a : List Val) {o : IoOp} (bs : List (BitVec 8))
    (ho : o = .write ∨ o = .writeZeroes) (hl : writeLen o a = bs.length) :
    Leaves (writeP s a bs) (Adm s.io o a) := by
  unfold writeP
  dsimp only
  by_cases hp : s.io.permit (selfOf a) < bs.length
  · rw [ite_eq_left hp]
    exact leaves_pure (by rw [Adm, ansOk_write ho, ite_eq_right (by omega)]; rfl)
  · have hp' : writeLen o a ≤ s.io.permit (selfOf a) := hl ▸ Nat.not_lt.1 hp
    have hans : ∀ (st : ISt) r,
        Adm s.io o a (st, r) ↔ (stickyOk s.io (selfOf a) r && unitAns r) = true := by
      intro _ r; rw [Adm, ansOk_write ho, ite_eq_left hp']
    rw [ite_eq_right hp]
    cases hc : s.io.closed (selfOf a)
    · rw [ite_eq_right Bool.false_ne_true]
      exact write_good_open s a bs hans hc
    · rw [ite_eq_left rfl]
      exact leaves_pure ((hans _ _).2 (by rw [sticky_err, unit_err]; rfl))

theorem flushed_unit (st : ISt) (h : BitVec 32) : unitAns (flushed st h) = true := by
  unfold flushed
  split
  · split
    · exact unit_ok
    · exact unit_err
  · exact unit_err

theorem bwf_good (s : St) (a : List Val) {o : IoOp} (bs : List (BitVec 8))
    (ho : o = .bwf ∨ o = .bwzf) (hl : writeLen o a = bs.length) :
    Leaves (bwfP s a bs) (Adm s.io o a) := by
  unfold bwfP
  dsimp only
  cases hc : s.io.closed (selfOf a)
  · have hans : ∀ x : ISt × Option (List Val), unitAns x.2 = true → Adm s.io o a x := by
      intro x hx; rw [Adm, ansOk_bwf ho, sticky_open hc, hx]; rfl
    rw [ite_eq_right Bool.false_ne_true]
    by_cases hb : 4096 < bs.length
    · rw [ite_eq_left hb]
      exact leaves_pure (by rw [Adm, ansOk_bwf ho, sticky_open hc, hl]; simp [hb, unitAns_eq_hand, unitAnsH])
    · rw [ite_eq_right hb]
      split
      · exact leaves_pure (hans _ unit_err)
      · split
        · exact leaves_pure (hans _ unit_err)
        · exact leaves_bind_of (fun st => leaves_pure (hans _ (flushed_unit _ _))) _
  · rw [ite_eq_left rfl]
    exact leaves_pure (by rw [Adm, ansOk_bwf ho, sticky_err, unit_err]; rfl)

theorem flush_good (s : St) (a : List Val) : Leaves (flushP s a) (Adm s.io .flush a) := by
  have ho : IoOp.flush = .flush ∨ IoOp.flush = .bflush := .inl rfl
  unfold flushP
  dsimp only
  cases hc : s.io.closed (selfOf a)
  · rw [ite_eq_right Bool.false_ne_true]
    split
    · exact leaves_pure (by rw [Adm, ansOk_flush ho, sticky_err, unit_err]; rfl)
    · refine leaves_bind_of (fun o' => leaves_pure ?_) _
      show ansOk .loose s.io .flush a (if o'.err then errAns else okUnit) = true
      rw [ansOk_flush ho, sticky_open hc]
      split
      · rfl
      · rfl
  · rw [ite_eq_left rfl]
    exact leaves_pure (by rw [Adm, ansOk_flush ho, sticky_err, unit_err]; rfl)

theorem bflush_good (s : St) (a : List Val) : Leaves (bflushP s a) (Adm s.io .bflush a) := by
  have ho : IoOp.bflush = .flush ∨ IoOp.bflush = .bflush := .inr rfl
  unfold bflushP
  dsimp only
  cases hc : s.io.closed (selfOf a)
  · rw [ite_eq_right Bool.false_ne_true]
    exact leaves_bind_of (fun st => leaves_pure (by
      rw [Adm, ansOk_flush ho, sticky_open hc, flushed_unit]; rfl)) _
  · rw [ite_eq_left rfl]
    exact leaves_pure (by rw [Adm, ansOk_flush ho, sticky_err, unit_err]; rfl)

theorem splice_good (s : St) (a : List Val) {o : IoOp} (ho : o = .splice ∨ o = .bsplice) :
    Leaves (spliceP s a) (Adm s.io o a) := by
  show ansOk .loose s.io o a (if s.io.closed (selfOf a) then errAns else okN 0) = true
  rw [ansOk_splice ho]
  cases hc : s.io.closed (selfOf a)
  · rw [ite_eq_right Bool.false_ne_true, sticky_open hc, nat_okN (Nat.zero_le _)]; rfl
  · rw [ite_eq_left rfl, sticky_err, nat_err]; rfl

/-! ## Input streams -/

theorem ansOk_read {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .read ∨ o = .bread)
    (r : Option (List Val)) :
    ansOk .loose s o a r = (stickyOk s (selfOf a) r && bytesAns (lenOf a) false r) := by
  rcases ho with rfl | rfl <;> rfl

theorem ansOk_skip {s : IoSt} {a : List Val} {o : IoOp} (ho : o = .skip ∨ o = .bskip)
    (r : Option (List Val)) :
    ansOk .loose s o a r = (stickyOk s (selfOf a) r && natAns (lenOf a) r) := by
  rcases ho with rfl | rfl <;> rfl

theorem rdAns_bytes (len : Nat) (x : RdRes) : bytesAns len false (rdAns false len x) = true := by
  cases x with
  | data bs => exact bytes_ok (by simp)
  | eof => exact bytes_err _
  | blocked => exact bytes_ok (by simp)

theorem rdAns_nat (len : Nat) (x : RdRes) : natAns len (rdAns true len x) = true := by
  cases x with
  | data bs => exact nat_okN (Nat.min_le_left _ _)
  | eof => exact nat_err _
  | blocked => exact nat_okN (Nat.zero_le _)

/-- The answers of the read functions, from the shape of `rdAns`. -/
theorem read_good_of (s : St) (a : List Val) {o : IoOp} (blocking skip : Bool)
    (hok : ∀ x, ansOk .loose s.io o a errAns = true ∧
      (s.io.closed (selfOf a) = false → ansOk .loose s.io o a (rdAns skip (lenOf a) x) = true)) :
    Leaves (readP s a blocking skip) (Adm s.io o a) := by
  unfold readP
  dsimp only
  cases hc : s.io.closed (selfOf a)
  · rw [ite_eq_right Bool.false_ne_true]
    split
    · exact leaves_pure (hok .eof).1
    · split
      · exact leaves_pure (hok .eof).1
      · exact leaves_bind_of (fun x => leaves_pure ((hok x.2).2 hc)) _
  · rw [ite_eq_left rfl]
    exact leaves_pure (hok .eof).1

theorem read_good (s : St) (a : List Val) {o : IoOp} (blocking : Bool)
    (ho : o = .read ∨ o = .bread) : Leaves (readP s a blocking false) (Adm s.io o a) :=
  read_good_of s a blocking false fun x =>
    ⟨by rw [ansOk_read ho, sticky_err, bytes_err]; rfl,
     fun hc => by rw [ansOk_read ho, sticky_open hc, rdAns_bytes]; rfl⟩

theorem skip_good (s : St) (a : List Val) {o : IoOp} (blocking : Bool)
    (ho : o = .skip ∨ o = .bskip) : Leaves (readP s a blocking true) (Adm s.io o a) :=
  read_good_of s a blocking true fun x =>
    ⟨by rw [ansOk_skip ho, sticky_err, nat_err]; rfl,
     fun hc => by rw [ansOk_skip ho, sticky_open hc, rdAns_nat]; rfl⟩

/-! ## Pollables -/

theorem sub_good (s : St) (a : List Val) {o : IoOp} (k : BitVec 32 → PollK)
    (ho : o = .oSubscribe ∨ o = .iSubscribe) : Leaves (subP s a k) (Adm s.io o a) := by
  rcases ho with rfl | rfl <;> rfl

theorem ready_good (s : St) (a : List Val) : Leaves (readyP s a) (Adm s.io .ready a) :=
  leaves_bind_of (P := Adm s.io .ready a) (fun _ => leaves_pure rfl) _

theorem block_good (s : St) (a : List Val) : Leaves (blockP s a) (Adm s.io .block a) :=
  leaves_bind_of (P := Adm s.io .block a) (fun _ => leaves_pure rfl) _

theorem pdrop_good (s : St) (a : List Val) : Leaves (pdropP s a) (Adm s.io .pDrop a) := rfl

theorem idxOk_natV {n j : Nat} (h : j < n) : idxOk n (natV j) = true := by
  simp only [idxOk, natV, BitVec.toNat_ofNat, decide_eq_true_eq]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- The answer of `poll` lists valid indices, at least one. -/
theorem pollAnsOf_ok {n : Nat} (hn : 0 < n) (is : List Nat) :
    ∃ js, pollAnsOf n is = .record js ∧ js ≠ [] ∧ ∀ v ∈ js, idxOk n v = true := by
  unfold pollAnsOf
  cases hf : is.filter (· < n) with
  | nil => exact ⟨[natV 0], rfl, by simp, by simp [idxOk_natV hn]⟩
  | cons j js =>
    refine ⟨(j :: js).map natV, rfl, by simp, fun v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    have hmem : i ∈ is.filter (· < n) := hf ▸ hi
    exact idxOk_natV (by simpa using (List.mem_filter.1 hmem).2)

theorem poll_good (s : St) (a : List Val) : Leaves (pollP s a) (Adm s.io .poll a) := by
  unfold pollP
  split
  · rename_i ps
    by_cases he : ps.isEmpty
    · rw [ite_eq_left he]
      exact leaves_pure (by simp [Adm, ansOk, pollAns, he])
    · rw [ite_eq_right he]
      have hn : 0 < ps.length := List.length_pos_iff.2 (by simpa using he)
      refine leaves_bind_of (fun x => leaves_pure ?_) _
      show pollAns [.record ps] (some [pollAnsOf ps.length x.2]) = true
      obtain ⟨js, hjs, hne, hall⟩ := pollAnsOf_ok hn x.2
      simp [pollAns, he, hjs, hne, List.all_eq_true.2 hall]
  · rename_i hne
    refine leaves_pure ?_
    show pollAns a (some [.record []]) = true
    unfold pollAns
    split
    · exact absurd rfl (hne _)
    · rfl

end Silmaril.Wasi.Versions.P2OverP3
