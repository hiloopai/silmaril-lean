module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.ReadInv

/-!
# Proofs: `stream.read` of WASI 0.3 over 0.2 keeps the read invariant

`wp_sr`: under the 0.2 read theory `fsRead2 F`, the answer of `stream.read` is accepted by the
0.3 read theory `fsReadTh3w F` and the read invariant `RdJ` is kept. A live file binding reads
by `blocking-read` on its 0.2 stream: bytes are the next bytes of the file on both sides, an
error is the end on both sides.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy blocked CopyResult Store)
open Silmaril.Wasi.Versions.P3

variable (F : BitVec 32 → List (BitVec 8))

/-- Two handle arguments. -/
theorem arg2_spec {a : List Val} {r n : Nat} (h : arg2 a = some (r, n)) :
    ∃ rv nv, a = [rv, nv] ∧ natOf rv = some r ∧ natOf nv = some n := by
  match a, h with
  | [rv, nv], h =>
    simp only [arg2] at h
    split at h
    · rename_i x y hx hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rv, nv, rfl, hx, hy⟩
    · cases h

/-- The bindings after `setMode` at a bound end. -/
theorem inOf_setMode_at {c : Core} {r : Nat} {ib : InB} (hib : c.inOf r = some ib) (m : IMode)
    (r'' : Nat) : (c.setMode r m).inOf r'' =
      if r'' = r then some { ib with mode := m } else c.inOf r'' := by
  rw [inOf_setMode]
  split
  · rename_i h; subst h; rw [hib]; rfl
  · rfl

/-- The bindings of an unchanged state, read as a change of mode to the same mode. -/
theorem inOf_same {c : Core} {r : Nat} {ib : InB} (hib : c.inOf r = some ib) (hm : ib.mode = .live)
    (r'' : Nat) : c.inOf r'' = if r'' = r then some { ib with mode := .live } else c.inOf r'' := by
  split
  · rename_i h; subst h; rw [hib, ← hm]
  · rfl

/-- **`stream.read` keeps the read invariant.** -/
theorem wp_sr (c : Core) (k : ClockSt) (q2 q3 : RdSt) (a : List Val) (h : RdJ c q2 q3) :
    Wp (fsRead2 F) ((ioSr c a).bind fun d =>
      .pure (done k (let r := finSr c a d; (r.1, some [natV r.2.1, .record r.2.2]))))
      (fun x q2' => ∃ q3', (fsReadTh3w F).step q3 (.imp cStreamRead a x.2) = some q3' ∧
        RdJ x.1.core q2' q3') q2 := by
  rw [Wp.bind]
  cases ha : arg2 a with
  | none =>
    simp only [ioSr, ha]
    exact ⟨q3, by simp only [done, finSr, ha]; exact rd3_blocked F q3 a _, by simpa [done, finSr, ha]⟩
  | some p =>
    obtain ⟨r, n⟩ := p
    obtain ⟨rv, nv, rfl, hr, hn⟩ := arg2_spec ha
    by_cases h0 : r = 0
    · subst h0
      have hib : c.inOf 0 = none := by
        cases hc : c.inOf 0 with
        | none => rfl
        | some ib => exact absurd (h.bound 0 ib hc).1 (Nat.lt_irrefl 0)
      simp only [ioSr, ha, hib]
      exact ⟨q3, by simp only [done, finSr, ha, ite_true]; exact rd3_blocked F q3 _ _,
        by simpa [done, finSr, ha]⟩
    cases hib : c.inOf r with
    | none =>
      simp only [ioSr, ha, hib]
      have hq3 : rest q3 r = none := by
        cases hq : rest q3 r with
        | none => rfl
        | some bs =>
          rcases h.known r bs hq with h' | ⟨ib, h', -⟩
          · exact absurd h' h0
          · rw [hib] at h'; cases h'
      simp only [done, finSr, ha, h0, ite_false, hib]
      split
      · rename_i st' code xs hst
        exact ⟨q3, rd3_none F q3 _ _ hr hq3, h.dframe (DFrame.of_ins (astep_next hst) rfl)⟩
      · rename_i st' code hst
        exact ⟨q3, rd3_none F q3 _ _ hr hq3, h.dframe (DFrame.of_ins (astep_next hst) rfl)⟩
      · exact ⟨q3, rd3_none F q3 _ _ hr hq3, h⟩
    | some ib =>
      have hstdin : ib.file = false → rest q3 r = none := h.stdin r ib hib
      cases hm : ib.mode with
      | eof =>
        simp only [ioSr, ha, hib, hm]
        simp only [done, finSr, ha, h0, ite_false, hib, hm]
        refine ⟨q3, ?_, h⟩
        cases hf : ib.file
        · exact rd3_none F q3 _ _ hr (hstdin hf)
        · exact rd3_dropped F q3 _ hr hn (h.eof r ib hib hf hm)
      | dead =>
        simp only [ioSr, ha, hib, hm]
        simp only [done, finSr, ha, h0, ite_false, hib, hm]
        exact ⟨q3, rd3_blocked F q3 _ _, h⟩
      | live =>
        simp only [ioSr, ha, hib, hm, ite_true]
        intro ans q2' hstep
        obtain ⟨hother, hok, herr, hno⟩ := rd2_bread F hstep
        show ∃ q3', (fsReadTh3w F).step q3 (.imp cStreamRead [rv, nv]
          (some [natV (finSr c [rv, nv] ans).2.1, .record (finSr c [rv, nv] ans).2.2])) = some q3' ∧
          RdJ (finSr c [rv, nv] ans).1 q2' q3'
        simp only [finSr, ha, h0, ite_false, hib, hm]
        have hkn : ∀ bs, rest q3 r = some bs → ib.file = true := by
          intro bs hq; cases hf : ib.file
          · rw [hstdin hf] at hq; cases hq
          · rfl
        split
        · rename_i v
          split
          · -- no bytes: blocked
            rename_i hb
            refine ⟨q3, rd3_blocked F q3 _ _, h.at hib hm .live rfl (inOf_same hib hm) hother
              (fun _ _ => rfl) (fun hf _ => ?_) (fun _ h' => by cases h') hstdin hkn⟩
            obtain ⟨bs, h1, h1'⟩ := h.live r ib hib hf hm
            obtain ⟨-, h2⟩ := hok bs v h1' rfl
            exact ⟨bs, h1, by simpa [hb] using h2⟩
          · split
            · -- bytes within the count
              rename_i hb hle
              cases hf : ib.file
              · exact ⟨q3, rd3_none F q3 _ _ hr (hstdin hf), h.at hib hm .live rfl (inOf_same hib hm)
                  hother (fun _ _ => rfl) (fun h' => by cases h'.symm.trans hf)
                  (fun _ h' => by cases h') hstdin hkn⟩
              · obtain ⟨bs, h1, h1'⟩ := h.live r ib hib hf hm
                obtain ⟨hpre, h2⟩ := hok bs v h1' rfl
                have hk0 : 0 < (bytesOf v).length := List.length_pos_iff.2 hb
                have hkc : (bytesOf v).length ≤ cap := Nat.le_trans hle (Nat.min_le_right _ _)
                have hkn' : (bytesOf v).length ≤ n := Nat.le_trans hle (Nat.min_le_left _ _)
                refine ⟨_, rd3_completed F q3 hr hn h1 hk0 hkn' hkc hpre, h.at hib hm .live rfl
                  (inOf_same hib hm) hother (fun r'' hr'' => rest_setRest_ne _ _ hr'')
                  (fun _ _ => ⟨_, rest_setRest_eq _ _ _, h2⟩) (fun _ h' => by cases h')
                  (fun h' => by cases h'.symm.trans hf) (fun _ _ => hf)⟩
            · -- too many bytes: the binding dies
              refine ⟨q3, rd3_blocked F q3 _ _, h.at hib hm .dead rfl (inOf_setMode_at hib .dead)
                hother (fun _ _ => rfl) (fun _ h' => by cases h') (fun _ h' => by cases h')
                hstdin hkn⟩
        · -- an error: the end
          rename_i e
          cases hf : ib.file
          · exact ⟨q3, rd3_none F q3 _ _ hr (hstdin hf), h.at hib hm .eof rfl
              (inOf_setMode_at hib .eof) hother (fun _ _ => rfl) (fun h' => by cases h'.symm.trans hf)
              (fun h' => by cases h'.symm.trans hf) hstdin hkn⟩
          · obtain ⟨bs, h1, h1'⟩ := h.live r ib hib hf hm
            obtain ⟨hbs, rfl⟩ := herr bs e h1' rfl
            subst hbs
            exact ⟨q3, rd3_dropped F q3 _ hr hn h1, h.at hib hm .eof rfl
              (inOf_setMode_at hib .eof) (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ h' => by cases h') (fun _ _ => h1) hstdin hkn⟩
        · -- another answer: nothing changes
          rename_i hno1 hno2
          have hq2 : q2' = q2 := hno (fun v h' => hno1 v h') (fun e h' => hno2 e h')
          subst hq2
          exact ⟨q3, rd3_blocked F q3 _ _, h⟩

end Silmaril.Wasi.Versions.P3OverP2
