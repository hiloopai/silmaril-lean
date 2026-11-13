module

public import Silmaril.Proofs.Machine.Process.LpsBridge.Write

/-!
# Proofs: the `read` arm of the open-machine/LPS bridge



* `readBytesAux_isSome_of_le`, `takeFrom_length_le`, `lenWord_toNat`: helpers.
* `modify_emit_pure_iff`: the tail of LPS's stdin arm in closed form.
* `read_stdin_iff`: on a descriptor bound to stdin (channel `0`), with `access_ok` and a
  writable range `buf .. buf + count`, the outcomes of LPS `read_spec` are exactly: `ret = 0`
  at count `0` or end of file; otherwise any non-empty prefix `bs` of stdin, at most the
  clamped count, delivered at `buf`, stdin advanced by `|bs|`, one `readEv 0` per byte.
* `read_dispatch`: number 0 of the native table is LPS `read_spec`.
* **`readArm_holds : Task.readArm`** (the corrected statement, see `Defs`).
* Non-vacuity and mutation (Z4 review): `readNv_model`, `readNv_input`, `readNv_hyps` (the
  hypotheses of `Task.readArm` hold on a concrete request: one byte from stdin `[7]`),
  `readNv_pos` (the read of `[7]` is an outcome), `readNv_wrongByte` (a read of `[8]` is
  not), `readNv_notZero` (the `ret = 0` outcome is not, stdin being non-empty).

The process-level `read` rule over the flag-oracle machine is the `readArm` of
`Silmaril.Machine.Process.IoSpec` (`armSound_read`); there is no `psafe_read` on the old machine.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Sys
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge

theorem readBytesAux_isSome_of_le (mp : Word → Option Byte) :
    ∀ (n : Nat) (a : Word) (k : Nat), (readBytesAux mp a n).isSome → k ≤ n →
      (readBytesAux mp a k).isSome
  | _, _, 0, _, _ => rfl
  | 0, _, _ + 1, _, hk => absurd hk (by omega)
  | n + 1, a, k + 1, h, hk => by
    simp only [readBytesAux] at h ⊢
    cases e : mp a with
    | none => rw [e] at h; cases h
    | some b =>
      rw [e] at h
      simp only [Option.isSome_map] at h ⊢
      exact readBytesAux_isSome_of_le mp n (a + 1) k h (by omega)

theorem takeFrom_length_le (s : InputStream) : ∀ (start k : Nat), (s.takeFrom start k).length ≤ k
  | _, 0 => by simp [InputStream.takeFrom]
  | start, k + 1 => by
    simp only [InputStream.takeFrom]
    cases s.byteAt start with
    | none => simp
    | some b => simpa using takeFrom_length_le s (start + 1) k

theorem lenWord_toNat {α : Type} (l : List α) (h : l.length < 2 ^ 64) :
    (lenWord l).toNat = l.length := by
  simp only [lenWord, zw]
  rw [BitVec.toNat_ofInt]
  have : ((l.length : Int) % (2 ^ 64 : Nat)) = l.length := Int.emod_eq_of_lt (by omega) (by omega)
  rw [this]; rfl

theorem rwCountClamp_le_toNat (count : Word) : rwCountClamp count ≤ (count.toNat : Int) :=
  Int.min_le_left _ _

theorem rwCountClamp_le_max (count : Word) : rwCountClamp count ≤ MAX_RW_COUNT :=
  Int.min_le_right _ _

theorem modify_emit_pure_iff {α : Type} (f : Model → Model) (evs : List Event) (r : α)
    (i : SyscallInput) (m : Model) (o : Outcome α) :
    (modify f >>= fun _ => emit evs >>= fun _ => Sys.pure r) i m o ↔ o = .ok r (f m) evs := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ e =>
    constructor
    · rintro ⟨u, m₁, e₁, e₂, hm, ⟨u', m₃, e₃, e₄, he, hp, rfl⟩, rfl⟩
      cases hm; cases he; cases hp; simp
    · intro h
      cases h
      exact ⟨(), f m, [], evs, rfl, ⟨(), f m, evs, [], rfl, rfl, by simp⟩, by simp⟩
  | unmodeled =>
    constructor
    · rintro (hm | ⟨u, m₁, e₁, hm, hr⟩)
      · cases hm
      · cases hm
        rcases hr with he | ⟨u', m₃, e₃, he, hp⟩
        · cases he
        · cases he; cases hp
    · intro h; cases h

theorem retOnly_iff (r : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    retOnly r i m o ↔ o = .ok (mkEffect r [] []) m [] := Iff.rfl

/-- **LPS `read` from stdin, closed form.** -/
theorem read_stdin_iff (fd buf count : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (lookup : fdLookup m.fds fd = some (.channel 0))
    (ok : accessOkb buf (uns count) = true) (writable : (readBytesMap i.wmem buf count).isSome) :
    readSpec fd buf count i m o ↔
      ((wIs0 count || m.stdin.atEof) = true ∧ o = .ok (mkEffect 0 [] []) m []) ∨
      ((wIs0 count || m.stdin.atEof) = false ∧
        ∃ bs : List Byte, (1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp count ∧
          (m.stdin.take bs.length).1 = bs) ∧
          o = .ok (mkEffect (lenWord bs) [(buf, bs)] [])
            (m.withStdin (m.stdin.take bs.length).2) (bs.map (.readEv 0))) := by
  have hcl := rwCountClamp_le_toNat count
  have hmax := rwCountClamp_le_max count
  have hmaxv : MAX_RW_COUNT = 0x7ffff000 := rfl
  -- every length up to `count` is writable
  have wr : ∀ k : Nat, k ≤ count.toNat → (readBytesAux i.wmem buf k).isSome :=
    fun k hk => readBytesAux_isSome_of_le _ _ _ _ writable hk
  unfold readSpec readSpecWith
  rw [input_getModel_iff]
  simp only [lookup, ok, Bool.not_true, Bool.false_eq_true, ite_false]
  have w0 : wIs0 (0 : Word) = true := rfl
  simp only [w0, Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases hc : wIs0 count = true
  · simp only [hc, ite_true, Bool.true_or, true_and, retOnly_iff, reduceCtorEq, false_and,
      or_false]
  · have hc' : wIs0 count = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false, Bool.false_or]
    have hpos : 1 ≤ count.toNat := by
      simp only [wIs0, beq_eq_false_iff_ne] at hc'
      have := BitVec.toNat_ne_iff_ne.mpr hc'
      simp at this; omega
    by_cases he : m.stdin.atEof = true
    · simp only [he, ite_true, retOnly_iff, true_and, reduceCtorEq, false_and, or_false]
    · have he' : m.stdin.atEof = false := by simpa using he
      simp only [he', Bool.false_eq_true, ite_false, false_and, false_or, true_and]
      obtain ⟨v1, h1⟩ := Option.isSome_iff_exists.mp (wr 1 (by simpa using hpos))
      rw [show readBytesMap i.wmem buf 1 = some v1 from h1]
      dsimp only
      have hlen : (m.stdin.takeZ (rwCountClamp count)).1.length ≤ count.toNat := by
        unfold InputStream.takeZ
        split
        · simp only [InputStream.take]
          have := takeFrom_length_le m.stdin 0 (rwCountClamp count).toNat
          omega
        · simp
      obtain ⟨v2, h2⟩ := Option.isSome_iff_exists.mp (wr _ hlen)
      have h2' : readBytesMap i.wmem buf (lenWord (m.stdin.takeZ (rwCountClamp count)).1) =
          some v2 := by
        unfold readBytesMap
        rw [lenWord_toNat _ (by have := count.isLt; omega)]
        exact h2
      rw [h2']
      dsimp only
      rw [bind_choose_iff]
      simp only [modify_emit_pure_iff]
      constructor
      · rintro ⟨bs, ⟨h1, h2, h3, -⟩, rfl⟩
        exact ⟨bs, ⟨h1, h2, h3⟩, rfl⟩
      · rintro ⟨bs, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨bs, ⟨h1, h2, h3, ?_⟩, rfl⟩
        unfold readBytesMap
        rw [lenWord_toNat _ (by omega)]
        exact wr _ (by omega)

/-- Number 0 of the native table is LPS `read_spec`. -/
theorem read_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 0) :
    NativeX86.extendedSyscallSpec i m o ↔
      readSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)
        (NativeX86.referenceInputFor ⟨63, 0, "read"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

/-- **The `read` arm** (the corrected `Task.readArm`). -/
theorem readArm_holds : Task.readArm := by
  intro i model o number lookup ok writable
  exact (read_dispatch i model o number).trans
    (read_stdin_iff _ _ _ _ model o lookup ok writable)

/-! ## Non-vacuity and mutation (Z4 review) -/

/-- Any model, with descriptor `0` bound to stdin and stdin the one byte `7`. -/
def readNv_model (m0 : Model) : Model :=
  ({ m0 with fd := ⟨[(0, .channel 0)], []⟩ } : Model).withStdin
    (InputStream.cons 7 InputStream.eof)

/-- `read(0, 0x1000, 1)` over an all-writable memory. -/
def readNv_input : SyscallInput := ⟨0, [0, 0x1000, 1], fun _ => none, fun _ => some 0⟩

theorem readNv_stdin (m0 : Model) :
    (readNv_model m0).stdin = InputStream.cons 7 InputStream.eof := rfl

theorem readNv_flag (m0 : Model) :
    (wIs0 (readNv_input.arg 2) || (readNv_model m0).stdin.atEof) = false := by
  rw [readNv_stdin]; decide

/-- The hypotheses of `Task.readArm` are satisfiable. -/
theorem readNv_hyps (m0 : Model) :
    readNv_input.sysno.toNat = 0 ∧
    fdLookup (readNv_model m0).fds (fd32 (readNv_input.arg 0)) = some (.channel 0) ∧
    accessOkb (readNv_input.arg 1) (uns (readNv_input.arg 2)) = true ∧
    (readBytesMap readNv_input.wmem (readNv_input.arg 1) (readNv_input.arg 2)).isSome := by
  refine ⟨rfl, ?_, by decide, by decide⟩
  simp [readNv_model, Model.fds, Model.withStdin, fdLookup, readNv_input, SyscallInput.arg,
    fd32]
  decide

/-- Reading the byte `7` is an outcome. -/
theorem readNv_pos (m0 : Model) : spec readNv_input (readNv_model m0)
    (.ok (mkEffect (lenWord [7]) [(0x1000, [7])] [])
      ((readNv_model m0).withStdin ((readNv_model m0).stdin.take 1).2) [.readEv 0 7]) := by
  obtain ⟨h0, h1, h2, h3⟩ := readNv_hyps m0
  exact (readArm_holds readNv_input (readNv_model m0) _ h0 h1 h2 h3).2
    (.inr ⟨readNv_flag m0, [7], ⟨by decide, by decide, by rw [readNv_stdin]; rfl⟩, rfl⟩)

/-- Mutation: reading a byte stdin does not hold is not an outcome. -/
theorem readNv_wrongByte (m0 : Model) : ¬ spec readNv_input (readNv_model m0)
    (.ok (mkEffect (lenWord [8]) [(0x1000, [8])] [])
      ((readNv_model m0).withStdin ((readNv_model m0).stdin.take 1).2) [.readEv 0 8]) := by
  obtain ⟨h0, h1, h2, h3⟩ := readNv_hyps m0
  rw [readArm_holds readNv_input (readNv_model m0) _ h0 h1 h2 h3]
  rintro (⟨h, _⟩ | ⟨_, bs, ⟨hl, _, hp⟩, ho⟩)
  · rw [readNv_flag] at h; cases h
  · simp only [Outcome.ok.injEq] at ho
    obtain ⟨_, _, he⟩ := ho
    cases bs with
    | nil => simp at hl
    | cons b t =>
      simp only [List.map_cons, List.cons.injEq] at he
      obtain ⟨hb, _⟩ := he
      cases hb
      rw [readNv_stdin] at hp
      revert hp; simp [InputStream.take, InputStream.takeFrom, InputStream.cons]

/-- Mutation: on non-empty stdin with a non-zero count, `ret = 0` is not an outcome. -/
theorem readNv_notZero (m0 : Model) :
    ¬ spec readNv_input (readNv_model m0) (.ok (mkEffect 0 [] []) (readNv_model m0) []) := by
  obtain ⟨h0, h1, h2, h3⟩ := readNv_hyps m0
  rw [readArm_holds readNv_input (readNv_model m0) _ h0 h1 h2 h3]
  rintro (⟨h, _⟩ | ⟨_, bs, ⟨hl, _, _⟩, ho⟩)
  · rw [readNv_flag] at h; cases h
  · simp only [Outcome.ok.injEq] at ho
    obtain ⟨_, _, he⟩ := ho
    cases bs with
    | nil => simp at hl
    | cons b t => simp at he

end Silmaril.Proofs.Machine.Process.LpsBridge
