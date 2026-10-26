module

public import Silmaril.Apps.Sha256sum.Process

/-! # A reference program for the stdin path, proved against the specification

Stage S1 of `binary.md`: `sha256sum` with no operand, a finite standard input, and a
standard output that is not full. `refMachine` is the simplest program that does this over
the system-call model of `Sha256sum.Process`: read standard input to the end in chunks of
32768 bytes, then write `hex(SHA-256(input)) ++ "  -\n"` to standard output, retrying
partial writes, then close descriptors 0, 1 and 2 and exit 0. This is the call sequence
`binary.md` measured for the binary `sha256sum-min` on this path.

`ref_satisfies` proves that every exiting run of it, under **every** chunking of the reads
and **every** split of the writes that `worldEnv` admits, shows exactly `sha256sum w`.
`ref_live` proves that no run gets stuck and every run is at most
`|stdin| + 73` steps long. The x86 binary is meant to be connected to this program by a
trace refinement (`Sys.TraceRefines`), which then gives the binary the same two
statements without re-proving anything about `sha256sum`; see `Sha256sum/Plan.lean`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys

open Silmaril.Apps.Sha256sum

inductive RefState where
  /-- Reading standard input; `acc` is what has been read. -/
  | reading (acc : Bytes)
  /-- Writing `pending` to standard output. -/
  | writing (pending : Bytes)
  /-- Closing descriptors `n`, …, 2. -/
  | closing (n : Nat)
  /-- An error reply the program does not handle (unreachable on the domain). -/
  | failed
  deriving DecidableEq, Repr

/-- The record for standard input in the default format. -/
def stdinRecord (data : Bytes) : Bytes := hexDigest data ++ lit "  -\n"

def refStep : RefState → Action RefState
  | .reading acc => .call (.read 0 32768) fun
      | .data [] => .writing (stdinRecord acc)
      | .data b => .reading (acc ++ b)
      | _ => .failed
  | .writing [] => .tau (.closing 0)
  | .writing p => .call (.write 1 p) fun
      | .ok n => .writing (p.drop n)
      | _ => .failed
  | .closing n =>
    if n < 3 then .call (.close n) fun
      | .ok _ => .closing (n + 1)
      | _ => .failed
    else .exit 0
  | .failed => .stuck

def refMachine : Machine := ⟨RefState, refStep⟩

/-- The domain of stage S1: no operand, finite standard input, standard output not full. -/
def StdinDom (w : World) : Prop :=
  w.argv.length = 1 ∧ (∃ b, w.stdin = .bytes b) ∧ w.stdoutFull = false

/-! ## The specification on the domain -/

theorem sha256sum_stdin (P : Bytes) (posix : Bool) (fs : Bytes → ReadResult) (b : Bytes) :
    sha256sum { argv := [P], posix, fs, stdin := .bytes b } =
      { stdout := stdinRecord b, stderr := [], status := 0 } := by
  simp only [sha256sum, World.argv0, World.prog, List.headD_cons, List.tail_cons]
  have hs : scan P posix [] = .done {} [] := rfl
  have hv : validate {} = none := rfl
  simp only [hs, hv, runMode, operandsOrStdin, ↓reduceIte, computeAll, computeOne, readPath,
    readStdin, Bool.and_true]
  simp [finish, St.emit, computeLine, recordBody, delim, stdinRecord, dash, problematic, lit,
    isProblemByte]

/-! ## Inversion of the environment -/

theorem write_stdout_inv {w : World} {k : KState} {p : Bytes} {r : Ret} {k' : KState}
    (h1 : k.fds 1 = some .stdout) (hf : w.stdoutFull = false)
    (h : WorldStep w k (.write 1 p) r k') : ∃ n, r = .ok n ∧ Accepts p n ∧ k' = k := by
  cases h with
  | writeOut _ _ ha => exact ⟨_, rfl, ha, rfl⟩
  | writeFull _ hfull => simp_all
  | writeErr hs _ => simp_all
  | writeBad hb => rcases hb with hb | hb | ⟨_, _, hb⟩ <;> simp_all

theorem read_stdin_inv {w : World} {k : KState} {rest : Bytes} {r : Ret} {k' : KState}
    (h0 : k.fds 0 = some .stdin) (hin : k.stdin = .bytes rest)
    (h : WorldStep w k (.read 0 32768) r k') :
    ∃ b, r = .data b ∧ Chunk rest 32768 b ∧ k' = { k with stdin := .bytes (rest.drop b.length) } := by
  cases h with
  | readStdin _ hin' hc => rw [hin] at hin'; cases hin'; exact ⟨_, rfl, hc, rfl⟩
  | readStdinDir _ hd => simp_all
  | readFile hs _ => simp_all
  | readPartial hs _ _ _ => simp_all
  | readFail hs _ => simp_all
  | readBad hb => rcases hb with hb | hb | hb <;> simp_all

theorem close_inv {w : World} {k : KState} {fd : Nat} {r : Ret} {k' : KState}
    (ho : k.fds fd ≠ none) (h : WorldStep w k (.close fd) r k') :
    r = .ok 0 ∧ k' = k.set fd none := by
  cases h with
  | closeOk _ => exact ⟨rfl, rfl⟩
  | closeBad hb => exact absurd hb ho

/-! ## Safety -/

theorem written_read (fd fd' count : Nat) (b : Bytes) (evs : List Event) :
    written fd ((.read fd' count, .data b) :: evs) = written fd evs := rfl

theorem written_close (fd fd' : Nat) (r : Ret) (evs : List Event) :
    written fd ((.close fd', r) :: evs) = written fd evs := by
  cases r <;> rfl

theorem written_write (fd : Nat) (p : Bytes) (n : Nat) (evs : List Event) :
    written fd ((.write 1 p, .ok n) :: evs) = (if 1 = fd then p.take n else []) ++ written fd evs :=
  rfl

theorem closing_exec {w : World} {s : refMachine.State} {k : KState} {evs : List Event} {n : Nat}
    (h : Exec refMachine (WorldStep w) s k evs n) :
    ∀ m, s = RefState.closing m → (∀ i, m ≤ i → i < 3 → k.fds i ≠ none) →
      written 1 evs = [] ∧ written 2 evs = [] ∧ n = 0 := by
  induction h with
  | exit hs =>
    intro m e _; subst e
    simp only [refMachine, refStep] at hs
    split_ifs at hs
    simp only [Action.exit.injEq] at hs; subst hs; simp [written]
  | tau hs _ _ =>
    intro m e _; subst e
    simp only [refMachine, refStep] at hs
    split_ifs at hs
  | @call s c f k r k' evs n hs he _ ih =>
    intro m e ho; subst e
    simp only [refMachine, refStep] at hs
    split_ifs at hs with hm
    cases hs
    obtain ⟨rfl, rfl⟩ := close_inv (ho m le_rfl hm) he
    rw [written_close, written_close]
    refine ih (m + 1) rfl fun i hi hi3 => ?_
    simp only [KState.set]
    rw [ite_eq_right (by omega)]
    exact ho i (by omega) hi3

theorem writing_exec {w : World} (hf : w.stdoutFull = false) {s : refMachine.State} {k : KState}
    {evs : List Event} {n : Nat} (h : Exec refMachine (WorldStep w) s k evs n) :
    ∀ p, s = RefState.writing p → k.fds 0 ≠ none → k.fds 1 = some .stdout → k.fds 2 ≠ none →
      written 1 evs = p ∧ written 2 evs = [] ∧ n = 0 := by
  induction h with
  | exit hs =>
    intro p e; subst e
    cases p <;> simp [refMachine, refStep] at hs
  | @tau s s' k evs n hs run _ =>
    intro p e h0 h1 h2; subst e
    cases p with
    | nil =>
      simp only [refMachine, refStep] at hs
      cases hs
      have := closing_exec run 0 rfl fun i _ hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact h0
        · simp [h1]
        · exact h2
      simpa using this
    | cons _ _ => simp [refMachine, refStep] at hs
  | @call s c f k r k' evs n hs he _ ih =>
    intro p e h0 h1 h2; subst e
    cases p with
    | nil => simp [refMachine, refStep] at hs
    | cons x xs =>
      simp only [refMachine, refStep] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨m, rfl, -, rfl⟩ := write_stdout_inv h1 hf he
      obtain ⟨h1', h2', hn⟩ := ih _ rfl h0 h1 h2
      refine ⟨?_, ?_, hn⟩
      · rw [written_write, ite_eq_left rfl, h1', List.take_append_drop]
      · rw [written_write, h2']; simp

theorem reading_exec {w : World} (hf : w.stdoutFull = false) {s : refMachine.State} {k : KState}
    {evs : List Event} {n : Nat} (h : Exec refMachine (WorldStep w) s k evs n) :
    ∀ acc rest, s = RefState.reading acc → k.stdin = .bytes rest → k.fds 0 = some .stdin →
      k.fds 1 = some .stdout → k.fds 2 ≠ none →
      written 1 evs = stdinRecord (acc ++ rest) ∧ written 2 evs = [] ∧ n = 0 := by
  induction h with
  | exit hs => intro acc rest e; subst e; simp [refMachine, refStep] at hs
  | tau hs _ _ => intro acc rest e; subst e; simp [refMachine, refStep] at hs
  | @call s c f k r k' evs n hs he run ih =>
    intro acc rest e hin h0 h1 h2; subst e
    simp only [refMachine, refStep] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b, rfl, ⟨hpre, -, hnil⟩, rfl⟩ := read_stdin_inv h0 hin he
    rw [written_read, written_read]
    cases b with
    | nil =>
      have hr : rest = [] := (hnil rfl).resolve_right (by decide)
      subst hr
      have := writing_exec hf run _ rfl (by simp [h0]) h1 h2
      simpa using this
    | cons x xs =>
      obtain ⟨t, rfl⟩ := hpre
      have := ih (acc ++ x :: xs) t rfl (by simp) h0 h1 h2
      simpa [List.append_assoc] using this

/-- **S1 at the Lean level.** Every exiting run of the reference program, under every read
chunking and write split the kernel admits, shows exactly `sha256sum w`. -/
theorem ref_satisfies :
    Satisfies refMachine WorldStep (fun _ => .reading []) StdinDom := by
  intro w ⟨hargv, ⟨b, hb⟩, hf⟩ evs n run
  obtain ⟨P, hP⟩ : ∃ P, w.argv = [P] := by
    match h : w.argv, hargv with
    | [P], _ => exact ⟨P, rfl⟩
  have hw : w = { argv := [P], posix := w.posix, fs := w.fs, stdin := .bytes b } := by
    cases w; simp_all
  obtain ⟨h1, h2, hn⟩ := reading_exec hf run [] b rfl (by simp [KState.init, hb])
    (by simp [KState.init]) (by simp [KState.init]) (by simp [KState.init])
  rw [hw, sha256sum_stdin]
  simp only [observe, h1, h2, hn, List.nil_append]

/-! ## Liveness within a budget -/

/-- The invariant of every reachable configuration on the domain. -/
def RefInv : refMachine.State → KState → Prop
  | .reading _, k => k.fds 0 = some .stdin ∧ k.fds 1 = some .stdout ∧ k.fds 2 ≠ none ∧
      ∃ rest, k.stdin = .bytes rest
  | .writing _, k => k.fds 0 ≠ none ∧ k.fds 1 = some .stdout ∧ k.fds 2 ≠ none
  | .closing n, k => ∀ i, n ≤ i → i < 3 → k.fds i ≠ none
  | .failed, _ => False

/-- A bound on the number of steps left. -/
def refPot : refMachine.State → KState → Nat
  | .reading _, k => (match k.stdin with | .bytes r => r.length | .dir => 0) + 73
  | .writing p, _ => p.length + 4
  | .closing n, _ => 3 - n
  | .failed, _ => 0

theorem stdinRecord_length (d : Bytes) : (stdinRecord d).length = 68 := by
  simp [stdinRecord, hexDigest_length, lit]

theorem ref_reach {w : World} (hf : w.stdoutFull = false) {n : Nat} {s : refMachine.State}
    {k : KState} {t : refMachine.State} {kt : KState}
    (h : Reach refMachine (WorldStep w) n s k t kt) :
    RefInv s k → n + refPot t kt ≤ refPot s k ∧ RefInv t kt := by
  induction h with
  | refl => intro hi; exact ⟨by simp, hi⟩
  | @tau n s s' k t kt hs _ ih =>
    intro hi
    rcases s with acc | p | m | _
    · simp [refMachine, refStep] at hs
    · cases p with
      | nil =>
        simp only [refMachine, refStep] at hs
        cases hs
        obtain ⟨h0, h1, h2⟩ := hi
        obtain ⟨hle, hinv⟩ := ih fun i _ hi3 => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          · exact h0
          · simp [h1]
          · exact h2
        refine ⟨?_, hinv⟩
        simp only [refPot, List.length_nil] at hle ⊢
        omega
      | cons _ _ => simp [refMachine, refStep] at hs
    · simp only [refMachine, refStep] at hs
      split_ifs at hs
    · exact hi.elim
  | @call n s c f k r k' t kt hs he _ ih =>
    intro hi
    rcases s with acc | p | m | _
    · obtain ⟨h0, h1, h2, ⟨rest, hin⟩⟩ := hi
      simp only [refMachine, refStep] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨b, rfl, ⟨hpre, -, hnil⟩, rfl⟩ := read_stdin_inv h0 hin he
      cases b with
      | nil =>
        have hr : rest = [] := (hnil rfl).resolve_right (by decide)
        subst hr
        obtain ⟨hle, hinv⟩ := ih ⟨by simp [h0], h1, h2⟩
        refine ⟨?_, hinv⟩
        simp only [refPot, stdinRecord_length, hin] at hle ⊢
        omega
      | cons x xs =>
        obtain ⟨u, rfl⟩ := hpre
        obtain ⟨hle, hinv⟩ := ih ⟨h0, h1, h2, ⟨u, by simp⟩⟩
        refine ⟨?_, hinv⟩
        simp only [refPot, hin] at hle ⊢
        simp at hle ⊢
        omega
    · obtain ⟨h0, h1, h2⟩ := hi
      cases p with
      | nil => simp [refMachine, refStep] at hs
      | cons x xs =>
        simp only [refMachine, refStep] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨m, rfl, ⟨hm, hpos⟩, rfl⟩ := write_stdout_inv h1 hf he
        obtain ⟨hle, hinv⟩ := ih ⟨h0, h1, h2⟩
        refine ⟨?_, hinv⟩
        have := hpos (by simp)
        simp only [refPot, List.length_drop] at hle ⊢
        omega
    · simp only [refMachine, refStep] at hs
      split_ifs at hs with hm3
      cases hs
      obtain ⟨rfl, rfl⟩ := close_inv (hi m le_rfl hm3) he
      obtain ⟨hle, hinv⟩ := ih fun i hi1 hi3 => by
        simp only [KState.set]
        rw [ite_eq_right (by omega)]
        exact hi i (by omega) hi3
      refine ⟨?_, hinv⟩
      simp only [refPot] at hle ⊢
      omega
    · exact hi.elim

/-- **S1 liveness.** No run of the reference program on the domain gets stuck, and every run
takes at most `|stdin| + 73` steps: one per nonempty read, one end-of-file read, at most 68
writes of the 68-byte record, one internal step and three closes. -/
theorem ref_live :
    Live refMachine WorldStep (fun _ => .reading []) StdinDom
      (fun w => (match w.stdin with | .bytes b => b.length | .dir => 0) + 73) := by
  intro w ⟨_, ⟨b, hb⟩, hf⟩ n t kt r
  have hi : RefInv (RefState.reading []) (KState.init w) :=
    ⟨by simp [KState.init], by simp [KState.init], by simp [KState.init],
      ⟨b, by simp [KState.init, hb]⟩⟩
  obtain ⟨hle, hinv⟩ := ref_reach hf r hi
  refine ⟨?_, ?_⟩
  · simp only [refPot, KState.init, hb] at hle ⊢
    omega
  · rcases t with acc | p | m | _
    · simp [refMachine, refStep]
    · cases p <;> simp [refMachine, refStep]
    · simp only [refMachine, refStep]; split_ifs <;> simp
    · exact hinv.elim

end Silmaril.Apps.Sha256sum.Sys
