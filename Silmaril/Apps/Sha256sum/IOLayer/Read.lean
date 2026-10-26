module

public import Silmaril.Apps.Sha256sum.IOLayer.Write

/-! # Decompiling a userspace input buffer: the read layer

Status: **VERIFIED** (no `sorry`, no new axioms).

`sha256sum-min`'s `--check` reader (`struct reader { fd, eof, err, pos, len, b[4096] }`,
`rd_fill`, `rd_getline`) is the classic input buffer: refill with one `read` when the buffer
is empty, hand out bytes one at a time, sticky end-of-file and error flags. `rd_getline` is
a loop of "next byte" on top of it.

* `RAction`/`RMachine`: an abstract program with the reader's operations as primitives:
  `getc` (the next byte, `none` at end of file or after an error), `rreset fd` (start
  reading a new descriptor) and `rquery` (the sticky flags), and every `OAction`.
* `rb A cap`: the **concrete reader** as an `OMachine` transformer, so the full layered
  program is `lb (rb A cap) 4096`: reader under the output buffer.
* `Src w k fd inp`: descriptor `fd` reads `inp` to its end under `WorldStep w` (standard
  input, or a regular file at its position).
* `RInv w k t x` (**the read-buffer invariant**): the abstract input left is
  `x = unread ++ inp`, where `unread` is the buffered part and `inp` is what the kernel still
  has; at end of file `inp = []`.
* `mexec_getc`: at the stream level, `getc` returns `x.head?` and leaves `x.tail`, **for
  every chunking** the kernel chooses. The kernel changes only on the reader's descriptor,
  and the outputs are unchanged.
* `mexec_drain`: a loop that reads with `getc` to end of file sees exactly the input.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys.IOLayer

open Silmaril.Apps.Sha256sum

def OAction.map {S T : Type} (f : S → T) : OAction S → OAction T
  | .tau s => .tau (f s)
  | .call c k => .call c (f ∘ k)
  | .exit n => .exit n
  | .stuck => .stuck
  | .putc c s => .putc c (f s)
  | .flush k => .flush (f ∘ k)
  | .query k => .query fun a b => f (k a b)
  | .writeAll fd b k => .writeAll fd b (f ∘ k)

inductive RAction (S : Type) where
  | base (a : OAction S)
  | getc (k : Option UInt8 → S)
  | rreset (fd : Nat) (s : S)
  | rquery (k : Bool → Option Errno → S)

structure RMachine where
  State : Type
  step : State → RAction State

/-- The reader's state next to the program's. -/
structure RSt (S : Type) where
  s : S
  fd : Nat
  unread : Bytes
  eof : Bool
  err : Option Errno

def rbStep (A : RMachine) (cap : Nat) (t : RSt A.State) : OAction (RSt A.State) :=
  match A.step t.s with
  | .base a => a.map fun s' => { t with s := s' }
  | .rreset fd s' => .tau { s := s', fd, unread := [], eof := false, err := none }
  | .rquery k => .tau { t with s := k t.eof t.err }
  | .getc k =>
    match t.unread with
    | c :: rest => .tau { t with s := k (some c), unread := rest }
    | [] =>
      if t.eof || t.err.isSome then .tau { t with s := k none }
      else .call (.read t.fd cap) fun
        | .data [] => { t with s := k none, eof := true }
        | .data (c :: rest) => { t with s := k (some c), unread := rest }
        | .err e => { t with s := k none, err := some e }
        | .ok _ => { t with s := k none, err := some .EIO }

/-- The reader around `A`, with `cap`-byte refills (4096 in the binary). -/
def rb (A : RMachine) (cap : Nat) : OMachine := ⟨RSt A.State, rbStep A cap⟩

/-! ## Sources under the world's kernel -/

/-- `fd` reads `inp` to its end. -/
def Src (k : KState) (fd : Nat) (inp : Bytes) : Prop :=
  (k.fds fd = some .stdin ∧ k.stdin = .bytes inp) ∨
    ∃ d pos, k.fds fd = some (.file (.ok d) pos) ∧ inp = d.drop pos

/-- The kernel changes only what the reader's descriptor reads. -/
def Frame (k k' : KState) (fd : Nat) : Prop :=
  (∀ i, i ≠ fd → k'.fds i = k.fds i) ∧ (k.fds fd = some .stdin → k'.fds fd = some .stdin)

theorem read_src_inv {w : World} {k : KState} {fd cnt : Nat} {inp : Bytes} {r : Ret}
    {k' : KState} (hs : Src k fd inp) (h : WorldStep w k (.read fd cnt) r k') :
    ∃ b, r = .data b ∧ Chunk inp cnt b ∧ Src k' fd (inp.drop b.length) ∧ Frame k k' fd := by
  rcases hs with ⟨h0, hin⟩ | ⟨d, pos, hf, rfl⟩
  · cases h with
    | readStdin _ hin' hc =>
      rw [hin] at hin'; cases hin'
      exact ⟨_, rfl, hc, .inl ⟨h0, rfl⟩, fun _ _ => rfl, fun h => h⟩
    | readStdinDir _ hd => simp_all
    | readFile hs _ => simp_all
    | readPartial hs _ _ _ => simp_all
    | readFail hs _ => simp_all
    | readBad hb => rcases hb with hb | hb | hb <;> simp_all
  · cases h with
    | @readFile _ _ _ _ _ b hs hc =>
      rw [hf] at hs; cases hs
      refine ⟨_, rfl, hc, .inr ⟨d, pos + b.length, by simp [KState.set], by simp [List.drop_drop]⟩,
        fun i hi => by simp [KState.set, hi], fun h => by simp_all⟩
    | readStdin hs _ _ => simp_all
    | readStdinDir hs _ => simp_all
    | readPartial hs _ _ _ => simp_all
    | readFail hs _ => simp_all
    | readBad hb => rcases hb with hb | hb | hb <;> simp_all

/-- **The read-buffer invariant**: the abstract input left is the buffered bytes followed by
what the kernel still has, which is nothing once end of file was seen. -/
def RInv {S : Type} (k : KState) (t : RSt S) (x : Bytes) : Prop :=
  t.err = none ∧ ∃ inp, Src k t.fd inp ∧ x = t.unread ++ inp ∧ (t.eof = true → inp = [])

/-! ## `getc` at the stream level -/

/-- **Read buffering.** `getc` returns the next byte of the abstract input and consumes it,
whatever chunk the kernel delivers. -/
theorem mexec_getc {A : RMachine} {rcap cap : Nat} (hcap : 0 < rcap) {w : World}
    {t : RSt A.State} {g : Option UInt8 → A.State} {x : Bytes} {buf : Bytes} {err : Bool}
    {k : KState} {aevs : List AEvent} {n : Nat} (hinv : RInv k t x) (hs : A.step t.s = .getc g)
    (h : MExec (rb A rcap) cap (WorldStep w) (.run t buf err) k aevs n) :
    ∃ t' k' aevs', MExec (rb A rcap) cap (WorldStep w) (.run t' buf err) k' aevs' n ∧
      t'.s = g x.head? ∧ t'.fd = t.fd ∧ RInv k' t' x.tail ∧ Frame k k' t.fd ∧
      ∀ fd, awritten fd aevs = awritten fd aevs' := by
  obtain ⟨herr, inp, hsrc, rfl, heof⟩ := hinv
  have frefl : Frame k k t.fd := ⟨fun _ _ => rfl, fun h => h⟩
  rcases hu : t.unread with _ | ⟨c, rest⟩
  · by_cases he : t.eof = true
    · have hi := heof he; subst hi
      have m := mexec_tau (A := rb A rcap) (s' := { t with s := g none })
        (by simp [rb, rbStep, hs, hu, he]) h
      exact ⟨_, k, aevs, m, rfl, rfl, ⟨herr, [], by simpa using hsrc, by simp [hu], fun _ => rfl⟩,
        frefl, fun _ => rfl⟩
    · have hst : (rb A rcap).step t = .call (.read t.fd rcap) fun
          | .data [] => { t with s := g none, eof := true }
          | .data (c :: rest) => { t with s := g (some c), unread := rest }
          | .err e => { t with s := g none, err := some e }
          | .ok _ => { t with s := g none, err := some .EIO } := by
        simp [rb, rbStep, hs, hu, he, herr]
      obtain ⟨r, k', aevs', he', rfl, m⟩ := mexec_call hst h
      obtain ⟨b, rfl, ⟨⟨u, rfl⟩, -, hnil⟩, hsrc', hfr⟩ := read_src_inv hsrc he'
      have hw : ∀ fd, awritten fd (.raw (.read t.fd rcap, .data b) :: aevs') = awritten fd aevs' :=
        fun fd => by simp [awritten, written]
      cases b with
      | nil =>
        have hu0 : u = [] := by simpa using (hnil rfl).resolve_right (by omega)
        subst hu0
        exact ⟨_, k', aevs', m, by simp, rfl, ⟨herr, [], by simpa using hsrc', by simp [hu],
          fun _ => rfl⟩, hfr, hw⟩
      | cons c rest =>
        refine ⟨_, k', aevs', m, by simp, rfl, ⟨herr, u, by simpa [List.drop_left'] using hsrc',
          by simp, fun h => ?_⟩, hfr, hw⟩
        simp at h; exact absurd h he
  · have m := mexec_tau (A := rb A rcap) (s' := { t with s := g (some c), unread := rest })
      (by simp [rb, rbStep, hs, hu]) h
    exact ⟨_, k, aevs, m, by simp, rfl, ⟨herr, inp, hsrc, by simp, heof⟩, frefl, fun _ => rfl⟩

/-- **A drain loop sees the whole input.** If `P acc` reads a byte with `getc`, appends it and
loops, and goes to `Q acc` at end of file, then every run from `P acc` with abstract input
`x` passes through `Q (acc ++ x)`, for every read chunking. -/
theorem mexec_drain {A : RMachine} {rcap cap : Nat} (hcap : 0 < rcap) {w : World}
    {P Q : Bytes → A.State}
    (hP : ∀ acc, A.step (P acc) = .getc fun | some c => P (acc ++ [c]) | none => Q acc)
    {buf : Bytes} {err : Bool} {n : Nat} :
    ∀ x acc t k aevs, t.s = P acc → RInv k t x →
      MExec (rb A rcap) cap (WorldStep w) (.run t buf err) k aevs n →
      ∃ t' k' aevs', MExec (rb A rcap) cap (WorldStep w) (.run t' buf err) k' aevs' n ∧
        t'.s = Q (acc ++ x) ∧ t'.fd = t.fd ∧ RInv k' t' [] ∧ Frame k k' t.fd ∧
        ∀ fd, awritten fd aevs = awritten fd aevs' := by
  intro x
  induction x with
  | nil =>
    intro acc t k aevs hs hinv m
    obtain ⟨t', k', aevs', m', hs', hfd, hinv', hfr, hw⟩ := mexec_getc hcap hinv
      (g := fun | some c => P (acc ++ [c]) | none => Q acc) (by rw [hs, hP]) m
    exact ⟨t', k', aevs', m', by simpa using hs', hfd, hinv', hfr, hw⟩
  | cons c cs ih =>
    intro acc t k aevs hs hinv m
    obtain ⟨t1, k1, aevs1, m1, hs1, hfd1, hinv1, hfr1, hw1⟩ :=
      mexec_getc hcap hinv (g := fun | some c => P (acc ++ [c]) | none => Q acc) (by rw [hs, hP]) m
    obtain ⟨t2, k2, aevs2, m2, hs2, hfd2, hinv2, hfr2, hw2⟩ :=
      ih (acc ++ [c]) t1 k1 aevs1 (by simpa using hs1) hinv1 m1
    refine ⟨t2, k2, aevs2, m2, by simpa using hs2, hfd2.trans hfd1, hinv2, ?_,
      fun fd => (hw1 fd).trans (hw2 fd)⟩
    rw [hfd1] at hfr2
    exact ⟨fun i hi => (hfr2.1 i hi).trans (hfr1.1 i hi), fun h => hfr2.2 (hfr1.2 h)⟩

end Silmaril.Apps.Sha256sum.Sys.IOLayer
