module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.ReadWrite
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Backing8

/-! # The descriptor relation and the system-call obligations (VERIFIED)

`StdRel inp message`: LPS keeps the input's file system; each standard descriptor `n ≤ 2` is
open on both sides (middle `stdin`/`stdout`/`stderr`, LPS channel `n`) or closed on both; the
middle stdin is the message after the bytes read so far and LPS's stdin is the same stream;
every mapped byte is below `TASK_SIZE` and every writable byte is backed.

`syscallObligations` (VERIFIED): under `StdRel`, every field of `SyscallObligations` holds,
for every stdin-tier world. At a pending pair the invariant (`Safe`) fixes the call: the
middle model can move (so the request decodes), and the step it makes keeps `Ok`, so the
event is `Allowed`: `read(0)` of a positive count into a writable buffer, `write(1)` of a
nonempty buffer, `close(fd ≤ 2)` or the exit; `pend_read`, `pend_write`, `pend_close` and
`pend_exit` do the rest. What remains of the bridge is the launch (`LaunchObligation`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli (Below Backed Safe accessOkb_of_permitted)
open Silmaril.Apps.Sha256sum.Sys (Src KState)

/-! ## The relation -/

/-- Standard descriptor `n` is `src` in the middle kernel and channel `n` in LPS, or closed in
both. -/
def StdFd (model : Model) (k : KState) (n : Nat) (src : Src) : Prop :=
  (k.fds n = some src ∧ fdLookup model.fds (BitVec.ofNat 64 n) = some (.channel (BitVec.ofNat 64 n))) ∨
    (k.fds n = none ∧ fdLookup model.fds (BitVec.ofNat 64 n) = none)

/-- The descriptor relation. -/
structure StdRel (inp : ProcInput) (message : List Byte) (model : Model) (g : GS) (h : List Ev) :
    Prop where
  fs : model.fs = inp.fs
  fd0 : StdFd model g.k 0 .stdin
  fd1 : StdFd model g.k 1 .stdout
  fd2 : StdFd model g.k 2 .stderr
  stdin : g.k.stdin = .bytes (toSpec (message.drop (stdinRead h).length))
  lpsStdin : model.stdin = InputStream.drop (InputStream.ofList message) (stdinRead h).length
  below : Below g.x.memory
  backed : Backed g.x.memory

/-! ## Small facts -/

theorem fdLookup_fdRemove (fds : List (Word × FdEntry)) (fd fd' : Word) :
    fdLookup (fdRemove fds fd) fd' = if fd' = fd then none else fdLookup fds fd' := by
  induction fds with
  | nil => simp [fdRemove, fdLookup]
  | cons p rest ih =>
    obtain ⟨k, e⟩ := p
    by_cases hk : k = fd
    · subst hk
      have : fdRemove ((k, e) :: rest) k = fdRemove rest k := by
        unfold fdRemove
        rw [List.filter_cons_of_neg (by simp)]
      rw [this, ih]
      by_cases h' : fd' = k
      · simp [h']
      · simp only [h', ite_false, fdLookup]
        have : (k == fd') = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
        simp [this]
    · have : fdRemove ((k, e) :: rest) fd = (k, e) :: fdRemove rest fd := by
        simp [fdRemove, hk]
      rw [this]
      simp only [fdLookup, ih]
      by_cases h' : k = fd'
      · subst h'
        simp [hk]
      · have : (k == fd') = false := beq_eq_false_iff_ne.mpr h'
        simp [this]

theorem stdinRead_snoc_read (h : List Ev) (n : Nat) (bs : List Byte) :
    (stdinRead (h ++ [.sys (.read 0 n) (.data (toSpec bs))])).length =
      (stdinRead h).length + bs.length := by
  simp [stdinRead, readBytes, toBitVec_toSpec]

theorem stdinRead_snoc_other (h : List Ev) (e : Ev) (other : readBytes e = []) :
    stdinRead (h ++ [e]) = stdinRead h := by
  simp [stdinRead, other]

/-- What a decoded call is. -/
theorem decode_call_cases {t : Silmaril.X86.State} {m : Silmaril.Process.Memory}
    {c : Apps.Sha256sum.Sys.Call} (h : Apps.Sha256sum.X86Sys.decode t m = some (.call c)) :
    ((t.read .rax).toNat = 0 ∧
        c = .read (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi)) (t.read .rdx).toNat) ∨
      ((t.read .rax).toNat = 1 ∧ ∃ bs, m.readBytes (t.read .rsi).toNat (t.read .rdx).toNat = some bs ∧
        c = .write (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi)) (bs.map Apps.Sha256sum.X86Sys.toU8)) ∨
      ((t.read .rax).toNat = 3 ∧ c = .close (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi))) ∨
      ((t.read .rax).toNat = 257 ∧ ∃ p, c = .openat p) := by
  unfold Apps.Sha256sum.X86Sys.decode at h
  dsimp only at h
  split_ifs at h with h0 h1 h3 h12 h257 h60
  · cases h; exact .inl ⟨h0, rfl⟩
  · cases hb : m.readBytes (t.read .rsi).toNat (t.read .rdx).toNat with
    | none => rw [hb] at h; cases h
    | some bs =>
      rw [hb] at h; cases h
      exact .inr (.inl ⟨h1, bs, rfl, rfl⟩)
  · cases h; exact .inr (.inr (.inl ⟨h3, rfl⟩))
  · cases h
  · cases hp : Apps.Sha256sum.X86Sys.cstring m (t.read .rsi).toNat Silmaril.Process.addressLimit with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h; cases h
      exact .inr (.inr (.inr ⟨h257, p, rfl⟩))
  · cases h

theorem decode_exit_number {t : Silmaril.X86.State} {m : Silmaril.Process.Memory} {n : Nat}
    (h : Apps.Sha256sum.X86Sys.decode t m = some (.exit n)) :
    (t.read .rax).toNat = 60 ∨ (t.read .rax).toNat = 231 := by
  unfold Apps.Sha256sum.X86Sys.decode at h
  dsimp only at h
  by_cases h0 : (t.read .rax).toNat = 0
  · simp [h0] at h
  by_cases h1 : (t.read .rax).toNat = 1
  · simp [h1] at h
  by_cases h3 : (t.read .rax).toNat = 3
  · simp [h3] at h
  by_cases h12 : (t.read .rax).toNat = 12
  · simp [h12] at h
  by_cases h257 : (t.read .rax).toNat = 257
  · revert h
    simp only [h257]
    split_ifs <;> simp
  by_contra hx
  simp [h0, h1, h3, h12, h257, hx] at h

/-- The relation survives a retiring instruction. -/
theorem StdRel.retire {inp : ProcInput} {message : List Byte} {model : Model} {g : GS} {h : List Ev}
    {core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory} (r : StdRel inp message model g h)
    (step : CLI.X86Linux8.step g.x.core g.x.memory = .retired core' memory') :
    StdRel inp message model { g with x := { g.x with core := core', memory := memory' } } h :=
  have gr := grows_of_step8 step
  { r with below := r.below.of_grows gr, backed := r.backed.of_grows gr }

/-! ## The pending call -/

section Pending

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {message : List Byte} {c : Config (machine oracle)} {g : GS} {h : List Ev}
  {w : Apps.Sha256sum.World}

/-- **Every call from a pending pair under `StdRel`.** -/
theorem pend_std (p : PendRel (StdRel inp message) c g h)
    (safe : Safe (GStep w) (Ok message) (Done message) g h) (notFull : w.stdoutFull = false) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, GStep w g es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        Rel (StdRel inp message) c' y (h ++ es)) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∃ es y, GStep w g es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        Rel (StdRel inp message) c' y (h ++ es)) := by
  have r := p.model
  have trap := step8_trap p.trap
  obtain ⟨e, y, s⟩ := safe.2.1
  have next := safe.2.2 e y s
  cases s with
  | retire _ _ step => rw [trap] at step; cases step
  | exit _ _ step dec =>
    rw [trap] at step; cases step
    have number := decode_exit_number dec
    obtain ⟨a, b, c₃⟩ := pend_exit (refusals := refusals) (inp := inp) (w := w) p number r.fs
    refine ⟨fun evs st s => ?_, b, ?_⟩
    · obtain ⟨c', e', es, y', gs, flat, ex⟩ := a evs st s
      exact ⟨c', e', es, y', gs, flat, .inr ex⟩
    · obtain ⟨c', s', ex⟩ := c₃ _ _ (gstep_exit p number)
      exact ⟨_, _, gstep_exit p number, c', s', .inr ex⟩
  | @call _ call0 r0 k0 r11 _ _ step dec rb ws =>
    rw [trap] at step; cases step
    have allowed : Allowed (.sys call0 r0) := by
      rcases next with ok | done
      · exact ok.2.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
      · exact absurd done.1 (by simp)
    have rd : ∀ reg, ({ g.x.core with rip := g.x.core.rip + 2 } : Silmaril.X86.State).read reg =
        g.x.core.read reg := fun _ => rfl
    rcases decode_call_cases dec with ⟨number, rfl⟩ | ⟨number, bs, loaded, rfl⟩ |
      ⟨number, rfl⟩ | ⟨-, p0, rfl⟩
    · -- `read`
      simp only [rd] at number allowed rb ws
      obtain ⟨fd0, count, b, rfl⟩ := allowed
      rw [fd0] at ws
      have open0 : g.k.fds 0 = some .stdin := by
        rcases r.fd0 with ⟨o, -⟩ | ⟨none0, -⟩
        · exact o
        · cases ws <;> simp_all
      have lookup : fdLookup c.model.fds 0 = some (.channel 0) := by
        rcases r.fd0 with ⟨-, l⟩ | ⟨none0, -⟩
        · exact l
        · rw [none0] at open0; cases open0
      exact pend_read (w := w) (inp := inp) (refusals := refusals) p number fd0 lookup open0
        (stdinRead h).length r.stdin r.lpsStdin count rb
        (accessOkb_of_permitted r.below rb count) r.backed
        (fun r11 bs memory' written => by
          have gr := Silmaril.X86.Ext.Backing.Grows.of_stored
            (Silmaril.X86.Ext.Stored.of_writeBytes written)
          refine ⟨r.fs, r.fd0, r.fd1, r.fd2, ?_, ?_, r.below.of_grows gr, r.backed.of_grows gr⟩
          · show Apps.Sha256sum.Stdin.bytes _ = _
            rw [stdinRead_snoc_read]
          · show InputStream.drop _ _ = _
            rw [stdinRead_snoc_read])
    · -- `write`
      simp only [rd] at number allowed loaded ws
      obtain ⟨fd1, nonempty, n, rfl⟩ := allowed
      rw [fd1] at ws
      have open1 : g.k.fds 1 = some .stdout := by
        rcases r.fd1 with ⟨o, -⟩ | ⟨none1, -⟩
        · exact o
        · cases ws <;> simp_all
      have lookup : fdLookup c.model.fds 1 = some (.channel 1) := by
        rcases r.fd1 with ⟨-, l⟩ | ⟨none1, -⟩
        · exact l
        · rw [none1] at open1; cases open1
      have bytes_len : bs.length = (g.x.core.read .rdx).toNat :=
        (Silmaril.X86.Memory.readWith_eq_some_iff.mp loaded).1
      have count_pos : 0 < (g.x.core.read .rdx).toNat := by
        rw [← bytes_len]
        cases bs with
        | nil => exact absurd rfl nonempty
        | cons => simp
      have modeled : modeledRwRangeWith accessOkb (g.x.core.read .rsi) (g.x.core.read .rdx) =
          true := by
        unfold modeledRwRangeWith
        by_cases small : uns (g.x.core.read .rdx) ≤ rwBytesMax
        · simp [modeledRwCount, small]
        · have perm := (Silmaril.X86.Memory.readWith_eq_some_iff.mp loaded).2.1
          simp [accessOkb_of_permitted r.below perm count_pos]
      exact pend_write (w := w) (inp := inp) (refusals := refusals) p number fd1 lookup open1
        notFull loaded count_pos modeled
        (fun r11 n => ⟨r.fs, r.fd0, r.fd1, r.fd2,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.stdin,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.lpsStdin, r.below, r.backed⟩)
    · -- `close`
      simp only [rd] at number allowed ws
      have small : Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi) ≤ 2 := allowed
      set fd := Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi) with hfd
      have lpsFd : fd32 (g.x.core.read .rdi) = BitVec.ofNat 64 fd := fd32_eq _
      have std : ∀ n, n ≤ 2 → ∃ src, StdFd c.model g.k n src := by
        intro n hn
        interval_cases n
        · exact ⟨_, r.fd0⟩
        · exact ⟨_, r.fd1⟩
        · exact ⟨_, r.fd2⟩
      have corr : (fdLookup c.model.fds (fd32 (g.x.core.read .rdi))).isSome =
          (g.k.fds fd).isSome := by
        obtain ⟨src, hs⟩ := std fd small
        rw [lpsFd]
        rcases hs with ⟨o, l⟩ | ⟨o, l⟩ <;> simp [o, l]
      have ofNat_inj : ∀ a b : Nat, a ≤ 2 → b ≤ 2 →
          (BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b) := by
        intro a b ha hb
        constructor
        · intro e
          have := congrArg BitVec.toNat e
          simp only [BitVec.toNat_ofNat] at this
          omega
        · rintro rfl; rfl
      -- closing `fd` keeps the relation
      have keepStd : ∀ n src, n ≤ 2 → StdFd c.model g.k n src →
          StdFd (c.model.withFds (fdRemove c.model.fds (fd32 (g.x.core.read .rdi))))
            (g.k.set fd none) n src := by
        intro n src hn hs
        unfold StdFd
        show ((if n = fd then none else g.k.fds n) = some src ∧ _) ∨
          ((if n = fd then none else g.k.fds n) = none ∧ _)
        rw [lpsFd]
        show (_ ∧ fdLookup (fdRemove c.model.fds _) _ = _) ∨ (_ ∧ fdLookup (fdRemove c.model.fds _) _ = _)
        rw [fdLookup_fdRemove]
        by_cases e : n = fd
        · subst e; simp
        · have e' : ¬ BitVec.ofNat 64 n = BitVec.ofNat 64 fd := fun h' =>
            e ((ofNat_inj n fd hn small).1 h')
          simp only [e, e', ite_false]
          exact hs
      refine pend_close (w := w) (inp := inp) (refusals := refusals) p number corr ?_ ?_
      · intro r11 _
        exact ⟨r.fs, keepStd 0 _ (by omega) r.fd0, keepStd 1 _ (by omega) r.fd1,
          keepStd 2 _ (by omega) r.fd2,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.stdin,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.lpsStdin, r.below, r.backed⟩
      · intro r11 _
        exact ⟨r.fs, r.fd0, r.fd1, r.fd2,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.stdin,
          by rw [stdinRead_snoc_other _ _ rfl]; exact r.lpsStdin, r.below, r.backed⟩
    · -- `openat` is not allowed
      exact absurd allowed id

end Pending

/-- **The system-call obligations hold under `StdRel` (VERIFIED)**, on every world whose
standard output is not full (every stdin-tier world). -/
theorem syscallObligations {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg}
    {inp : ProcInput} {message : List Byte} {w : Apps.Sha256sum.World}
    (notFull : w.stdoutFull = false) :
    SyscallObligations oracle refusals inp message w (StdRel inp message) where
  retire := fun r step => r.retire step
  step := fun p safe s => (pend_std p safe notFull).1 _ _ s
  progress := fun p safe => (pend_std p safe notFull).2.1
  back := fun p safe => (pend_std p safe notFull).2.2

/-! ## What remains: the launch -/

/-- An LPS launch related to a middle-model launch under `StdRel`. -/
def LaunchSim (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (prog : List Byte) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (g₀ : GS), Launch (world [prog] posix fs message) g₀ ∧
      Rel (StdRel inp message) (initial oracle limit en inp) g₀ []

/-- The launch obligation: every admissible LPS launch is related to a middle-model launch. -/
def LaunchObligation : Prop :=
  ∀ oracle limit en inp message, Admissible oracle en inp message →
    LaunchSim oracle limit en inp message

/-- **Reduction (VERIFIED).** The launch obligation gives the bridge. -/
theorem bridge_of_launch (h : LaunchObligation) : BridgeSegment :=
  bridge_of_syscallSim fun oracle refusals limit en inp message admissible => by
    obtain ⟨prog, posix, fs, g₀, launch, related⟩ := h oracle limit en inp message admissible
    exact ⟨prog, posix, fs, g₀, StdRel inp message, launch, related, syscallObligations rfl⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
