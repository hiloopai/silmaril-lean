module

public import Silmaril.Process.LPS.Probes.KitReturns

/-! # Probe kit: reading stdin into the image

`Kit.lean` keeps the memory the initial memory `Probe.mem0`. A `read` of stdin
stores the bytes it delivers, so after it the configuration holds
`Probe.written boff bs`: the initial memory with `bs` installed at segment
offset `boff` (a buffer in an `rwx` image). This module has

* the hub's x86-64 reading of `read` from stdin (`read_stdin_iff`, the channel-0
  branch of LPS `Sys/Fs/ReadWrite.v:345` `read_spec`): any nonempty prefix of the
  stream of at most `count` bytes (`ReadPrefix`: a short read delivers fewer),
  one `readEv` per byte, and the bytes written to the buffer;
* the step rules for that read (`exec_read`, `run_read`), and instruction, trap,
  exit and channel-write rules over any memory (`exec_instrW`, …), with the
  facts that `Probe.written` keeps every code window before the buffer
  (`written_fetch`) and reads back the delivered bytes (`written_source`);
* `Probe.withStdin`: the probe launched with any other stdin stream.

The tactics `probe_instrW`, `probe_trapW` and `probe_exitW` are `probe_instr`,
`probe_trap` and `probe_exit` after the read; `probe_read off count` steps the
read itself and leaves `∀ bs, ReadPrefix … bs → …`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Machines.X86Launch
open Silmaril.Process (Memory Access)

/-- The reference-sanctioned results of a read of the stream `s` with clamped
count `count`: a nonempty prefix of the stream of at most `count` bytes. A read
that returns fewer bytes than available is a short read. -/
def ReadPrefix (s : InputStream) (count : Nat) (bs : List Byte) : Prop :=
  bs ≠ [] ∧ bs.length ≤ count ∧ (s.take bs.length).1 = bs

instance (s : InputStream) (count : Nat) (bs : List Byte) : Decidable (ReadPrefix s count bs) := by
  unfold ReadPrefix
  infer_instance

theorem InputStream.takeFrom_length_le (s : InputStream) (start k : Nat) :
    (s.takeFrom start k).length ≤ k := by
  induction k generalizing start with
  | zero => simp [InputStream.takeFrom]
  | succ k ih =>
    unfold InputStream.takeFrom
    split
    · simp
    · simp only [List.length_cons]
      have := ih (start + 1)
      omega

theorem InputStream.take_one_ne_nil (s : InputStream) (notEof : s.atEof = false) :
    (s.take 1).1 ≠ [] := by
  unfold InputStream.atEof at notEof
  unfold InputStream.take InputStream.takeFrom
  cases h : s.byteAt 0 with
  | none => simp [h] at notEof
  | some b => simp

theorem InputStream.take_one_length (s : InputStream) (notEof : s.atEof = false) :
    (s.take 1).1.length = 1 := by
  have bound := InputStream.takeFrom_length_le s 0 1
  have nonempty := InputStream.take_one_ne_nil s notEof
  have : (s.take 1).1.length ≠ 0 := fun h => nonempty (List.eq_nil_of_length_eq_zero h)
  change (s.takeFrom 0 1).length ≤ 1 at bound
  change (s.takeFrom 0 1).length = 1
  change (s.takeFrom 0 1).length ≠ 0 at this
  omega

theorem take_take_length {s : InputStream} {bs : List Byte} (taken : (s.take bs.length).1 = bs) :
    (s.take bs.length).1 = bs := taken

theorem lenWord_toNat {α : Type} (l : List α) (small : l.length < 2 ^ 64) :
    (lenWord l).toNat = l.length := by
  unfold lenWord zw
  simp only [BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem rwCountClamp_lenWord {α : Type} (l : List α) (small : l.length ≤ 131072) :
    rwCountClamp (lenWord l) = l.length := by
  unfold rwCountClamp uns
  rw [lenWord_toNat l (by omega)]
  unfold MAX_RW_COUNT
  omega

/-! ## The x86-64 `read` of stdin -/

section Arm

variable (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)

/-- `read_spec` with x86-64 `access_ok` on the stdin channel with a nonempty stream, an accessible
buffer whose first `count` bytes are writable and a positive clamped count. -/
theorem read_stdin_iff (number : input.sysno = 0)
    (clear : NativeX86.All.boundarySuspect 0 input = false)
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel 0))
    (accessible : accessOkbX86 (input.arg 1) (uns (input.arg 2)) = true)
    {count : Nat} (clamp : rwCountClamp (input.arg 2) = count) (positive : 0 < count)
    (small : count ≤ 131072) (notEof : model.stdin.atEof = false)
    (writable : ∀ k ≤ count, (readBytesAux input.wmem (input.arg 1) k).isSome = true) :
    spec input model outcome ↔
      ∃ bs, ReadPrefix model.stdin count bs ∧
        outcome = .ok (mkEffect (lenWord bs) [(input.arg 1, bs)] [])
          (model.withStdin (model.stdin.take bs.length).2) (bs.map (.readEv 0)) := by
  have zeroCount : wIs0 (input.arg 2) = false := by
    unfold wIs0
    by_contra zero
    simp only [beq_eq_false_iff_ne, ne_eq, not_not] at zero
    rw [zero] at clamp
    unfold rwCountClamp uns at clamp
    simp at clamp
    omega
  have writableWord (l : List Byte) (bound : l.length ≤ count) :
      (readBytesMap input.wmem (input.arg 1) (lenWord l)).isSome = true := by
    unfold readBytesMap
    rw [lenWord_toNat l (by omega)]
    exact writable _ bound
  obtain ⟨first, firstOk⟩ := Option.isSome_iff_exists.mp (writable 1 positive)
  have takeBound : (model.stdin.takeZ (count : Int)).1.length ≤ count := by
    unfold InputStream.takeZ
    split
    · simp only [Int.toNat_natCast]
      exact InputStream.takeFrom_length_le model.stdin 0 count
    · simp
  obtain ⟨whole, wholeOk⟩ := Option.isSome_iff_exists.mp
    (writableWord (model.stdin.takeZ (count : Int)).1 takeBound)
  have firstMap : readBytesMap input.wmem (input.arg 1) 1#64 = some first := firstOk
  have count0 : ¬ input.arg 2 = 0#64 := by
    intro zero
    simp [wIs0, zero] at zeroCount
  rw [dispatches_read.spec_iff (by rw [number]; rfl) clear model outcome]
  change readSpecX86 (fd32 (input.arg 0)) (input.arg 1) (input.arg 2) _ model outcome ↔ _
  cases outcome with
  | ok effect model' evs =>
    simp [readSpecX86, readSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, wIs0, count0, accessible,
      notEof, firstMap, clamp, wholeOk, Sys.choose, Sys.modify, Sys.emit, Sys.pure]
    constructor
    · rintro ⟨bs, ⟨one, le, taken, _⟩, ⟨rfl, rfl⟩, rfl⟩
      exact ⟨bs, ⟨fun empty => by simp [empty] at one, le, taken⟩, rfl, rfl, rfl⟩
    · rintro ⟨bs, ⟨nonempty, le, taken⟩, rfl, rfl, rfl⟩
      exact ⟨bs, ⟨List.length_pos_iff.mpr nonempty, le, taken, writableWord bs le⟩, ⟨rfl, rfl⟩, rfl⟩
  | unmodeled =>
    simp [readSpecX86, readSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, wIs0, count0, accessible,
      notEof, firstMap, clamp, wholeOk, Sys.choose, Sys.modify, Sys.emit, Sys.pure]

end Arm

namespace Probe

variable (P : Probe) {refused : RefusalFilter}

/-- The probe launched with another stdin stream. -/
def withStdin (s : InputStream) : Probe := { P with input := { P.input with stdin := s } }

/-- A configuration over any memory (`Probe.cfg` is the one over `Probe.mem0`). -/
abbrev cfgAt (core : Silmaril.X86.State) (mem : Memory) (pending : Option Word) (model : Model) :
    Config x86ExtNative :=
  ⟨⟨⟨core, mem⟩, pending⟩, model⟩

/-- The initial memory after a syscall stored `bs` at segment offset `boff`. -/
def written (boff : Nat) (bs : List Byte) : Memory :=
  ⟨P.mem0.regions, installWrapping P.mem0.bytes (P.base + boff) bs⟩

/-- The written memory has the regions of the initial memory. (Stated by
unfolding: a definitional check against `P.mem0` would evaluate its 8 MiB stack.) -/
theorem written_permits (boff : Nat) (bs : List Byte) (access : Access) (address : Nat) :
    (P.written boff bs).permits access address = P.mem0.permits access address := by
  unfold Memory.permits
  dsimp only [written]

/-! ### The written memory -/

section Written

variable {P} [checked : Checked P]

theorem readBacking_congr (first second : Silmaril.Process.ByteMemory) (address length : Nat)
    (same : ∀ k < length, first.get? (address + k) = second.get? (address + k)) :
    Silmaril.Process.Memory.readBacking first address length =
      Silmaril.Process.Memory.readBacking second address length := by
  induction length generalizing address with
  | zero => rfl
  | succ length ih =>
    have head := same 0 (by omega)
    simp only [Nat.add_zero] at head
    have tail := ih (address + 1) (fun k bound => by
      have := same (k + 1) (by omega)
      rwa [show address + (k + 1) = address + 1 + k by omega] at this)
    simp only [Silmaril.Process.Memory.readBacking, head, tail]

/-- Every code window before the buffer is unchanged. -/
theorem written_fetch {boff off len : Nat} {bs : List Byte}
    (small : boff + bs.length ≤ P.size) (start : off < P.size) (before : off + len ≤ boff) :
    (P.written boff bs).fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len) := by
  have read0 := P.mem0_window .execute (by decide) off len start (by omega)
  have fits := P.size_lt checked.layout
  unfold Memory.fetchBytes Memory.readWith Memory.checkSpan at *
  simp only [written_permits]
  dsimp only [written]
  rw [readBacking_congr _ P.mem0.bytes _ _ (fun k bound =>
    installWrapping_outside _ _ _ _ (by omega) (by omega))]
  exact read0

/-- The delivered bytes are read back from the buffer. -/
theorem written_source {boff : Nat} {bs : List Byte} (small : boff + bs.length ≤ P.size) :
    readableBytesAux (viewByte (P.written boff bs) .read) (BitVec.ofNat 64 (P.base + boff)) bs.length = bs := by
  have fits := P.size_lt checked.layout
  suffices general : ∀ k ≤ bs.length,
      readableBytesAux (viewByte (P.written boff bs) .read) (BitVec.ofNat 64 (P.base + boff + k))
        (bs.length - k) = bs.drop k by
    simpa using general 0 (Nat.zero_le _)
  intro k bound
  generalize remaining : bs.length - k = n
  induction n generalizing k with
  | zero =>
    have : k = bs.length := by omega
    subst this
    simp [readableBytesAux]
  | succ n ih =>
    have inside : k < bs.length := by omega
    have address : (BitVec.ofNat 64 (P.base + boff + k)).toNat = P.base + boff + k := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have view : viewByte (P.written boff bs) .read (BitVec.ofNat 64 (P.base + boff + k)) = some bs[k] := by
      unfold viewByte
      rw [address, written_permits, P.mem0_permits .read (by decide) _ (by omega) (by omega)]
      simp only [ite_true]
      rw [← Std.ExtHashMap.get?_eq_getElem?]
      dsimp only [written]
      exact installWrapping_get _ _ _ _ inside (by omega)
    simp only [readableBytesAux, view]
    have next : BitVec.ofNat 64 (P.base + boff + k) + 1 = BitVec.ofNat 64 (P.base + boff + (k + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    rw [next, ih (k + 1) (by omega) (by omega), List.drop_eq_getElem_cons inside]

/-- In an `rwx` image the bytes of the segment are writable. -/
theorem wmem_readBytesAux (rwx : P.programHeader.flags = 7) (boff k : Nat) (fits : boff + k ≤ P.size) :
    (readBytesAux (viewByte P.mem0 .write) (BitVec.ofNat 64 (P.base + boff)) k).isSome = true := by
  have sizes := checked.layout.sizes
  have bound := P.size_lt checked.layout
  induction k generalizing boff with
  | zero => rfl
  | succ k ih =>
    have address : (BitVec.ofNat 64 (P.base + boff)).toNat = P.base + boff := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have allowed : (segmentPermissions P.segment).allows .write = true := by
      simp [segmentPermissions, Silmaril.Process.Permissions.allows, P.segment_writable, rwx]
    have view : viewByte P.mem0 .write (BitVec.ofNat 64 (P.base + boff)) = some P.bytes[boff] := by
      unfold viewByte
      rw [address, permits_of_allows P.mem0 P.mem0_region .write allowed _ (by omega) (by omega)]
      simp only [ite_true]
      rw [← Std.ExtHashMap.get?_eq_getElem?]
      exact P.mem0_get boff (by omega)
    simp only [readBytesAux, view]
    have next : BitVec.ofNat 64 (P.base + boff) + 1 = BitVec.ofNat 64 (P.base + (boff + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    rw [next]
    have rest := ih (boff + 1) (by omega)
    revert rest
    cases readBytesAux (viewByte P.mem0 .write) (BitVec.ofNat 64 (P.base + (boff + 1))) k <;> simp

end Written

/-! ### Rules over any memory -/

section Rules

variable {P}

theorem resume_effectW (core : Silmaril.X86.State) (mem mem' : Memory) (n : Word) (other : n ≠ 158)
    (ret : Word) (writes : List (Word × List Byte)) (copyins : List (Word × Nat))
    (applied : applyMemoryEffect mem ((mkEffect ret writes []).withCopyins copyins) = mem') :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, mem⟩, some n⟩
      ((mkEffect ret writes []).withCopyins copyins)) = ⟨⟨resume core ret, mem'⟩, none⟩ := by
  have notArch : ¬ (some n = some (158 : Word) ∧ core.read .rdi = 0x1002 ∧ ret = 0) :=
    fun h => other (Option.some.inj h.1)
  change x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, mem⟩, some n⟩ _) = _
  unfold x86ApplyEffectNative
  split
  · next h => exact absurd h notArch
  · subst applied
    rfl

theorem resume_plainM (core : Silmaril.X86.State) (mem mem' : Memory) (n : Word) (other : n ≠ 158)
    (ret : Word) (writes : List (Word × List Byte))
    (applied : applyMemoryEffect mem (mkEffect ret writes []) = mem') :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, mem⟩, some n⟩ (mkEffect ret writes [])) =
      ⟨⟨resume core ret, mem'⟩, none⟩ :=
  resume_effectW core mem mem' n other ret writes [] applied

theorem accountStep_instrW {mem : Memory} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem) :
    accountStep x86ExtNative P.segs ⟨⟨core, mem⟩, none⟩ model = .ok (⟨⟨core', mem⟩, none⟩, model) := by
  apply Progress.accountStep_of_noLazy _ _ model _ lazy
  change x86NativeStep ⟨⟨core, mem⟩, none⟩ = _
  rw [x86NativeStep_of_fetch (s := ⟨⟨core, mem⟩, none⟩)
    (show mem.fetchBytes core.rip.toNat 2 ≠ some [0x0f, 0x05] by
      rw [rip, prefix2]
      exact fun h => notSyscall (Option.some.inj h))
    (show mem.fetchBytes core.rip.toNat len = some _ by rw [rip, fetched])
    decoded]
  change x86ExecResult _ (Silmaril.X86.Ext.exec instruction core mem len) = _
  rw [exec]
  rfl

theorem sstep_instrM_iff {mem : Memory} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core mem none model) evs target ↔
      evs = [] ∧ target = .next (cfgAt core' mem none model) := by
  have account := accountStep_instrW lazy rip notSyscall fetched prefix2 decoded exec
  constructor
  · intro step
    cases step with
    | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
    | instrFault _ _ h => rw [account] at h; cases h
    | instrUnmodeled _ _ h => rw [account] at h; cases h
    | syscall _ p => cases p
    | syscallMaterializationFault _ p => cases p
    | exit _ p => cases p
    | killed _ p => cases p
    | syscallUnmodeled _ p => cases p
  · rintro ⟨rfl, rfl⟩
    exact .instr running rfl account

theorem sstep_trapM_iff {mem : Memory} {off : Nat} {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (defined : (rflagsImage core.flags).isSome = true)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core mem none model) evs target ↔
      evs = [] ∧ target = .next (cfgAt core mem (some (core.read .rax)) model) := by
  have account : accountStep x86ExtNative P.segs ⟨⟨core, mem⟩, none⟩ model =
      .ok (⟨⟨core, mem⟩, some (core.read .rax)⟩, model) := by
    apply Progress.accountStep_of_noLazy _ _ model _ lazy
    exact x86NativeStep_syscall ⟨⟨core, mem⟩, none⟩ (by rw [rip, prefix2, isSyscall]) defined
  constructor
  · intro step
    cases step with
    | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
    | instrFault _ _ h => rw [account] at h; cases h
    | instrUnmodeled _ _ h => rw [account] at h; cases h
    | syscall _ p => cases p
    | syscallMaterializationFault _ p => cases p
    | exit _ p => cases p
    | killed _ p => cases p
    | syscallUnmodeled _ p => cases p
  · rintro ⟨rfl, rfl⟩
    exact .instr running rfl account

theorem sstep_exitM_iff {mem : Memory} {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core mem 60) = false) (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core mem (some 60) model) evs target ↔
      evs = [.exitEv (core.read .rdi &&& 255) model.fs] ∧
        target = .next (cfgAt core mem (some 60) (model.withHalted (core.read .rdi &&& 255))) := by
  have outcomes : ∀ outcome, spec (P.sysInM core mem 60) model outcome ↔
      outcome = .ok (mkEffect 0 [] []) (model.withHalted (core.read .rdi &&& 255)) [] :=
    fun outcome => native_exit_iff (P.sysInM core mem 60) model outcome rfl clear
  have halted : (model.withHalted (core.read .rdi &&& 255)).halted = some (core.read .rdi &&& 255) := rfl
  have unkilled : (model.withHalted (core.read .rdi &&& 255)).killedBy = none := by
    simp [Model.killedBy, Model.withHalted]
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s _ live =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at live
      cases live
    | syscallMaterializationFault _ p s _ live =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at live
      cases live
    | exit _ p s h _ =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at h
      cases h
      exact ⟨rfl, rfl⟩
    | killed _ p s k =>
      cases p
      cases (outcomes _).mp s
      rw [unkilled] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      cases (outcomes _).mp s
  · rintro ⟨rfl, rfl⟩
    exact .exit running rfl ((outcomes _).mpr rfl) halted unkilled

/-- A pending call over any memory whose outcomes return with an unchanged
model and memory. -/
theorem sstep_returnM_iff {mem : Memory} {core : Silmaril.X86.State} {n : Word} {model : Model}
    {α : Type} {allowed : α → Prop} {ret : α → Word} {copyins : α → List (Word × Nat)}
    {events : α → List Event} (other : n ≠ 158)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysInM core mem n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) model (events x))
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core mem (some n) model) evs target ↔
      ∃ x, (allowed x ∧ ¬ refused (P.sysInM core mem n) model
          ((mkEffect (ret x) [] []).withCopyins (copyins x))) ∧
        evs = events x ∧ target = .next (cfgAt (resume core (ret x)) mem none model) := by
  have materialized (accesses : List (Word × Nat)) :=
    Progress.materializeModelAccesses_noLazy model accesses lazy
  have unkilled : model.killedBy = none := by
    simp [Model.killedBy, Model.halted] at running ⊢
    simp [running]
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s notRefused _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [materialized] at m
      cases m
      refine ⟨x, ⟨hx, notRefused⟩, rfl, ?_⟩
      rw [resume_effectW core mem mem n other _ [] _ rfl]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      rw [materialized] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      rw [running] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      rw [unkilled] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, ⟨hx, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := n)
      (ms := (⟨⟨core, mem⟩, some n⟩ : X86State)) running rfl ((outcomes _).mpr ⟨x, hx, rfl⟩)
      notRefused running (materialized _)
    rwa [resume_effectW core mem mem n other _ [] _ rfl] at step

/-- A channel write of the bytes `bs` read back from any memory. -/
theorem sstep_writeM_iff {mem : Memory} {core : Silmaril.X86.State} {n : Word} {model : Model}
    {ch : Word} {bs : List Byte} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysInM core mem n) = false)
    (bounded : (bs.length : Int) ≤ rwCountClamp (core.read .rdx))
    (source : readableBytesAux (viewByte mem .read) (core.read .rsi)
      (zw (rwCountClamp (core.read .rdx))).toNat = bs)
    (nonempty : bs ≠ []) (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core mem (some n) model) evs target ↔
      ∃ ds, (WritePrefix bs ds ∧ ¬ refused (P.sysInM core mem n) model
          ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)])) ∧
        evs = ds.map (.writeEv ch) ∧ target = .next (cfgAt (resume core (lenWord ds)) mem none model) := by
  subst number
  refine sstep_returnM_iff (allowed := WritePrefix bs) (by decide) running lazy (fun outcome => ?_) evs target
  refine (native_write_iff (P.sysInM core mem 1) model outcome rfl clear lookup nonzero modeled nonzeroCount
    (bs := bs) source nonempty).trans ?_
  exact exists_congr fun ds => and_congr_left fun _ => writePrefix_iff bounded

theorem returned_resumeW {mem : Memory} {core : Silmaril.X86.State} {model : Model} (ret : Word)
    (running : model.halted = none) :
    returned (cfgAt (resume core ret) mem none model) = some ret := by
  simp [returned, running, resume]

/-! #### Execution and run rules -/

theorem exec_instrW {post : Omni.Post x86ExtNative} {mem : Memory} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem)
    (rest : Omni.Exec P.segs spec refused (cfgAt core' mem none model) post) :
    Omni.Exec P.segs spec refused (cfgAt core mem none model) post :=
  Omni.exec_of_unique running
    (sstep_instrM_iff running lazy rip notSyscall fetched prefix2 decoded exec) rest

theorem exec_trapW {post : Omni.Post x86ExtNative} {mem : Memory} {off : Nat}
    {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Omni.Exec P.segs spec refused (cfgAt core mem (some (core.read .rax)) model) post) :
    Omni.Exec P.segs spec refused (cfgAt core mem none model) post :=
  Omni.exec_of_unique running (sstep_trapM_iff running lazy rip isSyscall prefix2 defined) rest

theorem exec_exitW {post : Omni.Post x86ExtNative} {mem : Memory} {core : Silmaril.X86.State}
    {n status : Word} {model : Model} (number : n = 60) (rdi : core.read .rdi = status)
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core mem n) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (cfgAt core mem (some n) (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs spec refused (cfgAt core mem (some n) model) post := by
  subst number rdi
  refine Omni.exec_of_unique running (sstep_exitM_iff running clear)
    (.halt (by simp [Model.withHalted, Model.halted]) ?_)
  simpa only [List.append_nil] using done

theorem run_instrW {mem : Memory} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (fetched : mem.fetchBytes (P.base + off) len = some ((P.bytes.drop off).take len))
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core mem len = .ok core' mem)
    (rest : Run P.segs spec refused (cfgAt core' mem none model) calls trace outcome) :
    Run P.segs spec refused (cfgAt core mem none model) calls trace outcome :=
  .instr rfl ((sstep_instrM_iff running lazy rip notSyscall fetched prefix2 decoded exec _ _).mpr
    ⟨rfl, rfl⟩) rest

theorem run_trapW {mem : Memory} {off : Nat} {core : Silmaril.X86.State} {model : Model}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (prefix2 : mem.fetchBytes (P.base + off) 2 = some ((P.bytes.drop off).take 2))
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Run P.segs spec refused (cfgAt core mem (some (core.read .rax)) model) calls trace outcome) :
    Run P.segs spec refused (cfgAt core mem none model) calls trace outcome :=
  .instr rfl ((sstep_trapM_iff running lazy rip isSyscall prefix2 defined _ _).mpr ⟨rfl, rfl⟩) rest

theorem run_exitW {mem : Memory} {core : Silmaril.X86.State} {n status : Word} {model : Model}
    (number : n = 60) (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core mem n) = false) :
    Run P.segs spec refused (cfgAt core mem (some n) model)
      [⟨n, x86ExtNative.syscallArgs (⟨⟨core, mem⟩, some n⟩ : X86State), none⟩]
      [.exitEv (status &&& 255) model.fs]
      (.halt (cfgAt core mem (some n) (model.withHalted (status &&& 255)))) := by
  subst number rdi
  exact .sys rfl ((sstep_exitM_iff running clear _ _).mpr ⟨rfl, rfl⟩)
    (.halt (by simp [Model.withHalted, Model.halted]))

end Rules

/-! ### Reading stdin into the image and writing it back -/

section Echo

variable {P}

/-- `read` (0) of stdin into the buffer at segment offset `boff` of an `rwx`
image: every successor delivers a `ReadPrefix` of the stream, records one
`readEv` per byte, stores the bytes in the buffer and consumes them. -/
theorem sstep_read_iff [checked : Checked P] {core : Silmaril.X86.State} {n : Word} {model : Model}
    {boff count : Nat} (number : n = 0)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rwx : P.programHeader.flags = 7)
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel 0))
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (accessible : accessOkbX86 (core.read .rsi) (uns (core.read .rdx)) = true)
    (clear : NativeX86.All.boundarySuspect 0 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (positive : 0 < count) (small : count ≤ 131072)
    (fits : boff + count ≤ P.size) (notEof : model.stdin.atEof = false)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some n) model) evs target ↔
      ∃ bs, (ReadPrefix model.stdin count bs ∧ ¬ refused (P.sysIn core n) model
          (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])) ∧
        evs = bs.map (.readEv 0) ∧
        target = .next (cfgAt (resume core (lenWord bs)) (P.written boff bs) none
          (model.withStdin (model.stdin.take bs.length).2)) := by
  subst number
  have bound := P.size_lt checked.layout
  have outcomes : ∀ outcome, spec (P.sysIn core 0) model outcome ↔
      ∃ bs, ReadPrefix model.stdin count bs ∧
        outcome = .ok (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])
          (model.withStdin (model.stdin.take bs.length).2) (bs.map (.readEv 0)) :=
    fun outcome => read_stdin_iff (P.sysIn core 0) model outcome rfl clear lookup accessible
    clamp positive small notEof (fun k le => by
      change (readBytesAux (viewByte P.mem0 .write) (core.read .rsi) k).isSome = true
      rw [buffer]
      exact wmem_readBytesAux rwx boff k (by omega))
  have address : (core.read .rsi).toNat = P.base + boff := by
    rw [buffer]
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have applied (bs : List Byte) :
      applyMemoryEffect P.mem0 (mkEffect (lenWord bs) [(core.read .rsi, bs)] []) =
        P.written boff bs := by
    change { P.mem0 with bytes := installWrapping P.mem0.bytes (core.read .rsi).toNat bs } = _
    rw [address]
    rfl
  have materialized (bs : List Byte) (accesses : List (Word × Nat)) :=
    Progress.materializeModelAccesses_noLazy (model.withStdin (model.stdin.take bs.length).2) accesses lazy
  have running' (bs : List Byte) : (model.withStdin (model.stdin.take bs.length).2).halted = none := running
  have unkilled (bs : List Byte) : (model.withStdin (model.stdin.take bs.length).2).killedBy = none := by
    simp [Model.killedBy, Model.halted, Model.withStdin] at running ⊢
    simp [running]
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s notRefused _ m =>
      cases p
      obtain ⟨bs, read, same⟩ := (outcomes _).mp s
      cases same
      rw [materialized] at m
      cases m
      refine ⟨bs, ⟨read, notRefused⟩, rfl, ?_⟩
      rw [resume_plainM core P.mem0 (P.written boff bs) 0 (by decide) _ _ (applied bs)]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨bs, _, same⟩ := (outcomes _).mp s
      cases same
      rw [materialized] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨bs, _, same⟩ := (outcomes _).mp s
      cases same
      rw [running' bs] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨bs, _, same⟩ := (outcomes _).mp s
      cases same
      rw [unkilled bs] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨bs, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨bs, ⟨read, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := 0)
      (ms := (⟨⟨core, P.mem0⟩, some 0⟩ : X86State)) running rfl ((outcomes _).mpr ⟨bs, read, rfl⟩)
      notRefused (running' bs) (materialized bs _)
    rwa [resume_plainM core P.mem0 (P.written boff bs) 0 (by decide) _ _ (applied bs)] at step

theorem exec_read [checked : Checked P] {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State}
    {n : Word} {model : Model} {boff count : Nat} (number : n = 0)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rwx : P.programHeader.flags = 7)
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel 0))
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (accessible : accessOkbX86 (core.read .rsi) (uns (core.read .rdx)) = true)
    (clear : NativeX86.All.boundarySuspect 0 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (positive : 0 < count) (small : count ≤ 131072)
    (fits : boff + count ≤ P.size) (notEof : model.stdin.atEof = false)
    (rest : ∀ bs, ReadPrefix model.stdin count bs →
      Omni.Exec P.segs spec noFilter (cfgAt (resume core (lenWord bs)) (P.written boff bs) none
          (model.withStdin (model.stdin.take bs.length).2))
        (fun trace outcome => post (bs.map (.readEv 0) ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (P.cfg core (some n) model) post := by
  have one := InputStream.take_one_length model.stdin notEof
  refine Omni.exec_of_successors running
    (sstep_read_iff number running lazy rwx lookup buffer accessible clear clamp positive small fits notEof)
    ⟨(model.stdin.take 1).1, ⟨InputStream.take_one_ne_nil _ notEof, by omega, by rw [one]⟩,
      fun refusal => refusal⟩ (fun bs allowed => rest bs allowed.1)

theorem run_read [checked : Checked P] {core : Silmaril.X86.State} {n : Word} {model : Model}
    {boff count : Nat} {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (number : n = 0)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rwx : P.programHeader.flags = 7)
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel 0))
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (accessible : accessOkbX86 (core.read .rsi) (uns (core.read .rdx)) = true)
    (clear : NativeX86.All.boundarySuspect 0 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (positive : 0 < count) (small : count ≤ 131072)
    (fits : boff + count ≤ P.size) (notEof : model.stdin.atEof = false)
    (bs : List Byte) (read : ReadPrefix model.stdin count bs)
    (accepted : ¬ refused (P.sysIn core n) model (mkEffect (lenWord bs) [(core.read .rsi, bs)] []))
    (rest : Run P.segs spec refused (cfgAt (resume core (lenWord bs)) (P.written boff bs) none
      (model.withStdin (model.stdin.take bs.length).2)) calls trace outcome) :
    Run P.segs spec refused (P.cfg core (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, P.mem0⟩, some n⟩ : X86State), some (lenWord bs)⟩ :: calls)
      (bs.map (.readEv 0) ++ trace) outcome := by
  have run := Run.sys rfl ((sstep_read_iff number running lazy rwx lookup buffer accessible clear clamp positive
    small fits notEof _ _).mpr ⟨bs, ⟨read, accepted⟩, rfl, rfl⟩) rest
  rw [returned_resumeW (lenWord bs)
    (show (model.withStdin (model.stdin.take bs.length).2).halted = none from running)] at run
  exact run

/-- `write` (1) to a channel of the `bs.length` bytes just read into the buffer. -/
theorem sstep_write_written_iff [checked : Checked P] {core : Silmaril.X86.State} {n : Word}
    {model : Model} {ch : Word} {boff : Nat} {bs : List Byte} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (count : core.read .rdx = lenWord bs) (rwBound : P.size ≤ 131072)
    (small : boff + bs.length ≤ P.size) (nonempty : bs ≠ [])
    (clear : NativeX86.All.boundarySuspect 1 (P.sysInM core (P.written boff bs) n) = false)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgAt core (P.written boff bs) (some n) model) evs target ↔
      ∃ ds, (WritePrefix bs ds ∧ ¬ refused (P.sysInM core (P.written boff bs) n) model
          ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)])) ∧
        evs = ds.map (.writeEv ch) ∧
        target = .next (cfgAt (resume core (lenWord ds)) (P.written boff bs) none model) := by
  have clamp := rwCountClamp_lenWord bs (by omega)
  have length := lenWord_toNat bs (by omega)
  have positive := List.length_pos_iff.mpr nonempty
  refine sstep_writeM_iff number running lazy lookup nonzero ?_ ?_ clear ?_ ?_ nonempty evs target
  · unfold modeledRwRangeWith modeledRwCount
    rw [count]
    unfold uns rwBytesMax
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    left
    rw [length]
    omega
  · rw [count]
    intro zero
    rw [← length, zero] at positive
    simp at positive
  · rw [count, clamp]
  · rw [count, clamp, buffer]
    have : (zw (bs.length : Int)).toNat = bs.length := lenWord_toNat bs (by omega)
    rw [this]
    exact written_source small

theorem exec_write_written [checked : Checked P] {post : Omni.Post x86ExtNative}
    {core : Silmaril.X86.State} {n : Word} {model : Model} {ch : Word} {boff : Nat} {bs : List Byte}
    (number : n = 1) (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (count : core.read .rdx = lenWord bs) (rwBound : P.size ≤ 131072)
    (small : boff + bs.length ≤ P.size) (nonempty : bs ≠ [])
    (clear : NativeX86.All.boundarySuspect 1 (P.sysInM core (P.written boff bs) n) = false)
    (rest : ∀ ds, WritePrefix bs ds →
      Omni.Exec P.segs spec noFilter (cfgAt (resume core (lenWord ds)) (P.written boff bs) none model)
        (fun trace outcome => post (ds.map (.writeEv ch) ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgAt core (P.written boff bs) (some n) model) post :=
  Omni.exec_of_successors running
    (sstep_write_written_iff number running lazy lookup nonzero buffer count rwBound small nonempty clear)
    ⟨_, ⟨nonempty, List.prefix_refl _⟩, fun h => h⟩ (fun ds allowed => rest ds allowed.1)

theorem run_write_written [checked : Checked P] {core : Silmaril.X86.State} {n : Word} {model : Model}
    {ch : Word} {boff : Nat} {bs : List Byte} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (number : n = 1) (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + boff))
    (count : core.read .rdx = lenWord bs) (rwBound : P.size ≤ 131072)
    (small : boff + bs.length ≤ P.size) (nonempty : bs ≠ [])
    (clear : NativeX86.All.boundarySuspect 1 (P.sysInM core (P.written boff bs) n) = false)
    (ds : List Byte) (delivered : WritePrefix bs ds)
    (accepted : ¬ refused (P.sysInM core (P.written boff bs) n) model
      ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)]))
    (rest : Run P.segs spec refused (cfgAt (resume core (lenWord ds)) (P.written boff bs) none model)
      calls trace outcome) :
    Run P.segs spec refused (cfgAt core (P.written boff bs) (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, P.written boff bs⟩, some n⟩ : X86State), some (lenWord ds)⟩ ::
        calls)
      (ds.map (.writeEv ch) ++ trace) outcome := by
  have run := Run.sys rfl ((sstep_write_written_iff number running lazy lookup nonzero buffer count rwBound
    small nonempty clear _ _).mpr ⟨ds, ⟨delivered, accepted⟩, rfl, rfl⟩) rest
  rw [returned_resumeW (lenWord ds) running] at run
  exact run

end Echo

end Probe

/-! ## Tactics -/

/-- Evaluation, or a hypothesis in context (the bound on the bytes read). -/
macro "probe_sideW" : tactic => `(tactic| first | assumption | probe_side)

/-- `probe_instrW off len instr`: `probe_instr` over the memory written by a read. -/
macro "probe_instrW " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic| ((first
    | apply Probe.exec_instrW (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.run_instrW (off := $off) (len := $len) (instruction := $instr)) <;>
    (try (apply Probe.written_fetch <;> probe_sideW)) <;> probe_sides))

/-- `probe_trapW off`: `probe_trap` over the memory written by a read. -/
macro "probe_trapW " off:term:max : tactic =>
  `(tactic| ((first
    | apply Probe.exec_trapW (off := $off)
    | apply Probe.run_trapW (off := $off)) <;>
    (try (apply Probe.written_fetch <;> probe_sideW)) <;> probe_sides))

/-- `probe_exitW status`: `probe_exit` over the memory written by a read. -/
macro "probe_exitW " status:term:max : tactic =>
  `(tactic| ((first
    | apply Probe.exec_exitW (status := $status)
    | apply Probe.run_exitW (status := $status)) <;> probe_sides))

end Silmaril.Process.LPS.Probes
