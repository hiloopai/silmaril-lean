module

public import Silmaril.Process.LPS.Probes.Kit

/-! # File syscalls for probes

Characterizations of every outcome of the file calls the file probes make, on
the probe table (`Probes.table`): `openat` and `open` (the fs-io arms), `read`,
`write` and `close` (the hub's reviewed arms). Each theorem has the shape

`∀ o, spec input model o ↔ ∃ x, allowed x ∧ o = .ok (effect x) (model' x) (events x)`

that `Probe.exec_sys` and `Probe.run_sys` take, or, for a call with one outcome,
`∀ o, spec input model o ↔ o = .ok effect model' events` (`Probe.exec_det`,
`Probe.run_det`). The alternatives are the reference's: an `openat` that would
allocate a descriptor may instead fail with an injected `ENOMEM`, `EACCES`,
`EMFILE` or `ENFILE` (LPS `Sys/Fs/Open.v:27` `openat_errnos`, `OpenAllowed`);
a channel write may be short (`Probe.WritePrefix`).

The pathname and the bytes a call reads come from the loaded image through the
read view of any memory that still holds it (`Probe.Intact`): `readCstr_image`
and `Probe.Intact.readable`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process (Memory Access)

/-! ## The specification monad, one step at a time -/

section Monad

variable {β : Type} {i : SyscallInput} {m : Model}

theorem bind_det_iff {α : Type} {c : Sys α} {k : α → Sys β} {x : α} {m' : Model}
    (hc : ∀ o, c i m o ↔ o = .ok x m' []) (o : Outcome β) :
    (c >>= k) i m o ↔ k x i m' o := by
  show Sys.bind c k i m o ↔ k x i m' o
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x₁, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ok.inj ((hc _).mp h₁)
      simpa using h₂
    · intro h
      exact ⟨x, m', [], evs, (hc _).mpr rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h₁ | ⟨x₁, m₁, evs₁, h₁, h₂⟩)
      · cases (hc _).mp h₁
      · obtain ⟨rfl, rfl, rfl⟩ := Outcome.ok.inj ((hc _).mp h₁)
        exact h₂
    · intro h
      exact .inr ⟨x, m', [], (hc _).mpr rfl, h⟩

theorem input_bind_iff {k : SyscallInput → Sys β} (o : Outcome β) :
    (Sys.input >>= k) i m o ↔ k i i m o :=
  bind_det_iff (fun _ => Iff.rfl) o

theorem getModel_bind_iff {k : Model → Sys β} (o : Outcome β) :
    (Sys.getModel >>= k) i m o ↔ k m i m o :=
  bind_det_iff (fun _ => Iff.rfl) o

theorem modify_bind_iff {f : Model → Model} {k : Unit → Sys β} (o : Outcome β) :
    (Sys.modify f >>= k) i m o ↔ k () i (f m) o :=
  bind_det_iff (fun _ => Iff.rfl) o

theorem choose_bind_iff {α : Type} {P : α → Prop} {k : α → Sys β} (o : Outcome β) :
    (Sys.choose P >>= k) i m o ↔ ∃ x, P x ∧ k x i m o := by
  show Sys.bind (Sys.choose P) k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, ⟨x', hx, same⟩, h₂, rfl⟩
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ok.inj same
      exact ⟨x, hx, by simpa using h₂⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨x, m, [], evs, ⟨x, hx, rfl⟩, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (⟨x', _, same⟩ | ⟨x, m₁, evs₁, ⟨x', hx, same⟩, h₂⟩)
      · cases same
      · obtain ⟨rfl, rfl, rfl⟩ := Outcome.ok.inj same
        exact ⟨x, hx, h₂⟩
    · rintro ⟨x, hx, h⟩
      exact .inr ⟨x, m, [], ⟨x, hx, rfl⟩, h⟩

theorem alt_iff {c₁ c₂ : Sys β} (o : Outcome β) : Sys.alt c₁ c₂ i m o ↔ c₁ i m o ∨ c₂ i m o :=
  Iff.rfl

/-- `record_copyins` around a specification whose outcomes are all `ok`. -/
theorem recordCopyins_iff {reads : List (Word × Nat)} {spec : Sys SyscallEffect} {α : Type}
    {allowed : α → Prop} {effect : α → SyscallEffect} {model' : α → Model}
    {events : α → List Event}
    (h : ∀ o, spec i m o ↔ ∃ x, allowed x ∧ o = .ok (effect x) (model' x) (events x))
    (o : Outcome SyscallEffect) :
    recordCopyins reads spec i m o ↔ ∃ x, allowed x ∧
      o = .ok ((effect x).withCopyins (reads ++ (effect x).copyins)) (model' x) (events x) := by
  unfold recordCopyins
  cases o with
  | ok y m₂ evs₂ =>
    simp only [Sys.bind, Sys.pure]
    constructor
    · rintro ⟨e, m₁, evs₁, evsB, h₁, h₂, rfl⟩
      obtain ⟨x, hx, same⟩ := (h _).mp h₁
      cases same
      cases h₂
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, same⟩
      cases same
      exact ⟨effect x, model' x, events x, [], (h _).mpr ⟨x, hx, rfl⟩, rfl, by simp⟩
  | unmodeled =>
    simp only [Sys.bind, Sys.pure]
    constructor
    · rintro (h₁ | ⟨e, m₁, evs₁, _, h₂⟩)
      · obtain ⟨x, _, same⟩ := (h _).mp h₁
        cases same
      · cases h₂
    · rintro ⟨x, _, same⟩
      cases same

/-- One outcome, as a family indexed by `Unit`. -/
theorem det_family {s : Sys SyscallEffect} {effect : SyscallEffect} {model' : Model}
    {events : List Event} (h : ∀ o, s i m o ↔ o = .ok effect model' events) :
    ∀ o, s i m o ↔ ∃ _ : Unit, True ∧ o = .ok effect model' events :=
  fun o => (h o).trans ⟨fun same => ⟨(), trivial, same⟩, fun ⟨_, _, same⟩ => same⟩

/-- `record_copyins` around a specification with one outcome. -/
theorem recordCopyins_det {reads : List (Word × Nat)} {spec : Sys SyscallEffect}
    {effect : SyscallEffect} {model' : Model} {events : List Event}
    (h : ∀ o, spec i m o ↔ o = .ok effect model' events) (o : Outcome SyscallEffect) :
    recordCopyins reads spec i m o ↔
      o = .ok (effect.withCopyins (reads ++ effect.copyins)) model' events :=
  (recordCopyins_iff (allowed := fun _ : Unit => True) (effect := fun _ => effect)
    (model' := fun _ => model') (events := fun _ => events) (det_family h) o).trans
    ⟨fun ⟨_, _, same⟩ => same, fun same => ⟨(), trivial, same⟩⟩

/-- A specification chosen by a condition, applied. -/
theorem ite_sys_apply {c : Prop} [Decidable c] (a b : Sys β) (o : Outcome β) :
    (if c then a else b) i m o = if c then a i m o else b i m o := by
  split <;> rfl

end Monad

/-! ## Reading the image through a memory view -/

theorem shift_succ (a : Word) (k : Nat) :
    a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- `read_cstr` over a list: the reading of `bytes` from its first byte, with fuel. -/
def cstrOfList : List Byte → Nat → CstrResult
  | _, 0 => .tooLong
  | [], _ + 1 => .fault
  | b :: rest, k + 1 =>
    if b == 0 then .ok []
    else match cstrOfList rest k with
      | .ok r => .ok (b :: r)
      | r => r

theorem readCstrAux_of_list (mp : Word → Option Byte) (bytes : List Byte) :
    ∀ (a : Word) (fuel : Nat),
      (∀ k (bound : k < bytes.length), mp (a + BitVec.ofNat 64 k) = some bytes[k]) →
      cstrOfList bytes fuel ≠ .fault → readCstrAux mp a fuel = cstrOfList bytes fuel := by
  induction bytes with
  | nil =>
    intro a fuel _ notFault
    cases fuel with
    | zero => rfl
    | succ k => exact absurd rfl notFault
  | cons b rest ih =>
    intro a fuel present notFault
    cases fuel with
    | zero => rfl
    | succ k =>
      have first : mp a = some b := by
        have h := present 0 (by simp)
        rwa [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a] at h
      have later : ∀ k' (bound : k' < rest.length),
          mp (a + 1 + BitVec.ofNat 64 k') = some rest[k'] := by
        intro k' bound
        rw [shift_succ]
        exact present (k' + 1) (by simpa using bound)
      by_cases zero : b = 0
      · simp [readCstrAux, cstrOfList, first, zero]
      · have restNotFault : cstrOfList rest k ≠ .fault := by
          intro fault
          apply notFault
          simp [cstrOfList, fault]
          exact zero
        simp only [readCstrAux, cstrOfList, first]
        rw [ih (a + 1) k later restNotFault]
        cases cstrOfList rest k <;> rfl

/-- The pathname a call reads at image offset `off`. -/
theorem readCstr_image {P : Probe} [checked : Probe.Checked P] {memory : Memory}
    (intact : P.Intact memory) {a : Word} {off : Nat} {path : List Byte}
    (address : a = BitVec.ofNat 64 (P.base + off)) (inside : off < P.size)
    (reading : cstrOfList (P.bytes.drop off) pathMax = .ok path) :
    readCstr (viewByte memory .read) a = .ok path := by
  subst address
  have sizes := checked.layout.sizes
  unfold readCstr
  rw [readCstrAux_of_list (viewByte memory .read) (P.bytes.drop off)
    (BitVec.ofNat 64 (P.base + off)) pathMax ?_ (by rw [reading]; simp), reading]
  intro k bound
  simp only [List.length_drop] at bound
  have shifted : BitVec.ofNat 64 (P.base + off) + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (P.base + (off + k)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]
  rw [shifted, intact.view (off + k) (by omega), List.getElem_drop,
    List.getElem?_eq_getElem (by omega)]

/-- The bytes a call reads from the image at offset `off`. -/
theorem writeSource_image {P : Probe} [Probe.Checked P] {memory : Memory}
    (intact : P.Intact memory) {buf count : Word} {off length : Nat}
    (address : buf = BitVec.ofNat 64 (P.base + off))
    (clamp : (zw (rwCountClamp count)).toNat = length) (fits : off + length ≤ P.size) :
    writeSource (viewByte memory .read) buf count = (P.bytes.drop off).take length := by
  subst address
  unfold writeSource readableBytes
  rw [clamp]
  exact intact.readable off length fits

theorem readBytesAux_of (mp : Word → Option Byte) (bytes : List Byte) :
    ∀ (a : Word), (∀ k (bound : k < bytes.length), mp (a + BitVec.ofNat 64 k) = some bytes[k]) →
      readBytesAux mp a bytes.length = some bytes := by
  induction bytes with
  | nil => intro _ _; rfl
  | cons b rest ih =>
    intro a present
    have first : mp a = some b := by
      have h := present 0 (by simp)
      rwa [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a] at h
    have later : ∀ k' (bound : k' < rest.length),
        mp (a + 1 + BitVec.ofNat 64 k') = some rest[k'] := by
      intro k' bound
      rw [shift_succ]
      exact present (k' + 1) (by simpa using bound)
    simp only [List.length_cons, readBytesAux, first, ih (a + 1) later, Option.map]

theorem readableBytesAux_of (mp : Word → Option Byte) (bytes : List Byte) :
    ∀ (a : Word), (∀ k (bound : k < bytes.length), mp (a + BitVec.ofNat 64 k) = some bytes[k]) →
      readableBytesAux mp a bytes.length = bytes := by
  induction bytes with
  | nil => intro _ _; rfl
  | cons b rest ih =>
    intro a present
    have first : mp a = some b := by
      have h := present 0 (by simp)
      rwa [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a] at h
    have later : ∀ k' (bound : k' < rest.length),
        mp (a + 1 + BitVec.ofNat 64 k') = some rest[k'] := by
      intro k' bound
      rw [shift_succ]
      exact present (k' + 1) (by simpa using bound)
    simp only [List.length_cons, readableBytesAux, first, ih (a + 1) later]

theorem readBytesMap_of (mp : Word → Option Byte) (a len : Word) (bytes : List Byte)
    (length : len.toNat = bytes.length)
    (present : ∀ k (bound : k < bytes.length), mp (a + BitVec.ofNat 64 k) = some bytes[k]) :
    readBytesMap mp a len = some bytes := by
  unfold readBytesMap
  rw [length]
  exact readBytesAux_of mp bytes a present

/-- The source of a write whose bytes are present in the view `mp` at `a`. -/
theorem writeSource_of_view {mp : Word → Option Byte} {buf a count : Word} {bs : List Byte}
    (address : buf = a)
    (present : ∀ k (bound : k < bs.length), mp (a + BitVec.ofNat 64 k) = some bs[k])
    (clamp : (zw (rwCountClamp count)).toNat = bs.length) :
    writeSource mp buf count = bs := by
  subst address
  unfold writeSource readableBytes
  rw [clamp]
  exact readableBytesAux_of mp bs buf present

theorem openatErrnos_cases {e : Int} (member : e ∈ openatErrnos) :
    e = ENOMEM ∨ e = EACCES ∨ e = EMFILE ∨ e = ENFILE := by
  simpa [openatErrnos] using member

/-! ## Memory after a `read` into the stack -/

/-- The memory after `applyMemoryEffect` installs `bytes` at `a`. -/
abbrev memWith (memory : Memory) (a : Word) (bytes : List Byte) : Memory :=
  { memory with bytes := installWrapping memory.bytes a.toNat bytes }

theorem applyMemoryEffect_write (memory : Memory) (ret a : Word) (bytes : List Byte) :
    applyMemoryEffect memory (mkEffect ret [(a, bytes)] []) = memWith memory a bytes := rfl

theorem toNat_add_ofNat (a : Word) (k : Nat) (fits : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt fits

theorem view_installed (memory : Memory) (access : Access) (a : Word) (bytes : List Byte)
    (permitted : ∀ k < bytes.length, memory.permits access (a.toNat + k) = true)
    (nowrap : a.toNat + bytes.length < 2 ^ 64) (k : Nat) (bound : k < bytes.length) :
    viewByte (memWith memory a bytes) access (a + BitVec.ofNat 64 k) = some bytes[k] := by
  unfold viewByte
  rw [toNat_add_ofNat a k (by omega)]
  rw [show (memWith memory a bytes).permits access (a.toNat + k) =
    memory.permits access (a.toNat + k) from rfl, permitted k bound]
  simp only [ite_true]
  rw [← Std.ExtHashMap.get?_eq_getElem?]
  exact installWrapping_get _ _ _ k bound (by omega)

theorem view_of_get (memory : Memory) (access : Access) (a : Word) (bytes : List Byte)
    (permitted : ∀ k < bytes.length, memory.permits access (a.toNat + k) = true)
    (present : ∀ k (bound : k < bytes.length), memory.bytes.get? (a.toNat + k) = some bytes[k])
    (nowrap : a.toNat + bytes.length < 2 ^ 64) (k : Nat) (bound : k < bytes.length) :
    viewByte memory access (a + BitVec.ofNat 64 k) = some bytes[k] := by
  unfold viewByte
  rw [toNat_add_ofNat a k (by omega), permitted k bound]
  simp only [ite_true]
  rw [← Std.ExtHashMap.get?_eq_getElem?]
  exact present k bound

/-- The entry block's bytes in any initial memory. -/
theorem initialMemory_stack_get (segments : List Segment) (sp : Word) (stack : List Byte) (k : Nat)
    (bound : k < stack.length) (nowrap : sp.toNat + stack.length ≤ 2 ^ 64) :
    (initialMemory segments sp stack).bytes.get? (sp.toNat + k) = some stack[k] := by
  let low := sp.toNat - stackMaxSize.toNat
  change (installWrapping
    (installWrapping (segments.foldl (fun acc segment => installWrapping acc segment.base segment.bytes) ∅)
      low (List.replicate (sp.toNat - low) 0)) sp.toNat stack).get? (sp.toNat + k) = _
  exact installWrapping_get _ _ _ k bound nowrap

namespace Probe

variable (P : Probe)

/-- The entry block's bytes in the initial memory. -/
theorem mem0_stack_get (nowrap : P.entry.sp.toNat + P.stack.length ≤ 2 ^ 64) (k : Nat)
    (bound : k < P.stack.length) :
    P.mem0.bytes.get? (P.entry.sp.toNat + k) = some P.stack[k] :=
  initialMemory_stack_get [P.segment] P.entry.sp P.stack k bound nowrap

/-- Installing bytes above the segment keeps the image intact. -/
theorem Intact.install {P} [checked : Checked P] {memory : Memory} (intact : P.Intact memory)
    (a : Word) (bytes : List Byte) (above : P.base + P.size ≤ a.toNat)
    (nowrap : a.toNat + bytes.length ≤ 2 ^ 64) :
    P.Intact (memWith memory a bytes) := by
  have sizes := checked.layout.sizes
  refine ⟨intact.region, ?_⟩
  intro index bound
  change (installWrapping memory.bytes a.toNat bytes).get? (P.base + index) = _
  rw [installWrapping_outside _ _ _ _ nowrap (Or.inl (by omega))]
  exact intact.installed index bound

end Probe

/-! ## `openat` and `open` -/

/-- The alternatives of a descriptor-allocating `openat` (LPS `Sys/Fs/Open.v:268`
`open_result_spec`): `none` is success with the lowest free descriptor, `some e`
the injected failure `e` of `openat_errnos`. -/
def OpenAllowed : Option Int → Prop
  | none => True
  | some e => e ∈ openatErrnos

/-- The return value of each alternative. -/
def openRet (fd : Word) : Option Int → Word
  | none => fd
  | some e => errnoRet e

/-- The model after each alternative: `success`, or unchanged on a failure. -/
def openModel (m success : Model) : Option Int → Model
  | none => success
  | some _ => m

section Openat

variable {i : SyscallInput} {m : Model}

theorem openResultSpec_iff {mk : Word → Model → Model}
    (free : fdLookup m.fds (allocFd m.fds) = none) (o : Outcome SyscallEffect) :
    openResultSpec m mk i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok (mkEffect (openRet (allocFd m.fds) r) [] []) (openModel m (mk (allocFd m.fds) m) r) [] := by
  unfold openResultSpec
  rw [alt_iff, errnoFrom, lowestFd, choose_bind_iff, choose_bind_iff]
  constructor
  · rintro (⟨e, member, h⟩ | ⟨fd, ⟨_, rfl⟩, h⟩)
    · exact ⟨some e, member, h⟩
    · exact ⟨none, trivial, (modify_bind_iff _).mp h⟩
  · rintro ⟨r, allowed, rfl⟩
    cases r with
    | none => exact .inr ⟨_, ⟨free, rfl⟩, (modify_bind_iff _).mpr rfl⟩
    | some e => exact .inl ⟨e, allowed, rfl⟩

theorem createWronly_iff {path : Fs.Path} (free : fdLookup m.fds (allocFd m.fds) = none)
    (o : Outcome SyscallEffect) :
    createWronly path m i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok (mkEffect (openRet (allocFd m.fds) r) [] [])
        (openModel m ((m.withFs (Fs.set m.fs path [])).withFds
          (fdInsert m.fds (allocFd m.fds) (.fileW path 0))) r) [] := by
  unfold createWronly
  rw [alt_iff, errnoFrom, lowestFd, choose_bind_iff, choose_bind_iff]
  constructor
  · rintro (⟨e, member, h⟩ | ⟨fd, ⟨_, rfl⟩, h⟩)
    · exact ⟨some e, member, h⟩
    · exact ⟨none, trivial, (modify_bind_iff _).mp ((modify_bind_iff _).mp h)⟩
  · rintro ⟨r, allowed, rfl⟩
    cases r with
    | none => exact .inr ⟨_, ⟨free, rfl⟩, (modify_bind_iff _).mpr ((modify_bind_iff _).mpr rfl)⟩
    | some e => exact .inl ⟨e, allowed, rfl⟩

theorem openatSpec_iff {dirfd pathp flags : Word} {α : Type} {allowed : α → Prop}
    {effect : α → SyscallEffect} {model' : α → Model}
    (core : ∀ o, openatCoreSpec dirfd pathp flags i m o ↔
      ∃ x, allowed x ∧ o = .ok (effect x) (model' x) [])
    (o : Outcome SyscallEffect) :
    openatSpec dirfd pathp flags i m o ↔ ∃ x, allowed x ∧
      o = .ok ((effect x).withCopyins
        ([(pathp, cstrAccessLenAux i.mem pathp pathMax)] ++ (effect x).copyins)) (model' x) [] := by
  unfold openatSpec
  rw [input_bind_iff]
  exact recordCopyins_iff (events := fun _ => []) core o

theorem openatCoreSpec_iff {dirfd pathp flags : Word} (modeled : modeledOpenFlags flags = true)
    (o : Outcome SyscallEffect) :
    openatCoreSpec dirfd pathp flags i m o ↔ openatBodySpec i m dirfd pathp flags i m o := by
  unfold openatCoreSpec
  simp only [input_bind_iff, getModel_bind_iff, modeled, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

theorem openatBodySpec_ok {dirfd pathp flags : Word} {path : List Byte}
    (read : readCstr i.mem pathp = .ok path) (nonempty : Fs.pathEqb path [] = false)
    (cwd : (dirfd == AT_FDCWD32) = true) (o : Outcome SyscallEffect) :
    openatBodySpec i m dirfd pathp flags i m o ↔ openatResolvedSpec path flags m i m o := by
  unfold openatBodySpec
  simp only [read, nonempty, cwd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem openatBodySpec_fault {dirfd pathp flags : Word} (read : readCstr i.mem pathp = .fault)
    (o : Outcome SyscallEffect) :
    openatBodySpec i m dirfd pathp flags i m o ↔ o = .ok (mkEffect (errnoRet EFAULT) [] []) m [] := by
  unfold openatBodySpec
  simp only [read]
  exact Iff.rfl

theorem openatResolvedSpec_read {path : List Byte} {flags : Word}
    (slash : pathHasSlash path = false) (rdonly : (openResidue flags == 0) = true)
    (o : Outcome SyscallEffect) :
    openatResolvedSpec path flags m i m o ↔ openatReadSpec path m i m o := by
  unfold openatResolvedSpec
  simp only [slash, rdonly, Bool.false_eq_true, ↓reduceIte]

theorem openatResolvedSpec_create {path : List Byte} {flags : Word}
    (slash : pathHasSlash path = false) (notRead : (openResidue flags == 0) = false)
    (create : (openResidue flags == wrCreateFlags) = true) (o : Outcome SyscallEffect) :
    openatResolvedSpec path flags m i m o ↔ openatCreateSpec path m i m o := by
  unfold openatResolvedSpec
  simp only [slash, notRead, create, Bool.false_eq_true, ↓reduceIte]

theorem openatReadSpec_found {path data : List Byte} (dirref : pathIsDirref path = false)
    (found : Fs.lookup m.fs path = some data) (o : Outcome SyscallEffect) :
    openatReadSpec path m i m o ↔
      openResultSpec m (fun fd m' => m'.withFds (fdInsert m.fds fd (.file path 0))) i m o := by
  unfold openatReadSpec
  simp only [dirref, Bool.false_eq_true, ↓reduceIte, found]

theorem openatReadSpec_missing {path : List Byte} (dirref : pathIsDirref path = false)
    (missing : Fs.lookup m.fs path = none) (o : Outcome SyscallEffect) :
    openatReadSpec path m i m o ↔ o = .ok (mkEffect (errnoRet ENOENT) [] []) m [] := by
  unfold openatReadSpec
  simp only [dirref, Bool.false_eq_true, ↓reduceIte, missing]
  exact Iff.rfl

theorem openatCreateSpec_iff {path : List Byte} (dirref : pathIsDirref path = false)
    (notDir : fsUnder m.fs path = false) (o : Outcome SyscallEffect) :
    openatCreateSpec path m i m o ↔ createWronly path m i m o := by
  unfold openatCreateSpec
  simp only [dirref, notDir, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- `openat(dirfd, path, O_RDONLY)` of an existing file: the lowest free
descriptor on it, or an injected errno. -/
theorem openatCore_read {dirfd pathp flags : Word} {path data : List Byte}
    (modeled : modeledOpenFlags flags = true) (read : readCstr i.mem pathp = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (cwd : (dirfd == AT_FDCWD32) = true)
    (slash : pathHasSlash path = false) (rdonly : (openResidue flags == 0) = true)
    (dirref : pathIsDirref path = false) (found : Fs.lookup m.fs path = some data)
    (free : fdLookup m.fds (allocFd m.fds) = none) (o : Outcome SyscallEffect) :
    openatCoreSpec dirfd pathp flags i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok (mkEffect (openRet (allocFd m.fds) r) [] [])
        (openModel m (m.withFds (fdInsert m.fds (allocFd m.fds) (.file path 0))) r) [] :=
  (openatCoreSpec_iff modeled o).trans ((openatBodySpec_ok read nonempty cwd o).trans
    ((openatResolvedSpec_read slash rdonly o).trans ((openatReadSpec_found dirref found o).trans
      (openResultSpec_iff free o))))

/-- `openat(dirfd, path, O_RDONLY)` of a missing file: `ENOENT`. -/
theorem openatCore_missing {dirfd pathp flags : Word} {path : List Byte}
    (modeled : modeledOpenFlags flags = true) (read : readCstr i.mem pathp = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (cwd : (dirfd == AT_FDCWD32) = true)
    (slash : pathHasSlash path = false) (rdonly : (openResidue flags == 0) = true)
    (dirref : pathIsDirref path = false) (missing : Fs.lookup m.fs path = none)
    (o : Outcome SyscallEffect) :
    openatCoreSpec dirfd pathp flags i m o ↔ ∃ _ : Unit, True ∧
      o = .ok (mkEffect (errnoRet ENOENT) [] []) m [] :=
  det_family (fun o => (openatCoreSpec_iff modeled o).trans
    ((openatBodySpec_ok read nonempty cwd o).trans
      ((openatResolvedSpec_read slash rdonly o).trans (openatReadSpec_missing dirref missing o)))) o

/-- `openat` of an unreadable pathname: `EFAULT`. -/
theorem openatCore_fault {dirfd pathp flags : Word} (modeled : modeledOpenFlags flags = true)
    (read : readCstr i.mem pathp = .fault) (o : Outcome SyscallEffect) :
    openatCoreSpec dirfd pathp flags i m o ↔ ∃ _ : Unit, True ∧
      o = .ok (mkEffect (errnoRet EFAULT) [] []) m [] :=
  det_family (fun o => (openatCoreSpec_iff modeled o).trans (openatBodySpec_fault read o)) o

/-- `openat(dirfd, path, O_WRONLY|O_CREAT|O_TRUNC)`: the file (re)created empty on
the lowest free descriptor, write-only, or an injected errno. -/
theorem openatCore_create {dirfd pathp flags : Word} {path : List Byte}
    (modeled : modeledOpenFlags flags = true) (read : readCstr i.mem pathp = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (cwd : (dirfd == AT_FDCWD32) = true)
    (slash : pathHasSlash path = false) (notRead : (openResidue flags == 0) = false)
    (create : (openResidue flags == wrCreateFlags) = true) (dirref : pathIsDirref path = false)
    (notDir : fsUnder m.fs path = false) (free : fdLookup m.fds (allocFd m.fds) = none)
    (o : Outcome SyscallEffect) :
    openatCoreSpec dirfd pathp flags i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok (mkEffect (openRet (allocFd m.fds) r) [] [])
        (openModel m ((m.withFs (Fs.set m.fs path [])).withFds
          (fdInsert m.fds (allocFd m.fds) (.fileW path 0))) r) [] :=
  (openatCoreSpec_iff modeled o).trans ((openatBodySpec_ok read nonempty cwd o).trans
    ((openatResolvedSpec_create slash notRead create o).trans
      ((openatCreateSpec_iff dirref notDir o).trans (createWronly_iff free o))))

end Openat

/-! ### On the hub table -/

section Table

variable {i : SyscallInput} {m : Model}

theorem spec_openat (number : i.sysno = 257)
    (clear : NativeX86.All.boundarySuspect 257 i = false) (o : Outcome SyscallEffect) :
    spec i m o ↔ openatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) i m o :=
  dispatches_openat.spec_iff (by rw [number]; rfl) clear m o

theorem spec_open (number : i.sysno = 2)
    (clear : NativeX86.All.boundarySuspect 2 i = false) (o : Outcome SyscallEffect) :
    spec i m o ↔ openatSpec AT_FDCWD32 (i.arg 0) (i.arg 1) i m o :=
  dispatches_open.spec_iff (by rw [number]; rfl) clear m o

/-- `openat(AT_FDCWD, path, O_RDONLY)` of an existing file on the hub table. -/
theorem spec_openat_read {path : List Byte} (number : i.sysno = 257)
    (clear : NativeX86.All.boundarySuspect 257 i = false)
    (cwd : (fd32 (i.arg 0) == AT_FDCWD32) = true) (modeled : modeledOpenFlags (i.arg 2) = true)
    (rdonly : (openResidue (i.arg 2) == 0) = true) (read : readCstr i.mem (i.arg 1) = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (slash : pathHasSlash path = false)
    (dirref : pathIsDirref path = false) (found : (Fs.lookup m.fs path).isSome = true)
    (free : fdLookup m.fds (allocFd m.fds) = none) :
    ∀ o, spec i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet (allocFd m.fds) r) [] []).withCopyins
          [(i.arg 1, cstrAccessLenAux i.mem (i.arg 1) pathMax)])
        (openModel m (m.withFds (fdInsert m.fds (allocFd m.fds) (.file path 0))) r) [] :=
  fun o => (spec_openat number clear o).trans (openatSpec_iff
    (openatCore_read modeled read nonempty cwd slash rdonly dirref
      (Option.isSome_iff_exists.mp found).choose_spec free) o)

/-- Legacy x86-64 `open(path, O_RDONLY)` of an existing file on the hub table. -/
theorem spec_open_read {path : List Byte} (number : i.sysno = 2)
    (clear : NativeX86.All.boundarySuspect 2 i = false)
    (modeled : modeledOpenFlags (i.arg 1) = true)
    (rdonly : (openResidue (i.arg 1) == 0) = true) (read : readCstr i.mem (i.arg 0) = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (slash : pathHasSlash path = false)
    (dirref : pathIsDirref path = false) (found : (Fs.lookup m.fs path).isSome = true)
    (free : fdLookup m.fds (allocFd m.fds) = none) :
    ∀ o, spec i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet (allocFd m.fds) r) [] []).withCopyins
          [(i.arg 0, cstrAccessLenAux i.mem (i.arg 0) pathMax)])
        (openModel m (m.withFds (fdInsert m.fds (allocFd m.fds) (.file path 0))) r) [] :=
  fun o => (spec_open number clear o).trans (openatSpec_iff
    (openatCore_read modeled read nonempty rfl slash rdonly dirref
      (Option.isSome_iff_exists.mp found).choose_spec free) o)

/-- `openat(AT_FDCWD, path, O_RDONLY)` of a missing file on the hub table. -/
theorem spec_openat_missing {path : List Byte} (number : i.sysno = 257)
    (clear : NativeX86.All.boundarySuspect 257 i = false)
    (cwd : (fd32 (i.arg 0) == AT_FDCWD32) = true) (modeled : modeledOpenFlags (i.arg 2) = true)
    (rdonly : (openResidue (i.arg 2) == 0) = true) (read : readCstr i.mem (i.arg 1) = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (slash : pathHasSlash path = false)
    (dirref : pathIsDirref path = false) (missing : Fs.lookup m.fs path = none) :
    ∀ o, spec i m o ↔
      o = .ok ((mkEffect (errnoRet ENOENT) [] []).withCopyins
        [(i.arg 1, cstrAccessLenAux i.mem (i.arg 1) pathMax)]) m [] :=
  fun o => ((spec_openat number clear o).trans (openatSpec_iff
    (openatCore_missing modeled read nonempty cwd slash rdonly dirref missing) o)).trans
    ⟨fun ⟨_, _, same⟩ => same, fun same => ⟨(), trivial, same⟩⟩

/-- `openat` of an unreadable pathname on the hub table. -/
theorem spec_openat_fault (number : i.sysno = 257)
    (clear : NativeX86.All.boundarySuspect 257 i = false) (modeled : modeledOpenFlags (i.arg 2) = true)
    (read : readCstr i.mem (i.arg 1) = .fault) :
    ∀ o, spec i m o ↔
      o = .ok ((mkEffect (errnoRet EFAULT) [] []).withCopyins
        [(i.arg 1, cstrAccessLenAux i.mem (i.arg 1) pathMax)]) m [] :=
  fun o => ((spec_openat number clear o).trans (openatSpec_iff (openatCore_fault modeled read) o)).trans
    ⟨fun ⟨_, _, same⟩ => same, fun same => ⟨(), trivial, same⟩⟩

/-- `openat(AT_FDCWD, path, O_WRONLY|O_CREAT|O_TRUNC)` on the hub table. -/
theorem spec_openat_create {path : List Byte} (number : i.sysno = 257)
    (clear : NativeX86.All.boundarySuspect 257 i = false)
    (cwd : (fd32 (i.arg 0) == AT_FDCWD32) = true) (modeled : modeledOpenFlags (i.arg 2) = true)
    (notRead : (openResidue (i.arg 2) == 0) = false)
    (create : (openResidue (i.arg 2) == wrCreateFlags) = true)
    (read : readCstr i.mem (i.arg 1) = .ok path)
    (nonempty : Fs.pathEqb path [] = false) (slash : pathHasSlash path = false)
    (dirref : pathIsDirref path = false) (notDir : fsUnder m.fs path = false)
    (free : fdLookup m.fds (allocFd m.fds) = none) :
    ∀ o, spec i m o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet (allocFd m.fds) r) [] []).withCopyins
          [(i.arg 1, cstrAccessLenAux i.mem (i.arg 1) pathMax)])
        (openModel m ((m.withFs (Fs.set m.fs path [])).withFds
          (fdInsert m.fds (allocFd m.fds) (.fileW path 0))) r) [] :=
  fun o => (spec_openat number clear o).trans (openatSpec_iff
    (openatCore_create modeled read nonempty cwd slash notRead create dirref notDir free) o)

theorem spec_read (number : i.sysno = 0) (clear : NativeX86.All.boundarySuspect 0 i = false)
    (o : Outcome SyscallEffect) :
    spec i m o ↔ readSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) i m o :=
  dispatches_read.spec_iff (by rw [number]; rfl) clear m o

theorem spec_write (number : i.sysno = 1) (clear : NativeX86.All.boundarySuspect 1 i = false)
    (o : Outcome SyscallEffect) :
    spec i m o ↔ writeSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) i m o :=
  dispatches_write.spec_iff (by rw [number]; rfl) clear m o

theorem spec_close (number : i.sysno = 3) (clear : NativeX86.All.boundarySuspect 3 i = false)
    (o : Outcome SyscallEffect) :
    spec i m o ↔ closeSpec (fd32 (i.arg 0)) i m o :=
  dispatches_close.spec_iff (by rw [number]; rfl) clear m o

end Table

/-! ## `read`, `write` and `close` -/

section ReadWrite

variable {i : SyscallInput} {m : Model} {access : Word → Int → Bool}

/-- `read` of a regular file at its offset (LPS `Sys/Fs/ReadWrite.v:543-635`):
the bytes from the offset, advancing it. -/
theorem readSpec_file {fd buf count off : Word} {path data bs : List Byte}
    (lookup : fdLookup m.fds fd = some (.file path off)) (ok : access buf (uns count) = true)
    (found : Fs.lookup m.fs path = some data)
    (delivered : Fs.fileRead data off (zw (rwCountClamp count)) = bs) {w : List Byte}
    (writable : readBytesMap i.wmem buf (lenWord bs) = some w)
    (o : Outcome SyscallEffect) :
    readSpecWith access fd buf count i m o ↔
      o = .ok (mkEffect (lenWord bs) (deliveredWrites buf bs) [])
        (m.withFds (fdInsert m.fds fd (.file path (off + lenWord bs)))) [] := by
  subst delivered
  unfold readSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup]
  unfold readFileWith
  simp only [ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, found, writable]
  rw [modify_bind_iff]
  exact Iff.rfl

theorem readSpec_badfd {fd buf count : Word} (lookup : fdLookup m.fds fd = none)
    (o : Outcome SyscallEffect) :
    readSpecWith access fd buf count i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] := by
  unfold readSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup]
  exact Iff.rfl

theorem writeSpec_badfd {fd buf count : Word} (lookup : fdLookup m.fds fd = none)
    (o : Outcome SyscallEffect) :
    writeSpecWith access fd buf count i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] := by
  unfold writeSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup]
  exact Iff.rfl

/-- A write to a read-only file descriptor is `EBADF`. -/
theorem writeSpec_readOnly {fd buf count off : Word} {path : List Byte}
    (lookup : fdLookup m.fds fd = some (.file path off)) (o : Outcome SyscallEffect) :
    writeSpecWith access fd buf count i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] := by
  unfold writeSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup]
  exact Iff.rfl

/-- A zero-length channel write returns 0 and writes nothing. -/
theorem writeSpec_zero {fd buf count ch : Word} (lookup : fdLookup m.fds fd = some (.channel ch))
    (nonzero : wIs0 ch = false) (modeled : modeledRwRangeWith access buf count = true)
    (zero : wIs0 count = true) (ok : access buf (uns count) = true) (o : Outcome SyscallEffect) :
    writeSpecWith access fd buf count i m o ↔ o = .ok (mkEffect 0 [] []) m [] := by
  unfold writeSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup, nonzero, modeled, zero,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, accessOkZeroWith, ok]
  exact Iff.rfl

/-- A write of the readable source `bs` to a write-only regular file at its offset
(LPS `Sys/Fs/ReadWrite.v:1017-1072`): the bytes are placed, the offset advances,
the source copy-in is recorded. -/
theorem writeSpec_file {fd buf count off : Word} {path data bs : List Byte}
    (lookup : fdLookup m.fds fd = some (.fileW path off))
    (modeled : modeledRwRangeWith access buf count = true) (nonzero : wIs0 count = false)
    (source : writeSource i.mem buf count = bs) (nonempty : (bs.length == 0) = false)
    (found : Fs.lookup m.fs path = some data) (gap : modeledFileGap data off bs = true)
    (o : Outcome SyscallEffect) :
    writeSpecWith access fd buf count i m o ↔
      o = .ok ((mkEffect (lenWord bs) [] []).withCopyins [(buf, bs.length)])
        ((m.withFs (Fs.set m.fs path (Fs.fileWrite data off bs))).withFds
          (fdInsert m.fds fd (.fileW path (off + lenWord bs)))) [] := by
  unfold writeSpecWith
  simp only [input_bind_iff, getModel_bind_iff, lookup]
  unfold writeFileWith writeRangeGateWith writeFileTailWith
  simp only [modeled, Bool.not_true, Bool.false_eq_true, ↓reduceIte, source,
    nonzero, nonempty, Bool.not_false, Bool.true_and, found, gap]
  rw [modify_bind_iff, modify_bind_iff]
  unfold writeLedger
  simp only [nonzero, Bool.false_eq_true, ↓reduceIte]
  exact recordCopyins_det (fun _ => Iff.rfl) o

theorem closeSpec_open {fd : Word} {e : FdEntry} (lookup : fdLookup m.fds fd = some e)
    (o : Outcome SyscallEffect) :
    closeSpec fd i m o ↔ o = .ok (mkEffect 0 [] []) (m.withFds (fdRemove m.fds fd)) [] := by
  unfold closeSpec
  simp only [getModel_bind_iff, lookup]
  rw [modify_bind_iff]
  exact Iff.rfl

theorem closeSpec_badfd {fd : Word} (lookup : fdLookup m.fds fd = none)
    (o : Outcome SyscallEffect) :
    closeSpec fd i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] := by
  unfold closeSpec
  simp only [getModel_bind_iff, lookup]
  exact Iff.rfl

end ReadWrite

/-! ### `read`, `write` and `close` on the hub table -/

section TableReadWrite

variable {i : SyscallInput} {m : Model}

theorem spec_read_file {off a : Word} {path data bs : List Byte} (number : i.sysno = 0)
    (clear : NativeX86.All.boundarySuspect 0 i = false)
    (lookup : fdLookup m.fds (fd32 (i.arg 0)) = some (.file path off))
    (ok : accessOkbX86 (i.arg 1) (uns (i.arg 2)) = true) (found : Fs.lookup m.fs path = some data)
    (delivered : Fs.fileRead data off (zw (rwCountClamp (i.arg 2))) = bs)
    (address : i.arg 1 = a) (writable : (readBytesMap i.wmem a (lenWord bs)).isSome = true) :
    ∀ o, spec i m o ↔
      o = .ok (mkEffect (lenWord bs) (deliveredWrites (i.arg 1) bs) [])
        (m.withFds (fdInsert m.fds (fd32 (i.arg 0)) (.file path (off + lenWord bs)))) [] := by
  intro o
  obtain ⟨w, writable'⟩ := Option.isSome_iff_exists.mp writable
  rw [← address] at writable'
  exact (spec_read number clear o).trans
    (readSpec_file (i := i) (access := accessOkbX86) lookup ok found delivered
      writable' o)

theorem spec_read_badfd (number : i.sysno = 0)
    (clear : NativeX86.All.boundarySuspect 0 i = false) (lookup : fdLookup m.fds (fd32 (i.arg 0)) = none) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] :=
  fun o => (spec_read number clear o).trans (readSpec_badfd (access := accessOkbX86) lookup o)

theorem spec_write_badfd (number : i.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 i = false) (lookup : fdLookup m.fds (fd32 (i.arg 0)) = none) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] :=
  fun o => (spec_write number clear o).trans (writeSpec_badfd (access := accessOkbX86) lookup o)

theorem spec_write_readOnly {off : Word} {path : List Byte} (number : i.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 i = false)
    (lookup : fdLookup m.fds (fd32 (i.arg 0)) = some (.file path off)) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] :=
  fun o => (spec_write number clear o).trans (writeSpec_readOnly (access := accessOkbX86) lookup o)

theorem spec_write_zero {ch : Word} (number : i.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 i = false)
    (lookup : fdLookup m.fds (fd32 (i.arg 0)) = some (.channel ch)) (nonzero : wIs0 ch = false)
    (modeled : modeledRwRangeWith accessOkbX86 (i.arg 1) (i.arg 2) = true)
    (zero : wIs0 (i.arg 2) = true) (ok : accessOkbX86 (i.arg 1) (uns (i.arg 2)) = true) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect 0 [] []) m [] :=
  fun o => (spec_write number clear o).trans (writeSpec_zero (access := accessOkbX86) lookup nonzero modeled zero ok o)

theorem spec_write_file {off : Word} {path data bs : List Byte} (number : i.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 i = false)
    (lookup : fdLookup m.fds (fd32 (i.arg 0)) = some (.fileW path off))
    (modeled : modeledRwRangeWith accessOkbX86 (i.arg 1) (i.arg 2) = true)
    (nonzero : wIs0 (i.arg 2) = false) (source : writeSource i.mem (i.arg 1) (i.arg 2) = bs)
    (nonempty : (bs.length == 0) = false) (found : Fs.lookup m.fs path = some data)
    (gap : modeledFileGap data off bs = true) :
    ∀ o, spec i m o ↔
      o = .ok ((mkEffect (lenWord bs) [] []).withCopyins [(i.arg 1, bs.length)])
        ((m.withFs (Fs.set m.fs path (Fs.fileWrite data off bs))).withFds
          (fdInsert m.fds (fd32 (i.arg 0)) (.fileW path (off + lenWord bs)))) [] :=
  fun o => (spec_write number clear o).trans
    (writeSpec_file (i := i) (access := accessOkbX86) lookup modeled nonzero
      source nonempty found gap o)

theorem spec_write_channel {ch : Word} {bs : List Byte} (number : i.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 i = false)
    (lookup : fdLookup m.fds (fd32 (i.arg 0)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (modeled : modeledRwRangeWith accessOkbX86 (i.arg 1) (i.arg 2) = true) (positive : i.arg 2 ≠ 0)
    (source : writeSource i.mem (i.arg 1) (i.arg 2) = bs) (nonempty : bs ≠ [])
    (bounded : (bs.length : Int) ≤ rwCountClamp (i.arg 2)) :
    ∀ o, spec i m o ↔ ∃ ds, Probe.WritePrefix bs ds ∧
      o = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(i.arg 1, ds.length)]) m
        (ds.map (.writeEv ch)) :=
  fun o => (Probe.native_write_iff i m o number clear lookup nonzero modeled positive source nonempty).trans
    (exists_congr fun _ => and_congr_left fun _ => Probe.writePrefix_iff bounded)

theorem spec_close_open (number : i.sysno = 3)
    (clear : NativeX86.All.boundarySuspect 3 i = false)
    (present : (fdLookup m.fds (fd32 (i.arg 0))).isSome = true) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect 0 [] []) (m.withFds (fdRemove m.fds (fd32 (i.arg 0)))) [] := by
  intro o
  obtain ⟨e, lookup⟩ := Option.isSome_iff_exists.mp present
  exact (spec_close number clear o).trans (closeSpec_open lookup o)

theorem spec_close_badfd (number : i.sysno = 3)
    (clear : NativeX86.All.boundarySuspect 3 i = false) (lookup : fdLookup m.fds (fd32 (i.arg 0)) = none) :
    ∀ o, spec i m o ↔ o = .ok (mkEffect (errnoRet EBADF) [] []) m [] :=
  fun o => (spec_close number clear o).trans (closeSpec_badfd lookup o)

end TableReadWrite

/-! ## Rules for calls with one outcome -/

namespace Probe

variable (P : Probe) {refused : RefusalFilter} {memory : Memory}

theorem exec_det {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model model' : Model} {effect : SyscallEffect} {events : List Event} {memory' : Memory}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ o = .ok effect model' events)
    (live : model'.halted = none) (lazy : model'.vmLazy = [])
    (applied : applyMemoryEffect memory effect = memory')
    (rest : Omni.Exec P.segs spec noFilter (cfgM (resume core effect.ret) memory' none model')
      (fun trace outcome => post (events ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  P.exec_sys (allowed := fun _ : Unit => True) (effect := fun _ => effect) (model' := fun _ => model')
    (events := fun _ => events) (memory' := fun _ => memory') other running
    (det_family outcomes) (fun _ _ => live) (fun _ _ => lazy) (fun _ _ => applied) ⟨(), trivial⟩
    (fun _ _ => rest)

theorem run_det {core : Silmaril.X86.State} {n : Word} {model model' : Model}
    {effect : SyscallEffect} {events : List Event} {memory' : Memory} {calls : List Call}
    {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ o = .ok effect model' events)
    (live : model'.halted = none) (lazy : model'.vmLazy = [])
    (applied : applyMemoryEffect memory effect = memory')
    (accepted : ¬ refused (P.sysInM core memory n) model effect)
    (rest : Run P.segs spec refused (cfgM (resume core effect.ret) memory' none model') calls trace
      outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some effect.ret⟩ :: calls)
      (events ++ trace) outcome :=
  P.run_sys (allowed := fun _ : Unit => True) (effect := fun _ => effect) (model' := fun _ => model')
    (events := fun _ => events) (memory' := fun _ => memory') other running
    (det_family outcomes) (fun _ _ => live) (fun _ _ => lazy) (fun _ _ => applied) () trivial
    accepted rest

/-- A call with one outcome and no memory effect. -/
theorem exec_pure {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model model' : Model} {effect : SyscallEffect} {events : List Event}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ o = .ok effect model' events)
    (live : model'.halted = none) (lazy : model'.vmLazy = [])
    (pure : applyMemoryEffect memory effect = memory)
    (rest : Omni.Exec P.segs spec noFilter (cfgM (resume core effect.ret) memory none model')
      (fun trace outcome => post (events ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  P.exec_det other running outcomes live lazy pure rest

theorem run_pure {core : Silmaril.X86.State} {n : Word} {model model' : Model}
    {effect : SyscallEffect} {events : List Event} {calls : List Call}
    {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ o = .ok effect model' events)
    (live : model'.halted = none) (lazy : model'.vmLazy = [])
    (pure : applyMemoryEffect memory effect = memory)
    (accepted : ¬ refused (P.sysInM core memory n) model effect)
    (rest : Run P.segs spec refused (cfgM (resume core effect.ret) memory none model') calls trace
      outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some effect.ret⟩ :: calls)
      (events ++ trace) outcome :=
  P.run_det other running outcomes live lazy pure accepted rest

/-- A descriptor-allocating open (`spec_openat_read`, `spec_openat_create`,
`spec_open_read`): the success continuation and one for every injected errno. -/
theorem exec_open {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model success : Model} {fd : Word} {copyins : List (Word × Nat)}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet fd r) [] []).withCopyins copyins) (openModel model success r) [])
    (live : success.halted = none) (lazy : success.vmLazy = []) (lazy₀ : model.vmLazy = [])
    (opened : Omni.Exec P.segs spec noFilter (cfgM (resume core fd) memory none success)
      (fun trace outcome => post ([] ++ trace) outcome))
    (failed : ∀ e ∈ openatErrnos,
      Omni.Exec P.segs spec noFilter (cfgM (resume core (errnoRet e)) memory none model)
        (fun trace outcome => post ([] ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  P.exec_sys (allowed := OpenAllowed)
    (effect := fun r => (mkEffect (openRet fd r) [] []).withCopyins copyins)
    (model' := openModel model success) (events := fun _ => []) (memory' := fun _ => memory)
    other running outcomes
    (fun r _ => by cases r with | none => exact live | some _ => exact running)
    (fun r _ => by cases r with | none => exact lazy | some _ => exact lazy₀)
    (fun _ _ => rfl) ⟨none, trivial⟩
    (fun r allowed => by
      cases r with
      | none => exact opened
      | some e => exact failed e allowed)

/-- The successful alternative of a descriptor-allocating open. -/
theorem run_opened {core : Silmaril.X86.State} {n : Word} {model success : Model} {fd : Word}
    {copyins : List (Word × Nat)} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet fd r) [] []).withCopyins copyins) (openModel model success r) [])
    (live : success.halted = none) (lazy : success.vmLazy = []) (lazy₀ : model.vmLazy = [])
    (accepted : ¬ refused (P.sysInM core memory n) model ((mkEffect fd [] []).withCopyins copyins))
    (rest : Run P.segs spec refused (cfgM (resume core fd) memory none success) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some fd⟩ :: calls)
      ([] ++ trace) outcome :=
  P.run_sys (allowed := OpenAllowed)
    (effect := fun r => (mkEffect (openRet fd r) [] []).withCopyins copyins)
    (model' := openModel model success) (events := fun _ => []) (memory' := fun _ => memory)
    other running outcomes
    (fun r _ => by cases r with | none => exact live | some _ => exact running)
    (fun r _ => by cases r with | none => exact lazy | some _ => exact lazy₀)
    (fun _ _ => rfl) none trivial accepted rest

/-- A channel write of `bs` (`spec_write_channel`): every delivered prefix. -/
theorem exec_channel {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model : Model} {buf ch : Word} {bs : List Byte}
    (other : n ≠ 158) (running : model.halted = none) (lazy : model.vmLazy = [])
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ ∃ ds, WritePrefix bs ds ∧
      o = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)]) model
        (ds.map (.writeEv ch)))
    (nonempty : bs ≠ [])
    (rest : ∀ ds, WritePrefix bs ds →
      Omni.Exec P.segs spec noFilter (cfgM (resume core (lenWord ds)) memory none model)
        (fun trace outcome => post (ds.map (.writeEv ch) ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  P.exec_sys (allowed := WritePrefix bs)
    (effect := fun ds => (mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)])
    (model' := fun _ => model) (events := fun ds => ds.map (.writeEv ch))
    (memory' := fun _ => memory) other running outcomes (fun _ _ => running) (fun _ _ => lazy)
    (fun _ _ => rfl) ⟨bs, nonempty, List.prefix_refl _⟩ rest

theorem run_channel {core : Silmaril.X86.State} {n : Word} {model : Model} {buf ch : Word}
    {bs : List Byte} {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (other : n ≠ 158) (running : model.halted = none) (lazy : model.vmLazy = [])
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ ∃ ds, WritePrefix bs ds ∧
      o = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)]) model
        (ds.map (.writeEv ch)))
    (ds : List Byte) (delivered : WritePrefix bs ds)
    (accepted : ¬ refused (P.sysInM core memory n) model
      ((mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)]))
    (rest : Run P.segs spec refused (cfgM (resume core (lenWord ds)) memory none model) calls trace
      outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some (lenWord ds)⟩ :: calls)
      (ds.map (.writeEv ch) ++ trace) outcome :=
  P.run_sys (allowed := WritePrefix bs)
    (effect := fun ds => (mkEffect (lenWord ds) [] []).withCopyins [(buf, ds.length)])
    (model' := fun _ => model) (events := fun ds => ds.map (.writeEv ch))
    (memory' := fun _ => memory) other running outcomes (fun _ _ => running) (fun _ _ => lazy)
    (fun _ _ => rfl) ds delivered accepted rest

/-- A call with one outcome that writes `bs` at `a` (a `read` into the stack). The
continuation runs over `memWith memory a bs`. -/
theorem exec_read_stack {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model model' : Model} {ret buf a : Word} {bs : List Byte}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔
      o = .ok (mkEffect ret (deliveredWrites buf bs) []) model' [])
    (live : model'.halted = none) (lazy : model'.vmLazy = []) (nonempty : bs ≠ [])
    (address : buf = a)
    (rest : Omni.Exec P.segs spec noFilter (cfgM (resume core ret) (memWith memory a bs) none model')
      (fun trace outcome => post ([] ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  P.exec_det (memory' := memWith memory a bs) other running outcomes live lazy (by
    subst address
    cases bs with
    | nil => exact absurd rfl nonempty
    | cons b rest => rfl) rest

theorem run_read_stack {core : Silmaril.X86.State} {n : Word} {model model' : Model}
    {ret buf a : Word} {bs : List Byte} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (other : n ≠ 158) (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔
      o = .ok (mkEffect ret (deliveredWrites buf bs) []) model' [])
    (live : model'.halted = none) (lazy : model'.vmLazy = []) (nonempty : bs ≠ [])
    (address : buf = a)
    (accepted : ¬ refused (P.sysInM core memory n) model (mkEffect ret (deliveredWrites buf bs) []))
    (rest : Run P.segs spec refused (cfgM (resume core ret) (memWith memory a bs) none model') calls
      trace outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some ret⟩ :: calls)
      ([] ++ trace) outcome :=
  P.run_det (memory' := memWith memory a bs) other running outcomes live lazy (by
    subst address
    cases bs with
    | nil => exact absurd rfl nonempty
    | cons b rest => rfl) accepted rest

end Probe

/-! ## Tactics for the file calls -/

/-- `probe_call h`: the pending call has the one outcome `h` characterizes and no
memory effect. -/
macro "probe_call " h:term:max : tactic =>
  `(tactic| ((first
    | refine Probe.exec_pure _ ?_ ?_ $h ?_ ?_ ?_ ?_
    | apply Probe.run_pure _ ?_ ?_ $h) <;> probe_sides))

/-- `probe_open h`: a descriptor-allocating open. For an `Omni.Exec` goal it
leaves the success continuation and the continuation for every injected errno;
for a `Run` goal, the successful alternative. -/
macro "probe_open " h:term:max : tactic =>
  `(tactic| ((first
    | refine Probe.exec_open _ ?_ ?_ $h ?_ ?_ ?_ ?_ ?_
    | apply Probe.run_opened _ ?_ ?_ $h) <;> probe_sides))

/-- `probe_channel h`: a channel write; for a `Run` goal pass the delivered bytes
with `probe_channel h with ds`. -/
macro "probe_channel " h:term:max : tactic =>
  `(tactic| ((refine Probe.exec_channel _ ?_ ?_ ?_ $h ?_ ?_) <;> probe_sides))

macro "probe_channel " h:term:max " with " ds:term:max : tactic =>
  `(tactic| ((apply Probe.run_channel _ ?_ ?_ ?_ $h $ds) <;> probe_sides))

/-- `probe_read h at a`: a call with one outcome that writes into the stack at `a`
(`h` characterizes it, as `spec_read_file`). The continuation runs over the
memory with the delivered bytes installed; use the `…M` tactics after it. -/
macro "probe_read " h:term:max " at " a:term:max : tactic =>
  `(tactic| ((first
    | refine Probe.exec_read_stack _ (a := $a) ?_ ?_ $h ?_ ?_ ?_ ?_ ?_
    | apply Probe.run_read_stack _ (a := $a) ?_ ?_ $h) <;> probe_sides))

/-- `probe_instr`, over any memory that holds the image (`Probe.Intact`), without
trying the `Probe.mem0` rules. -/
macro "probe_instrM " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_instrM _ (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.run_instrM _ (off := $off) (len := $len) (instruction := $instr)) <;> probe_sides)

macro "probe_trapM " off:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_trapM _ (off := $off)
    | apply Probe.run_trapM _ (off := $off)) <;> probe_sides)

macro "probe_exitM " status:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_exitM _ (status := $status)
    | apply Probe.run_exitM _ (status := $status)) <;> probe_sides)

theorem viewByte_unmapped (memory : Memory) (access : Access) (a : Word)
    (unmapped : memory.permits access a.toNat = false) : viewByte memory access a = none := by
  simp [viewByte, unmapped]

/-- A pathname whose first byte is unreadable is `EFAULT` (`read_cstr`). -/
theorem readCstr_unmapped (mp : Word → Option Byte) (a : Word) (unmapped : mp a = none) :
    readCstr mp a = .fault := by
  unfold readCstr
  rw [show pathMax = 4095 + 1 from rfl]
  simp only [readCstrAux, unmapped]

/-- A pathname at an unmapped address of `memory` is `EFAULT`. -/
theorem readCstr_view_unmapped (memory : Memory) (a : Word)
    (unmapped : memory.permits .read a.toNat = false) :
    readCstr (viewByte memory .read) a = .fault :=
  readCstr_unmapped _ _ (viewByte_unmapped _ _ _ unmapped)

end Silmaril.Process.LPS.Probes
