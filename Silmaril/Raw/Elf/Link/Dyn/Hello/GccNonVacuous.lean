module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccRun
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Progress

/-! # hello-gcc: the hypotheses of `hello_gcc` are satisfiable

A concrete process (`s0`): the executable at `0x555555554000`, `libc.so.6` at `0x7ffff7c00000`,
`ld.so` at `0x7ffff7fc5000`, glibc files that agree with the pinned chunks (`Fc0`, `Fl0`: the
chunks and zeros elsewhere), a memory holding exactly the loader relation's image, and a
stack with `argc = 1`. `gcc_nonvacuous` proves that it meets every hypothesis of `hello_gcc`
(`ExeLoaded`, `GccStartState`, `GccEnv`), so the theorem is not vacuous, and `gcc_s0` is the
theorem's conclusion for it.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello.NonVacuous

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Hello

/-- A file holding the chunks, zeros elsewhere. -/
def blobOf (cs : List Chunk) : Blob :=
  ⟨cs.foldr (fun c n => n ||| ((c.n % 2 ^ (8 * c.len)) <<< (8 * c.off))) 0,
    (cs.map fun c => c.off + c.len).foldr max 0⟩

def Fc0 : Blob := blobOf libcChunks
def Fl0 : Blob := blobOf ldChunks

theorem hFc : ChunksOf Fc0 libcChunks := by
  unfold ChunksOf; decide +kernel

theorem hFl : ChunksOf Fl0 ldChunks := by
  unfold ChunksOf; decide +kernel

def b0 : Word := 0x555555554000#64
def lb0 : Word := 0x7ffff7c00000#64
def ldb0 : Word := 0x7ffff7fc5000#64
def gate0 : Word := 0x7ffff7c29d90#64
def sp0 : Word := 0x7ffffffde000#64
def ifn0 : Word → Option Word := fun _ => none
def res0 : Word := 0#64

/-- The slot table at these bases. -/
def T0 : List (Nat × Option Word) :=
  [(0x3db8, some (b0 + 0x1160#64)), (0x3dc0, some (b0 + 0x1120#64)), (0x4008, some (b0 + 0x4008#64)),
   (0x3fd8, some (lb0 + 0x2a200#64)), (0x3fe0, some 0#64), (0x3fe8, some 0#64), (0x3ff0, some 0#64),
   (0x3ff8, some (lb0 + 0x472c0#64)), (0x3fd0, some (lb0 + 0x87cc0#64))]

theorem hT0 : gccSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some T0 := by decide +kernel

/-- The `PT_LOAD` headers. -/
def loads : List Elf.Phdr := gccInfo.phs.filter (·.kind == 1)

/-- The segment holding `v`. -/
def segOf (v : Nat) : Option Elf.Phdr := loads.find? fun ph => ph.vaddr ≤ v && v < ph.vaddr + ph.memsz

/-- The byte the loader relation asks for at `v`. -/
def byteAt (v : Nat) : Byte :=
  match segOf v with
  | some ph => match expectedByte gccFile T0 ph v with
    | some (some x) => x
    | _ => 0
  | none => 0

@[irreducible] def img : List Byte := (List.range 0x4018).map byteAt

def perm (r w x : Bool) : Permissions := ⟨r, w, x⟩

def regions0 : List Region :=
  [⟨b0.toNat, 0x628, perm true false false⟩, ⟨b0.toNat + 0x1000, 0x179, perm true false true⟩,
   ⟨b0.toNat + 0x2000, 0xec, perm true false false⟩, ⟨b0.toNat + 0x3db8, 0x248, perm true false false⟩,
   ⟨b0.toNat + 0x4000, 0x18, perm true true false⟩, ⟨sp0.toNat - 4096, 8192, perm true true false⟩]

/-- The stack: `argc = 1` at `sp0`, zeros around it. -/
@[irreducible] def stack0 : List Byte := (List.range 8192).map fun k => if k = 4096 then 1#8 else 0#8

@[irreducible] def mem0 : Memory :=
  ⟨regions0, Memory.install (Memory.install ∅ b0.toNat img) (sp0.toNat - 4096) stack0⟩

theorem b0_toNat : b0.toNat = 0x555555554000 := rfl
theorem sp0_toNat : sp0.toNat = 0x7ffffffde000 := rfl

/-- The per-byte table: every byte of every segment lies in that segment alone, has a value in
the model, and has the segment's permissions in `mem0`. -/
def tableOk : Bool :=
  loads.all fun ph => (List.range ph.memsz).all fun k =>
    let v := ph.vaddr + k
    segOf v == some ph && (expectedByte gccFile T0 ph v).isSome &&
    mem0.permits .read (b0.toNat + v) == (ph.flags / 4 % 2 == 1) &&
    mem0.permits .execute (b0.toNat + v) == (ph.flags % 2 == 1) &&
    mem0.permits .write (b0.toNat + v) == (ph.flags / 2 % 2 == 1 && !inRelro gccInfo v)

theorem tableOk_true : tableOk = true := by decide +kernel

theorem img_get {v : Nat} (hv : v < 0x4018) : mem0.bytes.get? (b0.toNat + v) = some (byteAt v) := by
  unfold mem0
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inl (by rw [b0_toNat, sp0_toNat]; omega))]
  rw [Memory.install_get _ _ _ _ (by unfold img; simp; exact hv)]
  unfold img
  simp

theorem imageOk0 : ImageOk ⟨gccFile, b0⟩ gccInfo T0 mem0 := by
  intro ph hph hk v h1 h2
  have hl : ph ∈ loads := List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have ht := List.all_eq_true.mp (List.all_eq_true.mp tableOk_true ph hl) (v - ph.vaddr)
    (List.mem_range.mpr (by omega))
  simp only [Nat.add_sub_cancel' h1, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hseg, hsome⟩, hr⟩, hx⟩, hw⟩ := ht
  have hlt : ph.vaddr + ph.memsz ≤ 0x4018 := by
    have := List.all_eq_true.mp (show (loads.all fun ph => decide (ph.vaddr + ph.memsz ≤ 0x4018)) = true
      by decide +kernel) ph hl
    simpa using this
  have haddr : (b0 + BitVec.ofNat 64 v).toNat = b0.toNat + v := addr_toNat (by rw [b0_toNat]; omega)
  dsimp only
  rw [haddr]
  refine ⟨by rw [b0_toNat]; omega, hr, hx, hw, ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨e, he, by rw [img_get (by omega)]; rfl, fun x hx' => ?_⟩
  rw [img_get (by omega)]
  subst hx'
  simp [byteAt, hseg, he]

theorem loaded0 : ExeLoaded [gccFile, Fc0, Fl0] [b0, lb0, ldb0] ifn0 false res0 mem0 :=
  ⟨gccFile, b0, gccInfo, gccSlots, T0, rfl, rfl, gcc_info,
    ⟨fun h => absurd h (by decide), gcc_slots hFc hFl, hT0, imageOk0⟩⟩

def core0 : State := ⟨fun r => if r = .rsp then sp0 else 0, b0 + 0x1080#64, ⟨none, none, none, none, none, none⟩, 0⟩

def s0 : PState := ⟨⟨core0, mem0⟩, { jobs := [], out := [], atexit := [], done := none }⟩

theorem env0 : GccEnv b0 lb0 gate0 := by
  refine ⟨by rw [b0_toNat]; decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | (simp only [GccImg, b0_toNat]; decide)

theorem stack_len : stack0.length = 8192 := by
  unfold stack0; rw [List.length_map, List.length_range]

theorem stack0_get? (k : Nat) : stack0[k]? = if k < 8192 then some (if k = 4096 then 1#8 else 0#8) else none := by
  unfold stack0
  by_cases h : k < 8192
  · simp [h]
  · simp [h]

theorem stack_get {k : Nat} (hk : k < 8192) :
    mem0.bytes.get? (sp0.toNat - 4096 + k) = stack0[k]? := by
  unfold mem0
  rw [Memory.install_get _ _ _ _ (by rw [stack_len]; exact hk), List.getElem?_eq_getElem]

theorem stack_permits {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : sp0.toNat - 4096 ≤ a) (h2 : a < sp0.toNat + 4096) : mem0.permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  refine ⟨⟨sp0.toNat - 4096, 8192, perm true true false⟩, by simp [mem0, regions0], ?_⟩
  rcases hacc with rfl | rfl <;>
    simp [Region.Contains, perm, Permissions.allows] <;> omega

theorem start0 (rel : Bool) : GccStartState (gccWorld b0 lb0 gate0 rel) b0 s0 1#64 := by
  have hsp : core0.read .rsp = sp0 := rfl
  refine ⟨rfl, by show (core0.read .rsp).toNat % 16 = 0; rw [hsp, sp0_toNat], ?_, ?_, rfl⟩
  · refine ⟨by show 4096 ≤ (core0.read .rsp).toNat; rw [hsp, sp0_toNat]; decide,
      by show (core0.read .rsp).toNat + 8 < 2 ^ 64; rw [hsp, sp0_toNat]; decide, fun a h1 h2 => ?_⟩
    change sp0.toNat - 4096 ≤ a at h1
    change a < sp0.toNat + 8 at h2
    show mem0.permits _ a = true ∧ mem0.permits _ a = true ∧ _
    have h3 : a < sp0.toNat + 4096 := by rw [sp0_toNat] at h2 ⊢; omega
    refine ⟨stack_permits (Or.inl rfl) h1 h3, stack_permits (Or.inr rfl) h1 h3, ?_⟩
    rintro (h | h)
    · simp only [gccWorld_inImage, GccImg, b0_toNat, sp0_toNat] at h h1 h2
      omega
    · simp [gccWorld] at h
  · show mem0.readBytes (core0.read .rsp).toNat 8 = _
    rw [hsp]
    have := readWith_of_points (mem := mem0) (acc := .read)
      (l := Silmaril.Machine.LittleEndian.encodeWords [1#64]) (a := sp0.toNat)
      (by simp [sp0_toNat]) (by simp [sp0_toNat]) (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        refine ⟨stack_permits (Or.inl rfl) (by rw [sp0_toNat]; omega) (by rw [sp0_toNat]; omega), ?_⟩
        have := stack_get (k := 4096 + k) (by omega)
        rw [show sp0.toNat - 4096 + (4096 + k) = sp0.toNat + k by rw [sp0_toNat]; omega] at this
        rw [this, stack0_get?]
        have h1 : Silmaril.Machine.LittleEndian.encodeWords [1#64] =
            [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by decide
        simp only [h1]
        interval_cases k <;> rfl)
    simpa [Memory.readBytes] using this

/-- **Non-vacuity**: a concrete loaded process meets every hypothesis of `hello_gcc`. -/
theorem gcc_nonvacuous (rel : Bool) :
    ChunksOf Fc0 libcChunks ∧ ChunksOf Fl0 ldChunks ∧ GccEnv b0 lb0 gate0 ∧
    ExeLoaded [gccFile, Fc0, Fl0] [b0, lb0, ldb0] ifn0 false res0 s0.m.memory ∧
    GccStartState (gccWorld b0 lb0 gate0 rel) b0 s0 1#64 :=
  ⟨hFc, hFl, env0, loaded0, start0 rel⟩

/-- `hello_gcc` for that process. -/
theorem gcc_s0 (rel : Bool) : MustQ (gccWorld b0 lb0 gate0 rel) (HelloDone rel) s0 :=
  hello_gcc hFc hFl env0 loaded0 (start0 rel)

/-- **A run exists**: the process machine always has an outcome (`proc_progress`), so the
`Must` of `gcc_s0` yields an actual run of the concrete process that ends with status 0 having
written `"hello, world\n"` (exactly, when writes do not fail). -/
theorem gcc_room (rel : Bool) : (gccWorld b0 lb0 gate0 rel).base.toNat + (gccWorld b0 lb0 gate0 rel).size ≤ 2 ^ 62 := by
  show b0.toNat + 0x4018 ≤ 2 ^ 62
  rw [b0_toNat]; decide

theorem gcc_progress (rel : Bool) : Silmaril.X86.RelIsa.Progress (proc (gccWorld b0 lb0 gate0 rel)) :=
  proc_progress _ (gcc_room rel) (fun a h => by simp [gccWorld] at h) (fun res slots h => by cases h) (fun n s => ⟨.stop, rfl⟩)

theorem gcc_s0_run (rel : Bool) :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (gccWorld b0 lb0 gate0 rel)) (fun _ => True) s0 t ∧
      HelloDone rel t :=
  Silmaril.X86.RelIsa.Must.exists_run (gcc_progress rel) trivial (gcc_s0 rel)

end Silmaril.Elf.Link.Dyn.Hello.NonVacuous
