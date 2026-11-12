module

public import Silmaril.Elf.Link.Dyn.Hello.Defs
public import Silmaril.Elf.Link.Dyn.Glibc.Thms
public import Silmaril.Elf.Link.Dyn.Loader.Thms

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word)

theorem gcc_info : dynInfo.run (blobRead gccFile) = some gccInfo := by decide +kernel
theorem gcc_relas : (relas gccInfo).run (blobRead gccFile) = some (gccRela, gccJmpRel) := by
  decide +kernel
theorem gcc_bindNow : gccInfo.bindNow = true := by decide +kernel

def refsHold (b : Blob) (i : DynInfo) (R : List (Nat × Ref)) : Bool :=
  R.all fun e => (refOf i e.1).run (blobRead b) == some e.2 &&
    (lookupDef i e.2 false).run (blobRead b) == some none &&
    (lookupDef i e.2 true).run (blobRead b) == some none

theorem gcc_refs_hold : refsHold gccFile gccInfo gccRefs = true := by decide +kernel

theorem refsHold_sound {b : Blob} {i : DynInfo} {R : List (Nat × Ref)} (h : refsHold b i R = true) :
    ∀ e ∈ R, (refOf i e.1).run (blobRead b) = some e.2 ∧
      ∀ p, (lookupDef i e.2 p).run (blobRead b) = some none := by
  intro e he
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  refine ⟨this.1.1, fun p => ?_⟩
  cases p
  · exact this.1.2
  · exact this.2

/-- An executable that defines none of its references: its lookup table. -/
def exeFacts (R : List (Nat × Ref)) : List (Ref × Bool × Option Def) :=
  R.flatMap fun e => [(e.2, false, none), (e.2, true, none)]

theorem exeKnown_ok {b : Blob} {i : DynInfo} {R : List (Nat × Ref)}
    (hi : dynInfo.run (blobRead b) = some i) (h : refsHold b i R = true) :
    Known.Ok ⟨b, i, exeFacts R⟩ := by
  refine ⟨hi, ?_⟩
  intro e he
  simp only [exeFacts, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  obtain ⟨x, hx, he⟩ := he
  have := (refsHold_sound h x hx).2
  rcases he with rfl | rfl
  · exact this false
  · exact this true

/-- glibc's two objects as known objects. -/
def libcKnown (Fc : Blob) : Known := ⟨Fc, libcInfo, libcFacts⟩
def ldKnown (Fl : Blob) : Known := ⟨Fl, ldInfo, ldFacts⟩

theorem libcKnown_ok {Fc : Blob} (hc : ChunksOf Fc libcChunks) : (libcKnown Fc).Ok :=
  ⟨libc_info hc, fun e he => libc_lookup hc e he⟩

theorem ldKnown_ok {Fl : Blob} (hl : ChunksOf Fl ldChunks) : (ldKnown Fl).Ok :=
  ⟨ld_info hl, fun e he => ld_lookup hl e he⟩

/-! ## hello-gcc: the binding certificate -/

/-- The eager slot table of hello-gcc (`DF_BIND_NOW`), relative to the bases
(object 0: the executable, 1: `libc.so.6`). -/
def gccSlots : List (Nat × Val) :=
  [(0x3db8, .addr 0 4448), (0x3dc0, .addr 0 4384), (0x4008, .addr 0 16392),
   (0x3fd8, .addr 1 0x2a200), (0x3fe0, .abs 0), (0x3fe8, .abs 0), (0x3ff0, .abs 0),
   (0x3ff8, .addr 1 0x472c0), (0x3fd0, .addr 1 0x87cc0)]

/-- **The certificate check**, from the cached glibc tables: one closed kernel evaluation. -/
theorem gcc_slots_K :
    slotsWith (resolveK [exeFacts gccRefs, libcFacts, ldFacts]) false gccFile gccInfo =
      some gccSlots := by
  decide +kernel

theorem gcc_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) :
    slots [gccFile, Fc, Fl] false gccFile gccInfo = some gccSlots := by
  have := slots_of_known (ks := [⟨gccFile, gccInfo, exeFacts gccRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok gcc_info gcc_refs_hold
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) gcc_slots_K
  simpa [libcKnown, ldKnown] using this

/-! ## hello-clang: the binding certificates (eager and lazy) -/

theorem clang_info : dynInfo.run (blobRead clangFile) = some clangInfo := by decide +kernel
theorem clang_bindNow : clangInfo.bindNow = false := by decide +kernel
theorem clang_refs_hold : refsHold clangFile clangInfo clangRefs = true := by decide +kernel

/-- The relocations of hello-clang other than its `JUMP_SLOT`. -/
def clangRelaSlots : List (Nat × Val) :=
  [(0x3dd0, .addr 0 4400), (0x3dd8, .addr 0 4336), (0x4010, .addr 0 16400),
   (0x3fc0, .addr 1 0x2a200), (0x3fc8, .abs 0), (0x3fd0, .abs 0), (0x3fd8, .abs 0),
   (0x3fe0, .addr 1 0x472c0)]

/-- Eager binding (`LD_BIND_NOW`): `puts`'s slot holds `puts`. -/
def clangSlotsEager : List (Nat × Val) := clangRelaSlots ++ [(0x4000, .addr 1 0x87cc0)]

/-- Lazy binding: `GOT[1]` unconstrained, `GOT[2]` the resolver, `puts`'s slot its PLT entry's
`push`. -/
def clangSlotsLazy : List (Nat × Val) :=
  [(0x3ff0, .any), (0x3ff8, .resolver)] ++ clangRelaSlots ++ [(0x4000, .addr 0 0x1036)]

theorem clang_slots_K (lazy : Bool) :
    slotsWith (resolveK [exeFacts clangRefs, libcFacts, ldFacts]) lazy clangFile clangInfo =
      some (if lazy then clangSlotsLazy else clangSlotsEager) := by
  cases lazy <;> decide +kernel

theorem clang_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    (lazy : Bool) :
    slots [clangFile, Fc, Fl] lazy clangFile clangInfo =
      some (if lazy then clangSlotsLazy else clangSlotsEager) := by
  have := slots_of_known (ks := [⟨clangFile, clangInfo, exeFacts clangRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok clang_info clang_refs_hold
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) (clang_slots_K lazy)
  simpa [libcKnown, ldKnown] using this

end Silmaril.Elf.Link.Dyn.Hello
