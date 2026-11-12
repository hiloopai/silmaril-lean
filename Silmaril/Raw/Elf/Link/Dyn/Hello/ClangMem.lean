module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccMem

/-! # hello-clang: what the loaded image provides (eager or lazy binding) -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc

/-- The image facts the proof uses. `ps` is what `puts`'s slot holds: `puts` (eager), or
`puts@plt + 6` (lazy); `GOT[2]` is the resolver `res` under lazy binding. -/
structure ClangMem (b lb ps : Word) (mem : Memory) : Prop where
  code : Loaded mem (b + 0x1000#64) clangText
  str : mem.readBytes (b + 0x2004#64).toNat 13 = some (helloStr ++ [0])
  lsm : loadN mem (b + 0x3fc0#64) 8 = some (lb + 0x2a200#64)
  dereg : loadN mem (b + 0x3fc8#64) 8 = some 0#64
  gmon : loadN mem (b + 0x3fd0#64) 8 = some 0#64
  reg : loadN mem (b + 0x3fd8#64) 8 = some 0#64
  cxa : loadN mem (b + 0x3fe0#64) 8 = some (lb + 0x472c0#64)
  dso : loadN mem (b + 0x4010#64) 8 = some (b + 0x4010#64)

/-- `puts`'s slot and `GOT[2]`. -/
structure ClangPlt (b ps res : Word) (lazy : Bool) (mem : Memory) : Prop where
  slot : loadN mem (b + 0x4000#64) 8 = some ps
  got2 : lazy = true → loadN mem (b + 0x3ff8#64) 8 = some res
  got1 : ∃ w, loadN mem (b + 0x3ff0#64) 8 = some w
  slotRW : mem.Permitted .read (b + 0x4000#64).toNat 8 ∧ mem.Permitted .write (b + 0x4000#64).toNat 8

/-- `completed.0` (`0x4018`). -/
structure ClangBss (b : Word) (mem : Memory) : Prop where
  val : loadN mem (b + 0x4018#64) 1 = some 0#64
  wr : mem.Permitted .write (b + 0x4018#64).toNat 1

theorem clangText_len : clangText.length = 0x161 := by decide +kernel

def cTextPh : Elf.Phdr := ⟨1, 5, 0x1000, 0x1000, 0x161, 0x161⟩
def cRoPh : Elf.Phdr := ⟨1, 4, 0x2000, 0x2000, 0xcc, 0xcc⟩
def cRwPh : Elf.Phdr := ⟨1, 6, 0x2dd0, 0x3dd0, 0x248, 0x250⟩

theorem clang_plain (lazy : Bool) :
    plainOk clangFile cTextPh (if lazy then clangSlotsLazy else clangSlotsEager) 0x1000 clangText = true ∧
    plainOk clangFile cRoPh (if lazy then clangSlotsLazy else clangSlotsEager) 0x2004 (helloStr ++ [0]) = true ∧
    plainOk clangFile cRwPh (if lazy then clangSlotsLazy else clangSlotsEager) 0x4018 [0] = true := by
  cases lazy <;> decide +kernel

theorem clang_slotsOk (lazy : Bool) :
    let D := if lazy then clangSlotsLazy else clangSlotsEager
    slotOk D 0x3fc0 (.addr 1 0x2a200) = true ∧ slotOk D 0x3fc8 (.abs 0) = true ∧
    slotOk D 0x3fd0 (.abs 0) = true ∧ slotOk D 0x3fd8 (.abs 0) = true ∧
    slotOk D 0x3fe0 (.addr 1 0x472c0) = true ∧ slotOk D 0x4010 (.addr 0 16400) = true ∧
    slotOk D 0x4000 (if lazy then .addr 0 0x1036 else .addr 1 0x87cc0) = true ∧
    (lazy = true → slotOk D 0x3ff8 .resolver = true) := by
  cases lazy <;> decide +kernel

theorem clang_info_f : finfo clangFile = some clangInfo := clang_info

/-- What `puts`'s slot holds initially. -/
def clangPs (b lb : Word) (lazy : Bool) : Word := if lazy then b + 0x1036#64 else lb + 0x87cc0#64

set_option maxRecDepth 20000 in
/-- **The loader relation gives the image facts**, in both binding modes. -/
theorem clangMem_of_loaded {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res : Word} {ifn : Word → Option Word} {lazy : Bool} {mem : Memory}
    (h : ExeLoaded [clangFile, Fc, Fl] [b, lb, ldb] ifn lazy res mem) :
    ClangMem b lb (clangPs b lb lazy) mem ∧ ClangPlt b (clangPs b lb lazy) res lazy mem ∧
      ClangBss b mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [clang_info_f, Option.some.injEq] at hi
  subst hi
  rw [clang_slots hc hl, Option.some.injEq] at hD
  subst hD
  have htext : cTextPh ∈ clangInfo.phs := by decide
  have hro : cRoPh ∈ clangInfo.phs := by decide
  have hrw : cRwPh ∈ clangInfo.phs := by decide
  obtain ⟨p1, p2, p3⟩ := clang_plain lazy
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := clang_slotsOk lazy
  have hstr := himg.readPlain (l := helloStr ++ [0]) hT hro rfl (by decide) (by decide +kernel)
    (by decide +kernel) (acc := .read) rfl p2
  have hlen : (helloStr ++ [0]).length = 13 := rfl
  rw [hlen] at hstr
  refine ⟨⟨?_, hstr, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact himg.readPlain (l := clangText) hT htext rfl (by decide) (by decide +kernel)
      (by decide +kernel) (acc := .execute) rfl p1
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)
  · cases lazy
    · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)
    · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)
  · intro hlz
    subst hlz
    exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) (s8 rfl) (by rfl)
  · exact himg.loadSome hrw rfl (s := 0x3ff0) (by decide) (by decide) (by decide)
  · exact himg.permittedRW hrw rfl (v := 0x4000) (len := 8) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · have hr := himg.readPlain (l := [0]) hT hrw rfl (by decide) (by decide) (by decide)
      (acc := .read) rfl p3
    obtain ⟨hwrap, -, -, hwr, -⟩ := himg.point hrw rfl (v := 0x4018) (by decide) (by decide)
    simp only at hwrap hwr
    refine ⟨?_, ?_⟩
    · simp only [loadN, Memory.readBytes]
      rw [show (1 : Nat) = [(0 : Byte)].length from rfl, hr]
      rfl
    · rw [addr_toNat hwrap]
      rw [Memory.Permitted, Memory.checkSpan_iff]
      simp only [Silmaril.Process.addressLimit]
      refine ⟨by omega, by omega, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      rw [Nat.add_zero, hwr]
      decide

theorem helloStr_cstr' {m : Memory} {b lb ps : Word} (hm : ClangMem b lb ps m) :
    Silmaril.Elf.Link.Dyn.Proc.CStr m (b + 0x2004#64) helloStr := ⟨by decide, hm.str⟩

/-! ## Frames -/

/-- The executable's image at base `b` (extent `0x4020`). -/
def ClangImg (b : Word) (a : Nat) : Prop := b.toNat ≤ a ∧ a < b.toNat + 0x4020

/-- The image without `puts`'s slot and `completed.0` (the two bytes ranges a run writes). -/
def ClangImg' (b : Word) (a : Nat) : Prop :=
  ClangImg b a ∧ ¬ (b.toNat + 0x4000 ≤ a ∧ a < b.toNat + 0x4008) ∧ a ≠ b.toNat + 0x4018

theorem ckeeps_range {b : Word} (hb : b.toNat + 0x4020 < 2 ^ 64) {P : Nat → Prop} {m m' : Memory}
    (h : Keeps P m m') {off len : Nat} (hr : off + len ≤ 0x4020)
    (hP : ∀ k < len, P (b.toNat + off + k)) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len = m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith hP

theorem ClangMem.keep {b lb ps : Word} (hb : b.toNat + 0x4020 < 2 ^ 64) {m m' : Memory}
    (hm : ClangMem b lb ps m) (h : Keeps (ClangImg' b) m m') : ClangMem b lb ps m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩ := hm
  have hl : ∀ {off : Nat}, off + 8 ≤ 0x4000 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [ckeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by omega, by omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [clangText_len] at h1 ⊢
    rw [ckeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by omega, by omega⟩)]; exact h1
  · unfold Memory.readBytes at h2 ⊢
    rw [ckeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by omega, by omega⟩)]; exact h2
  · exact (hl (off := 0x3fc0) (by decide)).trans h3
  · exact (hl (off := 0x3fc8) (by decide)).trans h4
  · exact (hl (off := 0x3fd0) (by decide)).trans h5
  · exact (hl (off := 0x3fd8) (by decide)).trans h6
  · exact (hl (off := 0x3fe0) (by decide)).trans h7
  · simp only [loadN, Memory.readBytes] at h9 ⊢
    rw [ckeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by omega, by omega⟩)]; exact h9

theorem ClangBss.keep {b : Word} (hb : b.toNat + 0x4020 < 2 ^ 64) {m m' : Memory}
    (h : ClangBss b m) (hk : Keeps (ClangImg b) m m') : ClangBss b m' := by
  refine ⟨?_, ?_⟩
  · have := h.val
    simp only [loadN, Memory.readBytes] at this ⊢
    rw [ckeeps_range hb hk (off := 0x4018) (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact this
  · have hw := h.wr
    rw [addr_toNat (by omega)] at hw ⊢
    rw [hk.permitted (fun k hk' => ⟨by omega, by omega⟩)]
    exact hw

theorem ClangPlt.keep {b ps res : Word} {lazy : Bool} (hb : b.toNat + 0x4020 < 2 ^ 64) {m m' : Memory}
    (h : ClangPlt b ps res lazy m) (hk : Keeps (ClangImg b) m m') : ClangPlt b ps res lazy m' := by
  refine ⟨?_, fun hl => ?_, ?_, ?_⟩
  · have := h.slot
    simp only [loadN, Memory.readBytes] at this ⊢
    rw [ckeeps_range hb hk (off := 0x4000) (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact this
  · have := h.got2 hl
    simp only [loadN, Memory.readBytes] at this ⊢
    rw [ckeeps_range hb hk (off := 0x3ff8) (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact this
  · obtain ⟨w, hw⟩ := h.got1
    refine ⟨w, ?_⟩
    simp only [loadN, Memory.readBytes] at hw ⊢
    rw [ckeeps_range hb hk (off := 0x3ff0) (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact hw
  · have h4 : (b + 0x4000#64).toNat = b.toNat + 0x4000 := addr_toNat (by omega)
    have hs := h.slotRW
    rw [h4] at hs ⊢
    rw [hk.permitted (fun k hk' => ⟨by omega, by omega⟩), hk.permitted (fun k hk' => ⟨by omega, by omega⟩)]
    exact hs

end Silmaril.Elf.Link.Dyn.Hello
