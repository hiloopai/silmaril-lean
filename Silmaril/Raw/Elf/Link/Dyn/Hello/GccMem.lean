module

public import Silmaril.Elf.Link.Dyn.Hello.Cert
public import Silmaril.Elf.Link.Dyn.Hello.Listing
public import Silmaril.Elf.Link.Dyn.Image.Thms
public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-! # hello-gcc: what the loaded image provides

From `ExeLoaded` and the binding certificate `gcc_slots`: the code, the string, the GOT words
and `completed.0`, as reads of memory (`GccMem`), and their transfer across library steps and
stack writes (`GccMem.keep`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc

/-- `"hello, world"` -/
def helloStr : List Byte :=
  [0x68#8, 0x65#8, 0x6c#8, 0x6c#8, 0x6f#8, 0x2c#8, 0x20#8, 0x77#8, 0x6f#8, 0x72#8, 0x6c#8, 0x64#8]

theorem helloStr_nm : helloStr = (nm "hello, world").map (BitVec.ofNat 8) := by decide

/-- The image facts the proof uses. -/
structure GccMem (b lb : Word) (mem : Memory) : Prop where
  code : Loaded mem (b + 0x1000#64) gccText
  str : mem.readBytes (b + 0x2004#64).toNat 13 = some (helloStr ++ [0])
  lsm : loadN mem (b + 0x3fd8#64) 8 = some (lb + 0x2a200#64)
  dereg : loadN mem (b + 0x3fe0#64) 8 = some 0#64
  gmon : loadN mem (b + 0x3fe8#64) 8 = some 0#64
  reg : loadN mem (b + 0x3ff0#64) 8 = some 0#64
  cxa : loadN mem (b + 0x3ff8#64) 8 = some (lb + 0x472c0#64)
  puts : loadN mem (b + 0x3fd0#64) 8 = some (lb + 0x87cc0#64)
  dso : loadN mem (b + 0x4008#64) 8 = some (b + 0x4008#64)

theorem gccText_len : gccText.length = 0x179 := by decide +kernel

def textPh : Elf.Phdr := ⟨1, 5, 0x1000, 0x1000, 0x179, 0x179⟩
def roPh : Elf.Phdr := ⟨1, 4, 0x2000, 0x2000, 0xec, 0xec⟩
def rwPh : Elf.Phdr := ⟨1, 6, 0x2db8, 0x3db8, 0x258, 0x260⟩

theorem gcc_text_plain : plainOk gccFile textPh gccSlots 0x1000 gccText = true := by decide +kernel
theorem gcc_str_plain : plainOk gccFile roPh gccSlots 0x2004 (helloStr ++ [0]) = true := by
  decide +kernel
theorem gcc_bss_plain : plainOk gccFile rwPh gccSlots 0x4010 [0] = true := by decide +kernel

theorem gcc_slotsOk : slotOk gccSlots 0x3fd8 (.addr 1 0x2a200) = true ∧
    slotOk gccSlots 0x3fe0 (.abs 0) = true ∧ slotOk gccSlots 0x3fe8 (.abs 0) = true ∧
    slotOk gccSlots 0x3ff0 (.abs 0) = true ∧ slotOk gccSlots 0x3ff8 (.addr 1 0x472c0) = true ∧
    slotOk gccSlots 0x3fd0 (.addr 1 0x87cc0) = true ∧ slotOk gccSlots 0x4008 (.addr 0 16392) = true := by
  decide +kernel

theorem gcc_info_f : finfo gccFile = some gccInfo := gcc_info

set_option maxRecDepth 20000 in
/-- **The loader relation gives the image facts**, at every base, for every pair of glibc
files agreeing with the chunks. -/
theorem gccMem_of_loaded {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [gccFile, Fc, Fl] [b, lb, ldb] ifn false res mem) : GccMem b lb mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [gcc_info_f, Option.some.injEq] at hi
  subst hi
  rw [gcc_slots hc hl, Option.some.injEq] at hD
  subst hD
  have htext : textPh ∈ gccInfo.phs := by decide
  have hro : roPh ∈ gccInfo.phs := by decide
  have hrw : rwPh ∈ gccInfo.phs := by decide
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := gcc_slotsOk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := gccText) hT htext rfl (by decide) (by decide +kernel)
      (by decide +kernel) (acc := .execute) rfl gcc_text_plain
  · have := himg.readPlain (l := helloStr ++ [0]) hT hro rfl (by decide) (by decide +kernel)
      (by decide +kernel) (acc := .read) rfl gcc_str_plain
    have hlen : (helloStr ++ [0]).length = 13 := rfl
    rw [hlen] at this
    exact this
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)

/-- The executable's image at base `b` (extent `0x4018`). -/
def GccImg (b : Word) (a : Nat) : Prop := b.toNat ≤ a ∧ a < b.toNat + 0x4018

theorem keeps_range {b : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {m m' : Memory}
    (h : Keeps (GccImg b) m m') {off len : Nat} (hr : off + len ≤ 0x4018) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len = m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith (fun k hk => ⟨by omega, by omega⟩)

theorem keeps_loadN {b : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {m m' : Memory}
    (h : Keeps (GccImg b) m m') {off : Nat} (hr : off + 8 ≤ 0x4018) :
    loadN m' (b + BitVec.ofNat 64 off) 8 = loadN m (b + BitVec.ofNat 64 off) 8 := by
  simp only [loadN, Memory.readBytes]
  rw [keeps_range hb h hr]

theorem keeps_range' {b : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {P : Nat → Prop} {m m' : Memory}
    (h : Keeps P m m') {off len : Nat} (hr : off + len ≤ 0x4018)
    (hP : ∀ k < len, P (b.toNat + off + k)) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len = m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith hP

/-- The image without `completed.0`. -/
def GccImg' (b : Word) (a : Nat) : Prop := GccImg b a ∧ a ≠ b.toNat + 0x4010

/-- The image facts survive a step that keeps the image except `completed.0`. -/
theorem GccMem.keep' {b lb : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {m m' : Memory}
    (hm : GccMem b lb m) (h : Keeps (GccImg' b) m m') : GccMem b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hm
  have hl : ∀ {off : Nat}, off + 8 ≤ 0x4010 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [keeps_range' hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [gccText_len] at h1 ⊢
    rw [keeps_range' hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by omega⟩)]; exact h1
  · unfold Memory.readBytes at h2 ⊢
    rw [keeps_range' hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by omega⟩)]; exact h2
  · exact (hl (off := 0x3fd8) (by decide)).trans h3
  · exact (hl (off := 0x3fe0) (by decide)).trans h4
  · exact (hl (off := 0x3fe8) (by decide)).trans h5
  · exact (hl (off := 0x3ff0) (by decide)).trans h6
  · exact (hl (off := 0x3ff8) (by decide)).trans h7
  · exact (hl (off := 0x3fd0) (by decide)).trans h8
  · exact (hl (off := 0x4008) (by decide)).trans h9

/-- **The image facts survive every step that keeps the image.** -/
theorem GccMem.keep {b lb : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {m m' : Memory}
    (hm : GccMem b lb m) (h : Keeps (GccImg b) m m') : GccMem b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [gccText_len] at h1 ⊢
    rw [keeps_range hb h (by decide)]; exact h1
  · unfold Memory.readBytes at h2 ⊢
    rw [keeps_range hb h (by decide)]; exact h2
  · exact (keeps_loadN (off := 0x3fd8) hb h (by decide)).trans h3
  · exact (keeps_loadN (off := 0x3fe0) hb h (by decide)).trans h4
  · exact (keeps_loadN (off := 0x3fe8) hb h (by decide)).trans h5
  · exact (keeps_loadN (off := 0x3ff0) hb h (by decide)).trans h6
  · exact (keeps_loadN (off := 0x3ff8) hb h (by decide)).trans h7
  · exact (keeps_loadN (off := 0x3fd0) hb h (by decide)).trans h8
  · exact (keeps_loadN (off := 0x4008) hb h (by decide)).trans h9

/-- `completed.0` (`.bss`, `0x4010`): zero and writable. -/
structure GccBss (b : Word) (mem : Memory) : Prop where
  val : loadN mem (b + 0x4010#64) 1 = some 0#64
  wr : mem.Permitted .write (b + 0x4010#64).toNat 1

theorem GccBss.keep {b : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {m m' : Memory}
    (h : GccBss b m) (hk : Keeps (GccImg b) m m') : GccBss b m' := by
  refine ⟨?_, ?_⟩
  · have := h.val
    simp only [loadN, Memory.readBytes] at this ⊢
    rw [keeps_range hb hk (off := 0x4010) (by decide)]; exact this
  · have hw := h.wr
    rw [addr_toNat (by omega)] at hw ⊢
    unfold Memory.Permitted Memory.checkSpan at hw ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hw ⊢
    refine ⟨hw.1, fun k hk' => ?_⟩
    rw [(hk _ ⟨by omega, by omega⟩).2]
    exact hw.2 k hk'

set_option maxRecDepth 20000 in
theorem gccBss_of_loaded {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [gccFile, Fc, Fl] [b, lb, ldb] ifn false res mem) : GccBss b mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [gcc_info_f, Option.some.injEq] at hi
  subst hi
  rw [gcc_slots hc hl, Option.some.injEq] at hD
  subst hD
  have hrw : rwPh ∈ gccInfo.phs := by decide
  have hr := himg.readPlain (l := [0]) hT hrw rfl (by decide) (by decide) (by decide)
    (acc := .read) rfl gcc_bss_plain
  obtain ⟨hwrap, -, -, hwr, -⟩ := himg.point hrw rfl (v := 0x4010) (by decide) (by decide)
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

end Silmaril.Elf.Link.Dyn.Hello
