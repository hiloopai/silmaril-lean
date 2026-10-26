module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.StdRel
public import Silmaril.Process.LPS.Problems.Sha256Cli.Launch
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Fetchable

/-! # The launch correspondence for GNU `sha256sum` (VERIFIED)

Every admissible LPS launch of the pinned `sha256sum-min` (`X86Launch.init` of `snapshot`) is
related, under `StdRel`, to a `Launch` of the middle model: `X86Sys.Init` of
`Apps.Sha256sum.Binary.Image.image` (the `PT_LOAD` segments mapped with their bytes and
permissions, the System V stack with `argv` and `envp`, `rip` at `0x401000`, `rdx = 0`, the
heap above the image), the initial kernel of the world (descriptors 0, 1, 2), the stack window
above the image, and the image facts `ImageRo` (the headers, `.text` and `.rodata` are not
writable, so no store changes the code).

The facts about the LPS initial memory follow the `sha256` filter's `Sha256Cli.LaunchFacts`
at the GNU snapshot (the installer lemmas that do not mention the snapshot are reused).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli (Below Backed)
open Silmaril.Process.LPS.Problems.Sha256Cli.LaunchFacts (pageRoundUp_ge pageRoundUp_dvd
  pageRoundUp_of_dvd stack_get_gen zeros_get_gen foldl_install_get initialMemory_zero_bytes
  contains_of_any wordLe8_length encodeWords_singleton encodeWords_eq_flatMap stringAddrs_spec
  natToWord_toNat add_natToWord_toNat flatten_split buildAuxv_split drop_zero)

namespace LaunchFacts


/-- The entry block (stack bytes and slack). -/
abbrev block (en : ExecEntry) (inp : ProcInput) : List Byte :=
  X86Launch.entryStack snapshot.image en inp

/-- The initial memory. -/
abbrev mem₀ (en : ExecEntry) (inp : ProcInput) : Silmaril.Process.Memory :=
  initialMemory snapshot.image.segments en.sp (block en inp)

/-- The entry block ends at the page top. -/
theorem block_top (en : ExecEntry) (inp : ProcInput) :
    uns en.sp + (block en inp).length =
      entryPageTop en.sp (X86Launch.stackBytes snapshot.image en inp) := by
  have slack : ∀ (sp : Word) (bytes : List Byte) (f : Word → Byte),
      (entrySlack sp bytes f).length = entrySlackLen sp bytes := by
    intro sp bytes f; simp [entrySlack]
  simp only [block, X86Launch.entryStack, List.length_append, slack, entrySlackLen]
  have := pageRoundUp_ge (entryBlockTop en.sp (X86Launch.stackBytes snapshot.image en inp))
  simp only [entryPageTop, entryBlockTop] at this ⊢
  rw [Nat.cast_add, Int.toNat_of_nonneg (by omega)]
  omega

/-- What a valid entry gives about the stack. -/
structure Bounds (en : ExecEntry) (inp : ProcInput) : Prop where
  spLo : 0x7ffb7fffe000 ≤ en.sp.toNat
  spHi : en.sp.toNat ≤ 0x7ffffffff000
  aligned : en.sp.toNat % 16 = 0
  top : en.sp.toNat + (block en inp).length ≤ 0x7ffffffff000
  topAligned : (en.sp.toNat + (block en inp).length) % 4096 = 0

theorem bounds_of_valid {oracle : Nat → X86FlagChoices.Choice} {en : ExecEntry} {inp : ProcInput}
    (valid : X86Launch.ValidEntry (machine oracle) snapshot en inp) : Bounds en inp := by
  obtain ⟨-, lo, hi, al, -, -, -, -, top, -⟩ := valid
  have bt := block_top en inp
  have dvd := pageRoundUp_dvd (entryBlockTop en.sp (X86Launch.stackBytes snapshot.image en inp))
  simp only [x86LaunchBounds, x86AddressSpace, x86StackTopShiftMax, uns] at lo hi al top bt
  unfold entryPageTop at top bt
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  have : ((en.sp.toNat + (block en inp).length : Nat) : Int) % 4096 = 0 := by
    push_cast; rw [bt]; exact dvd
  omega

/-- The stack region. -/
def stackRegion (en : ExecEntry) (inp : ProcInput) : Silmaril.Process.Region :=
  ⟨en.sp.toNat - stackMaxSize.toNat,
    (pageRoundUp (uns en.sp + (block en inp).length)).toNat - (en.sp.toNat - stackMaxSize.toNat),
    ⟨true, true, false⟩⟩

theorem regions_eq (en : ExecEntry) (inp : ProcInput) :
    (mem₀ en inp).regions = snapshot.image.segments.map segmentRegion ++ [stackRegion en inp] := rfl

theorem stackRegion_top {en : ExecEntry} {inp : ProcInput} (b : Bounds en inp) :
    (stackRegion en inp).base + (stackRegion en inp).size = en.sp.toNat + (block en inp).length ∧
      (stackRegion en inp).base = en.sp.toNat - 0x800000 := by
  have p := pageRoundUp_of_dvd (uns en.sp + (block en inp).length) (by
    have := b.topAligned; simp only [uns]; omega)
  have sm : stackMaxSize.toNat = 0x800000 := by decide
  have e : (uns en.sp + ((block en inp).length : Int)).toNat = en.sp.toNat + (block en inp).length := by
    simp only [uns]; rw [← Nat.cast_add, Int.toNat_natCast]
  have := b.spLo
  simp only [stackRegion]
  rw [p, e, sm]
  constructor <;> omega

theorem permits_stack {en : ExecEntry} {inp : ProcInput} (b : Bounds en inp)
    (access : Silmaril.Process.Access) (h : access ≠ .execute) (a : Nat)
    (lo : en.sp.toNat - 0x800000 ≤ a) (hi : a < en.sp.toNat + (block en inp).length) :
    (mem₀ en inp).permits access a = true := by
  obtain ⟨t, base⟩ := stackRegion_top b
  unfold Silmaril.Process.Memory.permits
  rw [List.any_eq_true]
  refine ⟨stackRegion en inp, by rw [regions_eq]; simp, ?_⟩
  have c : (stackRegion en inp).Contains a := ⟨by omega, by omega⟩
  have perm : (stackRegion en inp).permissions.allows access = true := by
    cases access
    · rfl
    · rfl
    · exact absurd rfl h
  simp only [c, decide_true, perm, Bool.and_self]

theorem stack_get {en : ExecEntry} {inp : ProcInput} (b : Bounds en inp) (i : Nat)
    (bound : i < (block en inp).length) :
    (mem₀ en inp).bytes.get? (en.sp.toNat + i) = some (block en inp)[i] :=
  stack_get_gen _ _ _ i bound (by have := b.top; omega)

theorem below_get {en : ExecEntry} {inp : ProcInput} (b : Bounds en inp) (a : Nat)
    (below : a < en.sp.toNat - 0x800000) :
    (mem₀ en inp).bytes.get? a = (initialMemory snapshot.image.segments 0 []).bytes.get? a :=
  X86Launch.initialMemory_below_stack_get _ _ _ a (by simpa [stackMaxSize] using below)
    (by have := b.top; omega)

theorem zeros_get {en : ExecEntry} {inp : ProcInput} (b : Bounds en inp) (a : Nat)
    (lo : en.sp.toNat - 0x800000 ≤ a) (hi : a < en.sp.toNat) :
    (mem₀ en inp).bytes.get? a = some 0 :=
  zeros_get_gen _ _ _ a lo hi (by have := b.top; omega)

theorem bool_eq_decide (b : Bool) (P : Prop) [Decidable P] (h : P ↔ b = true) : b = decide P := by
  by_cases p : P <;> cases b <;> simp_all

/-- The region of a loaded segment, from its program header. -/
theorem region_of_header (ph : Silmaril.Formats.ELF.ProgramHeader) (kind : ph.kind = 1)
    (fits : ph.fileSize ≤ ph.memorySize) :
    segmentRegion (ELFImage.segment file ph) = ⟨ph.virtualAddress, ph.memorySize,
      ⟨decide (ph.flags / 4 % 2 = 1), decide (ph.flags / 2 % 2 = 1), decide (ph.flags % 2 = 1)⟩⟩ := by
  obtain ⟨-, va, msz, -, ex, wr, rd⟩ := ELFImage.segment_header_matches (file := file) kind fits
  simp only [segmentRegion, segmentPermissions, ← va, ← msz]
  rw [bool_eq_decide _ _ rd, bool_eq_decide _ _ wr, bool_eq_decide _ _ ex]

/-- The LPS segment regions are the transcribed image's. -/
theorem regions_image : snapshot.image.segments.map segmentRegion =
    Apps.Sha256sum.Binary.Image.image.segments.map Silmaril.Process.CLI.Segment.region := by
  show (records.image file).segments.map segmentRegion = _
  rw [segments_eq]
  simp only [List.map_cons, List.map_nil]
  rw [region_of_header _ rfl (by decide), region_of_header _ rfl (by decide),
    region_of_header _ rfl (by decide), region_of_header _ rfl (by decide)]
  decide

theorem region_mem (seg : Silmaril.Process.CLI.Segment)
    (member : seg ∈ Apps.Sha256sum.Binary.Image.image.segments) :
    seg.region ∈ snapshot.image.segments.map segmentRegion := by
  rw [regions_image]; exact List.mem_map_of_mem member

/-! ## The image -/

section Image

variable {isa : UserIsa} (valid : X86Launch.ValidSnapshot isa snapshot)
include valid

theorem seg_size : ∀ s ∈ snapshot.image.segments, s.bytes.length = s.size :=
  fun s m => (valid.2.2.1 s m).1

theorem seg_nowrap : ∀ s ∈ snapshot.image.segments, s.base + s.bytes.length ≤ 2 ^ 64 := by
  intro s m
  have := (valid.2.2.1 s m).2.2
  rw [seg_size valid s m]
  simp only [x86AddressSpace] at this
  omega

theorem seg_disjoint : snapshot.image.segments.Pairwise
    (fun a b => a.base + a.bytes.length ≤ b.base ∨ b.base + b.bytes.length ≤ a.base) := by
  have p := valid.2.2.2.1
  refine List.Pairwise.imp_of_mem ?_ p
  intro a b ma mb h
  rw [seg_size valid a ma, seg_size valid b mb]
  exact h

theorem image_get (seg : Silmaril.Process.CLI.Segment) (member : seg ∈ Apps.Sha256sum.Binary.Image.image.segments)
    (i : Nat) (bound : i < seg.contents.length) :
    (initialMemory snapshot.image.segments 0 []).bytes.get? (seg.vaddr + i) =
      some seg.contents[i] := by
  have inMap : (seg.vaddr, seg.contents) ∈ (records.image file).segments.map
      (fun s => (s.base, s.bytes)) := by
    rw [segs_bytes]; exact List.mem_map_of_mem member
  obtain ⟨s, sMem, sEq⟩ := List.mem_map.mp inMap
  simp only [Prod.mk.injEq] at sEq
  obtain ⟨hb, hbytes⟩ := sEq
  have get := foldl_install_get _ ∅ (seg_nowrap valid) (seg_disjoint valid) s sMem i
    (by rw [hbytes]; exact bound)
  rw [← hb, initialMemory_zero_bytes, get]
  simp [hbytes]

end Image

/-! ## The initial memory satisfies the CLI and relation facts -/

section Memory

variable {oracle : Nat → X86FlagChoices.Choice} {en : ExecEntry} {inp : ProcInput}
  (valid : X86Launch.ValidEntry (machine oracle) snapshot en inp)
include valid

theorem seg_below_stack : ∀ s ∈ snapshot.image.segments,
    s.base + s.size ≤ en.sp.toNat - 0x800000 := by
  intro s m
  have := valid.2.2.2.2.2.2.2.2.2 s m
  simp only [uns, stackMaxSize] at this
  omega

theorem mapped : Apps.Sha256sum.Binary.Image.image.Mapped (mem₀ en inp) := by
  have b := bounds_of_valid valid
  intro seg member
  refine ⟨?_, fun i bound => ?_⟩
  · rw [regions_eq]
    exact List.mem_append_left _ (region_mem seg member)
  · have ends : ∀ seg ∈ Apps.Sha256sum.Binary.Image.image.segments,
        seg.vaddr + seg.contents.length ≤ 0x413150 := by
      set_option maxRecDepth 200000 in decide +kernel
    have small : seg.vaddr + i < 0x413150 := by have := ends seg member; omega
    rw [below_get b _ (by have := b.spLo; omega)]
    exact image_get valid.1 seg member i bound

theorem backed : Backed (mem₀ en inp) := by
  have b := bounds_of_valid valid
  obtain ⟨t, base⟩ := stackRegion_top b
  intro a perm
  unfold Silmaril.Process.Memory.permits at perm
  rw [List.any_eq_true, regions_eq] at perm
  obtain ⟨r, rMem, rOk⟩ := perm
  replace rOk := contains_of_any rOk
  rcases List.mem_append.mp rMem with inSegs | inStack
  · obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp inSegs
    have below := seg_below_stack valid s sMem
    obtain ⟨lo, hi⟩ := rOk
    simp only [segmentRegion] at lo hi
    rw [below_get b _ (by omega), initialMemory_zero_bytes]
    have size := seg_size valid.1 s sMem
    have := foldl_install_get _ ∅ (seg_nowrap valid.1) (seg_disjoint valid.1) s sMem (a - s.base)
      (by omega)
    rw [show s.base + (a - s.base) = a by omega] at this
    rw [this]; rfl
  · rw [List.mem_singleton] at inStack
    subst inStack
    obtain ⟨lo, hi⟩ := rOk
    by_cases low : a < en.sp.toNat
    · rw [zeros_get b a (by omega) low]; rfl
    · have := stack_get b (a - en.sp.toNat) (by omega)
      rw [show en.sp.toNat + (a - en.sp.toNat) = a by omega] at this
      rw [this]; rfl

theorem below : Below (mem₀ en inp) := by
  have b := bounds_of_valid valid
  obtain ⟨t, base⟩ := stackRegion_top b
  intro access a perm
  unfold Silmaril.Process.Memory.permits at perm
  rw [List.any_eq_true, regions_eq] at perm
  obtain ⟨r, rMem, rOk⟩ := perm
  replace rOk := contains_of_any rOk
  simp only [taskSize]
  rcases List.mem_append.mp rMem with inSegs | inStack
  · obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp inSegs
    have below := seg_below_stack valid s sMem
    obtain ⟨lo, hi⟩ := rOk
    simp only [segmentRegion] at lo hi
    have := b.spHi
    omega
  · rw [List.mem_singleton] at inStack
    subst inStack
    obtain ⟨lo, hi⟩ := rOk
    have := b.top
    omega

end Memory

/-! ## The System V stack -/

/-- Bytes laid out in the entry block are readable there. -/
theorem bytesAt_block {oracle : Nat → X86FlagChoices.Choice} {en : ExecEntry} {inp : ProcInput}
    (valid : X86Launch.ValidEntry (machine oracle) snapshot en inp) (pre bytes post : List Byte)
    (layout : block en inp = pre ++ bytes ++ post) :
    CLI.X86Linux.BytesAt (mem₀ en inp) (en.sp.toNat + pre.length) bytes := by
  have b := bounds_of_valid valid
  have len : pre.length + bytes.length + post.length = (block en inp).length := by
    rw [layout]; simp; omega
  unfold CLI.X86Linux.BytesAt Silmaril.Process.Memory.readBytes
  refine Silmaril.X86.Memory.readWith_eq_some_iff.mpr ⟨rfl, ?_, fun i bound => ?_⟩
  · rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
    have := b.top
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega, fun o ho => ?_⟩
    exact permits_stack b .read (by decide) _ (by omega) (by omega)
  · have := stack_get b (pre.length + i) (by omega)
    rw [← Nat.add_assoc] at this
    rw [this]
    congr 1
    simp only [layout, List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left bound]

/-- The prefix of the entry block: the vector part. -/
def vectorPart (en : ExecEntry) (inp : ProcInput) : List Byte :=
  let stringBase := en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp)
  let a := stringAddrs stringBase inp.argv
  let e := stringAddrs a.2 inp.envp
  wordLe8 (lenWord inp.argv) ++ a.1.flatMap wordLe8 ++ wordLe8 0 ++
    e.1.flatMap wordLe8 ++ wordLe8 0 ++ buildAuxv (X86Launch.auxiliaryEntries snapshot.image en.sp inp)

theorem block_eq (en : ExecEntry) (inp : ProcInput) :
    block en inp = vectorPart en inp ++ flattenStrings inp.argv ++ flattenStrings inp.envp ++
      X86Launch.platformBytes ++ List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++
      atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack := by
  simp only [block, X86Launch.entryStack, X86Launch.stackBytes, vectorPart, List.append_assoc]

theorem vectorPart_length (en : ExecEntry) (inp : ProcInput) :
    (vectorPart en inp).length = X86Launch.structureSize inp.argv inp.envp := by
  have la := (stringAddrs_spec inp.argv (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))).1
  have le := (stringAddrs_spec inp.envp (stringAddrs (en.sp + natToWord
    (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2).1
  have flatLen : ∀ ws : List Word, (ws.flatMap wordLe8).length = 8 * ws.length := by
    intro ws; induction ws with
    | nil => rfl
    | cons w ws ih => simp [List.flatMap_cons, wordLe8_length, ih]; omega
  simp only [vectorPart, List.length_append, wordLe8_length, flatLen]
  rw [la, le]
  simp [buildAuxv, X86Launch.auxiliaryEntries, wordLe8_length, X86Launch.structureSize,
    X86Launch.auxiliarySize, X86Launch.auxiliaryCount]
  omega

section Stack

variable {oracle : Nat → X86FlagChoices.Choice} {en : ExecEntry} {inp : ProcInput}
  (valid : X86Launch.ValidEntry (machine oracle) snapshot en inp)
include valid

theorem stackLayout (message : List Byte) :
    CLI.X86Linux.StackLayout ⟨inp.argv, inp.envp, .ofList message⟩ (mem₀ en inp) en.sp.toNat := by
  have b := bounds_of_valid valid
  have blk := block_eq en inp
  have vlen := vectorPart_length en inp
  have total : (block en inp).length + en.sp.toNat ≤ 0x7ffffffff000 := by have := b.top; omega
  have lenEq := congrArg List.length blk
  simp only [List.length_append] at lenEq
  obtain ⟨la, ga, ea⟩ := stringAddrs_spec inp.argv
    (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
  obtain ⟨le, ge, ee⟩ := stringAddrs_spec inp.envp (stringAddrs (en.sp + natToWord
    (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2
  refine ⟨b.aligned, (stringAddrs (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
      inp.argv).1, (stringAddrs (stringAddrs (en.sp + natToWord
        (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2 inp.envp).1,
      (X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19, la, le, ?_, ?_, ?_, ?_, ?_⟩
  · -- the vectors
    have h := bytesAt_block valid [] (vectorPart en inp) (flattenStrings inp.argv ++
      flattenStrings inp.envp ++ X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk]; simp only [List.nil_append, List.append_assoc])
    simp only [List.length_nil, Nat.add_zero] at h
    convert h using 1
    rw [encodeWords_eq_flatMap]
    have aux : buildAuxv (X86Launch.auxiliaryEntries snapshot.image en.sp inp) =
        (((X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19).flatMap
          fun e => [e.1, e.2]).flatMap wordLe8 ++ wordLe8 CLI.X86Linux.atNull ++ wordLe8 0 := by
      have entries : X86Launch.auxiliaryEntries snapshot.image en.sp inp =
          (X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19 ++ [(AT_NULL, 0)] := rfl
      conv => lhs; rw [entries]
      exact buildAuxv_split _
    simp only [vectorPart]
    rw [aux]
    simp only [CLI.X86Linux.vectorWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]
    rw [la]
    simp only [lenWord, zw, BitVec.ofInt_natCast]
  · -- the argument strings
    intro i hi hs
    change i < inp.argv.length at hs
    have split := flatten_split inp.argv i hs
    have splitLen := congrArg List.length split
    simp only [List.length_append, List.length_singleton] at splitLen
    have addr : (stringAddrs (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
        inp.argv).1[i].toNat =
        en.sp.toNat + (vectorPart en inp ++ flattenStrings (inp.argv.take i)).length := by
      rw [ga i hi, add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by omega)]; omega), add_natToWord_toNat _ _ (by omega)]
      simp only [List.length_append, vlen]; omega
    rw [addr]
    exact bytesAt_block valid _ (inp.argv[i] ++ [0]) (flattenStrings (inp.argv.drop (i + 1)) ++
      flattenStrings inp.envp ++ X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk, split]; simp only [List.append_assoc])
  · -- the environment strings
    intro i hi hs
    change i < inp.envp.length at hs
    have split := flatten_split inp.envp i hs
    have splitLen := congrArg List.length split
    simp only [List.length_append, List.length_singleton] at splitLen
    have addr : (stringAddrs (stringAddrs (en.sp + natToWord
        (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2 inp.envp).1[i].toNat =
        en.sp.toNat + (vectorPart en inp ++ flattenStrings inp.argv ++
          flattenStrings (inp.envp.take i)).length := by
      rw [ge i hi, ea]
      rw [add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
          add_natToWord_toNat _ _ (by omega)]; omega)]
      rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
        add_natToWord_toNat _ _ (by omega)]
      simp only [List.length_append, vlen]; omega
    rw [addr]
    exact bytesAt_block valid _ (inp.envp[i] ++ [0]) (flattenStrings (inp.envp.drop (i + 1)) ++
      X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk, split]; simp only [List.append_assoc])
  · -- no early `AT_NULL`
    intro h
    simp (config := { decide := true }) [X86Launch.auxiliaryEntries, CLI.X86Linux.atNull, AT_PHDR,
      AT_PHENT, AT_PHNUM, AT_PAGESZ, X86Launch.AT_BASE, X86Launch.AT_FLAGS, X86Launch.AT_ENTRY,
      AT_UID, AT_EUID, X86Launch.AT_GID, X86Launch.AT_EGID, X86Launch.AT_PLATFORM, AT_HWCAP,
      X86Launch.AT_CLKTCK, AT_SECURE, AT_RANDOM, X86Launch.AT_HWCAP2, X86Launch.AT_EXECFN,
      X86Launch.AT_SYSINFO_EHDR] at h
  · -- `AT_RANDOM` points at sixteen bytes
    intro value h
    have hv : value = X86Launch.randomPtr en.sp inp.argv inp.envp := by
      simp (config := { decide := true }) [X86Launch.auxiliaryEntries, CLI.X86Linux.atRandom,
        AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, X86Launch.AT_BASE, X86Launch.AT_FLAGS,
        X86Launch.AT_ENTRY, AT_UID, AT_EUID, X86Launch.AT_GID, X86Launch.AT_EGID,
        X86Launch.AT_PLATFORM, AT_HWCAP, X86Launch.AT_CLKTCK, AT_SECURE, AT_RANDOM,
        X86Launch.AT_HWCAP2, X86Launch.AT_EXECFN, X86Launch.AT_SYSINFO_EHDR] at h
      exact h
    refine ⟨atRandomBytes en.draw.random, by simp [atRandomBytes], ?_⟩
    have addr : value.toNat = en.sp.toNat + (vectorPart en inp ++ flattenStrings inp.argv ++
        flattenStrings inp.envp ++ X86Launch.platformBytes ++
        List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0).length := by
      rw [hv, X86Launch.randomPtr, add_natToWord_toNat _ _ (by
        simp only [X86Launch.beforeRandomSize, X86Launch.platformOffset, List.length_replicate,
          ← vlen] at lenEq ⊢
        simp [X86Launch.platformBytes] at lenEq ⊢
        omega)]
      simp only [List.length_append, vlen, List.length_replicate, X86Launch.beforeRandomSize,
        X86Launch.platformOffset]
    rw [addr]
    exact bytesAt_block valid _ _
      (entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk])

/-- The vectors and the strings of the entry block, with every string above the vector words
(`SysModel.StackAbove`). -/
theorem vectorsAbove :
    ∃ (argv envp : List Word) (auxv : List (Word × Word)),
      argv.length = inp.argv.length ∧ envp.length = inp.envp.length ∧
      CLI.X86Linux.BytesAt (mem₀ en inp) en.sp.toNat
        (Machine.LittleEndian.encodeWords (CLI.X86Linux.vectorWords argv envp auxv)) ∧
      (∀ i (hi : i < argv.length) (hs : i < inp.argv.length),
        CLI.X86Linux.BytesAt (mem₀ en inp) argv[i].toNat (inp.argv[i] ++ [0])) ∧
      (∀ i (hi : i < envp.length) (hs : i < inp.envp.length),
        CLI.X86Linux.BytesAt (mem₀ en inp) envp[i].toNat (inp.envp[i] ++ [0])) ∧
      (∀ p ∈ argv ++ envp, en.sp.toNat + 8 * (argv.length + envp.length + 3) ≤ p.toNat) := by
  have b := bounds_of_valid valid
  have blk := block_eq en inp
  have vlen := vectorPart_length en inp
  have total : (block en inp).length + en.sp.toNat ≤ 0x7ffffffff000 := by have := b.top; omega
  have lenEq := congrArg List.length blk
  simp only [List.length_append] at lenEq
  obtain ⟨la, ga, ea⟩ := stringAddrs_spec inp.argv
    (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
  obtain ⟨le, ge, ee⟩ := stringAddrs_spec inp.envp (stringAddrs (en.sp + natToWord
    (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2
  refine ⟨(stringAddrs (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
      inp.argv).1, (stringAddrs (stringAddrs (en.sp + natToWord
        (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2 inp.envp).1,
      (X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19, la, le, ?_, ?_, ?_, ?_⟩
  · -- the vectors
    have h := bytesAt_block valid [] (vectorPart en inp) (flattenStrings inp.argv ++
      flattenStrings inp.envp ++ X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk]; simp only [List.nil_append, List.append_assoc])
    simp only [List.length_nil, Nat.add_zero] at h
    convert h using 1
    rw [encodeWords_eq_flatMap]
    have aux : buildAuxv (X86Launch.auxiliaryEntries snapshot.image en.sp inp) =
        (((X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19).flatMap
          fun e => [e.1, e.2]).flatMap wordLe8 ++ wordLe8 CLI.X86Linux.atNull ++ wordLe8 0 := by
      have entries : X86Launch.auxiliaryEntries snapshot.image en.sp inp =
          (X86Launch.auxiliaryEntries snapshot.image en.sp inp).take 19 ++ [(AT_NULL, 0)] := rfl
      conv => lhs; rw [entries]
      exact buildAuxv_split _
    simp only [vectorPart]
    rw [aux]
    simp only [CLI.X86Linux.vectorWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]
    rw [la]
    simp only [lenWord, zw, BitVec.ofInt_natCast]
  · -- the argument strings
    intro i hi hs
    have split := flatten_split inp.argv i hs
    have splitLen := congrArg List.length split
    simp only [List.length_append, List.length_singleton] at splitLen
    have addr : (stringAddrs (en.sp + natToWord (X86Launch.structureSize inp.argv inp.envp))
        inp.argv).1[i].toNat =
        en.sp.toNat + (vectorPart en inp ++ flattenStrings (inp.argv.take i)).length := by
      rw [ga i hi, add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by omega)]; omega), add_natToWord_toNat _ _ (by omega)]
      simp only [List.length_append, vlen]; omega
    rw [addr]
    exact bytesAt_block valid _ (inp.argv[i] ++ [0]) (flattenStrings (inp.argv.drop (i + 1)) ++
      flattenStrings inp.envp ++ X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk, split]; simp only [List.append_assoc])
  · -- the environment strings
    intro i hi hs
    have split := flatten_split inp.envp i hs
    have splitLen := congrArg List.length split
    simp only [List.length_append, List.length_singleton] at splitLen
    have addr : (stringAddrs (stringAddrs (en.sp + natToWord
        (X86Launch.structureSize inp.argv inp.envp)) inp.argv).2 inp.envp).1[i].toNat =
        en.sp.toNat + (vectorPart en inp ++ flattenStrings inp.argv ++
          flattenStrings (inp.envp.take i)).length := by
      rw [ge i hi, ea]
      rw [add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
          add_natToWord_toNat _ _ (by omega)]; omega)]
      rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
        add_natToWord_toNat _ _ (by omega)]
      simp only [List.length_append, vlen]; omega
    rw [addr]
    exact bytesAt_block valid _ (inp.envp[i] ++ [0]) (flattenStrings (inp.envp.drop (i + 1)) ++
      X86Launch.platformBytes ++
      List.replicate (X86Launch.randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random ++
      entrySlack en.sp (X86Launch.stackBytes snapshot.image en inp) en.draw.slack)
      (by rw [blk, split]; simp only [List.append_assoc])
  · -- every string lies above the vector words
    intro p hp
    have vsz : en.sp.toNat + 8 * (inp.argv.length + inp.envp.length + 3) ≤
        en.sp.toNat + (vectorPart en inp).length := by
      rw [vlen]; simp only [X86Launch.structureSize]; omega
    rw [la, le]
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      have hs : i < inp.argv.length := by rw [← la]; exact hi
      have split := flatten_split inp.argv i hs
      have splitLen := congrArg List.length split
      simp only [List.length_append, List.length_singleton] at splitLen
      rw [ga i hi, add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by omega)]; omega), add_natToWord_toNat _ _ (by omega)]
      omega
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      have hs : i < inp.envp.length := by rw [← le]; exact hi
      have split := flatten_split inp.envp i hs
      have splitLen := congrArg List.length split
      simp only [List.length_append, List.length_singleton] at splitLen
      rw [ge i hi, ea]
      rw [add_natToWord_toNat _ _ (by
        rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
          add_natToWord_toNat _ _ (by omega)]; omega)]
      rw [add_natToWord_toNat _ _ (by rw [add_natToWord_toNat _ _ (by omega)]; omega),
        add_natToWord_toNat _ _ (by omega)]
      omega

end Stack


/-! ## The image is read-only below `.data` -/

section Ro

variable {oracle : Nat → X86FlagChoices.Choice} {en : ExecEntry} {inp : ProcInput}
  (valid : X86Launch.ValidEntry (machine oracle) snapshot en inp)
include valid

theorem imageRo : ImageRo (mem₀ en inp) := by
  have b := bounds_of_valid valid
  obtain ⟨t, base⟩ := stackRegion_top b
  intro a lo hi
  unfold Silmaril.Process.Memory.permits
  rw [regions_eq, regions_image, List.any_eq_false]
  intro r hr hok
  replace hok := (Bool.and_eq_true _ _).mp hok
  have contains := of_decide_eq_true hok.1
  rcases List.mem_append.mp hr with inImage | inStack
  · simp only [Apps.Sha256sum.Binary.Image.image, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at inImage
    rcases inImage with rfl | rfl | rfl | rfl <;>
      simp_all [Silmaril.Process.CLI.Segment.region, Apps.Sha256sum.Binary.Image.seg0,
        Apps.Sha256sum.Binary.Image.seg1, Apps.Sha256sum.Binary.Image.seg2,
        Apps.Sha256sum.Binary.Image.seg3, Silmaril.Process.Permissions.allows,
        Silmaril.Process.Region.Contains]
    omega
  · rw [List.mem_singleton] at inStack
    subst inStack
    have := b.spLo
    simp only [Silmaril.Process.Region.Contains] at contains
    omega

end Ro

end LaunchFacts

open LaunchFacts in
/-- **The launch correspondence (VERIFIED).** Every admissible LPS launch of the pinned ELF is
related, under `StdRel`, to a `Launch` of the middle model on a stdin-tier world of the same
message (`argv` the LPS one, `POSIXLY_CORRECT` as the LPS environment says). -/
theorem launchObligation : LaunchObligation := by
  intro oracle limit en inp message ⟨stdin, argc, validInput, validEntry⟩
  have b := bounds_of_valid validEntry
  obtain ⟨prog, hprog⟩ : ∃ prog, inp.argv = [prog] := by
    match h : inp.argv, argc with
    | [p], _ => exact ⟨p, rfl⟩
  classical
  let posix := decide (Apps.Sha256sum.X86Sys.HasPosix inp.envp)
  let fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult := fun _ => .openErr .ENOENT
  let w := world [prog] posix fs message
  let core₀ : Silmaril.X86.State := (initial oracle limit en inp).ms.native.m.core
  let g₀ : GS := ⟨⟨core₀, mem₀ en inp,
      Apps.Sha256sum.X86Sys.imageEnd Apps.Sha256sum.Binary.Image.image,
      Apps.Sha256sum.X86Sys.imageEnd Apps.Sha256sum.Binary.Image.image, false⟩,
    Apps.Sha256sum.Sys.KState.init w, none⟩
  have rsp : core₀.read .rsp = en.sp := rfl
  have rdx : core₀.read .rdx = 0 := rfl
  have rip : core₀.rip.toNat = 0x401000 := by
    simp only [core₀, initial, X86Launch.init, initConfigWithStack, x86WithFlagOracle8]
    rw [initPc_eq]; rfl
  have memEq : (initial oracle limit en inp).ms.native.m.memory = mem₀ en inp := rfl
  have imageEnd : Apps.Sha256sum.X86Sys.imageEnd Apps.Sha256sum.Binary.Image.image = 0x413150 := by
    set_option maxRecDepth 200000 in decide +kernel
  have spStack : ∀ access : Silmaril.Process.Access, access ≠ .execute → ∀ (lo n : Nat),
      en.sp.toNat - 0x800000 ≤ lo → lo + n ≤ en.sp.toNat →
      (mem₀ en inp).Permitted access lo n := by
    intro access ne lo n hlo hn
    rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
    have := b.spHi
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega, fun o ho => ?_⟩
    exact permits_stack b access ne _ (by omega) (by omega)
  have inputOf : Apps.Sha256sum.X86Sys.InputOf w ⟨inp.argv, inp.envp, .ofList message⟩ := by
    refine ⟨?_, ?_⟩
    · show inp.argv = ([prog].map toSpec).map (·.map Apps.Sha256sum.X86Sys.ofU8)
      rw [hprog]; simp [ofU8_toSpec]
    · show _ ↔ decide _ = true
      simp
  have loaded : CLI.X86Linux.Loaded Apps.Sha256sum.Binary.Image.image
      ⟨inp.argv, inp.envp, .ofList message⟩ core₀ (mem₀ en inp) := by
    refine ⟨mapped validEntry, by rw [rip]; rfl, by rw [rsp]; exact stackLayout validEntry message,
      ?_, ?_, rdx⟩
    · rw [rsp]; have := b.spLo; simp only [CLI.X86Linux.stackRoom]; omega
    · rw [rsp]; exact spStack .write (by decide) _ _ (by simp [CLI.X86Linux.stackRoom]; omega)
        (by have := b.spLo; simp [CLI.X86Linux.stackRoom]; omega)
  have stackAbove : StackAbove w g₀ := by
    have argc1 : w.argv.length = 1 := by simp [w, world]
    refine ⟨?_, fun acc ne => ?_, ?_⟩
    · show (core₀.read .rsp).toNat ≤ _
      rw [rsp]; exact b.spHi
    · show (mem₀ en inp).Permitted acc ((core₀.read .rsp).toNat - CLI.X86Linux.stackRoom)
        (CLI.X86Linux.stackRoom + 8 * (w.argv.length + 1))
      rw [rsp, argc1]
      have blkLen := congrArg List.length (block_eq en inp)
      have vlen := vectorPart_length en inp
      simp only [List.length_append] at blkLen
      have := b.spHi
      have := b.spLo
      have := b.top
      rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
      refine ⟨by simp [Silmaril.Process.addressLimit, CLI.X86Linux.stackRoom]; omega,
        by simp [Silmaril.Process.addressLimit, CLI.X86Linux.stackRoom]; omega, fun o ho => ?_⟩
      simp only [CLI.X86Linux.stackRoom] at ho ⊢
      exact permits_stack b acc ne _ (by omega) (by
        simp only [X86Launch.structureSize] at vlen; omega)
    · obtain ⟨argv, envp, auxv, la, le, vec, sa, se, above⟩ := vectorsAbove validEntry
      exact ⟨_, argv, envp, auxv, inputOf, la, le, rsp ▸ vec, sa, se, rsp ▸ above⟩
  refine ⟨prog, posix, fs, g₀, ⟨⟨_, inputOf, loaded, le_refl _, rfl, rfl⟩, rfl, rfl, ?_,
    imageRo validEntry, stackAbove⟩, .inl ?_⟩
  · show _ ≤ (core₀.read .rsp).toNat
    rw [rsp, imageEnd]; have := b.spLo; simp only [CLI.X86Linux.stackRoom]; omega
  · refine { pending := rfl, core := Sha256Cli.FlagMono.CoreLe.refl _, memory := memEq, running := rfl,
             faulted := rfl, alive := rfl, lazy := rfl, model := ?_ }
    refine ⟨rfl, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, rfl, ?_,
      below validEntry, backed validEntry⟩
    show inp.stdin = _
    rw [stdin]
    exact (drop_zero _).symm

/-- **The simulation obligation (VERIFIED).** -/
theorem simulationObligation : SimulationObligation :=
  fun oracle refusals limit en inp message admissible =>
    simulationAt_of_syscallSim (by
      obtain ⟨prog, posix, fs, g₀, launch, related⟩ :=
        launchObligation oracle limit en inp message admissible
      exact ⟨prog, posix, fs, g₀, StdRel inp message, launch, related, syscallObligations rfl⟩)

/-- **The bridge (VERIFIED).** The middle statement implies the LPS statement. -/
theorem bridge : BridgeSegment := bridge_of_simulation simulationObligation

/-- **Glue (VERIFIED).** The LPS target from the middle statement alone. -/
theorem totalGoal_of_sys (sys : SysTotalOn fun _ => True) : TotalGoal :=
  totalOn_of_sys sys bridge

end Silmaril.Process.LPS.Problems.GnuSha256sum
