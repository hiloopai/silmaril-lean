module

public import Silmaril.Process.LPS.Problems.Sha256Cli.ReadSim

/-! # The launch: an LPS launch of the pinned ELF is a CLI launch (VERIFIED)

Facts about the LPS initial memory `initialMemory segments sp (entryStack …)` of a valid entry:
the entry block ends at a page boundary below `TASK_SIZE`, the stack region is mapped
read-write and fully backed, the entry block and the zeros below it are where the installer
put them, and the image bytes are those of the chain's CLI image.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines

namespace LaunchFacts

/-- The entry block (stack bytes and slack). -/
abbrev block (en : ExecEntry) (inp : ProcInput) : List Byte :=
  X86Launch.entryStack snapshot.image en inp

/-- The initial memory. -/
abbrev mem₀ (en : ExecEntry) (inp : ProcInput) : Silmaril.Process.Memory :=
  initialMemory snapshot.image.segments en.sp (block en inp)

theorem pageRoundUp_ge (n : Int) : n ≤ pageRoundUp n := by
  unfold pageRoundUp pageSize; omega

theorem pageRoundUp_dvd (n : Int) : pageRoundUp n % 4096 = 0 := by
  unfold pageRoundUp pageSize; omega

theorem pageRoundUp_of_dvd (n : Int) (h : n % 4096 = 0) : pageRoundUp n = n := by
  unfold pageRoundUp pageSize; omega

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

/-- The stack installs, for any segments. -/
theorem stack_get_gen (segs : List Segment) (sp : Word) (stack : List Byte) (i : Nat)
    (bound : i < stack.length) (nowrap : sp.toNat + stack.length ≤ 2 ^ 64) :
    (initialMemory segs sp stack).bytes.get? (sp.toNat + i) = some stack[i] :=
  installWrapping_get _ _ _ i bound nowrap

theorem zeros_get_gen (segs : List Segment) (sp : Word) (stack : List Byte) (a : Nat)
    (lo : sp.toNat - 0x800000 ≤ a) (hi : a < sp.toNat) (nowrap : sp.toNat + stack.length ≤ 2 ^ 64) :
    (initialMemory segs sp stack).bytes.get? a = some 0 := by
  have sm : stackMaxSize.toNat = 0x800000 := by decide
  show (installWrapping (installWrapping _ (sp.toNat - stackMaxSize.toNat)
    (List.replicate (sp.toNat - (sp.toNat - stackMaxSize.toNat)) 0)) sp.toNat stack).get? a = _
  rw [installWrapping_outside _ _ _ _ nowrap (.inl hi), sm]
  have := installWrapping_get (segs.foldl
      (fun acc segment => installWrapping acc segment.base segment.bytes) ∅)
    (sp.toNat - 0x800000) (List.replicate (sp.toNat - (sp.toNat - 0x800000)) 0)
    (a - (sp.toNat - 0x800000)) (by simp; omega) (by simp; have := sp.isLt; omega)
  rw [show sp.toNat - 0x800000 + (a - (sp.toNat - 0x800000)) = a by omega] at this
  rw [this]; simp

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

/-! ## The image -/

set_option maxRecDepth 100000 in
theorem segs_bytes : (records.image file).segments.map (fun s => (s.base, s.bytes)) =
    CLI.Sha256Cli.image.segments.map (fun s => (s.vaddr, s.contents)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem segs_shape : (records.image file).segments.map (fun s => (s.base, s.bytes.length)) =
    [(0x400000, 1472), (0x4015c0, 192)] := by
  decide +kernel

/-- Installing disjoint, non-wrapping segments puts each segment's bytes at its base. -/
theorem foldl_install_get :
    ∀ (segs : List Segment) (acc : Silmaril.Process.ByteMemory),
      (∀ s ∈ segs, s.base + s.bytes.length ≤ 2 ^ 64) →
      segs.Pairwise (fun a b => a.base + a.bytes.length ≤ b.base ∨ b.base + b.bytes.length ≤ a.base) →
      ∀ s ∈ segs, ∀ i (bound : i < s.bytes.length),
        (segs.foldl (fun acc s => installWrapping acc s.base s.bytes) acc).get? (s.base + i) =
          some s.bytes[i] := by
  intro segs
  induction segs using List.reverseRecOn with
  | nil => intro _ _ _ s mem; simp at mem
  | append_singleton rest last ih =>
    intro acc nowrap disjoint s mem i bound
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.pairwise_append] at disjoint
    rcases List.mem_append.mp mem with inRest | isLast
    · have apart := disjoint.2.2 s inRest last (List.mem_singleton_self _)
      rw [installWrapping_outside _ _ _ _ (nowrap last (by simp)) (by omega)]
      exact ih acc (fun t ht => nowrap t (by simp [ht])) disjoint.1 s inRest i bound
    · rw [List.mem_singleton] at isLast
      subst isLast
      exact installWrapping_get _ _ _ i bound (nowrap _ (by simp))

theorem initialMemory_zero_bytes (segs : List Segment) :
    (initialMemory segs 0 []).bytes = segs.foldl (fun acc s => installWrapping acc s.base s.bytes) ∅ :=
  rfl

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

theorem image_get (seg : Silmaril.Process.CLI.Segment) (member : seg ∈ CLI.Sha256Cli.image.segments)
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

theorem region_mem (seg : Silmaril.Process.CLI.Segment)
    (member : seg ∈ CLI.Sha256Cli.image.segments) :
    seg.region ∈ snapshot.image.segments.map segmentRegion := by
  have inMap : (seg.vaddr, seg.contents) ∈ (records.image file).segments.map
      (fun s => (s.base, s.bytes)) := by
    rw [segs_bytes]; exact List.mem_map_of_mem member
  obtain ⟨s, sMem, sEq⟩ := List.mem_map.mp inMap
  simp only [Prod.mk.injEq] at sEq
  obtain ⟨hb, hbytes⟩ := sEq
  obtain ⟨ph, phMem, kind, va, msz, -, ex, wr, rd⟩ := valid.2.1.1 s sMem
  refine List.mem_map.mpr ⟨s, sMem, ?_⟩
  have size : s.size = seg.contents.length := by rw [← seg_size valid s sMem, hbytes]
  change ph ∈ [textHeader, bssHeader, stackHeader] at phMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at phMem
  change seg ∈ [CLI.Sha256Cli.Binary.seg0, CLI.Sha256Cli.Binary.seg1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have c0 : CLI.Sha256Cli.Binary.seg0.contents.length = 0x5c0 := by
    set_option maxRecDepth 100000 in decide +kernel
  have c1 : CLI.Sha256Cli.Binary.seg1.contents.length = 0xc0 := by
    set_option maxRecDepth 100000 in decide +kernel
  simp only [segmentRegion, segmentPermissions, Silmaril.Process.CLI.Segment.region]
  rcases member with rfl | rfl <;> rcases phMem with rfl | rfl | rfl <;>
    simp_all [textHeader, bssHeader, stackHeader, CLI.Sha256Cli.Binary.seg0,
      CLI.Sha256Cli.Binary.seg1]

end Image

/-! ## The initial memory satisfies the CLI and relation facts -/

theorem contains_of_any {r : Silmaril.Process.Region} {a : Nat} {acc : Silmaril.Process.Access}
    (h : (decide (r.Contains a) && r.permissions.allows acc) = true) :
    r.base ≤ a ∧ a < r.base + r.size :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1

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

theorem mapped : CLI.Sha256Cli.image.Mapped (mem₀ en inp) := by
  have b := bounds_of_valid valid
  intro seg member
  refine ⟨?_, fun i bound => ?_⟩
  · rw [regions_eq]
    exact List.mem_append_left _ (region_mem valid.1 seg member)
  · have small : seg.vaddr + i < 0x401680 := by
      change seg ∈ [CLI.Sha256Cli.Binary.seg0, CLI.Sha256Cli.Binary.seg1] at member
      have c0 : CLI.Sha256Cli.Binary.seg0.contents.length = 0x5c0 := by
        set_option maxRecDepth 100000 in decide +kernel
      have c1 : CLI.Sha256Cli.Binary.seg1.contents.length = 0xc0 := by
        set_option maxRecDepth 100000 in decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [c0] at bound; simp only [CLI.Sha256Cli.Binary.seg0]; omega
      · rw [c1] at bound; simp only [CLI.Sha256Cli.Binary.seg1]; omega
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

theorem wordLe8_length (w : Word) : (wordLe8 w).length = 8 := by simp [wordLe8]

theorem encodeWords_singleton (w : Word) :
    Silmaril.Machine.LittleEndian.encodeWords [w] = wordLe8 w := by
  apply List.ext_getElem
  · simp [wordLe8]
  · intro i h1 h2
    rw [Silmaril.Machine.LittleEndian.encodeWords_get]
    simp only [wordLe8, List.getElem_map, List.getElem_range, Silmaril.Machine.LittleEndian.wordByte]
    have : i / 8 = 0 := by simp at h1; omega
    simp only [this, List.getElem_cons_zero]
    have hi : i % 8 = i := by simp at h1; omega
    rw [hi]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.extractLsb', BitVec.toNat_ushiftRight]

theorem encodeWords_eq_flatMap :
    ∀ ws : List Word, Silmaril.Machine.LittleEndian.encodeWords ws = ws.flatMap wordLe8
  | [] => rfl
  | w :: ws => by
    rw [show w :: ws = [w] ++ ws from rfl, Silmaril.Machine.LittleEndian.encodeWords_append,
      encodeWords_singleton, encodeWords_eq_flatMap ws]
    rfl

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

/-- `stringAddrs` puts the `i`-th string after the first `i` NUL-terminated strings. -/
theorem stringAddrs_spec : ∀ (strs : List (List Byte)) (base : Word),
    (stringAddrs base strs).1.length = strs.length ∧
    (∀ i (h : i < (stringAddrs base strs).1.length),
      (stringAddrs base strs).1[i] = base + natToWord (flattenStrings (strs.take i)).length) ∧
    (stringAddrs base strs).2 = base + natToWord (flattenStrings strs).length
  | [], base => by simp [stringAddrs, flattenStrings, natToWord, zw]
  | s :: rest, base => by
    obtain ⟨l, g, e⟩ := stringAddrs_spec rest (base + lenWord s + 1)
    have shift : ∀ k : Nat, base + lenWord s + 1 + natToWord k =
        base + natToWord ((s ++ [0]).length + k) := by
      intro k
      simp only [lenWord, natToWord, zw, List.length_append, List.length_singleton]
      rw [BitVec.add_assoc, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofInt]
      omega
    refine ⟨by simp only [stringAddrs, List.length_cons]; exact congrArg (· + 1) l, ?_, ?_⟩
    · intro i h
      cases i with
      | zero => simp [stringAddrs, flattenStrings, natToWord, zw]
      | succ i =>
        simp only [stringAddrs, List.getElem_cons_succ]
        rw [g i (by simpa [stringAddrs] using h), shift]
        simp [flattenStrings, List.take_succ_cons, List.flatMap_cons]
        congr 1; omega
    · simp only [stringAddrs]
      rw [e, shift]
      simp [flattenStrings, List.flatMap_cons]
      congr 1; omega

theorem natToWord_toNat (k : Nat) (h : k < 2 ^ 64) : (natToWord k).toNat = k := by
  rw [natToWord, zw, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem add_natToWord_toNat (w : Word) (k : Nat) (h : w.toNat + k < 2 ^ 64) :
    (w + natToWord k).toNat = w.toNat + k := by
  rw [BitVec.toNat_add, natToWord_toNat k (by omega)]
  exact Nat.mod_eq_of_lt h

theorem flatten_split (strs : List (List Byte)) (i : Nat) (h : i < strs.length) :
    flattenStrings strs =
      flattenStrings (strs.take i) ++ (strs[i] ++ [0]) ++ flattenStrings (strs.drop (i + 1)) := by
  have e : strs = strs.take i ++ strs[i] :: strs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons h, List.take_append_drop]
  conv => lhs; rw [e]
  rw [flattenStrings, List.flatMap_append, List.flatMap_cons]
  simp only [flattenStrings, List.append_assoc]

theorem buildAuxv_split (auxv : List (Word × Word)) :
    buildAuxv (auxv ++ [(AT_NULL, 0)]) =
      (auxv.flatMap fun e => [e.1, e.2]).flatMap wordLe8 ++ wordLe8 CLI.X86Linux.atNull ++ wordLe8 0 := by
  have h : ∀ l : List (Word × Word), l.flatMap (fun e => wordLe8 e.1 ++ wordLe8 e.2) =
      (l.flatMap fun e => [e.1, e.2]).flatMap wordLe8 := by
    intro l; induction l with
    | nil => rfl
    | cons e l ih => simp [List.flatMap_cons, ih]
  simp [buildAuxv, List.flatMap_append, h, AT_NULL, CLI.X86Linux.atNull]

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

end Stack

set_option maxRecDepth 100000 in
theorem initPc_eq : snapshot.image.initPc = 0x4000f0 := by
  show (records.image file).initPc = _
  decide +kernel

theorem drop_zero (s : InputStream) : InputStream.drop s 0 = s :=
  StreamFacts.ext fun i => by simp [InputStream.drop]

end LaunchFacts

open LaunchFacts in
/-- **The launch obligation (VERIFIED).** Every admissible LPS launch of the pinned ELF is
related to a CLI launch of the chain's image. -/
theorem launchObligation : LaunchObligation := by
  intro oracle limit en inp message ⟨stdin, validInput, validEntry⟩
  have b := bounds_of_valid validEntry
  obtain ⟨t, base⟩ := stackRegion_top b
  let env₀ : Syscall.State := ⟨mem₀ en inp, fun fd =>
      if fd = 0 then some ⟨true, false, .ofList message, 0, []⟩
      else if fd = 1 ∨ fd = 2 then some ⟨false, true, .ofList [], 0, []⟩ else none, none⟩
  let core₀ : Silmaril.X86.State := (initial oracle limit en inp).ms.native.m.core
  have rsp : core₀.read .rsp = en.sp := rfl
  have rdx : core₀.read .rdx = 0 := rfl
  have rip : core₀.rip.toNat = 0x4000f0 := by
    simp only [core₀, initial, X86Launch.init, initConfigWithStack, x86WithFlagOracle, x86ExtNative,
      x86Ext, Silmaril.X86.State.write]
    rw [initPc_eq]; rfl
  have memEq : (initial oracle limit en inp).ms.native.m.memory = mem₀ en inp := rfl
  have spStack : ∀ access : Silmaril.Process.Access, access ≠ .execute → ∀ (lo n : Nat),
      en.sp.toNat - 0x800000 ≤ lo → lo + n ≤ en.sp.toNat →
      (mem₀ en inp).Permitted access lo n := by
    intro access ne lo n hlo hn
    rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
    have := b.spHi
    refine ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega, fun o ho => ?_⟩
    exact permits_stack b access ne _ (by omega) (by omega)
  refine ⟨⟨inp.argv, inp.envp, .ofList message⟩, ⟨core₀, env₀⟩, rfl,
    ⟨validInput.1.1.2.2.2.2.1, validInput.1.2.1.2.2.2⟩, ⟨⟨mem₀ en inp, ⟨mapped validEntry, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, rfl, by simp [CLI.StdDescriptors, env₀]⟩, ?_, ?_⟩, .inl ?_⟩
  · rw [rip]; rfl
  · rw [rsp]; exact stackLayout validEntry message
  · rw [rsp]; have := b.spLo; simp only [CLI.X86Linux.stackRoom]; omega
  · rw [rsp]; exact spStack .write (by decide) _ _ (by simp [CLI.X86Linux.stackRoom]; omega)
      (by have := b.spLo; simp [CLI.X86Linux.stackRoom]; omega)
  · exact rdx
  · show CLI.Sha256Cli.CompressionStack.Geometry (core₀.read .rsp).toNat
    rw [rsp]
    exact ⟨by have := b.spLo; omega, by have := b.spHi; simp [Silmaril.Process.addressLimit]; omega,
      b.aligned⟩
  · show CLI.Sha256Cli.CompressionStack.Mapping (mem₀ en inp) (core₀.read .rsp).toNat
    rw [rsp]
    exact ⟨spStack .read (by decide) _ _ (by omega) (by have := b.spLo; omega),
      spStack .write (by decide) _ _ (by omega) (by have := b.spLo; omega)⟩
  · refine { pending := rfl, core := FlagMono.CoreLe.refl _, memory := memEq, running := rfl,
             alive := rfl, lazy := rfl, model := ?_ }
    refine ⟨rfl, rfl, rfl, ?_, below validEntry, backed validEntry⟩
    intro d hd
    have hd' : some ⟨true, false, .ofList message, 0, []⟩ = some d := hd
    cases hd'
    show inp.stdin = _
    rw [stdin, drop_zero]
    rfl

end Silmaril.Process.LPS.Problems.Sha256Cli
