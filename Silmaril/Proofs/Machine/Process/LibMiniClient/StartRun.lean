module

public import Silmaril.Proofs.Machine.Process.LibMiniClient.Start
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Process

/-!
# Proofs: `Task.startRun` for ladder rung 12, and the unconditional process theorem

`startRun_holds : Task.startRun`. For every launch of the rung-12 image that LPS's x86 launch
accepts, the open machine run from the launch state does not get stuck before the
`exit(6)` request. The pieces:

* **The link** (`rung12_link`): R1's `validated_compose` on the validated ld.bfd output gives
  `Safe n` for `memset`, `memcpy` (the separation-logic layer's `fillSpec`/`copySpec`, libmini not re-verified)
  and `len1` (`len1Spec`, from R1's client contract) at their linked addresses, for every
  `n`. The bytes of `_start` and `cmain` are in the linked image (`start_in`, `cmain_in`,
  kernel evaluation of `Relocation.link`).
* **The code** (`Cmain.cmain_safeB`, `Start.start_run`): `cmain` is `SafeB (n + 1)` for
  `cmainSpec`, and `_start` runs to `ExitAt`.
* **The launch state** (this file): LPS's initial memory (`initialMemory`) holds the
  image's segments (`image_loaded`, via silmaril's `initialMemory_below_stack_get` and
  `initialMemory_segments_get`), the 64 bytes below the entry `rsp` are zero-backed and
  read-write (`stack_zero`, `stack_rw`), the entry `rsp` is 16-aligned and far above the
  image (`ValidEntry`), and `rip = 0x401000`. So the launch fragment splits as
  `Code ∗ startPre rsp ∗ F` (`launch_split`).

`rung12_processSafe_unconditional`: R8's `rung12_processSafe` with its `Task.startRun`
hypothesis discharged.

Copied (adapted): `entrySlack_length`, `entryStack_end` and `stackFits_of` from silmaril-lean
`Silmaril/Process/LPS/Probes/Launches.lean` (rev of the pinned `silmaril` package), which is
not built in this tree.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.X86 (State MState Reg)
open Silmaril.Process (Memory Region Permissions addressLimit ByteMemory)
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Formats.ELF.Link (LinkedSection)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (Le)
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.BackedSpec
open Silmaril.Machine.Link.Unit (Contains TU)
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Proofs.Machine.Link.FnSpec
open Silmaril.Proofs.Machine.Link.BackedSpec
open Silmaril.Proofs.Machine.Link.LibMiniClient
open Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity

/-! ## The link -/

set_option maxRecDepth 100000 in
theorem memset_addr : Silmaril.Machine.Link.Unit.globalValuation (units.map TU.object)
    witness.layout witness.absolute nMemset = some 0x4010b0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem memcpy_addr : Silmaril.Machine.Link.Unit.globalValuation (units.map TU.object)
    witness.layout witness.absolute nMemcpy = some 0x401080 := by decide +kernel

/-- **The callees of `cmain` in the validated link**: `memset`, `memcpy` and `len1` are
`Safe n` at their linked addresses, for every `n` (R1's `validated_compose`). -/
theorem rung12_link : ∃ out, Silmaril.X86.Linking.Relocation.link prepared witness.layout
      witness.absolute = some out ∧
    ∀ n, Safe n 0x4010b0 fillSpec out ∧ Safe n 0x401080 copySpec out ∧
      Safe n 0x401060 len1Spec out := by
  obtain ⟨records, out, -, hlink, h⟩ := validated_compose sound prep_of_parse abi units_sat
    closed
  rw [units_objects] at hlink
  refine ⟨out, hlink, fun n => ⟨?_, ?_, ?_⟩⟩
  · exact (h n 3 (libminiTU (obj 3)) rfl ⟨nMemset, .sysv64, fillSpec⟩ (by simp [libminiTU])
      0x4010b0 memset_addr).1
  · exact (h n 3 (libminiTU (obj 3)) rfl ⟨nMemcpy, .sysv64, copySpec⟩ (by simp [libminiTU])
      0x401080 memcpy_addr).1
  · exact (h n 2 (clientTU (obj 2)) rfl ⟨nLen1, .sysv64, len1Spec⟩ (List.mem_singleton_self _)
      0x401060 len1_addr).1

set_option maxRecDepth 100000 in
theorem start_in_linked : ∀ i (hi : i < startCode.length), ∃ s ∈ linked,
    s.address ≤ 0x401000 + i ∧ s.data[0x401000 + i - s.address]? = some startCode[i] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cmain_in_linked : ∀ i (hi : i < cmainCode.length), ∃ s ∈ linked,
    s.address ≤ 0x401020 + i ∧ s.data[0x401020 + i - s.address]? = some cmainCode[i] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every linked section of rung 12 is executable (flags AX). -/
theorem linked_exec : ∀ s ∈ linked, s.flags = 6 := by decide +kernel

/-- In rung 12, every linked byte is a code byte. -/
theorem containsX_linked {a : Nat} {b : BitVec 8} (h : Contains linked a b) : ContainsX linked a b := by
  obtain ⟨s, hs, hle, hb⟩ := h
  exact ⟨6, by decide, s, hs, linked_exec s hs, hle, hb⟩

set_option maxRecDepth 100000 in
/-- Every linked byte is the image's second segment's byte at that address. -/
theorem linked_in_seg1 : ∀ s ∈ linked, 0x401000 ≤ s.address ∧
    s.address + s.data.size ≤ 0x401113 ∧
    ∀ i < s.data.size, seg1.bytes[s.address - 0x401000 + i]? = s.data[i]? := by
  decide +kernel

theorem out_eq {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
      some out) : out = linked := by
  unfold linked; simp [h]

/-! ## The launch memory -/

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

set_option maxRecDepth 20000 in
theorem entrySlack_length' (sp : Word) (bytes : List Byte) (slack : Word → Byte) :
    (entrySlack sp bytes slack).length = entrySlackLen sp bytes := by
  simp [entrySlack]

/-- The entry stack fits below `2 ^ 64` (adapted from silmaril's `stackFits_of`). -/
theorem stackFits (img : Image) (en : ExecEntry) (inp : ProcInput)
    (top : entryPageTop en.sp (X86Launch.stackBytes img en inp) ≤ x86AddressSpace.taskSize) :
    en.sp.toNat + (X86Launch.entryStack img en inp).length ≤ 2 ^ 64 := by
  have e : (uns en.sp : Int) + (X86Launch.entryStack img en inp).length =
      entryPageTop en.sp (X86Launch.stackBytes img en inp) := by
    simp only [X86Launch.entryStack, List.length_append, entrySlack_length', entrySlackLen,
      entryPageTop, entryBlockTop, pageRoundUp, pageSize]
    push_cast
    omega
  have t : x86AddressSpace.taskSize = 0x7ffffffff000 := rfl
  have u : uns en.sp = (en.sp.toNat : Int) := rfl
  rw [t] at top
  rw [u] at e
  omega

/-- Zero bytes below the entry block. -/
theorem stack_zero {segs : List Segment} {sp : Word} {stack : List Byte} {a : Nat}
    (hnw : sp.toNat + stack.length ≤ 2 ^ 64) (hlo : sp.toNat - stackMaxSize.toNat ≤ a)
    (hhi : a < sp.toNat) : (initialMemory segs sp stack).bytes.get? a = some 0 := by
  change (installWrapping (installWrapping (segs.foldl (fun acc segment =>
    installWrapping acc segment.base segment.bytes) ∅) (sp.toNat - stackMaxSize.toNat)
      (List.replicate (sp.toNat - (sp.toNat - stackMaxSize.toNat)) 0)) sp.toNat stack).get? a = _
  rw [installWrapping_outside _ _ _ _ hnw (Or.inl hhi),
    installWrapping_get_ite _ _ _ _ (by simp only [List.length_replicate]; omega),
    ite_t (by simp only [List.length_replicate]; omega)]
  simp only [List.getElem?_replicate]
  rw [ite_t (by omega)]

/-- The stack region is readable and writable below the entry block. -/
theorem stack_rw {segs : List Segment} {sp : Word} {stack : List Byte} {a : Nat}
    (hlo : sp.toNat - stackMaxSize.toNat ≤ a) (hhi : a < sp.toNat) :
    RW (permsAt (initialMemory segs sp stack) a) := by
  have hreg : ∀ acc : Silmaril.Process.Access, acc ≠ .execute →
      (initialMemory segs sp stack).permits acc a = true := by
    intro acc hacc
    unfold Memory.permits
    rw [List.any_eq_true]
    refine ⟨⟨sp.toNat - stackMaxSize.toNat,
      (pageRoundUp (uns sp + stack.length)).toNat - (sp.toNat - stackMaxSize.toNat),
      ⟨true, true, false⟩⟩, by simp [initialMemory], ?_⟩
    have hu : uns sp = (sp.toNat : Int) := rfl
    simp only [Region.Contains, hu, pageRoundUp, pageSize, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hlo, by omega⟩, ?_⟩
    cases acc <;> simp_all [Permissions.allows]
  exact ⟨hreg .read (by decide), hreg .write (by decide)⟩

theorem seg_facts : seg1.executable = true ∧ seg0.executable = false := by
  have h : seg1.perms = "rx" ∧ seg0.perms = "r" := by
    set_option maxRecDepth 100000 in decide +kernel
  unfold Segment.executable
  rw [h.1, h.2]
  simp

/-- **The launch memory holds the image.** -/
theorem image_loaded {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput}
    (himg : snapshot.image = image) (hnw : en.sp.toNat +
      (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    (hbelow : 0x401113 ≤ en.sp.toNat - stackMaxSize.toNat) :
    ImageLoaded image (launchState snapshot en inp) := by
  obtain ⟨b0, s0, l0⟩ := seg0_facts
  obtain ⟨b1, s1, l1⟩ := seg1_facts
  have hsegs : image.segments = [seg0, seg1] := loadImg_segments
  have hnws : ∀ seg ∈ image.segments, seg.base + seg.bytes.length ≤ 2 ^ 64 := by
    rw [hsegs]; intro seg hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> omega
  intro seg hseg i hi b hb
  have hmem : (launchState snapshot en inp).memory =
      initialMemory image.segments en.sp (X86Launch.entryStack snapshot.image en inp) := by
    simp only [launchState, himg]
  have hget : ∀ a, a < 0x401113 → (launchState snapshot en inp).memory.bytes.get? a =
      segmentsView image.segments a none := by
    intro a ha
    rw [hmem, X86Launch.initialMemory_below_stack_get _ _ _ _ (by omega) hnw,
      initialMemory_segments_get _ _ hnws]
  rw [hsegs] at hseg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hseg
  rcases hseg with rfl | rfl
  · refine ⟨?_, fun h => by rw [seg_facts.2] at h; cases h⟩
    rw [hget _ (by omega), hsegs]
    simp only [segmentsView, List.foldl_cons, List.foldl_nil]
    rw [ite_f (by omega), ite_t (by omega)]
    simpa using hb
  · refine ⟨?_, fun _ => ?_⟩
    · rw [hget _ (by omega), hsegs]
      simp only [segmentsView, List.foldl_cons, List.foldl_nil]
      rw [ite_t (by omega)]
      simpa using hb
    · rw [hmem]
      unfold Memory.permits
      rw [List.any_eq_true]
      refine ⟨segmentRegion seg1, by simp [initialMemory, hsegs], ?_⟩
      simp only [segmentRegion, segmentPermissions, Region.Contains, Bool.and_eq_true,
        decide_eq_true_eq, Permissions.allows, seg_facts.1]
      exact ⟨⟨by omega, by omega⟩, trivial⟩

/-! ## The launch fragment -/

theorem sexists_in {α : Sort _} {P : α → SProp} {s : Frag} {D : Loc → Prop} (x : α)
    (h : HoldsIn (P x) s D) : HoldsIn (sexists P) s D := by
  obtain ⟨f, hp, hl, hd⟩ := h; exact ⟨f, ⟨x, hp⟩, hl, hd⟩

theorem initPc_eq : image.initPc = 0x401000 := by
  set_option maxRecDepth 100000 in decide +kernel

set_option linter.unusedTactic false in
/-- **The launch fragment splits** as `startPre rsp` and a frame, off the image bytes. -/
theorem launch_split {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput}
    (himg : snapshot.image = image) (hnw : en.sp.toNat +
      (X86Launch.entryStack snapshot.image en inp).length ≤ 2 ^ 64)
    (hbelow : 0x401113 ≤ en.sp.toNat - stackMaxSize.toNat) {out : List LinkedSection}
    (hdom : ∀ a, Dom out a → a < 0x401113) :
    ∃ F : SProp, (startPre en.sp ∗ F) (offBytes (Dom out) (toFrag (launchState snapshot en inp))) := by
  have hsm : stackMaxSize.toNat = 8388608 := rfl
  have hlim : en.sp.toNat < 2 ^ 64 := en.sp.isLt
  have hrip : (launchState snapshot en inp).core.rip = pcs 0 := by
    show BitVec.ofNat 64 snapshot.image.initPc = _
    rw [himg, initPc_eq]; rfl
  have hrsp : (launchState snapshot en inp).core.read .rsp = en.sp := by
    simp [launchState, launchCore]
  have hmem : (launchState snapshot en inp).memory =
      initialMemory snapshot.image.segments en.sp (X86Launch.entryStack snapshot.image en inp) :=
    rfl
  have hstk : ∀ a, en.sp.toNat - 56 ≤ a → a < en.sp.toNat → a < addressLimit ∧
      (launchState snapshot en inp).memory.bytes.get? a = some 0 ∧
      RW (permsAt (launchState snapshot en inp).memory a) := by
    intro a h1 h2
    rw [hmem]
    exact ⟨by simp only [addressLimit]; omega, stack_zero hnw (by omega) h2,
      stack_rw (by omega) h2⟩
  have hB : HoldsIn (blockB (en.sp.toNat - 56) 48) (toFrag (launchState snapshot en inp))
      (fun l => ∃ i < 48, l = .mem (en.sp.toNat - 56 + i)) := by
    have hb := bytesAt_in (need := RW) (launchState snapshot en inp) (en.sp.toNat - 56)
      (List.replicate 48 0) (fun i hi => by
        simp only [List.length_replicate] at hi
        obtain ⟨a1, a2, a3⟩ := hstk (en.sp.toNat - 56 + i) (by omega) (by omega)
        exact ⟨a1, by rw [a2, List.getElem_replicate], a3⟩)
    refine sexists_in (List.replicate 48 0) (mono_in (sep_in (pure_in _ (by simp)) hb ?_) ?_)
    · intro l h; exact h.elim
    · rintro l (h | ⟨i, hi, rfl⟩)
      · exact h.elim
      · exact ⟨i, by simpa using hi, rfl⟩
  have hS := blockAny_in (launchState snapshot en inp) (en.sp.toNat - 8) 8 (fun i hi => by
    obtain ⟨a1, -, a3⟩ := hstk (en.sp.toNat - 8 + i) (by omega) (by omega)
    exact ⟨a1, a3⟩)
  have hR := ripPt_in (launchState snapshot en inp)
  rw [hrip] at hR
  have hP := regPt_in (launchState snapshot en inp) .rsp
  rw [hrsp] at hP
  have hAll := sep_in hR (sep_in hP (sep_in (regAny_in _ .rbp) (sep_in (flagsAny_in _)
    (sep_in (regAny_in _ .rdi) (sep_in (regAny_in _ .rsi) (sep_in (regAny_in _ .rdx)
      (sep_in (regAny_in _ .rcx) (sep_in (regAny_in _ .r8) (sep_in (regAny_in _ .r9)
        (sep_in (regAny_in _ .rax) (sep_in (regAny_in _ .r10) (sep_in (regAny_in _ .r11)
          (sep_in hS hB ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨h, hp, hl, hd⟩ := hAll
    refine ⟨_, sep_diff (s := offBytes (Dom out) (toFrag (launchState snapshot en inp))) hp ?_⟩
    intro l v e
    have hm := hl l v e
    cases l with
    | mem a =>
      have ha := hd _ (by rw [e]; rfl)
      simp only [reduceCtorEq, Loc.mem.injEq, false_or] at ha
      have hnd : ¬ Dom out a := fun hda => by
        have := hdom a hda
        rcases ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> omega
      simp [offBytes, hnd, hm]
    | _ => simpa [offBytes] using hm
  all_goals clear hR hP hS hB hstk hmem hrip hrsp hdom hnw
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      try simp only [reduceCtorEq, Loc.mem.injEq] at h1 h2
      all_goals casesm* _ ∨ _, ∃ _, _, _ ∧ _
      all_goals omega
    | _ => simp_all)

/-! ## `Task.startRun` -/

theorem start_contains {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
      some out) : ∀ i (hi : i < startCode.length), ContainsX out (0x401000 + i) startCode[i] := by
  rw [out_eq h]; exact fun i hi => containsX_linked (start_in_linked i hi)

theorem cmain_contains {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
      some out) : ∀ i (hi : i < cmainCode.length), ContainsX out (0x401020 + i) cmainCode[i] := by
  rw [out_eq h]; exact fun i hi => containsX_linked (cmain_in_linked i hi)

/-- **The launch, ready for `_start`**: for a valid launch of the rung-12 image, the validated
link `out` covers the launch state's image bytes, the launch fragment splits as
`Code ∗ startPre rsp ∗ F`, and `rsp` is 16-aligned and above 64. -/
theorem launch_setup {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput}
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ∃ out, Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
        some out ∧ Covers out (Dom out) (byteOf (launchState snapshot en inp)) ∧
      en.sp.toNat % 16 = 0 ∧ 64 ≤ en.sp.toNat ∧
      ∃ F : SProp, ((Code (Dom out) (byteOf (launchState snapshot en inp)) ∗ startPre en.sp) ∗ F)
        (toFrag (launchState snapshot en inp)) := by
  obtain ⟨-, hlo, -, hal, -, -, -, -, htop, hsegs⟩ := hv
  have hnw := stackFits snapshot.image en inp htop
  have hmem1 : seg1 ∈ image.segments := by
    rw [show image.segments = [seg0, seg1] from loadImg_segments]; simp
  have hseg1 := hsegs seg1 (by rw [himg]; exact hmem1)
  obtain ⟨b1, s1, l1⟩ := seg1_facts
  rw [b1, s1] at hseg1
  have hu : uns en.sp = (en.sp.toNat : Int) := rfl
  have hsm : stackMaxSize.toNat = 8388608 := rfl
  have hsm' : stackMaxSize = 8388608 := rfl
  rw [hu, hsm'] at hseg1
  rw [hu] at hal
  have hbelow : 0x401113 ≤ en.sp.toNat - stackMaxSize.toNat := by rw [hsm]; omega
  have hal' : en.sp.toNat % 16 = 0 := by omega
  obtain ⟨out, hlink, -⟩ := rung12_link
  have heq := out_eq hlink
  have hl := image_loaded (inp := inp) himg hnw hbelow
  have hcon : ∀ a b, Contains out a b → a < 2 ^ 64 ∧
      (launchState snapshot en inp).memory.bytes.get? a = some b ∧
      (launchState snapshot en inp).memory.permits .execute a = true := by
    intro a b ⟨s, hs, hle, hd⟩
    rw [heq] at hs
    obtain ⟨hlo', hhi', hby⟩ := linked_in_seg1 s hs
    have hi : a - s.address < s.data.size := by
      rcases Nat.lt_or_ge (a - s.address) s.data.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hd; cases hd
    have e := hby (a - s.address) hi
    rw [hd, show s.address - 0x401000 + (a - s.address) = a - 0x401000 by omega] at e
    obtain ⟨hg, hx⟩ := hl seg1 hmem1 (a - 0x401000) (by omega) b e
    rw [b1, show 0x401000 + (a - 0x401000) = a by omega] at hg hx
    exact ⟨by omega, hg, hx seg_facts.1⟩
  have hcov : Covers out (Dom out) (byteOf (launchState snapshot en inp)) := by
    intro a b hc
    refine ⟨⟨b, hc⟩, ?_⟩
    show ((launchState snapshot en inp).memory.bytes.get? a).getD 0 = b
    rw [(hcon a b hc.contains).2.1]; rfl
  have hcode : Code (Dom out) (byteOf (launchState snapshot en inp))
      (onBytes (Dom out) (toFrag (launchState snapshot en inp))) := by
    refine code_onBytes fun a ⟨b, hc⟩ => ?_
    obtain ⟨hlim, hget, hexe⟩ := hcon a b hc.contains
    refine ⟨hlim, ?_, hexe⟩
    show _ = some (((launchState snapshot en inp).memory.bytes.get? a).getD 0)
    rw [hget]; rfl
  have hdom : ∀ a, Dom out a → a < 0x401113 := by
    intro a ⟨b, hc⟩
    obtain ⟨s, hs, hle, hd⟩ := hc.contains
    rw [heq] at hs
    obtain ⟨-, hhi', -⟩ := linked_in_seg1 s hs
    have hi : a - s.address < s.data.size := by
      rcases Nat.lt_or_ge (a - s.address) s.data.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hd; cases hd
    omega
  obtain ⟨F, hF⟩ := launch_split himg hnw hbelow hdom
  have hm : ((Code (Dom out) (byteOf (launchState snapshot en inp)) ∗ startPre en.sp) ∗ F)
      (toFrag (launchState snapshot en inp)) := by
    rw [sep_assoc]; exact sep_onBytes hcode hF
  exact ⟨out, hlink, hcov, hal', by omega, F, hm⟩

/-- **`Task.startRun` holds** (R8's open task, discharged). -/
theorem startRun_holds : Task.startRun := by
  intro snapshot en inp himg hv n
  obtain ⟨out, hlink, hcov, hal, hlow, F, hm⟩ := launch_setup himg hv
  obtain ⟨out', hlink', hsafe⟩ := rung12_link
  rw [hlink, Option.some.injEq] at hlink'
  subst hlink'
  have hDs : ∀ i (hi : i < startCode.length), Dom out (0x401000 + i) ∧
      byteOf (launchState snapshot en inp) (0x401000 + i) = startCode[i] :=
    fun i hi => hcov _ _ (start_contains hlink i hi)
  cases n with
  | zero => trivial
  | succ k =>
    have hcm : SafeB k 0x401020 cmainSpec out := by
      cases k with
      | zero => exact safeB_zero _ _ _
      | succ j =>
        exact cmain_safeB (cmain_contains hlink) (hsafe j).1 (hsafe j).2.1 (hsafe j).2.2
    exact safeN_post (fun m' h => exitAt_of hDs h)
      (start_run (start_contains hlink) hcm hcov hal hlow F _ hm)

/-! ## The process theorem, unconditionally -/

/-- **Ladder rung 12 as a Linux process, unconditionally.** Every launch of the rung-12
executable (the validated ld.bfd link of `_start`, `cmain`, `len1` and libmini) that LPS's
x86 launch accepts is process-safe for `exitAllowed inp.fs`: for every flag oracle,
refusal configuration and budget, every finite LPS execution produces either no event or
exactly `exit(6)` with the launch file system, and no execution reaches an error. -/
theorem rung12_processSafe_unconditional (snapshot : X86Launch.Snapshot)
    (refusals : SpuriousCfg) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp (exitAllowed inp.fs) :=
  rung12_processSafe startRun_holds snapshot refusals limit en inp himg hv

end Silmaril.Proofs.Machine.Process.LibMiniClient
