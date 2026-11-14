module

public import Silmaril.Proofs.Machine.Link.LibMiniClient.Compose

/-!
# Proofs: `len1_composed` fires on a concrete machine (non-vacuity)

The loaded-machine half of `len1_composed` has three hypotheses about a machine state `m`:
it holds the executable's loader image (`ImageLoaded`), the stack pointer is System V aligned
with room for the budget, and the non-image part of `m` splits as
`len1Spec.SysVPre x 0x401060 sp ret ∗ F`. This file exhibits one state satisfying all three,
for the very `records` and `out` of the validated rung-12 link, and applies `len1_composed`
to it.

The state `m`: one region mapping every address read/write/execute; the two loader segments
of the executable (`0x400000`, 232 bytes, `r`; `0x401000`, 275 bytes, `rx`) installed from
the parsed image itself (not transcribed); the return address `0x401000` at `rsp = 0x7008`;
the string `"A"` (bytes `0x41 0x00`) at `rdi = 0x8000`; `rip = 0x401060`. So `x = ⟨0x8000,
[0x41]⟩` and the spec promises `rax = 2`.

The image and link facts (`loadImg_segments`, `seg0_facts`, `seg1_facts`, `linked_low`) are
kernel evaluations (`decide +kernel`) of `ELFImage.parse` and `Relocation.link` on the fixture.

`HoldsIn`, `sep_in`, `bytesAt_in` and friends restate the helpers of the separation-logic layer's
`Silmaril.Proofs.Machine.X86.Sep.Demo.NonVacuity`, which is not exported by a header.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Formats.ELF.Link (LinkedSection)
open Silmaril.Process.LPS.ELFImage (x86Policy)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint Le)
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.Unit (Contains)
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd

/-! ## Fragment helpers (restated from the separation-logic layer's demo) -/

/-- `P` holds of a part of `s` whose domain lies in `D`. -/
def HoldsIn (P : SProp) (s : Frag) (D : Loc → Prop) : Prop :=
  ∃ h, P h ∧ Le h s ∧ ∀ l, (h l).isSome → D l

theorem emp_in (s : Frag) : HoldsIn emp s (fun _ => False) :=
  ⟨Frag.empty, rfl, fun _ _ e => by simp [Frag.empty] at e, fun _ e => by simp [Frag.empty] at e⟩

theorem pure_in (s : Frag) {φ : Prop} (h : φ) : HoldsIn ⌜φ⌝ s (fun _ => False) :=
  ⟨Frag.empty, ⟨rfl, h⟩, fun _ _ e => by simp [Frag.empty] at e,
    fun _ e => by simp [Frag.empty] at e⟩

theorem sep_in {P Q : SProp} {s : Frag} {D₁ D₂ : Loc → Prop} (hp : HoldsIn P s D₁)
    (hq : HoldsIn Q s D₂) (hd : ∀ l, D₁ l → D₂ l → False) :
    HoldsIn (P ∗ Q) s (fun l => D₁ l ∨ D₂ l) := by
  obtain ⟨h₁, hP, hl₁, hD₁⟩ := hp
  obtain ⟨h₂, hQ, hl₂, hD₂⟩ := hq
  have disj : Disjoint h₁ h₂ := by
    intro l
    cases e₁ : h₁ l with
    | none => exact .inl rfl
    | some v =>
      cases e₂ : h₂ l with
      | none => exact .inr rfl
      | some w => exact absurd (hd l (hD₁ l (by simp [e₁])) (hD₂ l (by simp [e₂]))) id
  refine ⟨union h₁ h₂, ⟨h₁, h₂, disj, rfl, hP, hQ⟩, ?_, ?_⟩
  · intro l v e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact hl₂ l v e
    | some u => rw [e₁] at e; cases e; exact hl₁ l _ e₁
  · intro l e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact .inr (hD₂ l e)
    | some u => exact .inl (hD₁ l (by simp [e₁]))

theorem mono_in {P : SProp} {s : Frag} {D D' : Loc → Prop} (hp : HoldsIn P s D)
    (hD : ∀ l, D l → D' l) : HoldsIn P s D' := by
  obtain ⟨h, a, b, c⟩ := hp; exact ⟨h, a, b, fun l e => hD l (c l e)⟩

theorem single_le {l : Loc} {v : Val} {s : Frag} (e : s l = some v) :
    Le (Frag.single l v) s := by
  intro l' w h; simp only [Frag.single] at h; split at h <;> simp_all

theorem single_dom {l : Loc} {v : Val} : ∀ l', (Frag.single l v l').isSome → l' = l := by
  intro l' h; simp only [Frag.single] at h; split at h <;> simp_all

theorem regPt_in (m : MState) (r : Reg) :
    HoldsIn (regPt r (m.core.read r)) (toFrag m) (· = .reg r) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem regAny_in (m : MState) (r : Reg) : HoldsIn (regAny r) (toFrag m) (· = .reg r) := by
  obtain ⟨h, a, b, c⟩ := regPt_in m r; exact ⟨h, ⟨_, a⟩, b, c⟩

theorem ripPt_in (m : MState) : HoldsIn (ripPt m.core.rip) (toFrag m) (· = .rip) :=
  ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem flagsAny_in (m : MState) : HoldsIn flagsAny (toFrag m) (· = .flags) :=
  ⟨_, ⟨m.core.flags, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩

theorem bytesAt_in {need : Permissions → Prop} (m : MState) :
    ∀ (a : Nat) (bs : List Byte), (∀ i (hi : i < bs.length), a + i < addressLimit ∧
      m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i))) →
      HoldsIn (bytesAt need a bs) (toFrag m) (fun l => ∃ i < bs.length, l = .mem (a + i))
  | a, [], _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, b :: bs, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hb : HoldsIn (byteAt need a b) (toFrag m) (· = .mem a) := by
      refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2.2, rfl⟩, single_le ?_, single_dom⟩
      simp only [toFrag, h0.2.1]
    have ht := bytesAt_in m (a + 1) bs (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩

theorem blockAny_in (m : MState) :
    ∀ (a n : Nat), (∀ i < n, a + i < addressLimit ∧ RW (permsAt m.memory (a + i))) →
      HoldsIn (blockAny a n) (toFrag m) (fun l => ∃ i < n, l = .mem (a + i))
  | a, 0, _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hb : HoldsIn (byteAny a) (toFrag m) (· = .mem a) :=
      ⟨Frag.single (.mem a) (.cell ⟨m.memory.bytes.get? a, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩
    have ht := blockAny_in m (a + 1) n (fun i hi => by
      have := h (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨i, -, e⟩; simp at e; omega
    · rintro l (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨i + 1, by omega, by simp; omega⟩

/-- A part `h` of `s` and the rest of `s` split `s`. -/
theorem sep_diff {P : SProp} {h s : Frag} (hp : P h) (hl : Le h s) :
    (P ∗ fun r => r = Frag.diff s h) s := by
  refine ⟨h, Frag.diff s h, ?_, ?_, hp, rfl⟩
  · intro l
    simp only [Frag.diff]
    cases e : h l with
    | none => exact .inl rfl
    | some v => exact .inr (by simp)
  · funext l
    simp only [Frag.union, Frag.diff]
    cases e : h l with
    | none => simp
    | some v => exact (hl l v e).symm ▸ rfl

/-! ## Kernel facts about the validated executable and the link -/

/-- The loader image of the executable (default if it did not parse; it does). -/
@[irreducible] def loadImg : Silmaril.Process.LPS.Image :=
  ((Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes).map (·.image exe.bytes)).getD
    ⟨[], 0, ⟨0, 0, 0⟩⟩

def noSeg : Silmaril.Process.LPS.Segment := ⟨0, 0, "", []⟩
@[irreducible] def seg0 : Silmaril.Process.LPS.Segment := loadImg.segments.getD 0 noSeg
@[irreducible] def seg1 : Silmaril.Process.LPS.Segment := loadImg.segments.getD 1 noSeg

set_option maxRecDepth 100000 in
theorem loadImg_segments : loadImg.segments = [seg0, seg1] := by decide +kernel

set_option maxRecDepth 100000 in
theorem seg0_facts : seg0.base = 0x400000 ∧ seg0.size = 232 ∧ seg0.bytes.length = 232 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem seg1_facts : seg1.base = 0x401000 ∧ seg1.size = 275 ∧ seg1.bytes.length = 275 := by
  decide +kernel

theorem image_eq {records : Silmaril.Process.LPS.ELFImage.Records}
    (h : Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes = some records) :
    records.image exe.bytes = loadImg := by
  unfold loadImg; simp [h]

/-- The linked sections (empty if the link failed; it does not). -/
@[irreducible] def linked : List LinkedSection :=
  (Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute).getD []

set_option maxRecDepth 100000 in
theorem linked_low : linked.all (fun s => decide (0x401000 ≤ s.address)) = true := by
  decide +kernel

/-- Every byte of the linked image lies at or above `0x401000`. -/
theorem dom_low {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute = some out)
    {a : Nat} (ha : Dom out a) : 0x401000 ≤ a := by
  have e : out = linked := by unfold linked; simp [h]
  obtain ⟨b, -, -, s, hs, -, hle, -⟩ := ha
  rw [e] at hs
  have := List.all_eq_true.mp linked_low s hs
  simp only [decide_eq_true_eq] at this
  omega

/-! ## The concrete machine -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩
def spW : Word := 0x7008
def retW : Word := 0x401000
def strW : Word := 0x8000
def entryW : Word := BitVec.ofNat 64 0x401060

/-- The string `"A"`. -/
def str : List Byte := [0x41]

def mem : Memory :=
  ⟨[allRegion], Memory.install (Memory.install (Memory.install (Memory.install ∅ spW.toNat
    (Silmaril.Machine.LittleEndian.encodeWords [retW])) strW.toNat (str ++ [0]))
    seg1.base seg1.bytes) seg0.base seg0.bytes⟩

def core : State :=
  ⟨fun r => match r with | .rdi => strW | .rsp => spW | _ => 0, entryW,
    ⟨none, none, none, none, none, none⟩, 0⟩

def m : MState := ⟨core, mem⟩

def x : ScanArg := ⟨strW, str⟩

theorem perms_all (a : Nat) (ha : a < 2 ^ 64) : permsAt mem a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem, allRegion, Region.Contains, Permissions.allows, this]

theorem permits_exec (a : Nat) (ha : a < 2 ^ 64) : mem.permits .execute a = true := by
  have := congrArg Permissions.execute (perms_all a ha)
  simpa [permsAt] using this

/-- The machine holds the executable's loader image. -/
theorem loaded : ImageLoaded loadImg m := by
  obtain ⟨b0, s0, l0⟩ := seg0_facts
  obtain ⟨b1, s1, l1⟩ := seg1_facts
  intro seg hseg i hi b hb
  rw [loadImg_segments] at hseg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hseg
  rcases hseg with e | e <;> rw [e] at hi hb ⊢
  · have hi' : i < seg0.bytes.length := by omega
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hb
    refine ⟨?_, fun _ => permits_exec _ (by omega)⟩
    show (Memory.install _ _ _).get? _ = _
    rw [Memory.install_get _ _ _ _ hi', hb]
  · have hi' : i < seg1.bytes.length := by omega
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hb
    refine ⟨?_, fun _ => permits_exec _ (by omega)⟩
    show (Memory.install _ _ _).get? _ = _
    rw [Memory.install_outside _ _ _ _ (by omega), Memory.install_get _ _ _ _ hi', hb]

set_option maxHeartbeats 1000000 in
set_option linter.unusedTactic false in
/-- The System V precondition of `len1Spec` holds of a part of `m` below `0x9000`. -/
theorem pre_in : ∃ h, (len1Spec.SysVPre x entryW spW retW) h ∧ Le h (toFrag m) ∧
    ∀ a, (h (.mem a)).isSome → a < 0x9000 := by
  obtain ⟨b0, -, l0⟩ := seg0_facts
  obtain ⟨b1, -, l1⟩ := seg1_facts
  have eS : spW.toNat = 0x7008 := rfl
  have eT : strW.toNat = 0x8000 := rfl
  have hword := bytesAt_in (need := RW) m spW.toNat
      (Silmaril.Machine.LittleEndian.encodeWords [retW]) (fun i hi => by
    simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
      List.length_nil] at hi
    refine ⟨by rw [eS]; simp only [addressLimit]; omega, ?_, ?_⟩
    · show (Memory.install _ _ _).get? _ = _
      rw [Memory.install_outside _ _ _ _ (by rw [eS]; omega),
        Memory.install_outside _ _ _ _ (by rw [eS]; omega),
        Memory.install_outside _ _ _ _ (by rw [eS, eT]; simp [str]; omega)]
      exact Memory.install_get _ _ _ _ (by simp; omega)
    · show RW (permsAt mem _)
      rw [perms_all (spW.toNat + i) (by rw [eS]; omega)]; exact ⟨rfl, rfl⟩)
  have hstr := bytesAt_in (need := RO) m strW.toNat (str ++ [0]) (fun i hi => by
    simp only [str, List.length_append, List.length_cons, List.length_nil] at hi
    refine ⟨by rw [eT]; simp only [addressLimit]; omega, ?_, ?_⟩
    · show (Memory.install _ _ _).get? _ = _
      rw [Memory.install_outside _ _ _ _ (by rw [eT]; omega),
        Memory.install_outside _ _ _ _ (by rw [eT]; omega)]
      exact Memory.install_get _ _ _ _ (by simp [str]; omega)
    · show RO (permsAt mem _)
      rw [perms_all (strW.toNat + i) (by rw [eT]; omega)]; rfl)
  have hblock := blockAny_in m (spW.toNat - len1Spec.stack) len1Spec.stack (fun i hi => by
    have hs : len1Spec.stack = 16 := rfl
    rw [hs] at hi ⊢
    refine ⟨by rw [eS]; simp only [addressLimit]; omega, ?_⟩
    show RW (permsAt mem _)
    rw [perms_all _ (by rw [eS]; omega)]; exact ⟨rfl, rfl⟩)
  have hArgs := sep_in (regPt_in m .rdi) (sep_in (regAny_in m .rsi) (sep_in (regAny_in m .rdx)
      (sep_in (regAny_in m .rcx) (sep_in (regAny_in m .r8) (sep_in (regAny_in m .r9) (emp_in _)
        ?_) ?_) ?_) ?_) ?_) ?_
  have hScr := sep_in (regAny_in m .rax) (sep_in (regAny_in m .r10) (sep_in (regAny_in m .r11)
      (emp_in _) ?_) ?_) ?_
  have hRegs := sep_in hArgs hScr ?_
  have hEntry := sep_in (ripPt_in m) (sep_in (regPt_in m .rsp) (sep_in hRegs
    (sep_in (flagsAny_in m) (sep_in hword hblock ?_) ?_) ?_) ?_) ?_
  have hPre := sep_in (pure_in (toFrag m) (show (0 : Byte) ∉ str by decide)) hstr ?_
  have hAll := sep_in hEntry hPre ?_
  · obtain ⟨h, hp, hl, hd⟩ := hAll
    refine ⟨h, hp, hl, fun a ha => ?_⟩
    have hd := hd _ ha
    simp only [reduceCtorEq, Loc.mem.injEq, false_or, or_self] at hd
    have hs : len1Spec.stack = 16 := rfl
    rw [eS, eT, hs] at hd
    simp only [Silmaril.Machine.LittleEndian.encodeWords_length, str, List.length_append,
      List.length_cons, List.length_nil] at hd
    rcases hd with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> omega
  all_goals (intro l h1 h2; cases l with
    | reg r => cases r <;> simp_all
    | mem a =>
      clear hword hstr hblock
      try clear hArgs
      try clear hScr
      try clear hRegs
      try clear hEntry
      try clear hPre
      have hs : len1Spec.stack = 16 := rfl
      try simp only [Silmaril.Machine.LittleEndian.encodeWords_length, str, hs, eS, eT,
        List.length_append, List.length_cons, List.length_nil, reduceCtorEq, Loc.mem.injEq,
        false_or, or_false] at h1 h2
      all_goals (casesm* _ ∨ _, ∃ _, _, _ ∧ _ <;> omega)
    | _ => simp_all)

/-! ## Non-vacuity -/

/-- **The hypotheses of `len1_composed` are jointly satisfiable** on the validated rung-12
link: for the very `records` and `out` that `len1_composed` speaks about, the concrete state
`m` holds the loader image, `rsp = 0x7008` is aligned with room for `len1Spec`'s budget, and
the non-image part of `m` splits as `len1Spec.SysVPre ⟨0x8000, "A"⟩ 0x401060 0x7008 0x401000`
and a frame. -/
theorem len1_nonvacuous :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes = some records ∧
      Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
        some out ∧
      ImageLoaded (records.image exe.bytes) m ∧ FnSpec.EntryAligned spW ∧ 16 ≤ spW.toNat ∧
      ∃ F : SProp, (len1Spec.SysVPre x (BitVec.ofNat 64 0x401060) spW retW ∗ F)
        (offBytes (Dom out) (toFrag m)) := by
  obtain ⟨records, out, hrec, hlink, -⟩ := len1_composed
  refine ⟨records, out, hrec, hlink, image_eq hrec ▸ loaded, (rfl : spW.toNat % 16 = 8), by decide, ?_⟩
  obtain ⟨h, hp, hl, hb⟩ := pre_in
  refine ⟨_, sep_diff hp (s := offBytes (Dom out) (toFrag m)) ?_⟩
  intro l v e
  have hm := hl l v e
  cases l with
  | mem a =>
    have ha := hb a (by simp [e])
    have hnd : ¬ Dom out a := fun hd => by have := dom_low hlink hd; omega
    simp [offBytes, hnd, hm]
  | _ => simpa [offBytes] using hm

/-- **`len1_composed` applied to the concrete state.** On `m` (the loaded rung-12 executable,
`len1("A")` called from `0x401000`), for every step budget `n` the open machine does not get
stuck within `n` steps before it reaches a state where the image is unchanged, `rip = 0x401000`,
`rsp = 0x7010` and `len1Spec`'s postcondition holds (`rax = 1 + 1`, the string unchanged). -/
theorem len1_concrete :
    ∃ (out : List LinkedSection) (F : SProp), Silmaril.X86.Linking.Relocation.link prepared witness.layout
        witness.absolute = some out ∧
      (len1Spec.SysVPre x (BitVec.ofNat 64 0x401060) spW retW ∗ F)
        (offBytes (Dom out) (toFrag m)) ∧
      ∀ n, SafeN (fun m' => ((Code (Dom out) (byteOf m) ∗ len1Spec.SysVPost x spW retW) ∗ F)
        (toFrag m')) n m := by
  obtain ⟨records, out, hrec, hlink, hl, hA, hst, F, hF⟩ := len1_nonvacuous
  obtain ⟨records', out', hrec', hlink', h⟩ := len1_composed
  rw [hrec, Option.some.injEq] at hrec'
  rw [hlink, Option.some.injEq] at hlink'
  subst hrec' hlink'
  exact ⟨out, F, hlink, hF, fun n => (h n).2 m hl x spW retW hA hst F hF⟩

end Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity
