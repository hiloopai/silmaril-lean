module

public import Silmaril.Proofs.Machine.Link.FnSpec.Unit
public import Silmaril.Machine.Link.Validate.Thms

/-!
# Proofs: from a validated `ld` output to safety in the loaded executable (S-validate-compose)

* `linkSection_meta`, `link_meta`: what every linked section satisfies: it comes from an
  allocated input section with the same flags, its data fit its memory size, and it lies
  below `2 ^ 64`.
* `contains_loaded`: in a machine that holds the loader image (`ImageLoaded`) of an
  executable in which every linked section sits (`SectionIn`), every byte of the linked
  sections is present, below `2 ^ 64`, and executable when the section is.
* `code_onBytes`, `sep_onBytes`: the machine's own bytes on the image's locations form a
  `Code` region, and the rest of the fragment is the frame.
* `validated_compose`: **the bridge.** `Validated objs exe W` (from `validate_sound`), units
  whose objects are the prepared (`prepare`) parsed inputs, `TU.Sat` for every unit,
  `AbiCompatible` and `ImportsClosed` give (, F3, without the earlier
  all-executable-sections hypothesis; `Code` covers executable sections only), for every export of every
  unit at its linked address and every step index: `logic.Safe` in the linked image, and
  `SafeN` on every machine state that holds the executable's loader image.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.FnSpec

open Silmaril.X86 (MState Word Byte)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection ResolvedRelocation Relocator Layout
  AbsoluteSymbols allocated linkSection sectionAt)
open Silmaril.X86.Linking (Relocation.link Relocation.relocate)
open Silmaril.Process.LPS.ELFImage (x86Policy)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint)
open Silmaril.Machine.Link.Unit
open Silmaril.Machine.Link.Contract
open Silmaril.Machine.Link.Validate
open Silmaril.Machine.Link.FnSpec

theorem guard_prop {p : Prop} [Decidable p] {u : Unit} (h : (guard p : Option Unit) = some u) :
    p := by
  by_contra hn
  simp [guard, hn] at h

theorem mapM_mem_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp at hy
  | a :: as, l', h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, by simp, hb⟩
    · obtain ⟨x, hx, hfx⟩ := mapM_mem_some hbs y hy
      exact ⟨x, by simp [hx], hfx⟩

/-- What a linked section is made of. -/
theorem linkSection_meta {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkSection objects rels relocate pl = some s) :
    ∃ part, sectionAt objects pl.key = some part ∧ allocated part = true ∧
      s.key = pl.key ∧ s.flags = part.header.flags ∧ s.data.size ≤ s.memorySize ∧
      s.address + s.memorySize ≤ 2 ^ 64 := by
  unfold linkSection at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨part, hpart, _, hal, _, _, _, _, _, hlim, _, _, patches, _, _, _, data, _, _, hsz,
    rfl⟩ := h
  exact ⟨part, hpart, guard_prop hal, rfl, rfl, guard_prop hsz, guard_prop hlim⟩

theorem link_meta {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : Relocation.link objects layout absolute = some out)
    {s : LinkedSection} (hs : s ∈ out) :
    ∃ part, sectionAt objects s.key = some part ∧ allocated part = true ∧
      s.flags = part.header.flags ∧ s.data.size ≤ s.memorySize ∧
      s.address + s.memorySize ≤ 2 ^ 64 := by
  obtain ⟨-, rels, -, hmap, -⟩ := Silmaril.Machine.Link.link_some (x86_link_some h)
  obtain ⟨pl, -, hpl⟩ := mapM_mem_some hmap s hs
  obtain ⟨part, hpart, hal, hkey, hfl, hsz, hlim⟩ := linkSection_meta hpl
  exact ⟨part, hkey ▸ hpart, hal, hfl, hsz, hlim⟩

/-- A code byte is a byte of the image. -/
theorem _root_.Silmaril.Machine.Link.FnSpec.ContainsX.contains {ctx : Silmaril.Machine.Link.Contract.Image} {a : Nat}
    {b : Byte} (h : ContainsX ctx a b) : Contains ctx a b := by
  obtain ⟨_, -, s, hs, -, hle, hb⟩ := h
  exact ⟨s, hs, hle, hb⟩

/-- **Every linked byte is in a machine that holds the loader image**, with the permissions
of its segment. -/
theorem containsF_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte} {f : Nat}
    (hc : ContainsF out a b f) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧
      ∃ seg ∈ image.segments, ∃ i < seg.size, seg.base + i = a ∧ PermsOk seg f ∧
        seg.bytes[i]? = some b := by
  obtain ⟨s, hs, hf, hle, hd⟩ := hc
  obtain ⟨hsz, hlim⟩ := hb s hs
  have hi : a - s.address < s.data.size := by
    rcases Nat.lt_or_ge (a - s.address) s.data.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hd; cases hd
  obtain ⟨seg, hseg, hbase, hend, hperm, hbytes⟩ := hin s hs
  have he : (expected s)[a - s.address]? = some b := by
    unfold expected
    rw [List.getElem?_append_left (by simpa using hi)]
    simpa using hd
  have hj := hbytes (a - s.address) (by omega)
  rw [he] at hj
  obtain ⟨hget, -⟩ := hl seg hseg (s.address - seg.base + (a - s.address)) (by omega) b hj
  rw [show seg.base + (s.address - seg.base + (a - s.address)) = a by omega] at hget
  exact ⟨by omega, hget, seg, hseg, s.address - seg.base + (a - s.address), by omega, by omega,
    hf ▸ hperm, hj⟩

/-- **Every code byte is in a machine that holds the loader image**, executable. -/
theorem contains_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte}
    (hc : ContainsX out a b) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧ m.memory.permits .execute a = true := by
  obtain ⟨f, hx, hcf⟩ := hc
  obtain ⟨hlim, hget, seg, hseg, i, hi, hia, hperm, hbi⟩ := containsF_loaded hin hb hl hcf
  obtain ⟨-, hexe⟩ := hl seg hseg i hi _ hbi
  exact ⟨hlim, hget, hia ▸ hexe (hperm.2.2 hx)⟩

/-- The machine's bytes on `D` form a code region. -/
theorem code_onBytes {D : Nat → Prop} {bs : Nat → Byte} {m : MState}
    (hD : ∀ a, D a → a < 2 ^ 64 ∧ m.memory.bytes.get? a = some (bs a) ∧
      m.memory.permits .execute a = true) :
    Code D bs (onBytes D (toFrag m)) := by
  refine ⟨fun a ha => ?_, fun l hl => ?_⟩
  · obtain ⟨hlim, hget, hexe⟩ := hD a ha
    refine ⟨hlim, permsAt m.memory a, hexe, ?_⟩
    simp only [onBytes, toFrag, ha, ite_true]
    rw [hget]
  · cases l with
    | mem a =>
      have : ¬ D a := fun ha => hl a ha rfl
      simp [onBytes, this]
    | _ => rfl

/-- A fragment splits into its part on `D` and its part off `D`. -/
theorem sep_onBytes {P R : SProp} {D : Nat → Prop} {h : Frag} (hP : P (onBytes D h))
    (hR : R (offBytes D h)) : (P ∗ R) h := by
  refine ⟨_, _, ?_, ?_, hP, hR⟩
  · intro l
    cases l with
    | mem a =>
      by_cases ha : D a
      · exact .inr (by simp [offBytes, ha])
      · exact .inl (by simp [onBytes, ha])
    | _ => exact .inl rfl
  · funext l
    cases l with
    | mem a =>
      by_cases ha : D a
      · simp [union, onBytes, offBytes, ha]
        cases h (.mem a) <;> rfl
      · simp [union, onBytes, offBytes, ha]
    | _ => simp [union, onBytes, offBytes]

/-- **S-validate-compose**, on any machine `step` (the logic laws hold for every machine). -/
theorem validated_compose {step : MState → Option MState} {Tag : Type} [DecidableEq Tag] {policy : Silmaril.Machine.Link.Abi.Policy Tag}
    {objs : List Bytes} {exe : Bytes} {W : Witness} {units : List (TU Tag FnSpec)}
    (hv : Validated objs exe W)
    (hprep : ∀ parsed, objs.mapM readObject = some parsed →
      prepare parsed W.dropped = units.map TU.object)
    (habi : AbiCompatible policy units)
    (hsat : ∀ u ∈ units, u.Sat (logicOn step) Relocation.relocate)
    (hclosed : ImportsClosed (logicOn step) units []) :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe = some records ∧
      Relocation.link (units.map TU.object) W.layout W.absolute = some out ∧
      ∀ (n slot : Nat) (u : TU Tag FnSpec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
        globalValuation (units.map TU.object) W.layout W.absolute e.name = some a →
        (logicOn step).Safe n a e.spec out ∧
        ∀ m, ImageLoaded (records.image exe) m →
          ∀ (x : e.spec.Arg) (sp ret : Word), FnSpec.EntryAligned sp → e.spec.stack ≤ sp.toNat →
          ∀ F : SProp, (e.spec.SysVPre x (BitVec.ofNat 64 a) sp ret ∗ F)
              (offBytes (Dom out) (toFrag m)) →
            Silmaril.Machine.X86.Safe.SafeN step (fun m' => ((Code (Dom out) (byteOf m) ∗ e.spec.SysVPost x sp ret) ∗ F)
              (toFrag m')) n m := by
  obtain ⟨parsed, records, out, hparse, hrec, hlink, hin, -⟩ := hv
  rw [hprep parsed hparse] at hlink
  refine ⟨records, out, hrec, hlink, fun n slot u hu e he a ha => ?_⟩
  have hsafe : (logicOn step).Safe n a e.spec out :=
    link_compose_valuation x86_sectionLocal (x86_link_some hlink) habi hsat hclosed
      (Extends.refl out) (fun x hx => by simp at hx) n slot u hu e he a ha
  refine ⟨hsafe, fun m hl x sp ret hA hst F hpre => ?_⟩
  have hcon : ∀ a b, ContainsX out a b →
      a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧ m.memory.permits .execute a = true :=
    fun a b hc => contains_loaded hin (fun s hs => by
      obtain ⟨_, _, _, _, hsz, hlim⟩ := link_meta hlink hs
      exact ⟨hsz, hlim⟩) hl hc
  have hcov : Covers out (Dom out) (byteOf m) := by
    intro a b hc
    refine ⟨⟨b, hc⟩, ?_⟩
    show (m.memory.bytes.get? a).getD 0 = b
    rw [(hcon a b hc).2.1]; rfl
  have hcode : Code (Dom out) (byteOf m) (onBytes (Dom out) (toFrag m)) := by
    refine code_onBytes fun a ⟨b, hc⟩ => ?_
    obtain ⟨hlim, hget, hexe⟩ := hcon a b hc
    refine ⟨hlim, ?_, hexe⟩
    show _ = some ((m.memory.bytes.get? a).getD 0)
    rw [hget]; rfl
  have hm : ((Code (Dom out) (byteOf m) ∗ e.spec.SysVPre x (BitVec.ofNat 64 a) sp ret) ∗ F)
      (toFrag m) := by
    rw [sep_assoc]; exact sep_onBytes hcode hpre
  exact hsafe (Dom out) (byteOf m) hcov x sp ret hA hst F m hm

end Silmaril.Proofs.Machine.Link.FnSpec
