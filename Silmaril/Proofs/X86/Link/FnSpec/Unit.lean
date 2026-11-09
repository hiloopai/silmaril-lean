module

public import Silmaril.Proofs.X86.Link.FnSpec.Logic
public import Silmaril.X86.Link.Contract.Thms

/-!
# Proofs: unit contracts of position-independent code under the `FnSpec` logic

* `image_mem`: a placed, unrelocated section of a unit image holds the object's bytes at its
  placement address (`linkPart_none`: with no relocations aimed at it, `linkPart` copies the
  section data).
* `safe_of_sat`: an export whose bytes `code` are in the image, and whose code meets its
  `FnSpec` wherever it is loaded (`FnSpec.Sat Open.isa (codePt entry code) entry`), is
  `Safe` at every index in every context extending the image.
* `safe_unverified`: the `unverified` spec (false precondition) is safe everywhere.
* `tu_sat_of_code`: **a unit without relocations whose every export is `unverified` or has a
  position-independent proof satisfies `TU.Sat`**, for every relocator. This turns per-function `FnSpec.Sat` proofs into a
  relocation-parametric unit contract, without re-verifying any function.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Link.FnSpec

open Silmaril.Formats.ELF.Link (mapM_some_mem)

open Silmaril.X86 (MState Word Byte)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection ResolvedRelocation Relocator Patch applyPatch)
open Silmaril.X86.Sep
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Link.FnSpec
open Silmaril.X86.Safe

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y
  | [], _, _, x, hx => by simp at hx
  | a :: as, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_some_mem hbs x hx
      exact ⟨y, by simp [hy], hfy⟩

/-- With no relocations, `linkPart` places the section's own bytes. -/
theorem linkPart_none {part : ObjectSection} {relocate : Relocator}
    {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkPart part [] relocate pl = some s) :
    s.address = pl.address ∧ s.data = part.data ∧ s.flags = part.header.flags := by
  unfold linkPart at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, List.filter_nil, List.mapM_nil] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, patches, hmap, _, _, data, hfold, h⟩ := h
  subst hmap
  simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, hfold.symm, rfl⟩

theorem placement_addr_mem {p : Placement} {k base : Nat} (h : p.addr k = some base) :
    (k, base) ∈ p := by
  unfold Placement.addr at h
  cases hf : p.find? (·.1 == k) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    rw [← h, ← hk]
    exact hm

/-- **A placed section of a relocation-free unit holds the object's bytes.** -/
theorem image_mem {object : ObjectFile} {slot : Nat} {p : Placement} {σ : Valuation}
    {relocate : Relocator} {img : List LinkedSection} (hrel : object.relocations = [])
    (himg : image object slot p σ relocate = some img) {k base : Nat} {part : ObjectSection}
    (hp : p.addr k = some base) (hpart : object.sections[k]? = some part) :
    ∃ s ∈ img, s.address = base ∧ s.data = part.data ∧ s.flags = part.header.flags := by
  unfold image at himg
  simp only [relocations, hrel, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Option.bind_some] at himg
  obtain ⟨secs, hsecs, -, -, rfl⟩ := himg
  obtain ⟨s, hs, hfs⟩ := mapM_some_mem hsecs _ (placement_addr_mem hp)
  simp only [hpart, Option.bind_some] at hfs
  obtain ⟨ha, hd, hf⟩ := linkPart_none hfs
  exact ⟨s, hs, ha, hd, hf⟩

/-- The address and the bytes of an export in a relocation-free unit image. -/
theorem exportCode_contains {Tag : Type} {u : TU Tag FnSpec} {slot : Nat} {p : Placement}
    {σ : Valuation} {relocate : Relocator} {img : List LinkedSection}
    (hrel : u.object.relocations = []) (himg : u.image slot p σ relocate = some img)
    {name : NameBytes} {code : List Byte} (hc : ExportCode u.object name code) {a : Nat}
    (ha : u.exportAddr p name = some a) :
    a < 2 ^ 64 ∧ ∀ i (hi : i < code.length), ContainsX img (a + i) code[i] := by
  obtain ⟨sym, hfind, habs, part, hpart, hx, hbytes⟩ := hc
  unfold TU.exportAddr at ha
  simp only [hfind, Option.bind_eq_bind, Option.bind_some] at ha
  unfold localValue at ha
  simp only [habs, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨_, _, part', hpart', _, _, base, hbase, _, hlim, rfl⟩ := ha
  rw [hpart] at hpart'
  cases hpart'
  obtain ⟨s, hs, haddr, hdata, hflags⟩ := image_mem hrel himg hbase hpart
  simp only [guard] at hlim
  refine ⟨?_, fun i hi => ⟨s.flags, by rw [hflags]; exact hx, s, hs, rfl, by omega, ?_⟩⟩
  · split at hlim <;> simp_all
  · rw [haddr, hdata, show base + sym.raw.value + i - base = sym.raw.value + i by omega]
    exact hbytes i hi

variable {σ : Type} {I : Silmaril.X86.SegVC.Isa σ}

/-- **A position-independent proof gives safety in every context**, on every machine that
extends the open machine. -/
theorem safe_of_sat (E : Silmaril.X86.Open.isa.Extends I) {a : Nat} {S : FnSpec} {code : List Byte} {ctx : Silmaril.X86.Link.Contract.Image} (ha : a < 2 ^ 64)
    (hcode : ∀ i (hi : i < code.length), ContainsX ctx (a + i) code[i])
    (hS : ∀ entry : Word, S.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry) (n : Nat) :
    SafeOn I n a S ctx := by
  intro D bs hc x sp ret hA hst
  have hD : ∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i] :=
    fun i hi => hc _ _ (hcode i hi)
  have hsat := hS (BitVec.ofNat 64 a) x sp ret hA hst
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hsat
  have h := STriple.of_triple (I := I) (n := n)
    (Triple.lift E (Triple.frame hsat (Code (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs)))
  rw [code_split code a hD]
  exact STriple.conseq (entails_of_eq (by ac_rfl)) h (entails_of_eq (by ac_rfl))

/-- The `unverified` spec cannot be called. -/
theorem safe_unverified (n a : Nat) (ctx : Silmaril.X86.Link.Contract.Image) :
    SafeOn I n a unverified ctx := by
  intro D bs _ x sp ret _ _ F m _ hm
  exfalso
  obtain ⟨_, _, _, _, ⟨_, _, _, _, _, ⟨_, _, _, _, _, hpre⟩⟩, _⟩ := hm
  exact hpre

/-- **Unit contracts of relocation-free, position-independent units.** -/
theorem tu_sat_of_code (E : Silmaril.X86.Open.isa.Extends I) {Tag : Type} {relocate : Relocator} (u : TU Tag FnSpec)
    (hrel : u.object.relocations = [])
    (hex : ∀ e ∈ u.exports, e.spec = unverified ∨ ∃ code, ExportCode u.object e.name code ∧
      ∀ entry : Word, e.spec.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry) :
    u.Sat (logicOn I) relocate := by
  intro slot p σ img _ himg n ctx hctx _ e he a ha
  rcases hex e he with hu | ⟨code, hc, hS⟩
  · show SafeOn I _ _ _ _
    rw [hu]; exact safe_unverified _ _ _
  · obtain ⟨hlim, hcon⟩ := exportCode_contains hrel himg hc ha
    exact safe_of_sat E hlim (fun i hi => by
      obtain ⟨f, hf, hc⟩ := hcon i hi
      exact ⟨f, hf, hctx _ _ f hc⟩) hS (n + 1)

/-- A unit whose exports are all `unverified` satisfies its contract trivially. -/
theorem tu_sat_unverified {Tag : Type} {relocate : Relocator} (u : TU Tag FnSpec)
    (hex : ∀ e ∈ u.exports, e.spec = unverified) : u.Sat (logicOn I) relocate := by
  intro _ _ _ _ _ _ _ _ _ _ e he _ _
  show SafeOn I _ _ _ _
  rw [hex e he]; exact safe_unverified _ _ _

theorem exportCode_of_check {object : ObjectFile} {name : NameBytes} {code : List Byte}
    (h : exportCodeB object name code = true) : ExportCode object name code := by
  unfold exportCodeB at h
  split at h
  · rename_i sym hfind
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨habs, h⟩ := h
    split at h
    · rename_i part hpart
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      refine ⟨sym, hfind, habs, part, hpart, h.1, fun i hi => ?_⟩
      have := List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)
      simp only [beq_iff_eq] at this
      rw [this, List.getElem?_eq_getElem hi]
    · cases h
  · cases h

end Silmaril.Proofs.X86.Link.FnSpec
