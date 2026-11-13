module

public import Silmaril.Proofs.Machine.Link.LibMiniClient.PlusOne
public import Silmaril.Machine.X86.Reloc.Thms

/-!
# Proofs: the client unit's relocation-parametric contract

`client_sat`: any unit shaped like `client.o` (one allocated section `.text.len1` holding
`sub $8,%rsp; call 0; add $8,%rsp; add $1,%rax; ret`, one `R_X86_64_PLT32 imp-4` at offset 5,
`exp` defined at its start, exporting `plusOneSpec S` and importing `S`) satisfies `TU.Sat`
under the `FnSpec` logic, for every slot, well-formed placement and valuation. The relocated
call field is read back with the linker's `patch_spec`, `encoded_rel32` and `plt_call_target`;
the rest is `plusOne_safe`.

`wellPlaced_single`, `image_single`, `linkPart_some'` and `patch_symbol_lt'` restate small
lemmas of the linker's two-TU example (`Silmaril.Proofs.Machine.Link.TwoTu`), which is not a header.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.LibMiniClient

open Silmaril.X86 (MState Word Byte Insn)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection ResolvedRelocation Relocator Patch applyPatch
  allocated)
open Silmaril.X86.Linking.Relocation (encoded patch value relocate Fits width relocate_success
  patch_spec)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.Link.Unit
open Silmaril.Machine.Link.Contract
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Proofs.Machine.Link.FnSpec

theorem wellPlaced_single {object : ObjectFile} {p : Placement} {k : Nat}
    (hw : WellPlaced object p) (ha : allocatedIndices object = [k]) :
    ∃ base, p = [(k, base)] := by
  have h := hw.2
  rw [ha, List.perm_singleton] at h
  match p, h with
  | [(i, base)], h => simp at h; exact ⟨base, by rw [h]⟩

theorem linkPart_some' {part : ObjectSection} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkPart part rels relocate pl = some s) :
    ∃ patches, (rels.filter (fun r => r.key == pl.key)).mapM (fun r => do
        let patch ← relocate rels r part.data
        guard (patch.offset = r.offset ∧ 0 < patch.bytes.size)
        pure patch) = some patches ∧
      patches.foldlM applyPatch part.data = some s.data ∧
      s.address = pl.address ∧ s.key = pl.key := by
  unfold linkPart at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, patches, hmap, _, _, data, hfold, h⟩ := h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨patches, hmap, hfold, rfl, rfl⟩

theorem image_single {object : ObjectFile} {slot k base : Nat} {σ : Valuation}
    {relocate : Relocator} {img : Silmaril.Machine.Link.Contract.Image}
    (h : image object slot [(k, base)] σ relocate = some img) :
    ∃ rels part s, relocations object slot [(k, base)] σ = some rels ∧
      object.sections[k]? = some part ∧
      linkPart part rels relocate ⟨⟨slot, k⟩, base⟩ = some s ∧ img = [s] := by
  unfold image at h
  cases hr : relocations object slot [(k, base)] σ with
  | none => simp [hr] at h
  | some rels =>
    cases hp : object.sections[k]? with
    | none => simp [hr, hp] at h
    | some part =>
      cases hs : linkPart part rels relocate ⟨⟨slot, k⟩, base⟩ with
      | none => simp [hr, hp, hs] at h
      | some s =>
        simp [hr, hp, hs] at h
        exact ⟨rels, part, s, rfl, rfl, hs, h.symm⟩

theorem linkPart_bound {part : ObjectSection} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkPart part rels relocate pl = some s) : pl.address + part.header.size ≤ 2 ^ 64 := by
  unfold linkPart at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, hlim, _⟩ := h
  exact Silmaril.Proofs.Machine.Link.FnSpec.guard_prop hlim

theorem linkPart_flags {part : ObjectSection} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkPart part rels relocate pl = some s) : s.flags = part.header.flags := by
  unfold linkPart at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  rfl

theorem patch_symbol_lt' {r : ResolvedRelocation} {bytes : Bytes} {q : Patch}
    (h : patch r bytes = .ok q) : r.symbolValue < 2 ^ 64 := by
  unfold patch at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h2; exact (not_not.mp h2).2

/-- `.text.len1` of `client.o`. -/
def lenText : ObjectSection :=
  ⟨⟨49, 1, 6, 0, 64, 18, 0, 0, 16, 0⟩, [0x2e, 0x74, 0x65, 0x78, 0x74, 0x2e, 0x6c, 0x65, 0x6e, 0x31],
    #[0x48, 0x83, 0xec, 0x08, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x08,
      0x48, 0x83, 0xc0, 0x01, 0xc3]⟩

theorem exportAddr_len {Tag : Type} {u : TU Tag FnSpec} {name : NameBytes} {base a : Nat}
    (hfind : u.object.symbols.find? (fun symbol =>
      symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == name) =
      some ⟨⟨10, 18, 0, 4, 0, 18⟩, name⟩)
    (hpart : u.object.sections[4]? = some lenText)
    (h : u.exportAddr [(4, base)] name = some a) : a = base ∧ base < 2 ^ 64 := by
  simp only [TU.exportAddr, hfind, localValue, hpart, Placement.addr, Option.bind_eq_bind,
    Option.bind_some] at h
  simp [lenText] at h
  by_cases hb : base < 2 ^ 64
  · simp_all
  · have : ¬ base < 18446744073709551616 := hb
    simp [this] at h

/-- **The client unit's contract**, relocation-parametric. -/
theorem client_sat {step : MState → Option MState} [Silmaril.Machine.X86.Safe.ExtendsOpen step]
    {Tag : Type} {u : TU Tag FnSpec} {S : FnSpec} {exp imp : NameBytes}
    {t t' : Tag}
    (halloc : allocatedIndices u.object = [4])
    (hrel : u.object.relocations = [⟨4, 5, 3, 4, -4⟩])
    (htext : u.object.sections[4]? = some lenText)
    (hsym : u.object.symbols[3]? = some ⟨⟨15, 16, 0, 0, 0, 0⟩, imp⟩) (himp : imp ≠ [])
    (hfind : u.object.symbols.find? (fun symbol =>
      symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == exp) =
      some ⟨⟨10, 18, 0, 4, 0, 18⟩, exp⟩)
    (hexp : u.exports = [⟨exp, t, plusOneSpec S⟩]) (himps : u.imports = [⟨imp, t', S⟩]) :
    u.Sat (logicOn step) relocate := by
  intro slot p σ img hw himg n ctx hext himport e he a ha
  obtain ⟨base, rfl⟩ := wellPlaced_single hw halloc
  obtain ⟨rels, part, s, hrels, hpart, hs, rfl⟩ := image_single himg
  rw [htext, Option.some.injEq] at hpart
  subst hpart
  rw [hexp, List.mem_singleton] at he
  subst he
  obtain ⟨rfl, hlim⟩ := exportAddr_len hfind htext ha
  cases hS : σ imp with
  | none =>
    simp [relocations, hrel, htext, Placement.addr, resolveIn, hsym, hS, lenText, allocated,
      ObjectSymbol.binding, himp] at hrels
  | some f =>
  have hrels' : rels = [⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩] := by
    simp [relocations, hrel, htext, Placement.addr, resolveIn, hsym, hS, lenText, allocated,
      ObjectSymbol.binding, himp] at hrels
    exact hrels.symm
  subst hrels'
  obtain ⟨patches, hmap, hfold, haddr, -⟩ := linkPart_some' hs
  simp only [List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil, List.mapM_cons,
    List.mapM_nil] at hmap
  cases hq : relocate [⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩] ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩
      lenText.data with
  | none => simp [hq] at hmap
  | some q =>
  have hpatch := relocate_success hq
  obtain ⟨-, -, hoff, hbytes, hsize, -⟩ := patch_spec hpatch
  have hfl := patch_symbol_lt' hpatch
  have hsz : 0 < q.bytes.size := by
    rw [hsize]; simp [Silmaril.X86.Linking.Relocation.width]
  simp [hq, hoff, hsz] at hmap
  subst hmap
  simp only [List.foldlM_cons, List.foldlM_nil] at hfold
  cases happ : applyPatch lenText.data q with
  | none => simp [happ] at hfold
  | some d =>
  simp [happ] at hfold
  -- the relocated bytes are `plusOneCode rel`
  simp only at haddr
  have henc := Silmaril.Machine.X86.Reloc.encoded_rel32 (kind := 4) (by decide)
    (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩)
  have hdata : s.data.toList =
      plusOneCode (BitVec.ofInt 32 (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩)) := by
    rw [← hfold]
    unfold applyPatch at happ
    have hb : q.offset + q.bytes.size ≤ lenText.data.size := by
      rw [hoff, hsize]; simp [lenText, Silmaril.X86.Linking.Relocation.width]
    simp only [hb, guard_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq] at happ
    subst happ
    rw [hoff, hsize, hbytes]
    rw [henc]
    rfl
  -- the call target
  have htarget : BitVec.ofNat 64 (a + 4) + 5#64 +
      (BitVec.ofInt 32 (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩)).signExtend 64 =
      BitVec.ofNat 64 f := by
    have h := Silmaril.Machine.X86.Reloc.plt_call_target (Or.inr rfl) hpatch rfl
    rw [← h]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hbound : a + 18 ≤ 2 ^ 64 := by simpa [lenText] using linkPart_bound hs
  -- the import
  have himp' : SafeOn step n f S ctx := by
    have := himport ⟨imp, t', S⟩ (by rw [himps]; simp) f hS
    exact this
  -- the bytes in the context
  have hcode : ∀ i (hi : i < (plusOneCode (BitVec.ofInt 32 (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩))).length),
      ContainsX ctx (a + i) (plusOneCode (BitVec.ofInt 32 (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩)))[i] := by
    intro i hi
    refine ⟨s.flags, by rw [linkPart_flags hs]; decide, hext _ _ _ ⟨s, by simp, rfl, by omega, ?_⟩⟩
    rw [haddr, show a + i - a = i by omega]
    have : s.data.toList[i]? = some (plusOneCode
        (BitVec.ofInt 32 (value ⟨⟨slot, 4⟩, 5, a + 5, f, 4, -4⟩)))[i] := by
      rw [hdata]; exact List.getElem?_eq_getElem hi
    simpa using this
  exact plusOne_safe hbound hcode htarget himp'

end Silmaril.Proofs.Machine.Link.LibMiniClient
