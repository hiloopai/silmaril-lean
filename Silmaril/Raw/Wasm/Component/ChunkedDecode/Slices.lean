module

public import Silmaril.Raw.Wasm.Component.ChunkedDecode.Module
public import Silmaril.Wasm.Component.Chunked.Thms

/-!
# The steps of `readModule.go` on slices of an included file (raw proofs)

The module is `slice L A Z` of a file `L`; its sections, code groups and custom sections are
slices `slice L s e` with the offsets of the file (`At` from `slice_slice`). Header:
`Silmaril.Wasm.Component.ChunkedDecode.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ChunkedDecode

open Silmaril.Wasm.Binary.Core.Decode
open Silmaril.Wasm.Component.Chunked (arr runAll slice chkVec chkSection CPlan codesOf codesOk
  chkDataVec chkCustom)

variable {L : List UInt8} {A Z : Nat}

theorem at_slice {s e : Nat} (hA : A ≤ s) (hse : s ≤ e) (hZ : e ≤ Z) (hL : Z ≤ L.length) :
    At (slice L A Z) (s - A) (slice L s e) := by
  refine ⟨?_, ?_⟩
  · have := Silmaril.Wasm.Component.Chunked.slice_slice L (A := A) (B := Z) hA hse hZ
    rw [← this]
    unfold slice
    rw [List.length_take, List.length_drop, List.length_take, List.length_drop]
    simp only [Nat.min_def]
    congr 1
    split <;> split <;> omega
  · simp only [slice, List.length_take, List.length_drop]; omega

theorem length_slice' {s e : Nat} (hse : s ≤ e) (hL : e ≤ L.length) :
    (slice L s e).length = e - s := by
  simp only [slice, List.length_take, List.length_drop]; omega

theorem get_slice {s : Nat} {b : UInt8} (h : slice L s (s + 1) = [b]) (hA : A ≤ s)
    (hZ : s + 1 ≤ Z) (hL : Z ≤ L.length) : (slice L A Z)[s - A]? = some b := by
  have := at_slice (e := s + 1) hA (by omega) hZ hL
  rw [h] at this
  exact this.get

theorem readU_slice {s e n : Nat} (h : runAll (readU 32) (slice L s e) = some n) (hA : A ≤ s)
    (hse : s ≤ e) (hZ : e ≤ Z) (hL : Z ≤ L.length) :
    readU 32 ⟨arr (slice L A Z), s - A⟩ = .ok (n, ⟨arr (slice L A Z), e - A⟩) := by
  have := run_of_runAll (frame_readU 32) h (at_slice hA hse hZ hL)
  rw [length_slice' hse (by omega), show s - A + (e - s) = e - A by omega] at this
  exact this

/-- A vector section on its slice. -/
theorem go_vec_s {α : Type} {f : DecodeM α} (hf : Frame f) (hm : Mono f) {N : UInt8}
    {upd : Sections → List α → Sections} (hbody : BodyOf N.toNat f upd)
    {kS kc s e fuel last : Nat} {ks : List Nat} {xs : List α} {S : Sections}
    (h : chkSection N kS (chkVec f kc ks) (slice L s e) = some xs) (hA : A ≤ s) (hse : s ≤ e)
    (hZ : e ≤ Z) (hL : Z ≤ L.length) (hN : N.toNat ≠ 0) (hlast : last < sectionRank N.toNat) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), s - A⟩ =
      readModule.go fuel (sectionRank N.toNat) (upd S xs) ⟨arr (slice L A Z), e - A⟩ := by
  rw [go_vec hf hm hbody h (at_slice hA hse hZ hL) hN hlast, length_slice' hse (by omega),
    show s - A + (e - s) = e - A by omega]

/-- The data section on its slice. -/
theorem go_data_s {kS kC s e fuel last : Nat} {ps : List (Nat × Nat × Nat)}
    {ds : List Silmaril.Wasm.Data} {S : Sections}
    (h : chkSection 11 kS (chkDataVec kC ps) (slice L s e) = some ds) (hA : A ≤ s) (hse : s ≤ e)
    (hZ : e ≤ Z) (hL : Z ≤ L.length) (hlast : last < 13) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), s - A⟩ =
      readModule.go fuel 13 { S with data := ds } ⟨arr (slice L A Z), e - A⟩ := by
  rw [go_data h (at_slice hA hse hZ hL) hlast, length_slice' hse (by omega),
    show s - A + (e - s) = e - A by omega]

/-- A custom section on its slice. -/
theorem go_custom_s {kS kN s e fuel last : Nat} {S : Sections}
    (h : chkCustom kS kN (slice L s e) = true) (hA : A ≤ s) (hse : s ≤ e)
    (hZ : e ≤ Z) (hL : Z ≤ L.length) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), s - A⟩ =
      readModule.go fuel last S ⟨arr (slice L A Z), e - A⟩ := by
  rw [go_customSec h (at_slice hA hse hZ hL), length_slice' hse (by omega),
    show s - A + (e - s) = e - A by omega]

/-- A custom section from its parts: the id byte, the size, and the name (the rest of its
bytes is not read). -/
theorem go_custom_parts {s x y e len fuel last : Nat} {nm : String} {S : Sections}
    (hid : slice L s (s + 1) = [0]) (hsz : runAll (readU 32) (slice L (s + 1) x) = some len)
    (hname : runAll readName (slice L x y) = some nm) (hlen : len = e - x)
    (hA : A ≤ s) (h₁ : s + 1 ≤ x) (h₂ : x ≤ y) (h₃ : y ≤ e) (hZ : e ≤ Z) (hL : Z ≤ L.length) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), s - A⟩ =
      readModule.go fuel last S ⟨arr (slice L A Z), e - A⟩ := by
  have hBl : (slice L A Z).length = Z - A := length_slice' (by omega) hL
  have hu := readU_slice (L := L) (A := A) (Z := Z) (s := s + 1) (e := x) hsz (by omega) h₁
    (by omega) hL
  rw [show s + 1 - A = s - A + 1 by omega] at hu
  have hn := run_of_runAll frame_readName hname (at_slice (L := L) (A := A) (Z := Z) (by omega) h₂
    (by omega) hL)
  rw [length_slice' h₂ (by omega), show x - A + (y - x) = y - A by omega] at hn
  have hc : readCustom len ⟨arr (slice L A Z), x - A⟩ = .ok ((), ⟨arr (slice L A Z), x - A + len⟩) := by
    unfold readCustom
    rw [bind_ok (remaining_apply _), bind_ok hn, bind_ok (remaining_apply _)]
    simp only [arr_size, hBl, show Z - A - (x - A) - (Z - A - (y - A)) = y - x by omega,
      show y - x ≤ len by omega, ↓reduceIte]
    rw [bind_apply, readBytes_apply]
    simp only [arr_size, hBl, show y - A + (len - (y - x)) ≤ Z - A by omega, ↓reduceIte]
    rw [show y - A + (len - (y - x)) = x - A + len by omega]
    rfl
  rw [go_custom (get_slice hid hA (by omega) hL) hu (by omega) hc, show x - A + len = e - A by omega]

/-- A group of code entries on its slice. -/
theorem codes_seg_s {ps : List CPlan} {s e : Nat} (h : codesOk ps (slice L s e) = true)
    (hl : chkLocals ps (slice L s e) = true) (hA : A ≤ s) (hse : s ≤ e) (hZ : e ≤ Z)
    (hL : Z ≤ L.length) :
    VecSeg readCode (slice L A Z) (s - A) (e - A) (codesOf ps (slice L s e)) := by
  have := codes_seg_of_ok h hl (at_slice hA hse hZ hL)
  rwa [length_slice' hse (by omega), show s - A + (e - s) = e - A by omega] at this

/-- The code section, from its id byte, size, count and groups. -/
theorem go_code_s {s x z e len fuel last : Nat}
    {cs : List (List Silmaril.Wasm.ValType × Silmaril.Wasm.Expr)} {S : Sections}
    (hid : slice L s (s + 1) = [10]) (hsz : runAll (readU 32) (slice L (s + 1) x) = some len)
    (hxe : x + len = e) (hcnt : runAll (readU 32) (slice L x z) = some cs.length)
    (hseg : VecSeg readCode (slice L A Z) (z - A) (e - A) cs)
    (hA : A ≤ s) (hsx : s + 1 ≤ x) (hxz : x ≤ z) (hze : z ≤ e) (hZ : e ≤ Z) (hL : Z ≤ L.length)
    (hn : cs.length ≤ Z - z) (hlast : last < 12) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), s - A⟩ =
      readModule.go fuel 12 { S with code := cs } ⟨arr (slice L A Z), e - A⟩ := by
  have hBl : (slice L A Z).length = Z - A := length_slice' (by omega) hL
  have h1 := readU_slice (L := L) (A := A) (Z := Z) (s := s + 1) (e := x) hsz (by omega) hsx (by omega) hL
  rw [show s + 1 - A = s - A + 1 by omega] at h1
  have h2 := readU_slice (L := L) (A := A) (Z := Z) (s := x) (e := z) hcnt (by omega) hxz (by omega) hL
  have hxe' : x - A + len = e - A := by omega
  have he' : e - A ≤ (slice L A Z).length := by omega
  have hn' : cs.length ≤ (slice L A Z).length - (z - A) := by omega
  exact go_code (get_slice hid hA (by omega) hL) h1 hxe' he' h2 hn' hseg hlast

theorem go_end_s {fuel last : Nat} {S : Sections} (hAZ : A ≤ Z) (hL : Z ≤ L.length) :
    readModule.go (fuel + 1) last S ⟨arr (slice L A Z), Z - A⟩ =
      .ok (S, ⟨arr (slice L A Z), Z - A⟩) := by
  have := go_end (B := slice L A Z) (fuel := fuel) (last := last) (S := S)
  rw [length_slice' hAZ hL] at this
  exact this

/-- **`decode?` of a module that is a slice of a file**, from a run of the section loop. -/
theorem decode_s {S : Sections}
    (hhdr : slice L A (A + 8) = Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version)
    (h8 : A + 8 ≤ Z) (hL : Z ≤ L.length)
    (hgo : readModule.go (Z - A) 0 {} ⟨arr (slice L A Z), (A + 8) - A⟩ =
      .ok (S, ⟨arr (slice L A Z), Z - A⟩))
    (hf : S.funcTypes.length = S.code.length) (hdc : S.dataCount = none)
    (hdi : Silmaril.Wasm.Binary.Core.codesDataIdxs S.code = []) :
    Silmaril.Wasm.Binary.Core.decode? (arr (slice L A Z)) = some
      { types := S.types, imports := S.imports, tags := S.tags, globals := S.globals,
        tables := S.tables, memories := S.memories, elems := S.elems,
        funcs := Silmaril.Wasm.Binary.Core.zipFuncs S.funcTypes S.code, data := S.data,
        start := S.start, exports := S.exports } := by
  have hl : (slice L A Z).length = Z - A := length_slice' (by omega) hL
  refine decode_of_go ?_ (by omega) ?_ hf hdc hdi
  · rw [← hhdr]; simp only [slice, List.take_take]; congr 1; omega
  · rw [hl, show (8 : Nat) = A + 8 - A by omega]; exact hgo

end Silmaril.Wasm.Component.ChunkedDecode

end
