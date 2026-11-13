module

public import Silmaril.Proofs.Wasm.OCaml.Decode.U32
public import Silmaril.Proofs.Wasm.OCaml.Decode.U64
public import Silmaril.Proofs.Wasm.OCaml.Decode.S32
public import Silmaril.Proofs.Wasm.OCaml.Decode.S64

/-!
# The reference interpreter's LEB128 decoders agree with the binary grammar (on test vectors)

`Decode.run` runs the **imported OCaml source** of `decode.ml`'s `uN`, `u32`, `sN`, `s32`,
`u64` and `s64` (`WebAssembly/spec@608711107b`), after linking it with the parts of the OCaml
standard library it reaches, in the semantics `Silmaril.ML.OCaml`. The theorems below compare
those runs with silmaril-lean's executable transcription `Silmaril.Wasm.Binary.RefInterp`
(`refUN`, `refSN`, …), which is proved equivalent to the binary grammar relations
`UN N` / `SN N` (`refUN_eq_some_iff`, `refSN_eq_some_iff`).

**What is proved.** For every test vector, the OCaml run returns exactly what the transcription
predicts: the decoded value (as the OCaml `int32`/`int64` the decoder returns) and the new
stream position when the transcription accepts, and the exception `Code` (the decoder's own
error, allocated by the generative functor `Error.Make ()`) when it rejects. Each run is
checked by the kernel (`decide +kernel`); no native code is used.

**What is not.** These are finitely many inputs, not all byte strings: a parametric proof needs
a program logic for the imported code (`docs/projects/wasm-wasi.md`, Gaps). The vectors are the
edge cases of LEB128: one-byte encodings, the largest value, values one bit too large, overlong
encodings that are allowed and the first that is too long, end of stream inside an
encoding, `FF 7E` (silmaril-lean#803), the 63-bit `int` boundary on the `u32` path
(`I64.to_int_u` keeps 63 bits, then `I32.of_int_u` masks), and nonzero start positions.
-/

@[expose] public section
namespace Silmaril.Wasm.OCaml.Decode

open Silmaril.ML.OCaml
open Silmaril.Wasm.Binary
open Silmaril.Wasm.Binary.RefInterp

/-! ## From agreement to the grammar -/

theorem agreesU_some {N : Nat} {mk : Value → Option Nat} {o : Out} {bs : List UInt8} {p m : Nat}
    {r : List UInt8} (h : agreesU N mk o bs p = true) (hr : refUN N (bs.drop p) = some (m, r)) :
    ∃ v, o = .ok v (bs.length - r.length) ∧ mk v = some m := by
  unfold agreesU at h
  rw [hr] at h
  cases o with
  | ok v q =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨v, by rw [h.2], h.1⟩
  | code => simp at h
  | other => simp at h

theorem agreesU_none {N : Nat} {mk : Value → Option Nat} {o : Out} {bs : List UInt8} {p : Nat}
    (h : agreesU N mk o bs p = true) (hr : refUN N (bs.drop p) = none) : o = .code := by
  unfold agreesU at h
  rw [hr] at h
  cases o <;> simp_all

theorem agreesS_some {N : Nat} {mk : Value → Option Int} {o : Out} {bs : List UInt8} {p : Nat}
    {i : Int} {r : List UInt8} (h : agreesS N mk o bs p = true)
    (hr : refSN N (bs.drop p) = some (i, r)) :
    ∃ v, o = .ok v (bs.length - r.length) ∧ mk v = some i := by
  unfold agreesS at h
  rw [hr] at h
  cases o with
  | ok v q =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨v, by rw [h.2], h.1⟩
  | code => simp at h
  | other => simp at h

theorem agreesS_none {N : Nat} {mk : Value → Option Int} {o : Out} {bs : List UInt8} {p : Nat}
    (h : agreesS N mk o bs p = true) (hr : refSN N (bs.drop p) = none) : o = .code := by
  unfold agreesS at h
  rw [hr] at h
  cases o <;> simp_all

/-- **`decode.ml`'s `u32`, run as OCaml, decodes the `u32` grammar** on every test case: if
the input from the stream position starts with an encoding `b` of `m` in the binary grammar
(`UN 32 b m`, silmaril-lean's `Silmaril.Wasm.Binary`), the imported OCaml returns `m` and
moves the stream past `b`; if no prefix is an encoding, it raises `Code`. -/
theorem u32_grammar {bs : List UInt8} {p : Nat} (hx : (bs, p) ∈ u32Cases) :
    (∀ b r m, bs.drop p = b ++ r → UN 32 b m →
      ∃ v, out (run .u32 [] bs p) = .ok v (bs.length - r.length) ∧ asU32 v = some m) ∧
    ((∀ b r m, bs.drop p = b ++ r → ¬ UN 32 b m) → out (run .u32 [] bs p) = .code) := by
  have h := List.all_eq_true.mp u32_agrees (bs, p) hx
  refine ⟨fun b r m hb hun => agreesU_some h ((refUN_eq_some_iff (by decide) _ _ _).mpr ⟨b, hb, hun⟩),
    fun hno => agreesU_none h ?_⟩
  cases hr : refUN 32 (bs.drop p) with
  | none => rfl
  | some mr =>
    obtain ⟨b, hb, hun⟩ := (refUN_eq_some_iff (by decide) _ _ _).mp hr
    exact absurd hun (hno b mr.2 mr.1 hb)

/-- **`decode.ml`'s `s32`, run as OCaml, decodes the `s32` grammar** on every test case
(`SN 32`; the OCaml returns the `int32` whose signed value is the decoded integer). -/
theorem s32_grammar {bs : List UInt8} {p : Nat} (hx : (bs, p) ∈ s32Cases) :
    (∀ b r i, bs.drop p = b ++ r → SN 32 b i →
      ∃ v, out (run .s32 [] bs p) = .ok v (bs.length - r.length) ∧ asS32 v = some i) ∧
    ((∀ b r i, bs.drop p = b ++ r → ¬ SN 32 b i) → out (run .s32 [] bs p) = .code) := by
  have h := List.all_eq_true.mp s32_agrees (bs, p) hx
  refine ⟨fun b r i hb hsn => agreesS_some h ((refSN_eq_some_iff (by decide) _ _ _).mpr ⟨b, hb, hsn⟩),
    fun hno => agreesS_none h ?_⟩
  cases hr : refSN 32 (bs.drop p) with
  | none => rfl
  | some ir =>
    obtain ⟨b, hb, hsn⟩ := (refSN_eq_some_iff (by decide) _ _ _).mp hr
    exact absurd hsn (hno b ir.2 ir.1 hb)

end Silmaril.Wasm.OCaml.Decode
