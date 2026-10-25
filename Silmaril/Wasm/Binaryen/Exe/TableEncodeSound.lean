module

public import Silmaril.Wasm.Binaryen.Exe.TableEncode
public import Silmaril.Wasm.Binaryen.Exe.MemoryEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.GcEncodeSound

@[expose] public section

/-! # Soundness of table encodings against the Core binary grammar -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-- The full table-index encoding uses Core 3.0's enabled index form. -/
theorem encTableIdx_sound {x : TableIdx} {bs : List UInt8}
    (h : encTableIdx x = .ok bs) : ReservedIdx true bs x := by
  cases Except.ok.inj h
  exact .idx rfl (encIdx_sound x)

/-- Table zero retains the one-byte encoding admitted by every legacy gate. -/
theorem encTableIdx_zero_sound {allow : Bool} {bs : List UInt8}
    (h : encTableIdx ⟨0⟩ = .ok bs) : ReservedIdx allow bs (⟨0⟩ : TableIdx) := by
  cases Except.ok.inj h
  change ReservedIdx allow (encU 0) (⟨0⟩ : TableIdx)
  rw [encU]
  exact .zero

theorem encTableType_sound {tt : Wasm.TableType} {bs : List UInt8}
    (h : encTableType tt = .ok bs) : Core.TableType Forms.all bs tt := by
  rcases tt with ⟨addr, limits, rt⟩
  unfold encTableType at h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases Except.ok.inj h
  cases encMemory_sound hb with
  | mk hl => exact .mk (encRefType_sound rt) hl

theorem encTable_sound {t : Wasm.Table} {bs : List UInt8}
    (h : encTable t = .ok bs) : Core.Table Forms.all bs t := by
  rcases t with ⟨tt, init⟩
  unfold encTable at h
  split at h
  · next ht hinit =>
    split at h
    · next hht =>
      simp only at hinit hht
      subst hinit hht
      exact .implicit (encTableType_sound h)
    · exact absurd h throw_ne_ok
  · exact absurd h throw_ne_ok

/-- The explicit table-initializer encoder is sound whenever its expression
encoder is sound. The default branch retains the original implicit encoding. -/
theorem encTableWith_sound {emitExpr : Wasm.Expr → Except String (List UInt8)}
    (emitSound : ∀ e bytes, emitExpr e = .ok bytes → Core.Expr Forms.all bytes e)
    {t : Wasm.Table} {bytes : List UInt8} (h : encTableWith emitExpr t = .ok bytes) :
    Core.Table Forms.all bytes t := by
  unfold encTableWith at h
  split at h
  · next original encoded =>
    cases Except.ok.inj h
    exact encTable_sound encoded
  · obtain ⟨typeBytes, typeEncoded, h⟩ := bind_ok h
    obtain ⟨initBytes, initEncoded, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact .explicit rfl (encTableType_sound typeEncoded) (emitSound _ _ initEncoded)

theorem elemFuncs?_spec {es : List Wasm.Expr} :
    ∀ {ys : List FuncIdx}, elemFuncs? es = some ys → es = refFuncs ys := by
  induction es with
  | nil =>
    intro ys h
    cases Option.some.inj h
    rfl
  | cons e es ih =>
    intro ys h
    unfold elemFuncs? at h
    split at h
    · next heq => exact absurd heq (List.cons_ne_nil _ _)
    · next y rest heq =>
      injection heq with h1 h2
      subst h1 h2
      obtain ⟨zs, hzs, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [ih hzs]
      rfl
    · simp at h

end Silmaril.Wasm.Binaryen.Exe
