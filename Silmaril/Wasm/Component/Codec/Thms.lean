module

public import Silmaril.Wasm.Component.Codec.Variant.Defs
public import Silmaril.Wasm.Component.BinaryP3.Strict.Thms
public import Silmaril.Wasm.Component.BinaryAsync.Thms
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The component binary codec: laws and the relations between the variants

For the decoder `Codec.decode` and the encoder `Codec.encode`:

* `decode_ok_iff`: `decode` succeeds with `c` exactly when `decodeLax` does and `c` satisfies
  the rules `BinaryP3.StrictOk`;
* `decode_sound`: the result is the component the grammar relates to the input, and satisfies
  the rules; `decode_functional`: no other component is related to the input;
* `decode_encode`: **round trip** for components satisfying the rules; `decodeLax_encode` for
  every component.

Between the variants (`Codec.Variant`):

* `decodeMvp_encodeMvp`, `decodeLax_of_decodeMvp`: the facade's `mvp` decoder round-trips
  and is extended by `decodeLax`;
* `decodeLax_of_mvp`, `accepts_lax_of_mvp`: **`mvp ⊆ lax`**: every binary the old decoder reads
  is read by `decodeLax` as its embedding `BinaryP3.Ast.ofV0`;
* `accepts_lax_of_strict`: **`strict ⊆ lax`**;
* `decodeLax_mvp_encode`, `async_mvp_encode`: the bytes `Binary.encode` writes are read by
  `decodeLax` and by `BinaryAsync.parseX` as the embedded component; `encode_ofV0`: on embedded
  components the encoder is the old encoder;
* `not_async_sub_lax`, `not_lax_sub_gc`: **`async ⊆ lax` and `lax ⊆ gc` are false**, with the
  witnesses `dropAsyncBytes` and `resourceF32Bytes` (evaluated by the kernel, `decide +kernel`).

Proofs: one or two lines each, from `Silmaril.Wasm.Component.BinaryP3.{Thms,Strict.Thms}` and
`Silmaril.Wasm.Component.BinaryAsync.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Codec

open BinaryP3 (StrictOk componentG)

/-! ## The decoder and the encoder -/

/-- **Strict decoding is the grammar and the rules.** -/
theorem decode_ok_iff {b : ByteArray} {c : Ast} :
    decode b = .ok c ↔ decodeLax b = .ok c ∧ StrictOk c :=
  BinaryP3.parseStrict_ok_iff

/-- **Soundness**: the result is the component the grammar relates to the whole input, and it
satisfies the rules. -/
theorem decode_sound {b : ByteArray} {c : Ast} (h : decode b = .ok c) :
    (componentG (b.size + 1)).G b.data.toList c ∧ StrictOk c :=
  BinaryP3.parseStrict_sound h

/-- **Unambiguity**: any component the grammar relates to the input is the decoded one. -/
theorem decode_functional {b : ByteArray} {c c' : Ast} (h : decode b = .ok c)
    (h' : (componentG (b.size + 1)).G b.data.toList c') : c' = c :=
  BinaryP3.parseStrict_functional h h'

/-- **Round trip**: a component satisfying the rules is decoded from its encoding. -/
theorem decode_encode {c : Ast} {b : ByteArray} (h : encode c = some b) (hs : StrictOk c) :
    decode b = .ok c :=
  BinaryP3.parseStrict_encode h hs

/-- Round trip of the grammar alone, for every encodable component. -/
theorem decodeLax_encode {c : Ast} {b : ByteArray} (h : encode c = some b) :
    decodeLax b = .ok c :=
  BinaryP3.parse_encode h

/-! ## Relations between the variants -/

/-- **`mvp ⊆ lax`**: a binary the old decoder reads is read by `decodeLax` as the embedding. -/
theorem decodeLax_of_mvp {b : ByteArray} {c : Binary.Ast} (h : Binary.parse b = .ok c) :
    decodeLax b = .ok (BinaryP3.Ast.ofV0 c) :=
  BinaryP3.parse_ofV0 h

/-- The `mvp` variant of the facade round-trips: `decodeMvp` reads what `encodeMvp` writes. -/
theorem decodeMvp_encodeMvp {c : Binary.Ast} {b : ByteArray} (h : encodeMvp c = some b) :
    decodeMvp b = .ok c :=
  Binary.parse_encode h

/-- What the facade's `mvp` decoder reads, `decodeLax` reads as its embedding. -/
theorem decodeLax_of_decodeMvp {b : ByteArray} {c : Binary.Ast} (h : decodeMvp b = .ok c) :
    decodeLax b = .ok (BinaryP3.Ast.ofV0 c) :=
  decodeLax_of_mvp h

theorem ok_iff {ε α : Type} {e : Except ε α} : ok e = true ↔ ∃ a, e = .ok a := by
  cases e <;> simp [ok]

/-- **`mvp ⊆ lax`**, as acceptance. -/
theorem accepts_lax_of_mvp {b : ByteArray} (h : Variant.mvp.accepts b = true) :
    Variant.lax.accepts b = true := by
  obtain ⟨c, hc⟩ : ∃ c, Binary.parse b = .ok c := ok_iff.mp h
  exact ok_iff.mpr ⟨_, decodeLax_of_mvp hc⟩

/-- **`strict ⊆ lax`**. -/
theorem accepts_lax_of_strict {b : ByteArray} (h : Variant.strict.accepts b = true) :
    Variant.lax.accepts b = true := by
  obtain ⟨c, hc⟩ : ∃ c, decode b = .ok c := ok_iff.mp h
  exact ok_iff.mpr ⟨c, (decode_ok_iff.mp hc).1⟩

/-- On embedded old components the encoder is the old encoder. -/
theorem encode_ofV0 (c : Binary.Ast) : encode (BinaryP3.Ast.ofV0 c) = Binary.encode c :=
  BinaryP3.encode_ofV0 c

/-- The bytes the old encoder writes are read by `decodeLax` as the embedded component. -/
theorem decodeLax_mvp_encode {c : Binary.Ast} {b : ByteArray} (h : Binary.encode c = some b) :
    decodeLax b = .ok (BinaryP3.Ast.ofV0 c) :=
  BinaryP3.parse_encode_ofV0 h

/-- The bytes the old encoder writes are read by the `async` variant as the embedded
component. -/
theorem async_mvp_encode {c : Binary.Ast} {b : ByteArray} (h : Binary.encode c = some b) :
    BinaryAsync.parseX b = .ok (BinaryAsync.AstX.ofAst c) :=
  BinaryAsync.parseX_encode h

/-- `async` reads `dropAsyncBytes` (`resource.drop async 0`). -/
theorem accepts_async_dropAsync : Variant.async.accepts dropAsyncBytes = true := by
  decide +kernel

/-- `lax` rejects `dropAsyncBytes`: `Binary.md` at `d095e2f` has no built-in with tag `0x07`. -/
theorem accepts_lax_dropAsync : Variant.lax.accepts dropAsyncBytes = false := by
  decide +kernel

/-- **`async ⊆ lax` is false.** -/
theorem not_async_sub_lax :
    ¬ ∀ b, Variant.async.accepts b = true → Variant.lax.accepts b = true := fun h => by
  have hl := h dropAsyncBytes accepts_async_dropAsync
  rw [accepts_lax_dropAsync] at hl
  exact Bool.false_ne_true hl

/-- `lax` reads `resourceF32Bytes` (a resource type represented as `f32`). -/
theorem accepts_lax_resourceF32 : Variant.lax.accepts resourceF32Bytes = true := by
  decide +kernel

/-- `gc` rejects `resourceF32Bytes`: its reference syntax represents resources by `i32` or
`i64` only (`Conformance.ToRef.addrType`). -/
theorem accepts_gc_resourceF32 : Variant.gc.accepts resourceF32Bytes = false := by
  decide +kernel

/-- **`lax ⊆ gc` is false.** -/
theorem not_lax_sub_gc :
    ¬ ∀ b, Variant.lax.accepts b = true → Variant.gc.accepts b = true := fun h => by
  have hg := h resourceF32Bytes accepts_lax_resourceF32
  rw [accepts_gc_resourceF32] at hg
  exact Bool.false_ne_true hg

end Silmaril.Wasm.Component.Codec
