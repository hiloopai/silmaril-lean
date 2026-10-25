module

public import Silmaril.Wasm.Binary.Core.Decode.Mem
public import Silmaril.Wasm.Binary.Core.Decode.Ops
public import Silmaril.Wasm.Binary.Core.Decode.VecOps
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Soundness of the executable decoder

The top theorem `decode?_sound`: if `decode? b = some m`, then `b` encodes `m` under the
specification's grammar (`Encodes`, `Modules.lean`). With `Binary.Core.functional`,
`m` is then the *only* module that `b` encodes.

The proof is split production by production. `Sound G p` says that whenever the
decoder `p` succeeds from a cursor, it consumed a prefix of the remaining input that
`G` relates to the result, and left the input array unchanged. Each reader of
`Decode.lean` has a `Sound` lemma against its grammar nonterminal:

| Reader | Nonterminal |
|---|---|
| `readByte`, `readBytes`, `readU`, `readS`, `readIdx` | `Byte`, raw bytes, `UN`, `SN`, `Index` |
| `readVec`, `readName` | `Vec`, `Name` |
| `readValType`, `readBlockType`, `readRecType` | `ValType`, `BlockType`, `RecType` |
| `readPlain`, `readInstr`/`readSeq`, `readExpr` | `Instr`, `Instrs` with a terminator, `Expr` |
| `readImport`, `readGlobal`, `readExport`, `readCode`, `readCustom` | `Import`, `Global`, `Export`, `Code`, `Custom` |
| `readHeader`, `readModule` | `magic ++ version`, `Encodes` |

The correctness statements concern the actual readers used by `decode?`.
A reader can be refactored while preserving each stated encoding relation.
-/

namespace Silmaril.Wasm.Binary.Core.Decode

open Silmaril.Wasm

/-- The parser `p` is sound for the production `G`: from any cursor, a successful run
leaves the input array unchanged and consumes a prefix `pre` of the remaining bytes
with `G pre a`. -/
def Sound {α : Type} (G : Bytes → α → Prop) (p : DecodeM α) : Prop :=
  ∀ ⦃c : Cursor⦄ ⦃a : α⦄ ⦃c' : Cursor⦄, p.run c = .ok (a, c') →
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ G pre a

theorem noError {α} (msg : String) {c c' : Cursor} {a : α} :
    (decodeError msg).run c ≠ .ok (a, c') := by
  intro h
  change Except.error _ = Except.ok _ at h
  cases h

/-- A successful bind has successful runs of both parsers. -/
theorem bindOk {α β} {p : DecodeM α} {f : α → DecodeM β} {c c' : Cursor} {b : β}
    (h : (p >>= f).run c = .ok (b, c')) :
    ∃ a cm, p.run c = .ok (a, cm) ∧ (f a).run cm = .ok (b, c') := by
  simp only [StateT.run_bind] at h
  cases hp : p.run c with
  | error e => simp [hp, Except.bind, bind] at h
  | ok r => exact ⟨r.1, r.2, rfl, by simpa [hp, Except.bind, bind] using h⟩

/-! ## Bytes and integers -/

theorem readByte_sound : Sound Byte readByte := by
  intro c a c' h
  obtain ⟨h₁, h₂⟩ := readByte_ok h
  exact ⟨h₁, [a], h₂, Byte.mk a⟩

theorem readBytes_sound (n : Nat) :
    Sound (fun pre (ba : ByteArray) => pre = ba.data.toList ∧ pre.length = n) (readBytes n) := by
  intro c a c' h
  obtain ⟨h₁, h₂, h₃⟩ := readBytes_ok h
  exact ⟨h₁, _, h₂, rfl, h₃⟩

theorem readU_sound (N : Nat) : Sound (UN N) (readU N) := by
  intro c a c' h
  simp only [readU] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  split at h
  · rename_i hlt
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨h₁, pre, m, h₂, rfl, hm⟩ := readU_go_ok _ hn
    rw [Nat.pow_zero, Nat.mul_one] at hlt ⊢
    exact ⟨h₁, pre, h₂, hm N (Nat.le_refl _) hlt⟩
  · exact (run_throw_ok h).elim

theorem readS_sound (N : Nat) : Sound (SN N) (readS N) := by
  intro c a c' h
  simp only [readS] at h
  obtain ⟨i, c₁, hi, h⟩ := run_bind_ok h
  split at h
  · rename_i hlt
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨h₁, pre, j, h₂, rfl, hj⟩ := readS_go_ok _ hi
    rw [Int.pow_zero, Int.mul_one, Int.zero_add] at hlt ⊢
    exact ⟨h₁, pre, h₂, hj N (Nat.le_refl _) hlt.1 hlt.2⟩
  · exact (run_throw_ok h).elim

theorem readIdx_sound {k : IndexKind} : Sound Index (readIdx (k := k)) := by
  intro c a c' h
  simp only [readIdx] at h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  split at h
  · obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact readU_sound 32 hn
  · exact (decodeError_ok h).elim

/-! ## Vectors and names -/

/-- Checking the allocation bound does not consume any further bytes. -/
theorem readCount_run {c c' : Cursor} {n : Nat} (h : readCount.run c = .ok (n, c')) :
    (readU 32).run c = .ok (n, c') := by
  obtain ⟨m, cm, hm, h⟩ := bindOk (show (readU 32 >>= _).run c = _ from h)
  simp only [StateT.run_bind, remaining, StateT.run_get, pure_bind, StateT.run_pure] at h
  split at h
  next => cases h; exact hm
  next => exact False.elim (noError _ h)

/-- The structural loop reads exactly the requested number of elements. -/
theorem readVec_go_sound {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f) (n : Nat) :
    Sound (fun pre xs => Seq G pre xs ∧ xs.length = n) (readVec.go f n) := by
  induction n with
  | zero =>
    intro c xs c' h
    change Except.ok ([], c) = Except.ok (xs, c') at h
    cases h
    exact ⟨rfl, [], by simp, Seq.nil, rfl⟩
  | succ n ih =>
    intro c xs c' h
    obtain ⟨x, cm, hx, h⟩ := bindOk (show (f >>= _).run c = _ from h)
    obtain ⟨ys, ce, hy, h⟩ := bindOk h
    cases h
    obtain ⟨hb, p, hp, hg⟩ := hf hx
    obtain ⟨hb', q, hq, hseq, hlen⟩ := ih hy
    exact ⟨hb'.trans hb, p ++ q, by simp [hp, hq, List.append_assoc],
      Seq.cons hg hseq, by simp [hlen]⟩

theorem readVec_sound {α : Type} {G : Bytes → α → Prop} {f : DecodeM α} (hf : Sound G f) :
    Sound (Vec G) (readVec f) := by
  intro c xs c' h
  obtain ⟨n, cm, hn, h⟩ := bindOk (show (readCount >>= _).run c = _ from h)
  obtain ⟨hb, p, hp, hu⟩ := readU_sound 32 (readCount_run hn)
  obtain ⟨hb', q, hq, hseq, hlen⟩ := readVec_go_sound hf n h
  exact ⟨hb'.trans hb, p ++ q, by simp [hp, hq, List.append_assoc],
    Vec.mk (hlen ▸ hu) hseq⟩

theorem seqByte (bs : Bytes) : Seq Byte bs bs := by
  induction bs with
  | nil => exact Seq.nil
  | cons b bs ih => exact Seq.cons (Byte.mk b) ih

theorem fromUTF8_eq {bs : ByteArray} {s : String} (h : String.fromUTF8? bs = some s) :
    s.toUTF8 = bs := by
  unfold String.fromUTF8? at h
  split at h
  next => cases h; rw [String.toUTF8_eq_toByteArray]; rfl
  next => cases h

theorem readName_sound : Sound Name readName := by
  intro c s c' h
  obtain ⟨n, cm, hn, h⟩ := bindOk (show (readCount >>= _).run c = _ from h)
  obtain ⟨bs, cb, hbs, h⟩ := bindOk h
  change (match String.fromUTF8? bs with
    | some s => pure s
    | none => decodeError _).run cb = .ok (s, c') at h
  split at h
  next su hs =>
    cases h
    obtain ⟨hnbytes, pn, hnrest, hng⟩ := readU_sound 32 (readCount_run hn)
    obtain ⟨hbbytes, pb, hbrest, hbg, hblen⟩ := readBytes_sound n hbs
    refine ⟨hbbytes.trans hnbytes, pn ++ pb, by simp [hnrest, hbrest, List.append_assoc], ?_⟩
    subst pb
    refine Name.mk (Vec.mk (by simpa only [hblen] using hng) (seqByte _)) ?_
    simpa only [fromUTF8_eq hs] using Utf8.toUTF8 s
  next => exact False.elim (noError _ h)

/-! ## Types -/

theorem peekByte_readByte {c cm : Cursor} {b : UInt8} (h : peekByte.run c = .ok (some b, cm)) :
    ∃ c', readByte.run cm = .ok (b, c') := by
  change Except.ok (c.bytes[c.pos]?, c) = Except.ok (some b, cm) at h
  obtain ⟨he, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  obtain ⟨hh, he'⟩ := getElem_of_getElem? he
  refine ⟨⟨c.bytes, c.pos + 1⟩, ?_⟩
  simp only [readByte, StateT.run_bind, StateT.run_get, pure_bind, dite_eq_left hh,
    StateT.run_set, StateT.run_pure]
  rw [he']
  rfl

theorem readRefType_absHeapType_sound : Sound AbsHeapType readRefType.absHeapType := by
  intro c a c' h
  obtain ⟨b, cm, hb, h⟩ := bindOk (show (readByte >>= _).run c = _ from h)
  obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hb
  cases hg
  split at h
  next he =>
    have be : b = 0x69 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.exn⟩
  next he =>
    have be : b = 0x6a := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.array⟩
  next he =>
    have be : b = 0x6b := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.struct⟩
  next he =>
    have be : b = 0x6c := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.i31⟩
  next he =>
    have be : b = 0x6d := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.eq⟩
  next he =>
    have be : b = 0x6e := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.any⟩
  next he =>
    have be : b = 0x6f := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.extern⟩
  next he =>
    have be : b = 0x70 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.func⟩
  next he =>
    have be : b = 0x71 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.none⟩
  next he =>
    have be : b = 0x72 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.noextern⟩
  next he =>
    have be : b = 0x73 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.nofunc⟩
  next he =>
    have be : b = 0x74 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbytes, _, hrest, AbsHeapType.noexn⟩
  next => exact False.elim (noError _ h)

theorem readRefType_heapType_sound : Sound HeapType readRefType.heapType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  change (match ob.map UInt8.toNat with
    | some n => _
    | none => decodeError _).run c = .ok (a, c') at h
  split at h
  next n he =>
    split at h
    next =>
      obtain ⟨ht, cm, hh, h⟩ := bindOk h
      cases h
      obtain ⟨hb, pre, hr, hg⟩ := readRefType_absHeapType_sound hh
      exact ⟨hb, pre, hr, HeapType.abs hg⟩
    next =>
      obtain ⟨x, cm, hx, h⟩ := bindOk h
      split at h
      next hxnonneg =>
        cases h
        obtain ⟨hb, pre, hr, hs⟩ := readS_sound 33 hx
        exact ⟨hb, pre, hr, HeapType.idx _
          (by simpa [Idx.toNat, Int.toNat_of_nonneg hxnonneg.1] using hs)⟩
      next => exact False.elim (noError _ h)
  next => exact False.elim (noError _ h)

theorem readRefType_sound : Sound (RefType Forms.all) readRefType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  change ((match ob.map UInt8.toNat with
    | some 0x63 => do let _ ← readByte; pure ⟨true, ← readRefType.heapType⟩
    | some 0x64 => do let _ ← readByte; pure ⟨false, ← readRefType.heapType⟩
    | _ => do pure ⟨true, .abstract (← readRefType.absHeapType)⟩) : DecodeM Wasm.RefType).run c = .ok (a, c') at h
  split at h
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x63 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨ht, ch, hh, h⟩ := bindOk h
    cases h
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    obtain ⟨hb', ph, hr', hg'⟩ := readRefType_heapType_sound hh
    exact ⟨hb'.trans hbytes, [0x63] ++ ph,
      by simp [hrest, hr'], RefType.null rfl hg'⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x64 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨ht, ch, hh, h⟩ := bindOk h
    cases h
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    obtain ⟨hb', ph, hr', hg'⟩ := readRefType_heapType_sound hh
    exact ⟨hb'.trans hbytes, [0x64] ++ ph,
      by simp [hrest, hr'], RefType.nonNull rfl hg'⟩
  next =>
    obtain ⟨ht, cm, hh, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hr, hg⟩ := readRefType_absHeapType_sound hh
    exact ⟨hb, pre, hr, RefType.abs hg⟩

theorem readValType_sound : Sound (ValType Forms.all) readValType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  change ((match ob.map UInt8.toNat with
    | some 0x7F => do let _ ← readByte; pure (.num (.int .i32))
    | some 0x7E => do let _ ← readByte; pure (.num (.int .i64))
    | some 0x7D => do let _ ← readByte; pure (.num (.float .f32))
    | some 0x7C => do let _ ← readByte; pure (.num (.float .f64))
    | some 0x7B => do let _ ← readByte; pure (.vec .v128)
    | _ => do pure (.ref (← readRefType))) : DecodeM Wasm.ValType).run c = .ok (a, c') at h
  split at h
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x7f := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, ValType.num NumType.i32⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x7e := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, ValType.num NumType.i64⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x7d := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, ValType.num NumType.f32⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x7c := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, ValType.num NumType.f64⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x7b := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, ValType.vec VecType.v128⟩
  next =>
    obtain ⟨rt, cm, hr, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hre, hg⟩ := readRefType_sound hr
    exact ⟨hb, pre, hre, ValType.ref hg⟩

theorem readBlockType_sound : Sound (BlockType Forms.all) readBlockType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  split at h
  next he =>
    have he : ob = some 0x40 := by simpa using he
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (he ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, pre, hrest, hg⟩ := readByte_sound hx
    cases hg
    exact ⟨hbytes, _, hrest, BlockType.empty⟩
  next =>
    split at h
    next =>
      obtain ⟨vt, cm, ht, h⟩ := bindOk h
      cases h
      obtain ⟨hb, pre, hr, hg⟩ := readValType_sound ht
      exact ⟨hb, pre, hr, BlockType.value hg⟩
    next =>
      obtain ⟨x, cm, hx, h⟩ := bindOk h
      split at h
      next hxnonneg =>
        cases h
        obtain ⟨hb, pre, hr, hs⟩ := readS_sound 33 hx
        exact ⟨hb, pre, hr, BlockType.idx _
          (by simpa [Idx.toNat, Int.toNat_of_nonneg hxnonneg.1] using hs)⟩
      next => exact False.elim (noError _ h)

theorem readStorageType_sound : Sound (StorageType Forms.all) readStorageType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  change ((match ob.map UInt8.toNat with
    | some 0x77 => do let _ ← readByte; pure (.packed .i16)
    | some 0x78 => do let _ ← readByte; pure (.packed .i8)
    | _ => do pure (.val (← readValType))) : DecodeM Wasm.StorageType).run c = .ok (a, c') at h
  split at h
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x77 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, hrest⟩ := readByte_ok hx
    exact ⟨hbytes, [0x77], hrest, StorageType.packed PackType.i16⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x78 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cm, hx, h⟩ := bindOk h
    cases h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨hbytes, hrest⟩ := readByte_ok hx
    exact ⟨hbytes, [0x78], hrest, StorageType.packed PackType.i8⟩
  next =>
    obtain ⟨t, cm, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hr, hg⟩ := readValType_sound ht
    exact ⟨hb, pre, hr, StorageType.val hg⟩

theorem readFieldType_sound : Sound (FieldType Forms.all) readFieldType := by
  intro c a c' h
  obtain ⟨t, ct, ht, h⟩ := bindOk (show (readStorageType >>= _).run c = _ from h)
  obtain ⟨b, cb, hb, h⟩ := bindOk h
  obtain ⟨hbt, pt, hrt, hgt⟩ := readStorageType_sound ht
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  next he =>
    have be : b = 0 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb.trans hbt, pt ++ [0], by simp [hrt, hrb], FieldType.mk hgt Mut.const⟩
  next he =>
    have be : b = 1 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb.trans hbt, pt ++ [1], by simp [hrt, hrb], FieldType.mk hgt Mut.var⟩
  next => exact (noError _ h).elim

theorem readCompType_sound : Sound (CompType Forms.all) readCompType := by
  intro c a c' h
  obtain ⟨b, cb, hb, h⟩ := bindOk (show (readByte >>= _).run c = _ from h)
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  next he =>
    have be : b = 0x5E := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hbt, pt, hrt, hgt⟩ := readFieldType_sound ht
    exact ⟨hbt.trans hbb, 0x5E :: pt, by simp [hrb, hrt], CompType.array hgt⟩
  next he =>
    have be : b = 0x5F := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨ts, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hbt, pt, hrt, hgt⟩ := readVec_sound readFieldType_sound ht
    exact ⟨hbt.trans hbb, 0x5F :: pt, by simp [hrb, hrt], CompType.struct hgt⟩
  next he =>
    have be : b = 0x60 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨params, cp, hp, h⟩ := bindOk h
    obtain ⟨results, cr, hr, h⟩ := bindOk h
    cases h
    obtain ⟨hpbyte, pp, hprest, hpg⟩ := readVec_sound readValType_sound hp
    obtain ⟨hrbyte, pr, hrrest, hrg⟩ := readVec_sound readValType_sound hr
    refine ⟨hrbyte.trans (hpbyte.trans hbb), [0x60] ++ pp ++ pr, ?_, CompType.func hpg hrg⟩
    simp [hrb, hprest, hrrest, List.append_assoc]
  next => exact (noError _ h).elim

theorem readSubType_sound : Sound (SubType Forms.all) readSubType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  change ((match ob.map UInt8.toNat with
    | some 0x4F => do
      let _ ← readByte
      let supers ← readVec readIdx
      pure ⟨true, supers, ← readCompType⟩
    | some 0x50 => do
      let _ ← readByte
      let supers ← readVec readIdx
      pure ⟨false, supers, ← readCompType⟩
    | _ => do pure ⟨true, [], ← readCompType⟩) : DecodeM Wasm.SubType).run c = .ok (a, c') at h
  split at h
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x4F := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cb, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨supers, cs, hs, h⟩ := bindOk h
    obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hbb, hrb⟩ := readByte_ok hx
    obtain ⟨hbs, ps, hrs, hgs⟩ := readVec_sound readIdx_sound hs
    obtain ⟨hbt, pt, hrt, hgt⟩ := readCompType_sound ht
    exact ⟨hbt.trans (hbs.trans hbb), [0x4F] ++ ps ++ pt,
      by simp [hrb, hrs, hrt, List.append_assoc], SubType.final rfl hgs hgt⟩
  next he =>
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp he
    have be : b = 0x50 := UInt8.toNat_inj.mp he
    subst b
    obtain ⟨x, cb, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (hb ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨supers, cs, hs, h⟩ := bindOk h
    obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hbb, hrb⟩ := readByte_ok hx
    obtain ⟨hbs, ps, hrs, hgs⟩ := readVec_sound readIdx_sound hs
    obtain ⟨hbt, pt, hrt, hgt⟩ := readCompType_sound ht
    exact ⟨hbt.trans (hbs.trans hbb), [0x50] ++ ps ++ pt,
      by simp [hrb, hrs, hrt, List.append_assoc], SubType.open_ rfl hgs hgt⟩
  next =>
    obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hr, hg⟩ := readCompType_sound ht
    exact ⟨hb, pre, hr, SubType.plain hg⟩

theorem readRecType_sound : Sound (RecType Forms.all) readRecType := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  split at h
  next he =>
    have he : ob = some 0x4E := by simpa using he
    obtain ⟨x, cb, hx, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (he ▸ hob)
    rw [hx] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨ts, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hbb, hrb⟩ := readByte_ok hx
    obtain ⟨hbt, pt, hrt, hgt⟩ := readVec_sound readSubType_sound ht
    exact ⟨hbt.trans hbb, 0x4E :: pt, by simp [hrb, hrt], RecType.group rfl hgt⟩
  next =>
    obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hr, hg⟩ := readSubType_sound ht
    exact ⟨hb, pre, hr, RecType.single hg⟩

/-! ## Memories and data (`Decode/Mem.lean`) -/

theorem readLimits_sound : Sound (Limits Forms.all) readLimits := fun _ _ _ h => readLimits_ok h

theorem readMemType_sound : Sound (MemType Forms.all) readMemType := fun _ _ _ h => readMemType_ok h

theorem readMemArg_sound : Sound (Memarg Forms.all) readMemArg := fun _ _ _ h => readMemArg_ok h

/-! ## Instructions -/

theorem sound_map {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    {p : DecodeM α} (hp : Sound G p) (f : α → β)
    (hf : ∀ b x, G b x → H b (f x)) :
    Sound H (do let x ← p; pure (f x)) := by
  intro c a c' h
  obtain ⟨x, cm, hx, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨hb, pre, hr, hg⟩ := hp hx
  exact ⟨hb, pre, hr, hf pre x hg⟩

/-- An instruction named by its opcode alone, or a load or store. -/
theorem readOpOnly_sound (op : UInt8) :
    Sound (fun pre i => Instr Forms.all ([op] ++ pre) i) (readOpOnly op.toNat) := by
  intro c a c' h
  simp only [readOpOnly, UInt8.ofNat_toNat] at h
  split at h
  · rename_i i hi
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨rfl, [], by simp, Instr.plain (plainOp?_spec hi)⟩
  · split at h
    · rename_i mk hmk
      exact sound_map readMemArg_sound _ (fun _ ⟨_, _⟩ hg => Instr.mem (memOp?_spec hmk) hg) h
    · exact (decodeError_ok h).elim

/-- A vector instruction after its `0xFD` prefix. -/
theorem readVecInstr_sound :
    Sound (fun pre i => Instr Forms.all ([0xFD] ++ pre) i) readVecInstr := by
  intro c a c' h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨hbn, pn, hrn, hgn⟩ := readU_sound 32 hn
  split at h
  · rename_i i hi
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    split at hi
    · exact ⟨hbn, pn, hrn, Instr.prefixFD (prefixFDOp?_spec ‹_› hi) hgn⟩
    · cases hi
  split at h
  · rename_i mk hmk
    obtain ⟨⟨x, ao⟩, cm, hm, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbm, pm, hrm, hgm⟩ := readMemArg_sound hm
    refine ⟨hbm.trans hbn, pn ++ pm, by simp [hrn, hrm], ?_⟩
    simpa [List.append_assoc] using Instr.vecMem (vecMemOp?_spec hmk) hgn hgm
  split at h
  · rename_i mk hmk
    obtain ⟨⟨x, ao⟩, cm, hm, h⟩ := run_bind_ok h
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbm, pm, hrm, hgm⟩ := readMemArg_sound hm
    obtain ⟨hbl, pl, hrl, hgl⟩ := readByte_sound hl
    cases hgl
    refine ⟨hbl.trans (hbm.trans hbn), pn ++ pm ++ [l], by simp [hrn, hrm, hrl], ?_⟩
    simpa [List.append_assoc] using Instr.vecMemLane (l := l) (vecMemLaneOp?_spec hmk) hgn hgm
  split at h
  · rename_i mk hmk
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbl, pl, hrl, hgl⟩ := readByte_sound hl
    cases hgl
    refine ⟨hbl.trans hbn, pn ++ [l], by simp [hrn, hrl], ?_⟩
    simpa [List.append_assoc] using Instr.vecLane (l := l) (vecLaneOp?_spec hmk) hgn
  split at h
  · rename_i h12
    subst h12
    obtain ⟨bs, cb, hbs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, rfl, hl⟩ := readBytes_sound 16 hbs
    refine ⟨hb.trans hbn, pn ++ bs.data.toList, by simp [hrn, hr], ?_⟩
    simpa [List.append_assoc] using Instr.vecConst (F := Forms.all) hgn hl
  split at h
  · rename_i h13
    subst h13
    obtain ⟨bs, cb, hbs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, rfl, hl⟩ := readBytes_sound 16 hbs
    refine ⟨hb.trans hbn, pn ++ bs.data.toList, by simp [hrn, hr], ?_⟩
    simpa [List.append_assoc] using Instr.vecShuffle (F := Forms.all) hgn hl
  exact (decodeError_ok h).elim

theorem readCastOp_sound : Sound CastOp readCastOp := by
  intro c a c' h
  obtain ⟨b, cb, hb, h⟩ := bindOk (show (readByte >>= _).run c = _ from h)
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  next he =>
    have be : b = 0 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb, [0], hrb, CastOp.r00⟩
  next he =>
    have be : b = 1 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb, [1], hrb, CastOp.r01⟩
  next he =>
    have be : b = 2 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb, [2], hrb, CastOp.r02⟩
  next he =>
    have be : b = 3 := UInt8.toNat_inj.mp he
    subst b
    cases h
    exact ⟨hbb, [3], hrb, CastOp.r03⟩
  next => exact (noError _ h).elim

/-- A GC instruction after its `0xFB` prefix. -/
theorem readGCInstr_sound :
    Sound (fun pre i => Instr Forms.all ([0xFB] ++ pre) i) readGCInstr := by
  intro c a c' h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  obtain ⟨hbn, pn, hrn, hgn⟩ := readU_sound 32 hn
  split at h
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.structNew hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.structNewDefault hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.structGet hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.structGetS hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.structGetU hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.structSet hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayNew hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayNewDefault hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayNewFixed hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayNewData hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayNewElem hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayGet hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayGetS hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayGetU hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arraySet hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.arrayFill hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayCopy hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayInitData hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
    · simp [hrn, hrx, hry, List.append_assoc]
    · simpa [List.append_assoc] using Instr.arrayInitElem hgn hgx hgy
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readRefType_heapType_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.refTest hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readRefType_heapType_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.refTestNull hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readRefType_heapType_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.refCast hgn hgx
  · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readRefType_heapType_sound hx
    refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.refCastNull hgn hgx
  · obtain ⟨⟨n₁, n₂⟩, cc, hc, h⟩ := run_bind_ok h
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨h₁, c₁, hh₁, h⟩ := run_bind_ok h
    obtain ⟨h₂, c₂, hh₂, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbc, pc, hrc, hgc⟩ := readCastOp_sound hc
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readRefType_heapType_sound hh₁
    obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readRefType_heapType_sound hh₂
    refine ⟨hb₂.trans (hb₁.trans (hbl.trans (hbc.trans hbn))), pn ++ pc ++ pl ++ p₁ ++ p₂, ?_, ?_⟩
    · simp [hrn, hrc, hrl, hr₁, hr₂, List.append_assoc]
    · simpa [List.append_assoc] using Instr.brOnCast hgn hgc hgl hg₁ hg₂
  · obtain ⟨⟨n₁, n₂⟩, cc, hc, h⟩ := run_bind_ok h
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨h₁, c₁, hh₁, h⟩ := run_bind_ok h
    obtain ⟨h₂, c₂, hh₂, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbc, pc, hrc, hgc⟩ := readCastOp_sound hc
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readRefType_heapType_sound hh₁
    obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readRefType_heapType_sound hh₂
    refine ⟨hb₂.trans (hb₁.trans (hbl.trans (hbc.trans hbn))), pn ++ pc ++ pl ++ p₁ ++ p₂, ?_, ?_⟩
    · simp [hrn, hrc, hrl, hr₁, hr₂, List.append_assoc]
    · simpa [List.append_assoc] using Instr.brOnCastFail hgn hgc hgl hg₁ hg₂
  · split at h
    · rename_i i hi
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hbn, pn, hrn, Instr.prefixFB (prefixFBOp?_spec hi) hgn⟩
    · exact (decodeError_ok h).elim

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- An instruction without nested instructions, after its opcode byte `op`. -/
theorem readPlain_sound (op : UInt8) :
    Sound (fun pre i => Instr Forms.all ([op] ++ pre) i) (readPlain op.toNat) := by
  intro c a c' h
  have hlt := op.toNat_lt
  generalize hn : op.toNat = n at h hlt
  have he : op = UInt8.ofNat n := by
    apply UInt8.toNat_inj.mp
    simp [← hn]
  subst op
  -- Enumerate the byte opcode, treating immediates before the opcode-only cases.
  interval_cases n
  case «8» => exact sound_map readIdx_sound Wasm.Instr.throw (fun _ _ hg => Instr.throw hg) h
  case «12» => exact sound_map readIdx_sound Wasm.Instr.br (fun _ _ hg => Instr.br hg) h
  case «13» => exact sound_map readIdx_sound Wasm.Instr.brIf (fun _ _ hg => Instr.brIf hg) h
  case «16» => exact sound_map readIdx_sound Wasm.Instr.call (fun _ _ hg => Instr.call hg) h
  case «32» => exact sound_map readIdx_sound Wasm.Instr.localGet (fun _ _ hg => Instr.localGet hg) h
  case «33» => exact sound_map readIdx_sound Wasm.Instr.localSet (fun _ _ hg => Instr.localSet hg) h
  case «34» => exact sound_map readIdx_sound Wasm.Instr.localTee (fun _ _ hg => Instr.localTee hg) h
  case «35» => exact sound_map readIdx_sound Wasm.Instr.globalGet (fun _ _ hg => Instr.globalGet hg) h
  case «36» => exact sound_map readIdx_sound Wasm.Instr.globalSet (fun _ _ hg => Instr.globalSet hg) h
  case «37» => exact sound_map readIdx_sound Wasm.Instr.tableGet (fun _ _ hg => Instr.tableGet hg) h
  case «38» => exact sound_map readIdx_sound Wasm.Instr.tableSet (fun _ _ hg => Instr.tableSet hg) h
  case «210» => exact sound_map readIdx_sound Wasm.Instr.refFunc (fun _ _ hg => Instr.refFunc hg) h
  case «213» => exact sound_map readIdx_sound Wasm.Instr.brOnNull (fun _ _ hg => Instr.brOnNull hg) h
  case «214» => exact sound_map readIdx_sound Wasm.Instr.brOnNonNull (fun _ _ hg => Instr.brOnNonNull hg) h
  case «208» =>
    exact sound_map readRefType_heapType_sound Wasm.Instr.refNull (fun _ _ hg => Instr.refNull hg) h
  case «17» =>
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hby, py ++ px, by simp [hry, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.callIndirect hgy (.idx rfl hgx)
  case «18» =>
    exact sound_map readIdx_sound Wasm.Instr.returnCall (fun _ _ hg => Instr.returnCall hg) h
  case «19» =>
    obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
    obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    refine ⟨hbx.trans hby, py ++ px, by simp [hry, hrx, List.append_assoc], ?_⟩
    simpa [List.append_assoc] using Instr.returnCallIndirect hgy hgx
  case «20» =>
    exact sound_map readIdx_sound Wasm.Instr.callRef (fun _ _ hg => Instr.callRef hg) h
  case «21» =>
    exact sound_map readIdx_sound Wasm.Instr.returnCallRef
      (fun _ _ hg => Instr.returnCallRef hg) h
  case «28» =>
    exact sound_map (readVec_sound readValType_sound) (fun ts => Wasm.Instr.select (some ts))
      (fun _ _ hg => Instr.selectT hg) h
  case «63» =>
    exact sound_map readIdx_sound Wasm.Instr.memorySize
      (fun _ _ hg => Instr.memorySize (.idx rfl hg)) h
  case «64» =>
    exact sound_map readIdx_sound Wasm.Instr.memoryGrow
      (fun _ _ hg => Instr.memoryGrow (.idx rfl hg)) h
  case «252» =>
    obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
    obtain ⟨hbn, pn, hrn, hgn⟩ := readU_sound 32 hn
    split at h
    · obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
      obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans (hby.trans hbn), pn ++ py ++ px, ?_, ?_⟩
      · simp [hrn, hry, hrx, List.append_assoc]
      · simpa [List.append_assoc] using Instr.memoryInit hgn hgy (.idx rfl hgx)
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.dataDrop hgn hgx
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
      refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
      · simp [hrn, hrx, hry, List.append_assoc]
      · simpa [List.append_assoc] using Instr.memoryCopy hgn (.idx rfl hgx) (.idx rfl hgy)
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.memoryFill hgn (.idx rfl hgx)
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
      refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
      · simp [hrn, hrx, hry, List.append_assoc]
      · simpa [List.append_assoc] using Instr.tableInit hgn hgx hgy
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.elemDrop hgn hgx
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨y, cy, hy, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      obtain ⟨hby, py, hry, hgy⟩ := readIdx_sound hy
      refine ⟨hby.trans (hbx.trans hbn), pn ++ px ++ py, ?_, ?_⟩
      · simp [hrn, hrx, hry, List.append_assoc]
      · simpa [List.append_assoc] using Instr.tableCopy hgn hgx hgy
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.tableGrow hgn hgx
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.tableSize hgn hgx
    · obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
      refine ⟨hbx.trans hbn, pn ++ px, by simp [hrn, hrx, List.append_assoc], ?_⟩
      simpa [List.append_assoc] using Instr.tableFill hgn hgx
    · split at h
      · rename_i i hi
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        exact ⟨hbn, pn, hrn, Instr.prefixFC (prefixFCOp?_spec hi) hgn⟩
      · exact (decodeError_ok h).elim
  case «65» =>
    exact sound_map (readS_sound 32) (fun v => Wasm.Instr.intConst .i32 (BitVec.ofInt 32 v))
      (fun _ _ hg => Instr.i32Const (IN.mk hg)) h
  case «66» =>
    exact sound_map (readS_sound 64) (fun v => Wasm.Instr.intConst .i64 (BitVec.ofInt 64 v))
      (fun _ _ hg => Instr.i64Const (IN.mk hg)) h
  case «67» =>
    obtain ⟨bs, cb, hbs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, rfl, hl⟩ := readBytes_sound 4 hbs
    exact ⟨hb, _, hr, Instr.f32Const (FN.mk _ hl)⟩
  case «68» =>
    obtain ⟨bs, cb, hbs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, rfl, hl⟩ := readBytes_sound 8 hbs
    exact ⟨hb, _, hr, Instr.f64Const (FN.mk _ hl)⟩
  case «14» =>
    obtain ⟨ls, cm, hls, h⟩ := run_bind_ok h
    obtain ⟨l, ce, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, p, hr, hg⟩ := readVec_sound readIdx_sound hls
    obtain ⟨hb', q, hr', hg'⟩ := readIdx_sound hl
    exact ⟨hb'.trans hb, p ++ q, by simp [hr, hr', List.append_assoc],
      Instr.brTable (b := p) (b' := q) hg hg'⟩
  case «251» => exact readGCInstr_sound h
  case «253» => exact readVecInstr_sound h
  all_goals exact readOpOnly_sound _ h

theorem readCatch_sound : Sound Catch readCatch := by
  intro c a c' h
  obtain ⟨b, cb, hb, h⟩ := run_bind_ok h
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  · rename_i he
    obtain rfl : b = 0x00 := UInt8.toNat_inj.mp he
    obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    exact ⟨hbl.trans (hbx.trans hbb), [0x00] ++ px ++ pl,
      by simp [hrb, hrx, hrl, List.append_assoc], Catch.catch_ hgx hgl⟩
  · rename_i he
    obtain rfl : b = 0x01 := UInt8.toNat_inj.mp he
    obtain ⟨x, cx, hx, h⟩ := run_bind_ok h
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbx, px, hrx, hgx⟩ := readIdx_sound hx
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    exact ⟨hbl.trans (hbx.trans hbb), [0x01] ++ px ++ pl,
      by simp [hrb, hrx, hrl, List.append_assoc], Catch.catchRef hgx hgl⟩
  · rename_i he
    obtain rfl : b = 0x02 := UInt8.toNat_inj.mp he
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    exact ⟨hbl.trans hbb, [0x02] ++ pl, by simp [hrb, hrl], Catch.catchAll hgl⟩
  · rename_i he
    obtain rfl : b = 0x03 := UInt8.toNat_inj.mp he
    obtain ⟨l, cl, hl, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hbl, pl, hrl, hgl⟩ := readIdx_sound hl
    exact ⟨hbl.trans hbb, [0x03] ++ pl, by simp [hrb, hrl], Catch.catchAllRef hgl⟩
  · exact (decodeError_ok h).elim

/-- An instruction after its opcode byte, and an instruction sequence with its
terminator (`end` or `else`), by induction on the fuel. -/
theorem readInstr_readSeq_sound (fuel : Nat) :
    (∀ op : UInt8, Sound (fun pre i => Instr Forms.all ([op] ++ pre) i) (readInstr fuel op.toNat)) ∧
    Sound (fun pre (r : List Wasm.Instr × UInt8) =>
      (r.2 = 0x0B ∨ r.2 = 0x05) ∧ ∃ b, pre = b ++ [r.2] ∧ Instrs Forms.all b r.1) (readSeq fuel) := by
  induction fuel with
  | zero =>
    constructor
    · intro op c a c' h
      exact (decodeError_ok h).elim
    · intro c a c' h
      exact (decodeError_ok h).elim
  | succ fuel ih =>
    obtain ⟨hi, hs⟩ := ih
    constructor
    · intro op c a c' h
      simp only [readInstr] at h
      split at h
      · rename_i hop
        have hop : op = 0x02 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.block hg hbody
        · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x03 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.loop hg hbody
        · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x04 := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨⟨thn, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans hbt, bt ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.if_ hg hbody
        · rename_i he
          obtain ⟨⟨els, term'⟩, ce, hels, h⟩ := run_bind_ok h
          dsimp only at h
          split at h
          · rename_i he'
            have he' : term' = 0x0B := by simpa using he'
            subst term'
            obtain ⟨rfl, rfl⟩ := run_pure_ok h
            obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
            obtain ⟨hbs, bs, hr', hterm, thnBytes, rfl, hthn⟩ := hs hseq
            have hterm : term = 0x05 := hterm.resolve_left (by simpa using he)
            subst term
            obtain ⟨hbe, be, hre, _, elsBytes, rfl, helse⟩ := hs hels
            refine ⟨hbe.trans (hbs.trans hbt), bt ++ thnBytes ++ [0x05] ++ elsBytes ++ [0x0B], ?_, ?_⟩
            · simp [hr, hr', hre, List.append_assoc]
            · simpa only [List.append_assoc] using Instr.ifElse hg hthn helse
          · exact (decodeError_ok h).elim
      · rename_i hop
        have hop : op = 0x1F := UInt8.toNat_inj.mp hop
        subst op
        obtain ⟨t, cm, ht, h⟩ := run_bind_ok h
        obtain ⟨cs, cc, hc, h⟩ := run_bind_ok h
        obtain ⟨⟨body, term⟩, cn, hseq, h⟩ := run_bind_ok h
        dsimp only at h
        split at h
        · rename_i he
          have he : term = 0x0B := by simpa using he
          subst term
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          obtain ⟨hbt, bt, hr, hg⟩ := readBlockType_sound ht
          obtain ⟨hbc, bc, hrc, hgc⟩ := readVec_sound readCatch_sound hc
          obtain ⟨hbs, bs, hr', _, bodyBytes, rfl, hbody⟩ := hs hseq
          refine ⟨hbs.trans (hbc.trans hbt), bt ++ bc ++ bodyBytes ++ [0x0B], ?_, ?_⟩
          · simp [hr, hrc, hr', List.append_assoc]
          · simpa only [List.append_assoc] using Instr.tryTable hg hgc hbody
        · exact (decodeError_ok h).elim
      · exact readPlain_sound op h
    · intro c a c' h
      simp only [readSeq] at h
      obtain ⟨b, cm, hb, h⟩ := run_bind_ok h
      obtain ⟨hbbytes, hbrest⟩ := readByte_ok hb
      split at h
      · rename_i hterm
        have hterm : b = 0x0B ∨ b = 0x05 := by simpa using hterm
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        exact ⟨hbbytes, [b], hbrest, hterm, [], rfl, Instrs.nil⟩
      · obtain ⟨i, ci, hi', h⟩ := run_bind_ok h
        obtain ⟨⟨is, term⟩, ce, hseq, h⟩ := run_bind_ok h
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hibytes, bi, hirest, hig⟩ := hi b hi'
        obtain ⟨hsbytes, bs, hsrest, hterm, bodyBytes, rfl, hbody⟩ := hs hseq
        refine ⟨hsbytes.trans (hibytes.trans hbbytes), [b] ++ bi ++ (bodyBytes ++ [term]), ?_,
          hterm, [b] ++ bi ++ bodyBytes, ?_, Instrs.cons hig hbody⟩
        · simp [hbrest, hirest, hsrest, List.append_assoc]
        · simp [List.append_assoc]

theorem readExpr_sound : Sound (Expr Forms.all) readExpr := by
  intro c a c' h
  obtain ⟨n, cm, hn, h⟩ := run_bind_ok (show (remaining >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (n, cm) at hn
    exact (Prod.mk.inj (Except.ok.inj hn)).2.symm
  subst cm
  obtain ⟨⟨is, term⟩, ce, hseq, h⟩ := run_bind_ok h
  dsimp only at h
  split at h
  · rename_i he
    have he : term = 0x0B := by simpa using he
    subst term
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, _, b, rfl, hg⟩ := (readInstr_readSeq_sound (n + 1)).2 hseq
    exact ⟨hb, b ++ [0x0B], hr, Expr.mk hg⟩
  · exact (decodeError_ok h).elim

theorem readData_sound : Sound (Data Forms.all) readData :=
  fun _ _ _ h => readData_ok readExpr_sound h

theorem readTableType_sound : Sound (TableType Forms.all) readTableType := by
  intro c a c' h
  obtain ⟨rt, cr, hr, h⟩ := bindOk (show (readRefType >>= _).run c = _ from h)
  obtain ⟨⟨addr, lim⟩, cl, hl, h⟩ := bindOk h
  cases h
  obtain ⟨hbr, pr, hrr, hgr⟩ := readRefType_sound hr
  obtain ⟨hbl, pl, hrl, hgl⟩ := readLimits_sound hl
  exact ⟨hbl.trans hbr, pr ++ pl, by simp [hrr, hrl, List.append_assoc], TableType.mk hgr hgl⟩

theorem readTable_sound : Sound (Table Forms.all) readTable := by
  intro c a c' h
  obtain ⟨ob, cm, hob, h⟩ := bindOk (show (peekByte >>= _).run c = _ from h)
  have hc : cm = c := by
    change Except.ok (_, c) = Except.ok (ob, cm) at hob
    exact (Prod.mk.inj (Except.ok.inj hob)).2.symm
  subst cm
  split at h
  · rename_i he
    have he : ob = some 0x40 := by simpa using he
    obtain ⟨b, c₁, hb, h⟩ := bindOk h
    obtain ⟨ce, hread⟩ := peekByte_readByte (he ▸ hob)
    rw [hb] at hread
    obtain ⟨rfl, rfl⟩ := Except.ok.inj hread
    obtain ⟨z, c₂, hz, h⟩ := bindOk h
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hb
    obtain ⟨hb₂, hr₂⟩ := readByte_ok hz
    split at h
    · rename_i hz0
      have hz0 : z = 0x00 := by simpa using hz0
      subst z
      obtain ⟨t, c₃, ht, h⟩ := bindOk h
      obtain ⟨e, c₄, he, h⟩ := bindOk h
      cases h
      obtain ⟨hb₃, pt, hr₃, hgt⟩ := readTableType_sound ht
      obtain ⟨hb₄, pe, hr₄, hge⟩ := readExpr_sound he
      refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), [0x40, 0x00] ++ pt ++ pe,
        ?_, Table.explicit rfl hgt hge⟩
      simp [hr₁, hr₂, hr₃, hr₄, List.append_assoc]
    · obtain ⟨_, _, he, _⟩ := bindOk h
      exact (decodeError_ok he).elim
  · obtain ⟨t, ct, ht, h⟩ := bindOk h
    cases h
    obtain ⟨hb, pre, hr, hg⟩ := readTableType_sound ht
    exact ⟨hb, pre, hr, Table.implicit hg⟩

theorem readElem_sound : Sound (Elem Forms.all) readElem := by
  have funcInits_sound : Sound
      (fun pre es => ∃ bs ys, pre = [0x00] ++ bs ∧ Vec Index bs ys ∧ es = refFuncs ys)
      readElem.funcInits := by
    intro c es c' h
    obtain ⟨b, c₁, hb, h⟩ := bindOk (show (readByte >>= _).run c = _ from h)
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hb
    split at h
    · rename_i he
      have he : b = 0x00 := by simpa using he
      subst b
      obtain ⟨ys, c₂, hy, h⟩ := bindOk h
      cases h
      obtain ⟨hb₂, bs, hr₂, hg⟩ := readVec_sound readIdx_sound hy
      exact ⟨hb₂.trans hb₁, [0x00] ++ bs, by simp [hr₁, hr₂], bs, ys, rfl, hg, rfl⟩
    · obtain ⟨_, _, he, _⟩ := bindOk h
      exact (decodeError_ok he).elim
  intro c a c' h
  obtain ⟨k, c₁, hk, h⟩ := bindOk (show (readU 32 >>= _).run c = _ from h)
  obtain ⟨hb₁, pk, hr₁, hgk⟩ := readU_sound 32 hk
  split at h
  · obtain ⟨e, c₂, he, h⟩ := bindOk h
    obtain ⟨ys, c₃, hy, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, pe, hr₂, hge⟩ := readExpr_sound he
    obtain ⟨hb₃, py, hr₃, hgy⟩ := readVec_sound readIdx_sound hy
    exact ⟨hb₃.trans (hb₂.trans hb₁), pk ++ pe ++ py,
      by simp [hr₁, hr₂, hr₃, List.append_assoc], Elem.k0 hgk hge hgy⟩
  · obtain ⟨es, c₂, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, pre, hr₂, bs, ys, rfl, hgy, rfl⟩ := funcInits_sound hes
    exact ⟨hb₂.trans hb₁, pk ++ [0x00] ++ bs,
      by simp [hr₁, hr₂, List.append_assoc], Elem.k1 rfl hgk ElemKind.func hgy⟩
  · obtain ⟨x, c₂, hx, h⟩ := bindOk h
    obtain ⟨e, c₃, he, h⟩ := bindOk h
    obtain ⟨es, c₄, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, px, hr₂, hgx⟩ := readIdx_sound hx
    obtain ⟨hb₃, pe, hr₃, hge⟩ := readExpr_sound he
    obtain ⟨hb₄, pre, hr₄, bs, ys, rfl, hgy, rfl⟩ := funcInits_sound hes
    exact ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), pk ++ px ++ pe ++ [0x00] ++ bs,
      by simp [hr₁, hr₂, hr₃, hr₄, List.append_assoc], Elem.k2 rfl hgk hgx hge ElemKind.func hgy⟩
  · obtain ⟨es, c₂, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, pre, hr₂, bs, ys, rfl, hgy, rfl⟩ := funcInits_sound hes
    exact ⟨hb₂.trans hb₁, pk ++ [0x00] ++ bs,
      by simp [hr₁, hr₂, List.append_assoc], Elem.k3 rfl hgk ElemKind.func hgy⟩
  · obtain ⟨e, c₂, he, h⟩ := bindOk h
    obtain ⟨es, c₃, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, pe, hr₂, hge⟩ := readExpr_sound he
    obtain ⟨hb₃, pes, hr₃, hges⟩ := readVec_sound readExpr_sound hes
    exact ⟨hb₃.trans (hb₂.trans hb₁), pk ++ pe ++ pes,
      by simp [hr₁, hr₂, hr₃, List.append_assoc], Elem.k4 rfl hgk hge hges⟩
  · obtain ⟨rt, c₂, hrt, h⟩ := bindOk h
    obtain ⟨es, c₃, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, prt, hr₂, hgrt⟩ := readRefType_sound hrt
    obtain ⟨hb₃, pes, hr₃, hges⟩ := readVec_sound readExpr_sound hes
    exact ⟨hb₃.trans (hb₂.trans hb₁), pk ++ prt ++ pes,
      by simp [hr₁, hr₂, hr₃, List.append_assoc], Elem.k5 rfl hgk hgrt hges⟩
  · obtain ⟨x, c₂, hx, h⟩ := bindOk h
    obtain ⟨e, c₃, he, h⟩ := bindOk h
    obtain ⟨rt, c₄, hrt, h⟩ := bindOk h
    obtain ⟨es, c₅, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, px, hr₂, hgx⟩ := readIdx_sound hx
    obtain ⟨hb₃, pe, hr₃, hge⟩ := readExpr_sound he
    obtain ⟨hb₄, prt, hr₄, hgrt⟩ := readRefType_sound hrt
    obtain ⟨hb₅, pes, hr₅, hges⟩ := readVec_sound readExpr_sound hes
    exact ⟨hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans hb₁))), pk ++ px ++ pe ++ prt ++ pes,
      by simp [hr₁, hr₂, hr₃, hr₄, hr₅, List.append_assoc], Elem.k6 rfl hgk hgx hge hgrt hges⟩
  · obtain ⟨rt, c₂, hrt, h⟩ := bindOk h
    obtain ⟨es, c₃, hes, h⟩ := bindOk h
    cases h
    obtain ⟨hb₂, prt, hr₂, hgrt⟩ := readRefType_sound hrt
    obtain ⟨hb₃, pes, hr₃, hges⟩ := readVec_sound readExpr_sound hes
    exact ⟨hb₃.trans (hb₂.trans hb₁), pk ++ prt ++ pes,
      by simp [hr₁, hr₂, hr₃, List.append_assoc], Elem.k7 rfl hgk hgrt hges⟩
  · exact (decodeError_ok h).elim

/-! ## Module fields -/

theorem readTag_sound : Sound Tag readTag := by
  intro c a c' h
  obtain ⟨b, cb, hb, h⟩ := run_bind_ok h
  obtain ⟨hbb, hrb⟩ := readByte_ok hb
  split at h
  · rename_i he
    obtain rfl : b = 0x00 := by simpa using he
    have hidx : readIdx.run cb = .ok (a, c') := by simpa only [pure_bind] using h
    obtain ⟨hbi, pi, hri, hgi⟩ := readIdx_sound hidx
    exact ⟨hbi.trans hbb, [0x00] ++ pi, by simp [hrb, hri], TagType.mk hgi⟩
  · obtain ⟨_, _, he, _⟩ := run_bind_ok h
    exact (decodeError_ok he).elim

theorem readImport_sound : Sound (Import Forms.all) readImport := by
  intro c a c' h
  obtain ⟨m, c₁, hm, h⟩ := run_bind_ok h
  obtain ⟨n, c₂, hn, h⟩ := run_bind_ok h
  obtain ⟨k, c₃, hk, h⟩ := run_bind_ok h
  obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readName_sound hm
  obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readName_sound hn
  obtain ⟨hb₃, hr₃⟩ := readByte_ok hk
  dsimp only at h
  split at h
  · rename_i he
    obtain rfl : k = 0x00 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readIdx_sound hx
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), p₁ ++ p₂ ++ ([0x00] ++ p₄), ?_,
      Import.mk hg₁ hg₂ (ExternType.func hg₄)⟩
    simp [hr₁, hr₂, hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x01 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readTableType_sound hx
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), p₁ ++ p₂ ++ ([0x01] ++ p₄), ?_,
      Import.mk hg₁ hg₂ (ExternType.table hg₄)⟩
    simp [hr₁, hr₂, hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x02 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readMemType_sound hx
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), p₁ ++ p₂ ++ ([0x02] ++ p₄), ?_,
      Import.mk hg₁ hg₂ (ExternType.memory hg₄)⟩
    simp [hr₁, hr₂, hr₃, hr₄]
  · rename_i he
    obtain rfl : k = 0x03 := UInt8.toNat_inj.mp he
    obtain ⟨t, c₄, ht, h⟩ := run_bind_ok h
    obtain ⟨mb, c₅, hmut, h⟩ := run_bind_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readValType_sound ht
    obtain ⟨hb₅, hr₅⟩ := readByte_ok hmut
    split at h
    · rename_i he
      obtain rfl : mb = 0x00 := UInt8.toNat_inj.mp he
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans hb₁))),
        p₁ ++ p₂ ++ ([0x03] ++ (p₄ ++ [0x00])), ?_,
        Import.mk hg₁ hg₂ (ExternType.global (GlobalType.mk hg₄ Mut.const))⟩
      simp [hr₁, hr₂, hr₃, hr₄, hr₅]
    · rename_i he
      obtain rfl : mb = 0x01 := UInt8.toNat_inj.mp he
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      refine ⟨hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans hb₁))),
        p₁ ++ p₂ ++ ([0x03] ++ (p₄ ++ [0x01])), ?_,
        Import.mk hg₁ hg₂ (ExternType.global (GlobalType.mk hg₄ Mut.var))⟩
      simp [hr₁, hr₂, hr₃, hr₄, hr₅]
    · obtain ⟨_, _, he, _⟩ := run_bind_ok h
      exact (decodeError_ok he).elim
  · rename_i he
    obtain rfl : k = 0x04 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₄, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₄, p₄, hr₄, hg₄⟩ := readTag_sound hx
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), p₁ ++ p₂ ++ ([0x04] ++ p₄), ?_,
      Import.mk hg₁ hg₂ (ExternType.tag hg₄)⟩
    simp [hr₁, hr₂, hr₃, hr₄]
  · exact (decodeError_ok h).elim

theorem readGlobal_sound : Sound (Global Forms.all) readGlobal := by
  intro c a c' h
  obtain ⟨t, c₁, ht, h⟩ := run_bind_ok h
  obtain ⟨k, c₂, hk, h⟩ := run_bind_ok h
  obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readValType_sound ht
  obtain ⟨hb₂, hr₂⟩ := readByte_ok hk
  have key : ∀ m, Mut [k] m → (do let init ← readExpr; pure (⟨⟨m, t⟩, init⟩ : Wasm.Global)).run c₂ =
      .ok (a, c') → c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧ Global Forms.all pre a := by
    intro m hm h
    obtain ⟨e, c₃, he, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readExpr_sound he
    exact ⟨hb₃.trans (hb₂.trans hb₁), (p₁ ++ [k]) ++ p₃, by simp [hr₁, hr₂, hr₃],
      Global.mk (GlobalType.mk hg₁ hm) hg₃⟩
  dsimp only at h
  split at h
  · rename_i hk0
    obtain rfl : k = 0x00 := UInt8.toNat_inj.mp hk0
    exact key _ Mut.const (by simpa only [pure_bind] using h)
  · rename_i hk1
    obtain rfl : k = 0x01 := UInt8.toNat_inj.mp hk1
    exact key _ Mut.var (by simpa only [pure_bind] using h)
  · obtain ⟨_, _, he, _⟩ := run_bind_ok h
    exact (decodeError_ok he).elim

theorem readExport_sound : Sound Export readExport := by
  intro c a c' h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  obtain ⟨k, c₂, hk, h⟩ := run_bind_ok h
  obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readName_sound hn
  obtain ⟨hb₂, hr₂⟩ := readByte_ok hk
  split at h
  · rename_i he
    obtain rfl : k = 0x00 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₃, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readIdx_sound hx
    exact ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ ([0x00] ++ p₃), by simp [hr₁, hr₂, hr₃],
      Export.mk hg₁ (ExternIdx.func hg₃)⟩
  · rename_i he
    obtain rfl : k = 0x01 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₃, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readIdx_sound hx
    exact ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ ([0x01] ++ p₃), by simp [hr₁, hr₂, hr₃],
      Export.mk hg₁ (ExternIdx.table hg₃)⟩
  · rename_i he
    obtain rfl : k = 0x02 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₃, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readIdx_sound hx
    exact ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ ([0x02] ++ p₃), by simp [hr₁, hr₂, hr₃],
      Export.mk hg₁ (ExternIdx.memory hg₃)⟩
  · rename_i he
    obtain rfl : k = 0x03 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₃, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readIdx_sound hx
    exact ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ ([0x03] ++ p₃), by simp [hr₁, hr₂, hr₃],
      Export.mk hg₁ (ExternIdx.global hg₃)⟩
  · rename_i he
    obtain rfl : k = 0x04 := UInt8.toNat_inj.mp he
    obtain ⟨x, c₃, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readIdx_sound hx
    exact ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ ([0x04] ++ p₃), by simp [hr₁, hr₂, hr₃],
      Export.mk hg₁ (ExternIdx.tag hg₃)⟩
  · exact (decodeError_ok h).elim

/-- `remaining` is the length of the rest, and consumes nothing. -/
theorem remaining_run (c : Cursor) : remaining.run c = .ok (c.rest.length, c) := by
  simp [remaining, Cursor.rest]
  rfl

/-- One locals group, before its expansion. -/
theorem readLocals_sound :
    Sound (fun pre (p : Nat × Wasm.ValType) => Locals Forms.all pre (List.replicate p.1 p.2))
      (do let n ← readU 32; let t ← readValType; pure (n, t)) := by
  intro c a c' h
  obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
  obtain ⟨t, c₂, ht, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := run_pure_ok h
  obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readU_sound 32 hn
  obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readValType_sound ht
  exact ⟨hb₂.trans hb₁, p₁ ++ p₂, by simp [hr₁, hr₂], Locals.mk hg₁ hg₂⟩

theorem seq_map {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop} (f : α → β)
    (hf : ∀ b x, G b x → H b (f x)) {b : Bytes} {xs : List α} (h : Seq G b xs) :
    Seq H b (xs.map f) := by
  induction h with
  | nil => exact Seq.nil
  | cons ha _ ih => exact Seq.cons (hf _ _ ha) ih

theorem vec_map {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop} (f : α → β)
    (hf : ∀ b x, G b x → H b (f x)) {b : Bytes} {xs : List α} (h : Vec G b xs) :
    Vec H b (xs.map f) := by
  cases h with
  | mk hn hs => exact Vec.mk (by simpa using hn) (seq_map f hf hs)

theorem foldl_locals (gs : List (Nat × Wasm.ValType)) (k : Nat) :
    gs.foldl (fun s p => s + p.1) k = k + (gs.flatMap fun p => List.replicate p.1 p.2).length := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem readCode_sound : Sound (Code Forms.all) readCode := by
  intro c a c' h
  obtain ⟨size, c₁, hsize, h⟩ := run_bind_ok h
  obtain ⟨r₀, c₂, h₀, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c₁.rest.length = r₀ ∧ c₁ = c₂ := by
    rw [remaining_run] at h₀; cases h₀; exact ⟨rfl, rfl⟩
  split at h
  · obtain ⟨gs, c₃, hgs, h⟩ := run_bind_ok h
    dsimp only at h
    split at h
    · rename_i htot
      obtain ⟨body, c₄, hbody, h⟩ := run_bind_ok h
      obtain ⟨r₁, c₅, h₁, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ : c₄.rest.length = r₁ ∧ c₄ = c₅ := by
        rw [remaining_run] at h₁; cases h₁; exact ⟨rfl, rfl⟩
      split at h
      · rename_i hlen
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readU_sound 32 hsize
        obtain ⟨hb₂, p₂, hr₂, hg₂⟩ := readVec_sound readLocals_sound hgs
        obtain ⟨hb₃, p₃, hr₃, hg₃⟩ := readExpr_sound hbody
        have hlen : c₁.rest.length - c₄.rest.length = size := by simpa using hlen
        rw [hr₂, hr₃] at hlen
        refine ⟨hb₃.trans (hb₂.trans hb₁), p₁ ++ (p₂ ++ p₃), by simp [hr₁, hr₂, hr₃], ?_⟩
        have hfl : (gs.flatMap fun p => List.replicate p.1 p.2) =
            (gs.map fun p => List.replicate p.1 p.2).flatten := List.flatMap_def
        rw [hfl]
        refine Code.mk hg₁ (by simp at hlen ⊢; omega) (Func.mk (vec_map (fun p : Nat × Wasm.ValType => List.replicate p.1 p.2) (fun _ _ h => h) hg₂) hg₃ ?_)
        rw [← hfl]
        have := foldl_locals gs 0
        simp only [maxLocals] at htot
        omega
      · obtain ⟨_, _, he, _⟩ := run_bind_ok h
        exact (decodeError_ok he).elim
    · obtain ⟨_, _, he, _⟩ := run_bind_ok h
      exact (decodeError_ok he).elim
  · obtain ⟨_, _, he, _⟩ := run_bind_ok h
    exact (decodeError_ok he).elim

theorem readCustom_sound (size : Nat) :
    Sound (fun pre (_ : Unit) => pre.length = size ∧ Custom pre [()]) (readCustom size) := by
  intro c a c' h
  obtain ⟨r₀, c₀, h₀, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c.rest.length = r₀ ∧ c = c₀ := by
    rw [remaining_run] at h₀; cases h₀; exact ⟨rfl, rfl⟩
  obtain ⟨nm, c₁, hn, h⟩ := run_bind_ok h
  obtain ⟨r₁, c₂, h₁, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c₁.rest.length = r₁ ∧ c₁ = c₂ := by
    rw [remaining_run] at h₁; cases h₁; exact ⟨rfl, rfl⟩
  dsimp only at h
  split at h
  · rename_i hle
    obtain ⟨ba, c₃, hba, h⟩ := run_bind_ok h
    obtain ⟨-, rfl⟩ := run_pure_ok h
    obtain ⟨hb₁, p₁, hr₁, hg₁⟩ := readName_sound hn
    obtain ⟨hb₂, p₂, hr₂, -, hl₂⟩ := readBytes_sound _ hba
    refine ⟨hb₂.trans hb₁, p₁ ++ p₂, by simp [hr₁, hr₂], ?_, Custom.mk p₂ hg₁⟩
    have hl₁ : c.rest.length = p₁.length + c₁.rest.length := by rw [hr₁, List.length_append]
    simp only [List.length_append, hl₂]
    omega
  · obtain ⟨_, _, he, _⟩ := run_bind_ok h
    exact (decodeError_ok he).elim

/-! ## Modules -/

theorem readHeader_sound : Sound (fun pre (_ : Unit) => pre = magic ++ version) readHeader := by
  intro c a c' h
  obtain ⟨ba, c₁, hba, h⟩ := run_bind_ok h
  obtain ⟨hb, pre, hr, rfl, -⟩ := readBytes_sound 8 hba
  split at h
  · rename_i he
    obtain ⟨-, rfl⟩ := run_pure_ok h
    exact ⟨hb, _, hr, by simpa using he⟩
  · exact (decodeError_ok h).elim

/-- The section of rank `r` (`sectionRank`) holds the fields of `s` read so far. -/
def SecOK (s : Sections) : Nat → Bytes → Prop
  | 1, b => TypeSec Forms.all b s.types
  | 2, b => ImportSec Forms.all b s.imports
  | 3, b => FuncSec b s.funcTypes
  | 4, b => TableSec Forms.all b s.tables
  | 5, b => MemSec Forms.all b s.memories
  | 6, b => TagSec Forms.all b s.tags
  | 7, b => GlobalSec Forms.all b s.globals
  | 8, b => ExportSec b s.exports
  | 9, b => StartSec b s.start
  | 10, b => ElemSec Forms.all b s.elems
  | 11, b => DataCntSec Forms.all b s.dataCount
  | 12, b => CodeSec Forms.all b s.code
  | 13, b => DataSec Forms.all b s.data
  | _, _ => False

/-- `p` is the module after its header, up to the section of rank `r` and the custom
sections after it, in the layout of `Module.mk`. -/
def Prefix (s : Sections) : Nat → Bytes → Prop
  | 0, p => Customs p
  | r + 1, p => ∃ q b c, p = q ++ b ++ c ∧ Prefix s r q ∧ SecOK s (r + 1) b ∧ Customs c

theorem SecOK.empty : ∀ k, 0 < k → k ≤ 13 → SecOK {} k []
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 7, _, _ | 8, _, _ | 10, _, _ | 12, _, _
  | 13, _, _ => Section.empty
  | 6, _, _ => TagSec.absent
  | 9, _, _ => StartSec.mk (xs := []) Section.empty
  | 11, _, _ => DataCntSec.absent
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ + 14, _, h => absurd h (by omega)

theorem Customs.append_sec {p x : Bytes} (h : Customs p) (hx : CustomSec x) : Customs (p ++ x) := by
  induction h with
  | nil => simpa using Customs.cons hx Customs.nil
  | cons hb _ ih => simpa [List.append_assoc] using Customs.cons hb ih

theorem Prefix.custom {s : Sections} {x : Bytes} (hx : CustomSec x) :
    ∀ {r p}, Prefix s r p → Prefix s r (p ++ x)
  | 0, _, h => Customs.append_sec h hx
  | _ + 1, _, ⟨q, b, c, e, hq, hb, hc⟩ =>
    ⟨q, b, c ++ x, by simp [e, List.append_assoc], hq, hb, Customs.append_sec hc hx⟩

theorem Prefix.congr {s s' : Sections} :
    ∀ {r p}, Prefix s r p → (∀ k, k ≤ r → SecOK s' k = SecOK s k) → Prefix s' r p
  | 0, _, h, _ => h
  | r + 1, _, ⟨q, b, c, e, hq, hb, hc⟩, hk =>
    ⟨q, b, c, e, hq.congr fun k h => hk k (Nat.le_succ_of_le h), (hk (r + 1) (Nat.le_refl _)) ▸ hb, hc⟩

/-- Absent sections fill the ranks after `L`. -/
theorem Prefix.pad {s : Sections} {L : Nat} {p : Bytes} (h : Prefix s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK s k []) : ∀ n, L ≤ n → n ≤ 13 → Prefix s n p
  | n, hL, h13 => by
    rcases Nat.eq_or_lt_of_le hL with rfl | hlt
    · exact h
    · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨p, [], [], by simp, h.pad he n (by omega) (by omega), he _ hlt h13, Customs.nil⟩

/-- A section of rank `r` after the section of rank `L < r`. -/
theorem Prefix.sec {s s' : Sections} {L r : Nat} {p x : Bytes} (h : Prefix s L p)
    (he : ∀ k, L < k → k ≤ 13 → SecOK s k []) (hr : L < r) (h13 : r ≤ 13) (hx : SecOK s' r x)
    (hs : ∀ k, k ≠ r → SecOK s' k = SecOK s k) : Prefix s' r (p ++ x) := by
  obtain ⟨r, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  exact ⟨p, x, [], by simp, (h.pad he r (by omega) (by omega)).congr fun k hk => hs k (by omega),
    hx, Customs.nil⟩

theorem sectionRank_le (id : Nat) : sectionRank id ≤ 13 := by
  unfold sectionRank; split <;> omega

/-- The other ranks see the same fields. -/
local macro "agree" : tactic => `(tactic| (
  intro k hk
  funext x
  unfold SecOK
  split <;> first | rfl | exact absurd rfl hk))

/-- The contents of one non-custom section: `pre`, behind the id byte and a length `lb`. -/
theorem readSectionBody_ok {b : UInt8} {s s' : Sections} {c c' : Cursor}
    (h : (readSectionBody b.toNat s).run c = .ok (s', c')) :
    c'.bytes = c.bytes ∧ ∃ pre, c.rest = pre ++ c'.rest ∧
      (∀ lb, U32 lb pre.length → SecOK s' (sectionRank b.toNat) ([b] ++ lb ++ pre)) ∧
      ∀ k, k ≠ sectionRank b.toNat → SecOK s' k = SecOK s k := by
  unfold readSectionBody at h
  split at h
  case h_1 hid =>
    obtain rfl : b = 1 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readRecType_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_2 hid =>
    obtain rfl : b = 2 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readImport_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_3 hid =>
    obtain rfl : b = 3 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readIdx_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_4 hid =>
    obtain rfl : b = 4 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readTable_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_5 hid =>
    obtain rfl : b = 5 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readMemType_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_6 hid =>
    obtain rfl : b = 6 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readGlobal_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_7 hid =>
    obtain rfl : b = 7 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readExport_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_8 hid =>
    obtain rfl : b = 8 := UInt8.toNat_inj.mp hid
    obtain ⟨x, c₁, hx, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readIdx_sound hx
    exact ⟨hb, pre, hr, fun lb hl => StartSec.mk (Section.mk hl rfl (Start.mk hg)), by agree⟩
  case h_9 hid =>
    obtain rfl : b = 9 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readElem_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_10 hid =>
    obtain rfl : b = 10 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readCode_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_11 hid =>
    obtain rfl : b = 11 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readData_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => Section.mk hl rfl hg, by agree⟩
  case h_12 hid =>
    obtain rfl : b = 12 := UInt8.toNat_inj.mp hid
    obtain ⟨n, c₁, hn, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readU_sound 32 hn
    exact ⟨hb, pre, hr, fun lb hl => DataCntSec.present rfl (Section.mk hl rfl (DataCnt.mk hg)),
      by agree⟩
  case h_13 hid =>
    obtain rfl : b = 13 := UInt8.toNat_inj.mp hid
    obtain ⟨xs, c₁, hxs, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    obtain ⟨hb, pre, hr, hg⟩ := readVec_sound readTag_sound hxs
    exact ⟨hb, pre, hr, fun lb hl => TagSec.present rfl (Section.mk hl rfl hg), by agree⟩
  case h_14 => exact (decodeError_ok h).elim


theorem rest_of_remaining {c c₁ : Cursor} {r : Nat} (h : remaining.run c = .ok (r, c₁)) :
    c.rest.length = r ∧ c = c₁ := by
  rw [remaining_run] at h; cases h; exact ⟨rfl, rfl⟩

/-- The section loop: the bytes it consumes extend a layout prefix. -/
theorem readModule_go_ok (fuel : Nat) : ∀ {last : Nat} {s s' : Sections} {c c' : Cursor},
    (readModule.go fuel last s).run c = .ok (s', c') → last ≤ 13 →
    (∀ k, last < k → k ≤ 13 → SecOK s k []) →
    c'.bytes = c.bytes ∧ ∃ pre last', c.rest = pre ++ c'.rest ∧ last' ≤ 13 ∧
      (∀ k, last' < k → k ≤ 13 → SecOK s' k []) ∧ ∀ p, Prefix s last p → Prefix s' last' (p ++ pre) := by
  induction fuel with
  | zero =>
    intro last s s' c c' h h13 he
    obtain ⟨rfl, rfl⟩ := run_pure_ok h
    exact ⟨rfl, [], last, by simp, h13, he, fun p hp => by simpa using hp⟩
  | succ fuel ih =>
    intro last s s' c c' h h13 he
    unfold readModule.go at h
    obtain ⟨r, c₁, hr, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining hr
    try dsimp only at h
    split at h
    · obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨rfl, [], last, by simp, h13, he, fun p hp => by simpa using hp⟩
    obtain ⟨b, c₂, hb, h⟩ := run_bind_ok h
    obtain ⟨size, c₃, hsize, h⟩ := run_bind_ok h
    obtain ⟨r₀, c₄, h₀, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining h₀
    obtain ⟨hb₁, hr₁⟩ := readByte_ok hb
    obtain ⟨hb₂, lb, hr₂, hl⟩ := readU_sound 32 hsize
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    try dsimp only at h
    split at h
    · rename_i hid
      obtain ⟨u, c₅, hc, h⟩ := run_bind_ok h
      obtain ⟨hb₃, pc, hr₃, hlen, hcu⟩ := readCustom_sound size hc
      obtain ⟨hb₄, pre, last', hr₄, h13', he', hp'⟩ := ih h h13 he
      obtain rfl : b = 0 := UInt8.toNat_inj.mp (by simpa using hid)
      refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), ([0] ++ lb ++ pc) ++ pre, last',
        by simp [hr₁, hr₂, hr₃, hr₄], h13', he', fun p hp => ?_⟩
      simpa [List.append_assoc] using hp' _ (hp.custom ⟨[()], Section.mk hl hlen.symm hcu⟩)
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    rename_i hlt
    obtain ⟨s₁, c₅, hs₁, h⟩ := run_bind_ok h
    obtain ⟨r₁, c₆, h₁, h⟩ := run_bind_ok h
    obtain ⟨rfl, rfl⟩ := rest_of_remaining h₁
    try dsimp only at h
    split at h
    case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
    rename_i hsz
    obtain ⟨hb₃, pc, hr₃, hsec, hagree⟩ := readSectionBody_ok hs₁
    have hpc : pc.length = size := by
      have hsz : c₃.rest.length - c₅.rest.length = size := by simpa using hsz
      rw [hr₃, List.length_append] at hsz
      omega
    have he₁ : ∀ k, sectionRank b.toNat < k → k ≤ 13 → SecOK s₁ k [] := fun k hk hk13 =>
      (hagree k (by omega)) ▸ he k (by omega) hk13
    obtain ⟨hb₄, pre, last', hr₄, h13', he', hp'⟩ := ih h (sectionRank_le _) he₁
    refine ⟨hb₄.trans (hb₃.trans (hb₂.trans hb₁)), ([b] ++ lb ++ pc) ++ pre, last',
      by simp [hr₁, hr₂, hr₃, hr₄], h13', he', fun p hp => ?_⟩
    simpa [List.append_assoc] using
      hp' _ (hp.sec he hlt (sectionRank_le _) (hsec lb (hpc ▸ hl)) hagree)


/-- A complete layout is a module. -/
theorem Prefix.module {s : Sections} {p : Bytes} (h : Prefix s 13 p)
    (hf : s.funcTypes.length = s.code.length)
    (hcount : ∀ n ∈ s.dataCount, n = s.data.length)
    (hd : s.dataCount.isSome ∨ codesDataIdxs s.code = []) :
    Encodes (magic ++ version ++ p)
      { types := s.types, imports := s.imports, tags := s.tags, globals := s.globals,
        memories := s.memories, tables := s.tables, funcs := zipFuncs s.funcTypes s.code, data := s.data, elems := s.elems,
        start := s.start, exports := s.exports } := by
  obtain ⟨q, b₁₃, c₁₃, rfl, h, t₁₃, k₁₃⟩ := h
  obtain ⟨q, b₁₂, c₁₂, rfl, h, t₁₂, k₁₂⟩ := h
  obtain ⟨q, b₁₁, c₁₁, rfl, h, t₁₁, k₁₁⟩ := h
  obtain ⟨q, b₁₀, c₁₀, rfl, h, t₁₀, k₁₀⟩ := h
  obtain ⟨q, b₉, c₉, rfl, h, t₉, k₉⟩ := h
  obtain ⟨q, b₈, c₈, rfl, h, t₈, k₈⟩ := h
  obtain ⟨q, b₇, c₇, rfl, h, t₇, k₇⟩ := h
  obtain ⟨q, b₆, c₆, rfl, h, t₆, k₆⟩ := h
  obtain ⟨q, b₅, c₅, rfl, h, t₅, k₅⟩ := h
  obtain ⟨q, b₄, c₄, rfl, h, t₄, k₄⟩ := h
  obtain ⟨q, b₃, c₃, rfl, h, t₃, k₃⟩ := h
  obtain ⟨q, b₂, c₂, rfl, h, t₂, k₂⟩ := h
  obtain ⟨c₀, b₁, c₁, rfl, k₀, t₁, k₁⟩ := h
  have := Module.mk (F := Forms.all) k₀ t₁ k₁ t₂ k₂ t₃ k₃ t₄ k₄ t₅ k₅ t₆ k₆ t₇ k₇ t₈ k₈ t₉ k₉ t₁₀
    k₁₀ t₁₁ k₁₁ t₁₂ k₁₂ t₁₃ k₁₃ hcount hd hf
  simpa only [List.append_assoc] using this

/-- The whole input from any cursor: `readModule` succeeds only at the end of the input. -/
theorem readModule_sound {c c' : Cursor} {m : Wasm.Module} (h : readModule.run c = .ok (m, c')) :
    Encodes c.rest m := by
  unfold readModule at h
  obtain ⟨u, c₁, hh, h⟩ := run_bind_ok h
  obtain ⟨c₂, c₃, hg, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ : c₁ = c₂ ∧ c₁ = c₃ := by cases hg; exact ⟨rfl, rfl⟩
  obtain ⟨s, c₄, hs, h⟩ := run_bind_ok h
  obtain ⟨r, c₅, hr, h⟩ := run_bind_ok h
  obtain ⟨rfl, rfl⟩ := rest_of_remaining hr
  dsimp only at h
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hend
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hf
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hcount
  split at h
  case isFalse => obtain ⟨_, _, he, _⟩ := run_bind_ok h; exact (decodeError_ok he).elim
  rename_i hd
  obtain ⟨rfl, -⟩ := run_pure_ok h
  obtain ⟨-, pre, hr₁, rfl⟩ := readHeader_sound hh
  obtain ⟨-, pg, last, hr₂, h13, he, hp⟩ :=
    readModule_go_ok _ hs (Nat.zero_le _) fun k hk h13 => SecOK.empty k hk h13
  have hnil : c₄.rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hend)
  rw [hr₁, hr₂, hnil, List.append_nil]
  have hp := (hp [] Customs.nil).pad he 13 h13 (Nat.le_refl _)
  rw [List.nil_append] at hp
  have hcount' : ∀ n ∈ s.dataCount, n = s.data.length := by
    cases hc : s.dataCount with
    | none => simp
    | some n => simpa [hc] using hcount
  exact hp.module (by simpa using hf) hcount' (by simpa using hd)

theorem decodeModule_sound {b : ByteArray} {m : Wasm.Module} (h : decodeModule b = .ok m) :
    Encodes b.data.toList m := by
  unfold decodeModule at h
  rw [StateT.run'_eq] at h
  cases hr : readModule.run ⟨b, 0⟩ with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    cases h
    simpa [Cursor.rest] using readModule_sound hr

end Decode

/-- **Soundness of the decoder**: `decode?` returns only the module that the input
encodes (with `functional`, the unique one). -/
theorem decode?_sound {b : ByteArray} {m : Wasm.Module} (h : decode? b = some m) :
    Encodes b.data.toList m := by
  unfold decode? at h
  split at h
  · cases h
    exact Decode.decodeModule_sound ‹_›
  · cases h

end Silmaril.Wasm.Binary.Core
