module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Lit
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Load

/-!
# Round 5, pass 3, track read: a field literal and its bytes, read back

* `zbytes_lit_inv`: a typed literal `c : lit_(zt)` whose `$zbytes_(zt, c)` evaluates is the
  literal `litV zt k` of a word `k < 2 ^ |zt|` (numbers: `B`'s `$nbytes_` decodes `c`; vectors
  and packed types: the type of `c`, `lit_vec_inv`/`lit_pack_inv`), and the bytes are its
  little-endian encoding;
* `readField_of_slice`: a slice of a data segment that is the encoding of `k` is what Core's
  `readField?` reads, as `fieldOfLit zt k`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open R4Fwd (litV fieldOfLit)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem call_zbytes (a c : Value) :
    (BI P hn host).call "zbytes_" [.val a, .val c] = ZBytes.zbytesCall a c := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **A typed literal whose `$zbytes_` evaluates is the literal of a word that fits.** -/
theorem zbytes_lit_inv {ρ : VarEnv} {zt : CStorageType} {c v : Value} (h0 : 0 < storageSize zt)
    (hz : ρ.findVal? "zt" = some (tyV zt))
    (hc : HasTyp (simEnv (BI P hn host)) ρ (.varT "lit_" [.expA (.varE "zt")]) c)
    (h : Applies (simEnv (BI P hn host)) "zbytes_" [.val (tyV zt), .val c] v) :
    ∃ k, k < 2 ^ storageSize zt ∧ c = litV zt k ∧
      v = .list (FwdMem.leBytesV (storageSize zt / 8) k) := by
  have fin : ∀ k, k < 2 ^ storageSize zt → c = litV zt k →
      ∃ k, k < 2 ^ storageSize zt ∧ c = litV zt k ∧
        v = .list (FwdMem.leBytesV (storageSize zt / 8) k) := fun k hk hck => by
    subst hck
    exact ⟨k, hk, rfl, Applies.unique h (R4Fwd.applies_zbytes (R4Fwd.zB_builtins hn host) h0 hk)⟩
  match zt, h0, hz, h with
  | .val (.num t), _, _, h =>
    have hb := Simd.applies_noClause_iff (R4Fwd.findDef_zbytes _) h
    rw [show (simEnv (BI P hn host)).builtins = BI P hn host from rfl, call_zbytes] at hb
    have hz' : ZBytes.zbytesCall (tyV (Ty.val (Ty.num t) : CStorageType)) c =
        FwdMem.nbytesCall (Vec.numTypeV t) c := by
      rcases t with t | t <;> cases t <;> rfl
    rw [hz'] at hb
    cases hd : Floats.decNum t c with
    | none => simp [FwdMem.nbytesCall, Floats.decNumType_numTypeV, hd] at hb
    | some b =>
      refine fin b.toNat (by simp only [storageSize]; exact b.isLt) ?_
      rw [← decNum_eq_some hd]
      simp [litV]
  | .val (.vec .v128), _, hz, _ =>
    obtain ⟨k, rfl, hk⟩ := lit_vec_inv hz hc
    exact fin k (by simpa [storageSize] using hk) rfl
  | .pack p, _, hz, _ =>
    obtain ⟨k, rfl, hk⟩ := lit_pack_inv hz hc
    exact fin k (by simpa [storageSize] using hk) rfl

/-- **A slice of bytes that encodes `k` is what `readField?` reads.** -/
theorem readField_of_slice {zt : CStorageType} {bytes : ByteArray} {j k : Nat} {v : Value}
    (h0 : 0 < storageSize zt) (hk : k < 2 ^ storageSize zt)
    (hs : Value.slice? (.list (FwdMem.bytesV bytes)) j (storageSize zt / 8) = some v)
    (hv : v = .list (FwdMem.leBytesV (storageSize zt / 8) k)) :
    readField? zt bytes j = some (fieldOfLit zt k) := by
  have h8 := R4Fwd.storageSize_div8 zt h0
  cases zt with
  | val t =>
    cases t with
    | num t =>
      have hk' : k < 2 ^ t.width := hk
      obtain ⟨c, hl, hc⟩ := load_of_slice (k := t.width / 8) (n := k)
        (by rw [show 8 * (t.width / 8) = t.width from h8]; exact hk') hs hv
      show Option.map _ (Execution.Memory.load bytes j (t.width / 8)) = _
      rw [hl]
      refine congrArg some (congrArg (fun b => Val.num ⟨t, b⟩) (BitVec.eq_of_toNat_eq ?_))
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hc]
    | vec v =>
      cases v
      have hk' : k < 2 ^ 128 := hk
      obtain ⟨c, hl, hc⟩ := load_of_slice (k := 16) (n := k) hk' hs hv
      show Option.map _ (Execution.Memory.load bytes j 16) = _
      rw [hl]
      refine congrArg some (congrArg Val.vec (BitVec.eq_of_toNat_eq ?_))
      rw [BitVec.toNat_ofNat, hc, Nat.mod_eq_of_lt hk']
    | refv r => simp [storageSize] at h0
    | botv => simp [storageSize] at h0
  | pack p =>
    have hk' : k < 2 ^ p.width := hk
    obtain ⟨c, hl, hc⟩ := load_of_slice (k := p.width / 8) (n := k)
      (by rw [show 8 * (p.width / 8) = p.width from h8]; exact hk') hs hv
    show Option.map _ (Execution.Memory.load bytes j (p.width / 8)) = _
    rw [hl]
    refine congrArg some (congrArg Val.i32 (BitVec.eq_of_toNat_eq ?_))
    have h32 : k < 2 ^ 32 := lt_of_lt_of_le hk'
      (Nat.pow_le_pow_right (by decide) (by cases p <;> decide))
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hc]

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
