module

public import Silmaril.Wasm.Auto.Equiv.Defs
public import Silmaril.Proofs.Wasm.Auto.Equiv.Basic

/-!
# The simplifier of extended terms preserves values

`evX_canon`, `evM_canonM`: `canon` and `canonM` (`Silmaril.Wasm.Auto.Equiv.Defs`) preserve the
values of value and memory terms, at every type, in every environment and initial memory;
`holds_canon`: simplified guards hold exactly when the guards do.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {ρ : Env} {B0 : ByteArray}

theorem evX_ofTerm (t : IntType) (e : Term) : evX ρ B0 t (ofTerm e) = Silmaril.Wasm.Auto.Equiv.ev ρ t e := by
  induction e generalizing t with
  | var n => rfl
  | const c => rfl
  | un op a ih => simp [ofTerm, evX, Silmaril.Wasm.Auto.Equiv.ev, ih]
  | bin op a b iha ihb => simp [ofTerm, evX, Silmaril.Wasm.Auto.Equiv.ev, iha, ihb]
  | rel t' op a b iha ihb => simp [ofTerm, evX, Silmaril.Wasm.Auto.Equiv.ev, iha, ihb]

theorem toTerm?_eq {e : XT} {e' : Term} (h : toTerm? e = some e') : e = ofTerm e' := by
  induction e generalizing e' with
  | var n => cases h; rfl
  | const c => cases h; rfl
  | un op a ih =>
    simp only [toTerm?, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp [ofTerm, ih ha]
  | bin op a b iha ihb =>
    simp only [toTerm?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp [ofTerm, iha ha, ihb hb]
  | rel t op a b iha ihb =>
    simp only [toTerm?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp [ofTerm, iha ha, ihb hb]
  | _ => cases h

theorem evX_pureNorm (t : IntType) (e : XT) : evX ρ B0 t (pureNorm t e) = evX ρ B0 t e := by
  unfold pureNorm
  split
  · rename_i e' he
    rw [toTerm?_eq he, evX_ofTerm, evX_ofTerm, Silmaril.Proofs.Wasm.Auto.Equiv.ev_norm]
  · rfl

theorem evX_mkSel (t : IntType) (c a b : XT) :
    evX ρ B0 t (mkSel c a b) = evX ρ B0 t (.sel c a b) := by
  unfold mkSel
  split
  · rename_i k
    show evX ρ B0 t (if k % 2 ^ 32 = 0 then b else a) =
      (if BitVec.ofNat 32 k ≠ 0 then evX ρ B0 t a else evX ρ B0 t b)
    by_cases hk : k % 2 ^ 32 = 0
    · have h0 : BitVec.ofNat 32 k = 0 := by apply BitVec.eq_of_toNat_eq; simpa using hk
      rw [ite_eq_left hk, h0]
      simp
    · have h0 : BitVec.ofNat 32 k ≠ 0 := fun h0 => hk (by
        have := congrArg BitVec.toNat h0
        simpa using this)
      rw [ite_eq_right hk, ite_eq_left h0]
  · split
    · rename_i hab
      subst hab
      simp [evX]
    · rfl

theorem setWidth_signExtend_32 (x : BitVec 32) : (x.signExtend 64).setWidth 32 = x := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi]
  omega

theorem evX_mkWrap (a : XT) : evX ρ B0 .i32 (mkWrap a) = evX ρ B0 .i32 (.wrap a) := by
  unfold mkWrap
  split
  · rename_i c
    show BitVec.ofNat 32 (c % 2 ^ 32) = (BitVec.ofNat 64 c).setWidth 32
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_mod_of_dvd]
  · rename_i sx b
    show evX ρ B0 .i32 b = (evX ρ B0 .i64 (.ext sx b)).setWidth 32
    cases sx
    · exact (setWidth_signExtend_32 _).symm
    · show evX ρ B0 .i32 b = ((evX ρ B0 .i32 b).setWidth 64).setWidth 32
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      exact (BitVec.setWidth_eq (x := evX ρ B0 .i32 b)).symm
  · rfl

theorem evX_mkExt (sx : Signedness) (a : XT) :
    evX ρ B0 .i64 (mkExt sx a) = evX ρ B0 .i64 (.ext sx a) := by
  unfold mkExt
  split
  · rename_i c
    cases sx
    · simp [evX, IntType.width]
    · apply BitVec.eq_of_toNat_eq
      simp [evX, IntType.width]
  · rfl

theorem evX_mkBin (t : IntType) (op : IntBinOp) (a b : XT) :
    evX ρ B0 t (mkBin op a b) = evX ρ B0 t (.bin op a b) := by
  unfold mkBin
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [evX]
    rcases op <;> simp [commOp] at h <;>
      simp [binV, intBinOp, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
        BitVec.xor_comm]
  · rfl

theorem evX_mkRel (t t' : IntType) (op : IntRelOp) (a b : XT) :
    evX ρ B0 t (mkRel t' op a b) = evX ρ B0 t (.rel t' op a b) := by
  unfold mkRel
  split
  · rename_i s; cases s <;> rfl
  · rename_i s; cases s <;> rfl
  · rfl

/-- **The simplifier preserves values.** -/
theorem evX_canon_and : ∀ e : XT,
    (∀ t, evX ρ B0 t (canon t e) = evX ρ B0 t e) ∧ evM ρ B0 (canonM e) = evM ρ B0 e
  | .var n => ⟨fun t => by simp [canon, evX_pureNorm], by simp [canonM]⟩
  | .const c => ⟨fun t => by simp [canon, evX_pureNorm], by simp [canonM]⟩
  | .un op a => by
    obtain ⟨iha, -⟩ := evX_canon_and a
    exact ⟨fun t => by simp [canon, evX_pureNorm, evX, iha], by simp [canonM]⟩
  | .bin op a b => by
    obtain ⟨iha, -⟩ := evX_canon_and a
    obtain ⟨ihb, -⟩ := evX_canon_and b
    exact ⟨fun t => by simp [canon, evX_pureNorm, evX_mkBin, evX, iha, ihb], by simp [canonM]⟩
  | .rel t' op a b => by
    obtain ⟨iha, -⟩ := evX_canon_and a
    obtain ⟨ihb, -⟩ := evX_canon_and b
    exact ⟨fun t => by simp [canon, evX_pureNorm, evX_mkRel, evX, iha, ihb], by simp [canonM]⟩
  | .wrap a => by
    obtain ⟨iha, -⟩ := evX_canon_and a
    refine ⟨fun t => ?_, by simp [canonM]⟩
    by_cases ht : t = .i32
    · subst ht
      simp [canon, evX_mkWrap, evX, iha]
    · simp [canon, ht, evX, iha]
  | .ext sx a => by
    obtain ⟨iha, -⟩ := evX_canon_and a
    refine ⟨fun t => ?_, by simp [canonM]⟩
    by_cases ht : t = .i64
    · subst ht
      rw [show canon .i64 (.ext sx a) = mkExt sx (canon .i32 a) by simp [canon], evX_mkExt]
      cases sx <;> simp [evX, iha]
    · rw [show canon t (.ext sx a) = .ext sx (canon .i32 a) by simp [canon, ht]]
      cases sx <;> simp [evX, iha]
  | .sel c a b => by
    obtain ⟨ihc, -⟩ := evX_canon_and c
    obtain ⟨iha, -⟩ := evX_canon_and a
    obtain ⟨ihb, -⟩ := evX_canon_and b
    exact ⟨fun t => by simp [canon, evX_mkSel, evX, ihc, iha, ihb], by simp [canonM]⟩
  | .load m t' p a arg => by
    obtain ⟨-, ihm⟩ := evX_canon_and m
    obtain ⟨iha, -⟩ := evX_canon_and a
    exact ⟨fun t => by simp [canon, evX, ihm, iha], by simp [canonM]⟩
  | .minit => ⟨fun t => by simp [canon, evX_pureNorm], by simp [canonM]⟩
  | .mstore m t' p a arg v => by
    obtain ⟨-, ihm⟩ := evX_canon_and m
    obtain ⟨iha, -⟩ := evX_canon_and a
    obtain ⟨ihv, -⟩ := evX_canon_and v
    exact ⟨fun t => by simp [canon, evX_pureNorm, evX], by simp [canonM, evM, ihm, iha, ihv]⟩

theorem evX_canon (t : IntType) (e : XT) : evX ρ B0 t (canon t e) = evX ρ B0 t e :=
  (evX_canon_and e).1 t

theorem evM_canonM (e : XT) : evM ρ B0 (canonM e) = evM ρ B0 e := (evX_canon_and e).2

theorem holds_canon (g : Guard) : g.canon.holds ρ B0 = g.holds ρ B0 := by
  cases g <;> simp [Guard.canon, Guard.holds, evX_canon]

end Silmaril.Proofs.Wasm.Auto.Equiv