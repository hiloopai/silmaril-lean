module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsPaths

/-!
# Proofs (unrefined): `read-via-stream` of the filesystem extension

`wp_rvs`: the export `read-via-stream(d, off)` keeps the invariant: the 0.3 theory makes the new
readable end `k` deliver `(F d).drop off`, the 0.2 theory makes the new input stream deliver the
same bytes, and older live streams on `k` are marked not live (`rdInv_rvs`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step rdShaped rdStepZ)

variable {F : BitVec 32 → List (BitVec 8)}

/-! ## The theories on `read-via-stream` -/

theorem cliOk_rvs (r : Option (List Val)) : cliOk fdReadStream r = handleResOk r := by
  rw [cliOk_eq_hand]
  unfold cliOkH
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]

theorem fsOk_rvs (a : List Val) (r : Option (List Val)) : fsOk (.imp fdReadStream a r) = true := by
  unfold fsOk
  dsimp only
  repeat rw [ite_eq_right (by decide)]

theorem ioOp_rvs : ioOp fdReadStream = .other := by decide

theorem ioUpd_other (io : IoSt) (a : List Val) (r : Option (List Val)) : ioUpd io .other a r = io :=
  rfl

theorem rd2_rvs_err (q : RdSt) (a : List Val) : rd2Step F q (.imp fdReadStream a errFs) = some q := by
  unfold rd2Step
  dsimp only
  rw [ite_eq_left rfl]
  split
  · next h => simp [errFs, errV] at h
  · rfl

theorem rd2_rvs_ok (q : RdSt) (d : BitVec 32) (off : BitVec 64) (h : BitVec 32) :
    rd2Step F q (.imp fdReadStream [.u32 d, .u64 off] (some [okV (some (.u32 h))])) =
      some (setRest q h.toNat ((F d).drop off.toNat)) := by
  simp [rd2Step, okV]

theorem rd3_rvs {q q' : RdSt} {d : BitVec 32} {off : BitVec 64} {n : Option (List Val)}
    (h : (fsReadTh3w F).step q (.imp readVia3 [.u32 d, .u64 off] n) = some q') :
    ∃ rv fv k, n = some [.record [rv, fv]] ∧ natOf rv = some k ∧
      q' = setRest q k ((F d).drop off.toNat) := by
  have hs : rdStepZ F q (.imp readVia3 [.u32 d, .u64 off] n) = some q' := by
    have h0 : rdShaped (.imp readVia3 [.u32 d, .u64 off] n) = true := by simp [rdShaped]
    simpa [fsReadTh3w, h0] using h
  simp only [rdStepZ, ite_true] at hs
  split at hs
  · next _ _ d' off' rv fv heq =>
    simp only [List.cons.injEq, Val.u32.injEq, Val.u64.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split at hs
    · next k hk => exact ⟨rv, fv, k, rfl, hk, (Option.some.inj hs).symm⟩
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-! ## The invariant -/

theorem toNat_ne {h h' : BitVec 32} (hne : h' ≠ h) : h'.toNat ≠ h.toNat :=
  fun he => hne (BitVec.eq_of_toNat_eq he)

/-- **The invariant after `read-via-stream`.** -/
theorem rdInv_rvs {s s' : StF} {q2 q3 : RdSt} (hI : RdInv s q2 q3) {h : BitVec 32} {rv fv : Val}
    {k : Nat} (hk : natOf rv = some k) (v : List (BitVec 8))
    (hfs : s'.fs = fsUpd (poison s.fs k) h (some ⟨rv, fv, true⟩))
    (hcl : s'.io.closed = s.io.closed) (hh : s.io.closed h = false) :
    RdInv s' (setRest q2 h.toNat v) (setRest q3 k v) where
  known := fun h' hn => by
    rw [hfs]
    by_cases he : h' = h
    · simp [fsUpd, he]
    · rw [rest_setRest, ite_eq_right (toNat_ne he)] at hn
      have h0 := hI.known h' hn
      simp only [fsUpd, he, ite_false, poison]
      cases hx : s.fs h' with
      | none => exact absurd hx h0
      | some e => simp
  rel := fun h' e' bs he' hb => by
    rw [hfs] at he'
    rw [hcl]
    by_cases he : h' = h
    · subst he
      simp only [fsUpd, ite_true, Option.some.injEq] at he'
      subst he'
      rw [rest_setRest, ite_eq_left rfl] at hb
      cases hb
      exact ⟨fun _ => hh, fun _ => ⟨hh, k, hk, by rw [rest_setRest, ite_eq_left rfl]⟩⟩
    · rw [rest_setRest, ite_eq_right (toNat_ne he)] at hb
      simp only [fsUpd, he, ite_false, poison] at he'
      obtain ⟨e, he0, hee⟩ := Option.map_eq_some_iff.1 he'
      obtain ⟨hA, hB⟩ := hI.rel h' e bs he0 hb
      refine ⟨hA, fun hl => ?_⟩
      by_cases hek : natOf e.r = some k
      · rw [ite_eq_left hek] at hee; subst hee; exact absurd hl (by simp)
      · rw [ite_eq_right hek] at hee
        subst hee
        obtain ⟨hc, k0, hk0, hr⟩ := hB hl
        have hne : k0 ≠ k := fun h0 => hek (h0 ▸ hk0)
        exact ⟨hc, k0, hk0, by rw [rest_setRest, ite_eq_right hne]; exact hr⟩
  uniq := fun h1 h2 e1 e2 k' he1 he2 hl1 hl2 hk1 hk2 => by
    rw [hfs] at he1 he2
    -- a live entry other than `h` is an old live entry with an end other than `k`
    have old : ∀ x e', x ≠ h → fsUpd (poison s.fs k) h (some ⟨rv, fv, true⟩) x = some e' →
        e'.live = true → s.fs x = some e' ∧ natOf e'.r ≠ some k := fun x e' hx he hl => by
      simp only [fsUpd, hx, ite_false, poison] at he
      obtain ⟨e, he0, hee⟩ := Option.map_eq_some_iff.1 he
      by_cases hek : natOf e.r = some k
      · rw [ite_eq_left hek] at hee; subst hee; exact absurd hl (by simp)
      · rw [ite_eq_right hek] at hee; subst hee; exact ⟨he0, hek⟩
    have new : ∀ e', fsUpd (poison s.fs k) h (some ⟨rv, fv, true⟩) h = some e' → natOf e'.r = some k :=
      fun e' he => by simp only [fsUpd, ite_true, Option.some.injEq] at he; subst he; exact hk
    by_cases h1h : h1 = h <;> by_cases h2h : h2 = h
    · rw [h1h, h2h]
    · subst h1h
      obtain ⟨-, hne⟩ := old h2 e2 h2h he2 hl2
      have hkk : k' = k := Option.some.inj (hk1.symm.trans (new e1 he1))
      exact absurd (hkk ▸ hk2) hne
    · subst h2h
      obtain ⟨-, hne⟩ := old h1 e1 h1h he1 hl1
      have hkk : k' = k := Option.some.inj (hk2.symm.trans (new e2 he2))
      exact absurd (hkk ▸ hk1) hne
    · obtain ⟨he1', -⟩ := old h1 e1 h1h he1 hl1
      obtain ⟨he2', -⟩ := old h2 e2 h2h he2 hl2
      exact hI.uniq h1 h2 e1 e2 k' he1' he2' hl1 hl2 hk1 hk2
  keyed := fun h' e' he' hl => by
    rw [hfs] at he'
    by_cases he : h' = h
    · subst he
      simp only [fsUpd, ite_true, Option.some.injEq] at he'
      subst he'
      exact ⟨k, hk⟩
    · simp only [fsUpd, he, ite_false, poison] at he'
      obtain ⟨e, he0, hee⟩ := Option.map_eq_some_iff.1 he'
      by_cases hek : natOf e.r = some k
      · rw [ite_eq_left hek] at hee; subst hee; exact absurd hl (by simp)
      · rw [ite_eq_right hek] at hee; subst hee; exact hI.keyed h' e he0 hl

/-! ## The export call -/

theorem good_rvs_err {s : StF} {a : List Val} {q2 : RdSt} : Good F s fdReadStream a q2 errFs where
  ans := by rw [ioOp_rvs]; rfl
  p2 := by simp only [p2Ok, ioOp_rvs, ite_true, cliOk_rvs]; rfl
  fs := fsOk_rvs a _
  rd := ⟨q2, rd2_rvs_err q2 a, fun _ => rfl⟩
  closed := fun h hc => by
    rcases ioUpd_closed hc with hc | ⟨-, hst, -⟩
    · exact .inl hc
    · rw [ioOp_rvs] at hst; exact absurd hst (by decide)

/-- **`read-via-stream` keeps the invariant.** -/
theorem wp_rvs {s : StF} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) :
    Wp (t3F F) (rvsP s a) (PostF F s fdReadStream a g q2) qT := by
  have hn : fdReadStream ≠ clockNow := by decide
  have herr : Wp (t3F F) (.pure (s.impl, s.fs, errFs)) (PostF F s fdReadStream a g q2) qT :=
    wp_noread hn hJ (p := .pure (s.impl, s.fs, errFs)) ⟨shrinks_refl _, good_rvs_err⟩
  obtain ⟨-, hclk, hI⟩ := hJ
  unfold rvsP
  split
  · next d off =>
    dsimp only
    split
    · exact herr
    · next hh =>
      have hh' : s.io.closed s.impl.fresh.2 = false := by simpa using hh
      intro n qT' hstep
      obtain ⟨h1, h2⟩ := t3_step (qC := qT.1) (q3 := qT.2) (qC' := qT'.1) (q3' := qT'.2) hstep
      obtain ⟨rv, fv, k, rfl, hk, hq3⟩ := rd3_rvs h2
      show Wp (t3F F) (match natOf rv with
          | some k => .pure (s.impl.fresh.1, fsUpd (poison s.fs k) s.impl.fresh.2 (some ⟨rv, fv, true⟩),
              some [okV (some (.u32 s.impl.fresh.2))])
          | none => .pure (s.impl, s.fs, errFs)) _ _
      rw [hk]
      have hgood_ans : ansOk .loose s.io (ioOp fdReadStream) [.u32 d, .u64 off]
          (some [okV (some (.u32 s.impl.fresh.2))]) = true := by rw [ioOp_rvs]; rfl
      have hp2 : p2Ok (.imp fdReadStream [.u32 d, .u64 off] (some [okV (some (.u32 s.impl.fresh.2))])) =
          true := by simp only [p2Ok, ioOp_rvs, ite_true, cliOk_rvs]; rfl
      refine ⟨_, p2F_step s.io g q2 _ hgood_ans hp2 (fsOk_rvs _ _) hn (rd2_rvs_ok q2 d off _), rfl,
        clkLe_step hclk h1, ?_⟩
      rw [hq3]
      refine rdInv_rvs hI hk _ rfl ?_ hh'
      show (ioUpd s.io (ioOp fdReadStream) [.u32 d, .u64 off]
        (some [okV (some (.u32 s.impl.fresh.2))])).closed = s.io.closed
      rw [ioOp_rvs, ioUpd_other]
  · exact herr

end Silmaril.Wasi.Versions.P2OverP3
