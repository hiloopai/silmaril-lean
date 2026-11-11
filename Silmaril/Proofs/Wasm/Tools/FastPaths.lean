module

public import Silmaril.Wasm.Tools.FastPaths.Defs
public import Silmaril.Wasm.Tools.FastFrame.Thms

/-!
# `FastPaths`: proofs

Proofs for `Silmaril.Wasm.Tools.FastPaths.Thms` (see there for what they state).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.FastPaths

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing Silmaril.Wasm.Tools.FastFrame Silmaril.Wasm.Tools.Features
open Silmaril.Wasm.Tools Silmaril.Wasm.Tools.FastPaths

/-! ## Views of a frame -/

theorem readHeaderAt_index {b : ByteArray} {ex : Option Enc} {i e : Nat} {enc : Enc} {j : Nat}
    (h : readHeaderAt b ex i e = .ok (enc, j)) : j = i + 8 := by
  unfold readHeaderAt at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · cases h

theorem frameAt_split {b : ByteArray} {ex : Option Enc} {i e : Nat} {enc : Enc}
    {vs : List View} (h : frameAt b ex i e = .ok (enc, vs)) :
    splitAt b e (e - (i + 8)) (i + 8) = some vs := by
  unfold frameAt at h
  cases hh : readHeaderAt b ex i e with
  | error m => rw [hh] at h; cases h
  | ok p =>
    obtain ⟨enc', j⟩ := p
    have hj := readHeaderAt_index hh
    subst hj
    rw [hh] at h
    simp only [bind, Except.bind] at h
    cases hs : splitAt b e (e - (i + 8)) (i + 8) with
    | none => simp [hs] at h
    | some vs' =>
      cases hc : checkSecsAt b enc' vs' with
      | error m => simp [hs, hc] at h
      | ok u =>
        simp only [hs, hc, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ rfl

theorem frameAt_inside {b : ByteArray} {ex : Option Enc} {i e : Nat} {enc : Enc}
    {vs : List View} (h : frameAt b ex i e = .ok (enc, vs)) (he : e ≤ b.size) : Inside b vs := by
  have hs := frameAt_split h
  intro v hv
  have := splitAt_ok _ _ hs v hv
  exact ⟨this.2.1, by have := this.2.2; omega⟩

/-! ## `validate` -/

theorem binGates_eq (F : WFeatures) (b : ByteArray) :
    Validate.binGates F b.data.toList = binGatesAt F b := by
  have hw : b.data.toList.drop 8 = win b 8 b.size := by rw [← win_all, win_drop]
  simp only [Validate.binGates, binGatesAt, hw, splitSecs, win_length (Nat.le_refl _),
    splitSecsF_win (Nat.le_refl _)]
  split
  · rfl
  · cases splitAt b b.size (b.size - 8) 8 with
    | none => rfl
    | some vs =>
      simp only [Option.map_some, List.all_map, Function.comp_def, View.raw, winC_eq]

/-- **The fast validator is the validator.** -/
theorem checkFast_eq (F : WFeatures) (b : ByteArray) : checkFast F b = Validate.check F b := by
  simp only [checkFast, Validate.check, binGates_eq]
  rfl

/-! ## `strip` -/

theorem nestedEncV_eq (b : ByteArray) (e : Enc) (v : View) :
    nestedEncV e v = nestedEnc e (v.raw b) := by
  cases e <;> rfl

theorem keepAt_eq {b : ByteArray} (rm : String → Bool) {v : View} (h : v.cend ≤ b.size) :
    keepAt b rm v = Strip.keepSec rm (v.raw b) := by
  simp only [keepAt, Strip.keepSec, View.raw, customName_win h]
  rfl

theorem toList_mk (l : Bytes) : (ByteArray.mk l.toArray).data.toList = l := by simp

theorem toList_append (x y : ByteArray) : (x ++ y).data.toList = x.data.toList ++ y.data.toList := by
  simp [ByteArray.data_append]

theorem secBytes_toList (id : UInt8) (c : ByteArray) :
    (secBytes id c).data.toList = id :: (encUN c.data.toList.length ++ c.data.toList) := by
  simp only [secBytes, toList_append, length_data_toList]
  rfl

theorem extract_toList (b : ByteArray) (i e : Nat) : (b.extract i e).data.toList = win b i e :=
  winC_eq b i e

theorem stripAt_eq {b : ByteArray} (rm : String → Bool) :
    ∀ (fuel : Nat) (e : Enc) (vs : List View), Inside b vs →
      (stripAt b rm fuel e vs).map (·.data.toList) =
        (Strip.stripF rm fuel e (vs.map (View.raw b))).map join
  | _, _, [], _ => by simp [stripAt, Strip.stripF, Except.map, join]
  | fuel, e, v :: vs, h => by
    have ih := stripAt_eq rm fuel e vs h.tail
    have hv := h v List.mem_cons_self
    rw [stripAt, List.map_cons, Strip.stripF]
    cases hA : stripAt b rm fuel e vs with
    | error m =>
      cases hB : Strip.stripF rm fuel e (vs.map (View.raw b)) with
      | error m' =>
        rw [hA, hB] at ih
        simp only [Except.map, Except.error.injEq] at ih
        subst ih
        rfl
      | ok _ => rw [hA, hB] at ih; simp [Except.map] at ih
    | ok A =>
      cases hB : Strip.stripF rm fuel e (vs.map (View.raw b)) with
      | error m' => rw [hA, hB] at ih; simp [Except.map] at ih
      | ok B =>
        rw [hA, hB] at ih
        simp only [Except.map, Except.ok.injEq] at ih
        simp only [bind, Except.bind, keepAt_eq rm hv.2, ← nestedEncV_eq b]
        by_cases hk : Strip.keepSec rm (v.raw b) = true
        · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hn : nestedEncV e v with
          | none =>
            simp only [pure, Except.pure, Except.map, toList_append, secBytes_toList,
              extract_toList, ih, join, RawSec.bytes, RawSec.canon, View.raw, List.cons_append]
          | some e' =>
            cases fuel with
            | zero => rfl
            | succ fuel' =>
              simp only [View.raw]
              rw [frame_win hv.2]
              cases hF : frameAt b (some e') v.cstart v.cend with
              | error m => rfl
              | ok p =>
                obtain ⟨enc, inner⟩ := p
                have ih2 := stripAt_eq rm fuel' e' inner (frameAt_inside hF hv.2)
                simp only [Except.map]
                cases hI : stripAt b rm fuel' e' inner with
                | error m =>
                  cases hJ : Strip.stripF rm fuel' e' (inner.map (View.raw b)) with
                  | error m' =>
                    rw [hI, hJ] at ih2
                    simp only [Except.map, Except.error.injEq] at ih2
                    subst ih2
                    rfl
                  | ok _ => rw [hI, hJ] at ih2; simp [Except.map] at ih2
                | ok I =>
                  cases hJ : Strip.stripF rm fuel' e' (inner.map (View.raw b)) with
                  | error m' => rw [hI, hJ] at ih2; simp [Except.map] at ih2
                  | ok J =>
                    rw [hI, hJ] at ih2
                    simp only [Except.map, Except.ok.injEq] at ih2
                    simp only [pure, Except.pure, toList_append, secBytes_toList,
                      ih2, ih, join, RawSec.bytes, RawSec.canon, List.cons_append]
        · simp only [Bool.not_eq_true] at hk
          simp [hk, pure, Except.pure, Except.map, ih]
termination_by fuel _ vs => (fuel, vs.length)

/-- **The fast `strip` is `strip`.** -/
theorem stripFast_eq (rm : String → Bool) (b : ByteArray) :
    (stripFast rm b).map (·.data.toList) = Strip.strip rm b.data.toList := by
  simp only [stripFast, Strip.strip, frame_eq_frameAt, length_data_toList]
  cases hF : frameAt b none 0 b.size with
  | error m => rfl
  | ok p =>
    show (stripAt b rm b.size p.1 p.2 >>= fun out =>
        pure ({ data := p.1.header.toArray } ++ out)).map (·.data.toList) =
      Strip.stripF rm b.size p.1 (p.2.map (View.raw b)) >>= fun ss' => pure (p.1.header ++ join ss')
    obtain ⟨e, vs⟩ := p
    have ih : (stripAt b rm b.size e vs).map (·.data.toList) =
        (Strip.stripF rm b.size e (vs.map (View.raw b))).map join :=
      stripAt_eq rm b.size e vs (frameAt_inside hF (Nat.le_refl _))
    simp only [Except.map, bind, Except.bind]
    cases hA : stripAt b rm b.size e vs with
    | error m =>
      cases hB : Strip.stripF rm b.size e (vs.map (View.raw b)) with
      | error m' =>
        have hm : m = m' := by simpa only [hA, hB, Except.map, Except.error.injEq] using ih
        rw [hm]
      | ok _ => exact absurd ih (by simp [hA, hB, Except.map])
    | ok A =>
      cases hB : Strip.stripF rm b.size e (vs.map (View.raw b)) with
      | error m' => exact absurd ih (by simp [hA, hB, Except.map])
      | ok B =>
        have hAB : A.data.toList = join B := by
          simpa only [hA, hB, Except.map, Except.ok.injEq] using ih
        simp [pure, Except.pure, hAB]

/-! ## `objdump` -/

theorem offsets_split {b : ByteArray} {e : Nat} (he : e ≤ b.size) :
    ∀ (fuel i : Nat) {vs : List View}, splitAt b e fuel i = some vs →
      Objdump.offsets i (vs.map (View.raw b)) = vs.map (fun v => (v.raw b, v.cstart))
  | fuel, i, vs, h => by
    rw [splitAt] at h
    split at h
    · split at h
      · cases h
      · rename_i fuel'
        split at h
        · cases h
        · rename_i len j hr
          have hb := readUNAt_bounds 32 (i + 1) hr
          split at h
          · rename_i hl
            obtain ⟨vs', hs', rfl⟩ := Option.map_eq_some_iff.mp h
            have ih := offsets_split he fuel' (j + len) hs'
            have h1 : (win b (i + 1) j).length = j - (i + 1) := win_length (by omega)
            have h2 : (win b j (j + len)).length = j + len - j := win_length (by omega)
            have e1 : i + 1 + (j - (i + 1)) = j := by omega
            have e2 : i + (1 + (j - (i + 1)) + (j + len - j)) = j + len := by omega
            simp only [List.map_cons, Objdump.offsets, View.raw, h1, h2, e1, e2]
            simp only [View.raw] at ih
            rw [ih]
          · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl

theorem countAt_eq {b : ByteArray} (e : Enc) {v : View} (h : v.cend ≤ b.size) :
    Objdump.count e (v.raw b) = countAt b e v := by
  simp only [Objdump.count, countAt, View.raw, readU32, readUN_win h]
  cases readUNAt b v.cend 32 v.cstart <;> rfl

theorem linesAt_eq {b : ByteArray} :
    ∀ (fuel : Nat) (e : Enc) (vs : List View) (p : Objdump.Printer), Inside b vs →
      Objdump.lines.go fuel e (vs.map fun v => (v.raw b, v.cstart)) p = linesAt b fuel e vs p
  | _, _, [], _, _ => by simp [Objdump.lines.go, linesAt]
  | fuel, e, v :: vs, p, h => by
    have hv := h v List.mem_cons_self
    have ihr : ∀ p, Objdump.lines.go fuel e (vs.map fun v => (v.raw b, v.cstart)) p =
        linesAt b fuel e vs p := fun p => linesAt_eq fuel e vs p h.tail
    rw [List.map_cons, Objdump.lines.go, linesAt]
    simp only [ihr]
    have hc : (win b v.cstart v.cend).length = v.cend - v.cstart := win_length hv.2
    have hn : (v.raw b).content = win b v.cstart v.cend := rfl
    have hid : (v.raw b).id = v.id := rfl
    simp only [countAt_eq e hv.2, ← nestedEncV_eq b]
    simp only [hn, hc, hid, customName_win hv.2, frame_win hv.2]
    cases hN : nestedEncV e v with
    | none => rfl
    | some e' =>
      cases fuel with
      | zero => rfl
      | succ fuel' =>
        cases hF : frameAt b (some e') v.cstart v.cend with
        | error m =>
          simp only [hF, Except.map, bind, Except.bind]
          rfl
        | ok q =>
          obtain ⟨enc, inner⟩ := q
          have hin := frameAt_inside hF hv.2
          have hoff := offsets_split hv.2 _ _ (frameAt_split hF)
          have ih2 : ∀ p, Objdump.lines.go fuel' e' (inner.map fun v => (v.raw b, v.cstart)) p =
              linesAt b fuel' e' inner p := fun p => linesAt_eq fuel' e' inner p hin
          simp only [hF, Except.map, bind, Except.bind, hoff, ih2]
          rfl
termination_by fuel _ vs => (fuel, vs.length)

/-- **The fast `objdump` is `objdump`.** -/
theorem objdumpFast_eq (b : ByteArray) : objdumpFast b = Objdump.objdump b.data.toList := by
  simp only [objdumpFast, Objdump.objdump, frame_eq_frameAt, length_data_toList, Objdump.lines]
  cases hF : frameAt b none 0 b.size with
  | error m => rfl
  | ok q =>
    obtain ⟨e, vs⟩ := q
    have hoff := offsets_split (Nat.le_refl b.size) _ _ (frameAt_split hF)
    simp only [Nat.zero_add] at hoff
    simp only [Except.map, bind, Except.bind, hoff, linesAt_eq _ _ _ _ (frameAt_inside hF (Nat.le_refl _))]

end Silmaril.Proofs.Wasm.Tools.FastPaths
