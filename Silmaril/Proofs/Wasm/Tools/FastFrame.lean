module

public import Silmaril.Wasm.Tools.FastFrame.Defs
public import Silmaril.Wasm.Tools.Framing.Thms

/-!
# `FastFrame`: proofs

Proofs for `Silmaril.Wasm.Tools.FastFrame.Thms`, which restates the theorems other modules use
(see there for what they state).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.FastFrame

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools Silmaril.Wasm.Tools.Framing Silmaril.Wasm.Tools.FastFrame

/-! ## Windows -/

theorem length_data_toList (b : ByteArray) : b.data.toList.length = b.size := by
  simp

theorem win_all (b : ByteArray) : win b 0 b.size = b.data.toList := by
  unfold win
  rw [List.take_of_length_le (by simp)]
  rfl

theorem win_cons {b : ByteArray} {i e : Nat} (hi : i < e) (he : e ≤ b.size) :
    win b i e = b[i]'(by omega) :: win b (i + 1) e := by
  have hl : i < (b.data.toList.take e).length := by
    simp; omega
  rw [win, List.drop_eq_getElem_cons hl]
  simp [win, ByteArray.getElem_eq_getElem_data]

theorem win_nil {b : ByteArray} {i e : Nat} (h : e ≤ i) : win b i e = [] := by
  simp only [win]
  apply List.drop_eq_nil_of_le
  simp; omega

theorem win_length {b : ByteArray} {i e : Nat} (he : e ≤ b.size) : (win b i e).length = e - i := by
  simp [win]; omega

theorem win_take (b : ByteArray) (i e k : Nat) : (win b i e).take k = win b i (min (i + k) e) := by
  simp only [win, List.take_drop, List.take_take]

theorem win_drop (b : ByteArray) (i e k : Nat) : (win b i e).drop k = win b (i + k) e := by
  simp [win, List.drop_drop]

theorem winC_eq (b : ByteArray) (i e : Nat) : winC b i e = win b i e := by
  simp only [winC, win, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_take]

theorem extract_eq_mk (b : ByteArray) (i e : Nat) : b.extract i e = ⟨(win b i e).toArray⟩ := by
  have h : (b.extract i e).data = (win b i e).toArray := by
    apply Array.toList_inj.mp
    have := winC_eq b i e
    simp only [winC] at this
    simpa using this
  rw [← h]

/-! ## LEB128 -/

theorem readUNAt_bounds {b : ByteArray} {e : Nat} (N i : Nat) {v j : Nat}
    (h : readUNAt b e N i = some (v, j)) : i < j ∧ j ≤ e := by
  rw [readUNAt] at h
  split at h
  · rename_i hi
    simp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · cases h
    · split at h
      · split at h
        · rename_i m j' hr
          have := readUNAt_bounds (N - 7) (i + 1) hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega
        · cases h
      · cases h
  · cases h
termination_by e - i
decreasing_by omega

theorem readUN_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) (N i : Nat) :
    readUN N (win b i e) =
      (readUNAt b e N i).map (fun p => (p.1, win b i p.2, win b p.2 e)) := by
  by_cases hi : i < e
  · rw [win_cons hi he, readUNAt, dite_eq_left_of_eq_true (eq_true ⟨hi, by omega⟩)]
    simp only [readUN]
    by_cases h1 : (b[i]'(by omega)).toNat < 2 ^ 7
    · by_cases h2 : (b[i]'(by omega)).toNat < 2 ^ N
      · simp [h1, h2, win_cons (Nat.lt_succ_self i) (show i + 1 ≤ b.size by omega),
          win_nil (Nat.le_refl (i + 1))]
      · simp [h1, h2]
    · by_cases h7 : 7 < N
      · simp only [h1, h7, ↓reduceIte, readUN_win he (N - 7) (i + 1)]
        cases hr : readUNAt b e (N - 7) (i + 1) with
        | none => simp
        | some p =>
          obtain ⟨m, j⟩ := p
          have hb := readUNAt_bounds (N - 7) (i + 1) hr
          simp [win_cons (show i < j by omega) (show j ≤ b.size by omega)]
      · simp [h1, h7]
  · rw [win_nil (by omega), readUNAt, dite_eq_right_of_eq_false (eq_false (by omega))]
    simp [readUN]
termination_by e - i
decreasing_by omega

/-! ## Sections -/

theorem splitAt_ok {b : ByteArray} {e : Nat} :
    ∀ (fuel i : Nat) {vs : List View}, splitAt b e fuel i = some vs → ∀ v ∈ vs, View.ok e v
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
          · obtain ⟨vs', hs', rfl⟩ := Option.map_eq_some_iff.mp h
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact ⟨by simp; omega, by simp, by simp; omega⟩
            · exact splitAt_ok fuel' (j + len) hs' v hv
          · cases h
    · simp only [Option.some.injEq] at h
      subst h
      simp

theorem atLeast_win {b : ByteArray} {j e : Nat} (he : e ≤ b.size) (hj : j ≤ e) (len : Nat) :
    atLeast len (win b j e) = decide (j + len ≤ e) := by
  rw [Bool.eq_iff_iff, atLeast_iff, win_length he]
  simp; omega

theorem splitSecsF_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) :
    ∀ (fuel i : Nat), splitSecsF fuel (win b i e) = (splitAt b e fuel i).map (List.map (View.raw b))
  | fuel, i => by
    by_cases hi : i < e
    · rw [win_cons hi he, splitAt, dite_eq_left_of_eq_true (eq_true ⟨hi, by omega⟩)]
      cases fuel with
      | zero => simp [splitSecsF]
      | succ f =>
        simp only [splitSecsF, readU32, readUN_win he 32 (i + 1)]
        cases hr : readUNAt b e 32 (i + 1) with
        | none => simp
        | some p =>
          obtain ⟨len, j⟩ := p
          have hb := readUNAt_bounds 32 (i + 1) hr
          simp only [Option.map_some, atLeast_win he hb.2]
          by_cases hl : j + len ≤ e
          · simp only [hl, decide_true, ↓reduceIte, win_take, win_drop, splitSecsF_win he f (j + len),
              Option.map_map]
            have hm : min (j + len) e = j + len := by omega
            rw [hm]
            cases splitAt b e f (j + len) <;> simp [View.raw]
          · simp [hl]
    · rw [win_nil (by omega), splitAt, dite_eq_right_of_eq_false (eq_false (by omega))]
      cases fuel <;> rfl

/-! ## Names and counts -/

theorem customName_win {b : ByteArray} {i e : Nat} (he : e ≤ b.size) :
    customName (win b i e) = customNameAt b i e := by
  simp only [customName, readName, readU32, readUN_win he 32 i, customNameAt]
  rcases hr : readUNAt b e 32 i with _ | ⟨len, j⟩
  · rfl
  have hb : i < j ∧ j ≤ e := readUNAt_bounds 32 i hr
  simp only [Option.map_some, atLeast_win he hb.2]
  by_cases h1 : len > 100000
  · simp [h1]
  by_cases hl : j + len ≤ e
  · have hm : min (j + len) e = j + len := by omega
    simp only [h1, ↓reduceIte, hl, decide_true, Bool.not_true, Bool.false_eq_true,
      not_true_eq_false, win_take, hm, extract_eq_mk, win_drop]
    cases String.fromUTF8? ⟨(win b j (j + len)).toArray⟩ with
    | none => rfl
    | some str =>
      simp only [bind, Except.bind, pure, Except.pure, win_length he]
      congr 2
      omega
  · simp [h1, hl]

theorem secCount_win {b : ByteArray} {i e : Nat} (he : e ≤ b.size) :
    secCount (win b i e) = secCountAt b i e := by
  simp only [secCount, readU32, readUN_win he 32 i, secCountAt]
  cases readUNAt b e 32 i <;> rfl

/-! ## The parser's checks -/

theorem Inside.tail {b : ByteArray} {v : View} {vs : List View} (h : Inside b (v :: vs)) :
    Inside b vs := fun w hw => h w (List.mem_cons_of_mem _ hw)

/-- A loop over mapped elements with pointwise equal bodies. -/
theorem forIn_map_congr {α β : Type} {ε : Type} (vs : List α) (r : α → β)
    (f : β → PUnit → Except ε (ForInStep PUnit)) (g : α → PUnit → Except ε (ForInStep PUnit))
    (h : ∀ v ∈ vs, ∀ u, f (r v) u = g v u) (u : PUnit) :
    forIn (vs.map r) u f = forIn vs u g := by
  induction vs generalizing u with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.forIn_cons, h v List.mem_cons_self]
    congr 1
    funext x
    cases x with
    | done _ => rfl
    | yield u' => exact ih (fun w hw u => h w (List.mem_cons_of_mem _ hw) u) u'

theorem checkIds_win (b : ByteArray) (vs : List View) :
    checkIds (vs.map (View.raw b)) = checkIdsAt b vs := by
  simp only [checkIds, checkIdsAt]
  congr 1
  apply forIn_map_congr
  intro v _ u
  simp only [View.raw, winC_eq, win_take]
  rfl

theorem step_win {b : ByteArray} {v : View} (h : v.cend ≤ b.size) (st : ModState) :
    ModState.step st (v.raw b) = stepAt b st v := by
  simp only [ModState.step, stepAt, View.raw, customName_win h, secCount_win h, winC_eq]
  rfl

theorem checkModule_win {b : ByteArray} : ∀ {vs : List View}, Inside b vs →
    ∀ st : ModState, (vs.map (View.raw b)).foldlM ModState.step st = vs.foldlM (stepAt b) st
  | [], _, _ => rfl
  | v :: vs, h, st => by
    simp only [List.map_cons, List.foldlM_cons, step_win (h v List.mem_cons_self).2]
    cases stepAt b st v with
    | error _ => rfl
    | ok st' => exact checkModule_win (Inside.tail h) st'

theorem checkComponentSec_win {b : ByteArray} {v : View} (h : v.cstart ≤ v.cend ∧ v.cend ≤ b.size) :
    checkComponentSec (v.raw b) = checkComponentSecAt b v := by
  simp only [checkComponentSec, checkComponentSecAt, View.raw, customName_win h.2,
    secCount_win h.2, winC_eq, win_length h.2]
  rfl

theorem checkComponent_win {b : ByteArray} {vs : List View} (h : Inside b vs) :
    checkComponent (vs.map (View.raw b)) = checkComponentAt b vs := by
  have hf : (vs.map (View.raw b)).filter (·.id == 9) = (vs.filter (·.id == 9)).map (View.raw b) := by
    rw [List.filter_map]; rfl
  have hl : ((vs.map (View.raw b)).filter (·.id == 9)).length = (vs.filter (·.id == 9)).length := by
    rw [hf, List.length_map]
  simp only [checkComponent, checkComponentAt, hl]
  congr 1
  apply forIn_map_congr
  intro v hv u
  rw [checkComponentSec_win (h v hv)]

theorem checkSecs_win {b : ByteArray} {vs : List View} (h : Inside b vs) (e : Enc) :
    checkSecs e (vs.map (View.raw b)) = checkSecsAt b e vs := by
  cases e <;> simp only [checkSecs, checkSecsAt, checkIds_win b vs, checkModule, checkModuleAt,
    checkModule_win h, checkComponent_win h]

/-! ## The preamble and `frame` -/

theorem readHeader_rest {expect : Option Enc} {l : Bytes} {enc : Enc} {r : Bytes}
    (h : readHeader expect l = .ok (enc, r)) : r = l.drop 8 := by
  unfold readHeader at h
  by_cases h1 : l.take 4 = magic <;> by_cases h2 : atLeast 8 l <;>
    by_cases h3 : (l.drop 4).take 4 = [1, 0, 0, 0] <;>
    by_cases h4 : (l.drop 4).take 4 = [0x0d, 0, 1, 0] <;>
    by_cases h5 : expect = some .component <;> by_cases h6 : expect = some .module <;>
    simp_all

theorem readHeader_take (expect : Option Enc) (l : Bytes) :
    (readHeader expect (l.take 8)).map Prod.fst = (readHeader expect l).map Prod.fst := by
  have h4 : (l.take 8).take 4 = l.take 4 := by simp [List.take_take]
  have hv : ((l.take 8).drop 4).take 4 = (l.drop 4).take 4 := by
    simp [List.drop_take, List.take_take]
  have h8 : atLeast 8 (l.take 8) = atLeast 8 l := by
    rw [Bool.eq_iff_iff, atLeast_iff, atLeast_iff, List.length_take]; omega
  simp only [readHeader, h4, hv, h8]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- `readHeader` decides on the first eight bytes and leaves the rest. -/
theorem readHeader_eq_take (expect : Option Enc) (l : Bytes) :
    readHeader expect l = (readHeader expect (l.take 8)).map (fun p => (p.1, l.drop 8)) := by
  have key : (readHeader expect (l.take 8)).map Prod.fst = (readHeader expect l).map Prod.fst :=
    readHeader_take expect l
  rcases h : readHeader expect l with m | ⟨enc, r⟩ <;>
    rcases h' : readHeader expect (l.take 8) with m' | ⟨enc', r'⟩ <;>
    simp only [h, h', Except.map, Except.ok.injEq, Except.error.injEq, reduceCtorEq] at key ⊢
  · exact key.symm
  · rw [readHeader_rest h, key]

theorem readHeader_win (b : ByteArray) (e : Nat) (expect : Option Enc) (i : Nat) :
    readHeader expect (win b i e) =
      (readHeaderAt b expect i e).map (fun p => (p.1, win b p.2 e)) := by
  have ht : winC b i (min (i + 8) e) = (win b i e).take 8 := by rw [winC_eq, win_take]
  rw [readHeader_eq_take]
  unfold readHeaderAt
  rw [ht]
  cases readHeader expect ((win b i e).take 8) <;> simp [Except.map, win_drop]

/-- **`frame` on a window is `frameAt`** (with the views read back as sections). -/
theorem frame_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) (expect : Option Enc) (i : Nat) :
    frame expect (win b i e) =
      (frameAt b expect i e).map (fun p => (p.1, p.2.map (View.raw b))) := by
  simp only [frame, frameAt, readHeader_win]
  cases readHeaderAt b expect i e with
  | error m => rfl
  | ok p =>
    obtain ⟨enc, j⟩ := p
    simp only [Except.map, bind, Except.bind, splitSecs, win_length he, splitSecsF_win he]
    cases hs : splitAt b e (e - j) j with
    | none => rfl
    | some vs =>
      have hin : Inside b vs := fun v hv =>
        let h := splitAt_ok _ _ hs v hv
        ⟨h.2.1, by have := h.2.2; omega⟩
      simp only [Option.map_some, checkSecs_win hin]
      cases checkSecsAt b enc vs <;> rfl

/-- **`frame` of a whole binary is `frameAt` on the array.** -/
theorem frame_eq_frameAt (b : ByteArray) (expect : Option Enc) :
    frame expect b.data.toList =
      (frameAt b expect 0 b.size).map (fun p => (p.1, p.2.map (View.raw b))) := by
  rw [← win_all, frame_win (Nat.le_refl _)]

end Silmaril.Proofs.Wasm.Tools.FastFrame
