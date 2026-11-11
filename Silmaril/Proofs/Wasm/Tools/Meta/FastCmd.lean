module

public import Silmaril.Proofs.Wasm.Tools.Meta.FastWalk
public import Silmaril.Wasm.Tools.Meta.FastCmd.Defs

/-!
# Proofs: `demangleB` computes `demangle`

Restated in `Silmaril.Wasm.Tools.Meta.FastCmd.Thms`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta Silmaril.Wasm.Tools.Meta.Demangle

/-! ## Appending to arrays -/

theorem ewc_data (n : Nat) : (ByteArray.emptyWithCapacity n).data = #[] := by
  unfold ByteArray.emptyWithCapacity; rfl

theorem appendList_data (out : ByteArray) : ∀ l : List UInt8,
    (appendList out l).data.toList = out.data.toList ++ l
  | [] => by simp [appendList]
  | x :: l => by
    have := appendList_data (out.push x) l
    simp only [appendList, List.foldl_cons] at this ⊢
    rw [this]; simp [ByteArray.data_push]

theorem appendSlice_data (out ba : ByteArray) (a b : Nat) (hab : a ≤ b) :
    (appendSlice out ba a b).data.toList = out.data.toList ++ sl ba a b := by
  unfold appendSlice
  rw [ByteArray.copySlice_eq_append]
  have h1 : out.extract 0 out.size = out := ByteArray.extract_zero_size
  have h2 : out.extract (out.size + min (b - a) (ba.data.size - a)) out.data.size = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]
    have : out.data.size = out.size := by cases out; rfl
    omega
  rw [h1, h2, show a + (b - a) = b by omega]
  simp only [ByteArray.toList_data_append, sl, toList_eq]
  simp

theorem pushRawSec_data (out : ByteArray) (id : UInt8) (ba : ByteArray) (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ ba.size) :
    (pushRawSec out id ba a b).data.toList = out.data.toList ++ rawSec id (sl ba a b) := by
  unfold pushRawSec
  rw [appendSlice_data _ _ _ _ hab, appendList_data]
  simp [ByteArray.data_push, rawSec, sl_length ba a b hb]

/-! ## The items of a module lie inside the input -/

/-- Every section a walk reports ends inside the input, after its start. -/
def ItemB.inside (lim : Nat) : ItemB → Prop
  | .sec s => s.bodyAt ≤ s.bodyEnd ∧ s.bodyEnd ≤ lim
  | .nest _ _ a b _ _ => a ≤ b ∧ b ≤ lim

theorem secs_inside (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat) (v : List ItemB),
      lim ≤ ba.size → parseSecsHB ba hk f enc st pos lim none = .ok v → ∀ it ∈ v, ItemB.inside lim it
  | 0, _, _, _, _, _, _, h => by simp [parseSecsHB] at h
  | f + 1, enc, st, pos, lim, v, hl, h => by
    have h0 := h
    unfold parseSecsHB at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h; · cases h
      cases h; simp
    · rename_i hend
      split at h; · cases h
      split at h; · cases h
      split at h; · cases h
      rename_i _ r hr
      rcases r with ⟨len, a⟩
      have hal := rdU32_le ba lim (pos + 1) len a hr hl
      have hb := first_sec_le ba hk f enc st pos lim len a v hl (by omega) hr h0
      dsimp only at h
      split at h
      · -- nested
        split at h; · cases h
        split at h; · cases h
        split at h; · cases h
        rename_i _ is hs
        cases h
        intro it hit
        rcases List.mem_cons.mp hit with rfl | hit
        · exact ⟨by omega, hb⟩
        · exact secs_inside ba hk f enc st _ lim is hl hs it hit
      · split at h
        · -- code
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          split at h; · cases h
          rename_i _ is hs
          cases h
          intro it hit
          rcases List.mem_cons.mp hit with rfl | hit
          · exact ⟨by simp, hb⟩
          · exact secs_inside ba hk f enc _ _ lim is hl hs it hit
        · -- other sections
          split at h; · cases h
          split at h <;>
          · split at h; · cases h
            split at h
            · split at h; · cases h
              split at h; · cases h
              rename_i _ is hs
              cases h
              intro it hit
              rcases List.mem_cons.mp hit with rfl | hit
              · exact ⟨by simp, hb⟩
              · exact secs_inside ba hk f _ _ _ lim is hl hs it hit
            · split at h; · cases h
              rename_i _ is hs
              cases h
              intro it hit
              rcases List.mem_cons.mp hit with rfl | hit
              · exact ⟨by simp, hb⟩
              · exact secs_inside ba hk f _ _ _ lim is hl hs it hit

/-- The items of a successful walk lie inside the input. -/
theorem parseBinaryB_inside (ba : ByteArray) (enc : Enc) (items : List ItemB)
    (h : parseBinaryB ba = .ok (enc, items)) : ∀ it ∈ items, ItemB.inside ba.size it := by
  unfold parseBinaryB parseBinaryHB parseUnitHB at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hh : readHeaderB ba none ba.size 0 with
  | error _ => simp [hh] at h
  | ok r =>
    rcases r with ⟨en, p⟩
    simp only [hh] at h
    cases hs : parseSecsHB ba noHook (ba.size + 1) en {} p ba.size none with
    | error _ => simp [hs] at h
    | ok is =>
      simp only [hs, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact secs_inside ba noHook _ en {} p ba.size is (Nat.le_refl _) hs

/-! ## `demangle` -/

theorem demangleSecBody_raw (body : List UInt8)
    (h : (∃ e, customOf body = .error e) ∨ (∃ nm data, customOf body = .ok (nm, data) ∧ nm ≠ nameName)) :
    demangleSecBody 0 body = rawSec 0 body := by
  unfold demangleSecBody
  rcases h with ⟨e, he⟩ | ⟨nm, data, he, hn⟩
  · simp [he]
  · simp [he, hn]

/-- Copying a custom section for `demangle`: a `name` section is demangled, any other custom
section is copied raw. -/
theorem pushDemangleSec_custom (ba out : ByteArray) (s : SecB) (hs : ItemB.inside ba.size (.sec s))
    (hid : s.id = 0) :
    (pushDemangleSec ba out s).data.toList = out.data.toList ++ demangleItem (.sec (s.toSec ba)) := by
  obtain ⟨h1, h2⟩ := hs
  have hraw := pushRawSec_data out s.id ba s.bodyAt s.bodyEnd h1 h2
  have hc := customOf_ag ba s.bodyAt s.bodyEnd h2
  simp only [demangleItem, SecB.toSec]
  unfold pushDemangleSec
  simp only [hid, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hraw ⊢
  cases hcb : customOfB ba s.bodyAt s.bodyEnd with
  | error e =>
    obtain ⟨e', he'⟩ := hc.err e hcb
    rw [hraw, demangleSecBody_raw _ (Or.inl ⟨e', he'⟩)]
  | ok r =>
    rcases r with ⟨ns, ne⟩
    have he' := hc.ok_iff (ns, ne) hcb
    by_cases hn : sl ba ns ne = nameName
    · simp only [hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [appendList_data]
    · have : (sl ba ns ne != nameName) = true := by simpa [bne] using hn
      simp only [this, ↓reduceIte]
      rw [hraw, demangleSecBody_raw _ (Or.inr ⟨_, _, he', hn⟩)]

theorem pushDemangleSec_data (ba out : ByteArray) (s : SecB) (hs : ItemB.inside ba.size (.sec s)) :
    (pushDemangleSec ba out s).data.toList = out.data.toList ++ demangleItem (.sec (s.toSec ba)) := by
  by_cases hid : s.id = 0
  · exact pushDemangleSec_custom ba out s hs hid
  obtain ⟨h1, h2⟩ := hs
  have hraw := pushRawSec_data out s.id ba s.bodyAt s.bodyEnd h1 h2
  have hne : (s.id != 0) = true := by simpa [bne] using hid
  simp only [demangleItem, SecB.toSec]
  unfold pushDemangleSec
  simp only [hne, ↓reduceIte, hraw]
  unfold demangleSecBody
  simp [hne]

theorem demangle_fold (ba : ByteArray) : ∀ (items : List ItemB) (out : ByteArray),
    (∀ it ∈ items, ItemB.inside ba.size it) →
    (items.foldl (fun out it =>
        match it with
        | .sec s => pushDemangleSec ba out s
        | .nest id _ _ _ _ _ => appendList out (rawSec id [])) out).data.toList =
      out.data.toList ++ (items.map (ItemB.toItem ba)).flatMap demangleItem
  | [], out, _ => by simp
  | it :: items, out, hin => by
    simp only [List.foldl_cons, List.map_cons, List.flatMap_cons]
    rw [demangle_fold ba items _ (fun x hx => hin x (List.mem_cons_of_mem _ hx))]
    cases it with
    | sec s =>
      rw [pushDemangleSec_data ba out s (hin _ List.mem_cons_self), toItem_sec]
      simp
    | nest id sa a b enc its =>
      rw [appendList_data, toItem_nest]
      simp [demangleItem]

/-- After the preamble check, `demangle` and `demangleB` parse and copy alike. -/
theorem demangle_parse_ag (ba : ByteArray) :
    (match parseBinary ba.data.toList with
      | .error e => .error e
      | .ok (_, items) => .ok (Enc.module.header ++ items.flatMap demangleItem) :
        Except String (List UInt8)).toOption =
    (match parseBinaryB ba with
      | .error e => .error e.render
      | .ok (_, items) =>
        .ok (items.foldl (fun out it =>
          match it with
          | .sec s => pushDemangleSec ba out s
          | .nest id _ _ _ _ _ => appendList out (rawSec id []))
          (appendList (ByteArray.emptyWithCapacity (ba.size + 256)) Enc.module.header)) :
        Except String ByteArray).toOption.map (·.data.toList) := by
  have hp := parseBinaryB_spec_raw ba
  cases hfp : parseBinaryB ba with
  | error _ =>
    rw [hfp] at hp
    cases hsp : parseBinary ba.data.toList <;> simp_all [Except.toOption]
  | ok r =>
    rcases r with ⟨enc, items⟩
    rw [hfp] at hp
    cases hsp : parseBinary ba.data.toList with
    | error _ => rw [hsp] at hp; simp [Except.toOption] at hp
    | ok x =>
      rw [hsp] at hp
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at hp
      subst hp
      simp only [Except.toOption, Option.map_some, Option.some.injEq]
      have hf := demangle_fold ba items (appendList (ByteArray.emptyWithCapacity (ba.size + 256))
        Enc.module.header) (parseBinaryB_inside ba enc items hfp)
      rw [appendList_data] at hf
      exact (hf.trans (by simp [ewc_data])).symm

theorem sl_all (ba : ByteArray) : sl ba 0 ba.size = ba.data.toList := by
  rw [sl_eq, List.drop_zero, Nat.sub_zero, ← length_data, List.take_length]

/-- A preamble the array reader accepts, the list reader accepts too. -/
theorem readHeader_of_readHeaderB {ba : ByteArray} {en : Enc} {p : Nat}
    (hfh : readHeaderB ba none ba.size 0 = .ok (en, p)) :
    readHeader none ba.data.toList = .ok (en, sl ba p ba.size) := by
  have hh := readHeader_sl ba none ba.size 0 (Nat.le_refl _)
  rw [sl_all] at hh
  cases hr : readHeader none ba.data.toList with
  | ok x => rw [hr, hfh] at hh; simp [Except.toOption] at hh; rw [hh]
  | error _ => rw [hr, hfh] at hh; simp [Except.toOption] at hh

/-- A preamble the array reader rejects, the list reader rejects too. -/
theorem readHeader_err_of_readHeaderB {ba : ByteArray} {e : FErr}
    (hfh : readHeaderB ba none ba.size 0 = .error e) :
    ∃ e', readHeader none ba.data.toList = .error e' := by
  have hh := readHeader_sl ba none ba.size 0 (Nat.le_refl _)
  rw [sl_all] at hh
  cases hr : readHeader none ba.data.toList with
  | ok x => rw [hr, hfh] at hh; simp [Except.toOption] at hh
  | error e' => exact ⟨e', rfl⟩

/-- **`demangleB` computes `demangle`.** -/
theorem demangleB_spec_raw (ba : ByteArray) :
    (demangle ba.data.toList).toOption = (demangleB ba).toOption.map (·.data.toList) := by
  unfold demangleB demangle
  cases hfh : readHeaderB ba none ba.size 0 with
  | ok r =>
    rcases r with ⟨en, p⟩
    rw [readHeader_of_readHeaderB hfh]
    cases en with
    | component => simp [Except.toOption]
    | module => exact demangle_parse_ag ba
  | error e =>
    obtain ⟨e', he'⟩ := readHeader_err_of_readHeaderB hfh
    rw [he']
    exact demangle_parse_ag ba

end Silmaril.Proofs.Wasm.Tools.Meta

end
