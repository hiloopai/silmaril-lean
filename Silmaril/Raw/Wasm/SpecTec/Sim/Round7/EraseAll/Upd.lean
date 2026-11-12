module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Basic

/-!
# Round 7, the whole-evaluator erasure: updates along `updOk` paths keep the swap set (unrefined)

`updSafe_of_shape : QShape Q → UpdSafe Q env`. In a successful `pathSet` along a path whose last
field step is not a field of `moduleinst` (`updOk`), no write changes a field of a record of `Q`:

* the last field step cannot (`updOk`);
* an earlier field step `.a` at a record of `Q` is followed by another field step, whose prefix
  must be a record (`pathSet_write_struct`); but below `.a` there are only `Flat` values and lists
  of them (`pathGet_ext_flat`), so it is not.

A write into a record without an `EXPORTS` field keeps the swap set (`Swap.AllIn.setField`), and a
write of an absent field changes nothing (`Value.setField` maps over the fields).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Roots (IsWrite)

variable {Q : Value → Prop} {env : Env} {ρ : VarEnv}

/-- `q` is `b` followed by index and slice steps only. -/
inductive Ext (b : Path) : Path → Prop where
  | refl : Ext b b
  | idx {q : Path} {e : Exp} : Ext b q → Ext b (.idxP q e)
  | slice {q : Path} {e₁ e₂ : Exp} : Ext b q → Ext b (.sliceP q e₁ e₂)

theorem lastAtom_ext {q p : Path} {a : AtomS} (h : Ext (.dotP q a) p) : lastAtom? p = some a := by
  induction h with
  | refl => rfl
  | idx _ ih => exact ih
  | slice _ ih => exact ih

theorem isWrite_cases {q : Path} {a : AtomS} {p : Path} (h : IsWrite q a p) :
    Ext (.dotP q a) p ∨ ∃ q' b, IsWrite q' b p ∧ Ext (.dotP q a) q' := by
  induction h with
  | here => exact .inl .refl
  | idx _ ih =>
    rcases ih with h | ⟨q', b, hw, he⟩
    · exact .inl (.idx h)
    · exact .inr ⟨q', b, .idx hw, he⟩
  | slice _ ih =>
    rcases ih with h | ⟨q', b, hw, he⟩
    · exact .inl (.slice h)
    · exact .inr ⟨q', b, .slice hw, he⟩
  | @dot p b _ ih =>
    rcases ih with h | ⟨q', b', hw, he⟩
    · exact .inr ⟨p, b, .here, h⟩
    · exact .inr ⟨q', b', .dot hw, he⟩

theorem isWrite_ne_exports {q : Path} {a : AtomS} {p : Path} (h : IsWrite q a p)
    (hd : dotsOk p = true) : a ≠ "EXPORTS" := by
  induction h with
  | here =>
    simp only [dotsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    exact hd.1
  | idx _ ih => exact ih (by simpa [dotsOk] using hd)
  | slice _ ih => exact ih (by simpa [dotsOk] using hd)
  | dot _ ih =>
    simp only [dotsOk, Bool.and_eq_true] at hd
    exact ih hd.2

theorem pathGet_det {v : Value} {p : Path} {m₁ m₂ : Nat} {x y : Value}
    (h₁ : pathGet m₁ env ρ v p = .ok x) (h₂ : pathGet m₂ env ρ v p = .ok y) : x = y := by
  rcases Nat.le_total m₁ m₂ with h | h
  · have := Res.Le.ok ((monoAt_of_le h).pathGet env ρ v p) h₁
    rw [h₂] at this
    exact (Except.ok.inj this).symm
  · have := Res.Le.ok ((monoAt_of_le h).pathGet env ρ v p) h₂
    rw [h₁] at this
    exact Except.ok.inj this

theorem pathGet_allIn {v : Value} (hv : AllIn Q v) :
    ∀ (p : Path) (m : Nat) (x : Value), pathGet m env ρ v p = .ok x → AllIn Q x
  | _, 0, _, h => by simp [pathGet] at h
  | .rootP, _ + 1, x, h => by simp only [pathGet, Except.ok.injEq] at h; exact h ▸ hv
  | .idxP p e, m + 1, x, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u, hu, _, _, _, _, hx⟩ := h
    exact (pathGet_allIn hv p m u hu).idx? hx
  | .sliceP p e₁ e₂, m + 1, x, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u, hu, _, _, _, _, _, _, _, _, hx⟩ := h
    exact (pathGet_allIn hv p m u hu).slice? hx
  | .dotP p a, m + 1, x, h => by
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u, hu, hx⟩ := h
    exact (pathGet_allIn hv p m u hu).field? hx

theorem setField_isSome {u w : Value} {a : AtomS} {u' : Value} (h : u.setField a w = some u') :
    ∃ gs, u = .struct gs := by
  cases u with
  | struct gs => exact ⟨gs, rfl⟩
  | opt o => cases o <;> simp [Value.setField] at h
  | _ => simp [Value.setField] at h

/-- **Each field write of a successful update writes into a record.** -/
theorem pathSet_write_struct {v : Value} :
    ∀ (p : Path) (m : Nat) (w u : Value), pathSet m env ρ v p w = .ok u →
      ∀ q a, IsWrite q a p → ∃ m' gs, pathGet m' env ρ v q = .ok (.struct gs)
  | _, 0, _, _, h, _, _, _ => by simp [pathSet] at h
  | .rootP, _ + 1, _, _, _, _, _, hw => by cases hw
  | .idxP p e, m + 1, w, u, h, q, a, hw => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, u', _, hs⟩ := h
    cases hw with
    | idx hw => exact pathSet_write_struct p m u' u hs q a hw
  | .sliceP p e₁ e₂, m + 1, w, u, h, q, a, hw => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, u', _, hs⟩ := h
    cases hw with
    | slice hw => exact pathSet_write_struct p m u' u hs q a hw
  | .dotP p b, m + 1, w, u, h, q, a, hw => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨r, hr, u', hu', hs⟩ := h
    cases hw with
    | here =>
      obtain ⟨gs, rfl⟩ := setField_isSome hu'
      exact ⟨m, gs, hr⟩
    | dot hw => exact pathSet_write_struct p m u' u hs q a hw

/-- A list of `Flat` values, or a `Flat` value. -/
def FlatL (x : Value) : Prop := (∃ us, x = .list us ∧ ∀ u ∈ us, Flat u) ∨ Flat x

theorem FlatL.not_struct {x : Value} (h : FlatL x) (gs : List (AtomS × Value)) : x ≠ .struct gs := by
  rcases h with ⟨us, rfl, _⟩ | h
  · simp
  · exact h.1 gs

/-- **Below a field, only index and slice steps**: what they read is `FlatL` if the field is. -/
theorem pathGet_ext_flat {v : Value} {q : Path} {a : AtomS} :
    ∀ {q' : Path}, Ext (.dotP q a) q' → ∀ m x, pathGet m env ρ v q' = .ok x →
      ∃ m₀ r fa, pathGet m₀ env ρ v q = .ok r ∧ r.field? a = some fa ∧ (FlatL fa → FlatL x) := by
  intro q' he
  induction he with
  | refl =>
    intro m x h
    rcases m with _ | m
    · simp [pathGet] at h
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨r, hr, hx⟩ := h
    exact ⟨m, r, x, hr, hx, id⟩
  | @idx q₁ e _ ih =>
    intro m x h
    rcases m with _ | m
    · simp [pathGet] at h
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u, hu, _, _, i, _, hx⟩ := h
    obtain ⟨m₀, r, fa, hr, hfa, hf⟩ := ih m u hu
    refine ⟨m₀, r, fa, hr, hfa, fun hfl => ?_⟩
    rcases hf hfl with ⟨us, rfl, hus⟩ | hu'
    · exact .inr (hus x (List.mem_of_getElem? hx))
    · cases u with
      | list l => exact absurd rfl (hu'.2 l)
      | _ => simp [Value.idx?] at hx
  | @slice q₁ e₁ e₂ _ ih =>
    intro m x h
    rcases m with _ | m
    · simp [pathGet] at h
    simp only [pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨u, hu, _, _, _, _, i, _, k, _, hx⟩ := h
    obtain ⟨m₀, r, fa, hr, hfa, hf⟩ := ih m u hu
    refine ⟨m₀, r, fa, hr, hfa, fun hfl => ?_⟩
    rcases hf hfl with ⟨us, rfl, hus⟩ | hu'
    · simp only [Value.slice?] at hx
      split at hx
      · cases hx
        exact .inl ⟨_, rfl, fun y hy => hus y (List.mem_of_mem_drop (List.mem_of_mem_take hy))⟩
      · cases hx
    · cases u with
      | list l => exact absurd rfl (hu'.2 l)
      | _ => simp [Value.slice?] at hx

theorem field?_mem {gs : List (AtomS × Value)} {a : AtomS} {fa : Value}
    (h : (Value.struct gs).field? a = some fa) : ∃ p ∈ gs, p.1 = a ∧ p.2 = fa := by
  simp only [Value.field?_struct, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

/-- **No write of a successful update along an `updOk` path changes a field of a `Q`-record.** -/
theorem noModWrite (hQ : QShape Q) {v : Value} (hv : AllIn Q v) {p : Path} (hd : dotsOk p = true)
    (hu : updOk p = true) {m : Nat} {w u : Value} (h : pathSet m env ρ v p w = .ok u) :
    ∀ q a, IsWrite q a p → ∀ m' gs, pathGet m' env ρ v q = .ok (.struct gs) → hasExp gs = true →
      ∀ x, (a, x) ∉ gs := by
  intro q a hw m' gs hg he x hx
  have hA : AllIn Q (.struct gs) := pathGet_allIn hv q m' _ hg
  obtain ⟨gs', hgs', hshape⟩ := hQ _ (hA.1 he)
  cases hgs'
  have ha : a ∈ Roots.modAtoms := (hshape (a, x) hx).1
  rcases isWrite_cases hw with hext | ⟨q', b, hw', hext⟩
  · have hl := lastAtom_ext hext
    simp only [updOk, hl] at hu
    simp [ha] at hu
  · obtain ⟨m'', gs'', hg''⟩ := pathSet_write_struct p m w u h q' b hw'
    obtain ⟨m₀, r, fa, hr, hfa, hf⟩ := pathGet_ext_flat hext m'' _ hg''
    have hrr : r = .struct gs := pathGet_det hr hg
    subst hrr
    obtain ⟨p', hp', hpa, hpf⟩ := field?_mem hfa
    have hne : a ≠ "EXPORTS" := isWrite_ne_exports hw hd
    obtain ⟨us, hus, hflat⟩ := (hshape p' hp').2 (hpa ▸ hne)
    exact (hf (.inl ⟨us, hpf ▸ hus, hflat⟩)).not_struct gs'' rfl

theorem setField_absent {gs : List (AtomS × Value)} {a : AtomS} (h : ∀ x, (a, x) ∉ gs) (w : Value) :
    (gs.map fun f => if f.1 = a then (f.1, w) else f) = gs := by
  conv => rhs; rw [← List.map_id gs]
  refine List.map_congr_left fun f hf => ?_
  have : f.1 ≠ a := fun he => h f.2 (by rw [← he]; exact hf)
  simp [this]

/-- **Writes that change no field of a `Q`-record keep the swap set.** -/
theorem allIn_pathSet_of {v : Value} (hv : AllIn Q v) :
    ∀ (p : Path) (m : Nat) (w u : Value), AllIn Q w →
      (∀ q a, IsWrite q a p → ∀ m' gs, pathGet m' env ρ v q = .ok (.struct gs) →
        hasExp gs = true → ∀ x, (a, x) ∉ gs) →
      pathSet m env ρ v p w = .ok u → AllIn Q u
  | _, 0, _, _, _, _, h => by simp [pathSet] at h
  | .rootP, _ + 1, w, u, hw, _, h => by
    simp only [pathSet, Except.ok.injEq] at h; exact h ▸ hw
  | .idxP p e, m + 1, w, u, hw, hH, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨r, hr, _, _, _, _, u', hu', hs⟩ := h
    exact allIn_pathSet_of hv p m u' u ((pathGet_allIn hv p m r hr).setIdx hw hu')
      (fun q a hq => hH q a (.idx hq)) hs
  | .sliceP p e₁ e₂, m + 1, w, u, hw, hH, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨r, hr, _, _, _, _, _, _, _, _, u', hu', hs⟩ := h
    exact allIn_pathSet_of hv p m u' u ((pathGet_allIn hv p m r hr).setSlice hw hu')
      (fun q a hq => hH q a (.slice hq)) hs
  | .dotP p a, m + 1, w, u, hw, hH, h => by
    simp only [pathSet, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨r, hr, u', hu', hs⟩ := h
    have hrA := pathGet_allIn hv p m r hr
    obtain ⟨gs, rfl⟩ := setField_isSome hu'
    have hu'A : AllIn Q u' := by
      cases he : hasExp gs with
      | false => exact hrA.setField he hw hu'
      | true =>
        simp only [Value.setField_struct, Option.some.injEq] at hu'
        subst hu'
        rw [setField_absent (hH p a .here m gs hr he) w]
        exact hrA
    exact allIn_pathSet_of hv p m u' u hu'A (fun q a' hq => hH q a' (.dot hq)) hs

/-- **Updates along `updOk` paths keep the swap set**, for `Q` shaped like module instances. -/
theorem updSafe_of_shape (hQ : QShape Q) : UpdSafe Q env := by
  intro m ρ v p w u hd hu hv hw h
  exact allIn_pathSet_of hv p m w u hw (noModWrite hQ hv hd hu h) h

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
