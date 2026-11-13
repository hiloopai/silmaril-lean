module

public import Silmaril.Wasm.Tools.Component.DummyFast.Defs

/-!
# Bounded flattening agrees with full flattening

* `flatB_eq`, `flatKindB_eq`, `flatListB_eq`, `flatOptB_eq`: when wasm-jco's `flatR`
  (`flatKindR`, …) flattens a type to `l`, the bounded flattening with budget `lim` is
  `cut lim l` (`l` itself when at most `lim` long, else `none`);
* `liftCoreB_eq`, `lowerCoreB_eq`: hence the core signatures agree with `liftCoreR`,
  `lowerCoreR`;
* `dummyFast_eq`, `dummyOfPayloadFast_eq`: when `Dummy.dummy` (`Dummy.dummyOfPayload`)
  succeeds, `dummyFast` (`dummyOfPayloadFast`) gives the same module (bytes).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.DummyFast

open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (Ty Func TyDefKind DItem WorldFull IfaceName)
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Tools.Component.Dummy

/-! ## Lists, cuts and joins -/

theorem bind_eq_ok {α β : Type} {m : Except String α} {f : α → Except String β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem length_joinList : ∀ a b : List NumType, (joinList a b).length = max a.length b.length
  | _ :: as, _ :: bs => by
    have ih : (joinList as bs).length = max as.length bs.length := length_joinList as bs
    simp only [joinList, List.length_cons, ih, Nat.add_max_add_right]
  | [], bs => by simp only [joinList, List.length_nil, Nat.zero_max]
  | _ :: _, [] => by simp only [joinList, List.length_nil, Nat.max_zero]

theorem foldl_joinList_le : ∀ (fs : List (List NumType)) (acc : List NumType) (k : Nat),
    (fs.foldl joinList acc).length ≤ k ↔ acc.length ≤ k ∧ ∀ f ∈ fs, f.length ≤ k
  | [], acc, k => by simp only [List.foldl_nil, List.not_mem_nil, false_imp_iff, imp_true_iff,
      and_true]
  | f :: fs, acc, k => by
    have ih := foldl_joinList_le fs (joinList acc f) k
    rw [List.foldl_cons, ih, length_joinList, Nat.max_le]
    constructor
    · rintro ⟨⟨ha, hf⟩, hs⟩
      exact ⟨ha, fun g hg => (List.mem_cons.mp hg).elim (fun e => e ▸ hf) (hs g)⟩
    · rintro ⟨ha, hs⟩
      exact ⟨⟨ha, hs f List.mem_cons_self⟩, fun g hg => hs g (List.mem_cons_of_mem f hg)⟩

theorem allSome_map_cut : ∀ (fs : List (List NumType)) (k : Nat),
    allSome (fs.map (cut k)) = if ∀ f ∈ fs, f.length ≤ k then some fs else none
  | [], k => by simp only [List.map_nil, allSome, List.not_mem_nil, false_imp_iff,
      imp_true_iff, ite_true]
  | f :: fs, k => by
    have ih := allSome_map_cut fs k
    by_cases hf : f.length ≤ k
    · have hc : cut k f = some f := ite_eq_left hf
      rw [List.map_cons, hc, allSome, ih]
      by_cases hs : ∀ g ∈ fs, g.length ≤ k
      · have hall : ∀ g ∈ f :: fs, g.length ≤ k :=
          fun g hg => (List.mem_cons.mp hg).elim (fun e => e ▸ hf) (hs g)
        rw [ite_eq_left hs, ite_eq_left hall]
        rfl
      · have hall : ¬ ∀ g ∈ f :: fs, g.length ≤ k :=
          fun h => hs fun g hg => h g (List.mem_cons_of_mem f hg)
        rw [ite_eq_right hs, ite_eq_right hall]
        rfl
    · have hc : cut k f = none := ite_eq_right hf
      have hall : ¬ ∀ g ∈ f :: fs, g.length ≤ k := fun h => hf (h f List.mem_cons_self)
      rw [List.map_cons, hc, allSome, ite_eq_right hall]

theorem cut_cons_zero (a : NumType) (l : List NumType) : cut 0 (a :: l) = none := by
  unfold cut
  rw [ite_eq_right (by simp only [List.length_cons]; omega)]

theorem cut_cons {lim : Nat} (h : lim ≠ 0) (a : NumType) (l : List NumType) :
    (cut (lim - 1) l).map (a :: ·) = cut lim (a :: l) := by
  unfold cut
  by_cases hl : l.length ≤ lim - 1
  · have hl' : (a :: l).length ≤ lim := by simp only [List.length_cons]; omega
    rw [ite_eq_left hl, ite_eq_left hl']
    rfl
  · have hl' : ¬ (a :: l).length ≤ lim := by simp only [List.length_cons]; omega
    rw [ite_eq_right hl, ite_eq_right hl']
    rfl

theorem cut_append (lim : Nat) {a : List NumType} (ha : a.length ≤ lim) (b : List NumType) :
    (cut (lim - a.length) b).map (a ++ ·) = cut lim (a ++ b) := by
  unfold cut
  by_cases hb : b.length ≤ lim - a.length
  · have hab : (a ++ b).length ≤ lim := by simp only [List.length_append]; omega
    rw [ite_eq_left hb, ite_eq_left hab]
    rfl
  · have hab : ¬ (a ++ b).length ≤ lim := by simp only [List.length_append]; omega
    rw [ite_eq_right hb, ite_eq_right hab]
    rfl

theorem cut_append_none {lim : Nat} {a : List NumType} (ha : ¬ a.length ≤ lim)
    (b : List NumType) : cut lim (a ++ b) = none := by
  unfold cut
  rw [ite_eq_right (by simp only [List.length_append]; omega)]

theorem cut_eq_none {lim : Nat} {l : List NumType} (h : cut lim l = none) : ¬ l.length ≤ lim := by
  intro hl
  unfold cut at h
  rw [ite_eq_left hl] at h
  cases h

theorem cut_eq_some {lim : Nat} {l a : List NumType} (h : cut lim l = some a) :
    a = l ∧ l.length ≤ lim := by
  unfold cut at h
  by_cases hl : l.length ≤ lim
  · rw [ite_eq_left hl] at h
    exact ⟨(Option.some.inj h).symm, hl⟩
  · rw [ite_eq_right hl] at h
    cases h

theorem mapM_ok_map {α β γ : Type} {f : α → Except String β} {g : α → Except String γ}
    {k : β → γ} : ∀ (cs : List α) (fs : List β), cs.mapM f = .ok fs →
      (∀ c ∈ cs, ∀ x, f c = .ok x → g c = .ok (k x)) → cs.mapM g = .ok (fs.map k)
  | [], fs, h, _ => by
    have hfs : fs = [] := by
      rw [List.mapM_nil] at h
      exact (Except.ok.inj h).symm
    rw [hfs, List.mapM_nil]
    rfl
  | c :: cs, fs, h, hg => by
    rw [List.mapM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_eq_ok h
    obtain ⟨xs, hxs, h⟩ := bind_eq_ok h
    have hfs : fs = x :: xs := (Except.ok.inj h).symm
    have hc : g c = .ok (k x) := hg c List.mem_cons_self x hx
    have hcs : cs.mapM g = .ok (xs.map k) :=
      mapM_ok_map cs xs hxs fun c' hc' => hg c' (List.mem_cons_of_mem c hc')
    rw [hfs, List.mapM_cons, hc, hcs]
    rfl

/-! ## Flattening -/

section
variable (ρ : Resolver)

/-- Agreement of `flatB` with `flatR` at one fuel. -/
def RAgree (fuel : Nat) : Prop :=
  ∀ sc t l lim, flatR ρ fuel sc t = .ok l → flatB ρ fuel sc t lim = .ok (cut lim l)

/-- Agreement of `flatKindB` with `flatKindR` at one fuel. -/
def KAgree (fuel : Nat) : Prop :=
  ∀ sc k l lim, flatKindR ρ fuel sc k = .ok l → flatKindB ρ fuel sc k lim = .ok (cut lim l)

variable {ρ}

theorem flatOptB_of {fuel : Nat} (hR : RAgree ρ fuel) {sc : Scope} :
    ∀ (o : Option Ty) {l : List NumType} (lim : Nat), flatOptR ρ fuel sc o = .ok l →
      flatOptB ρ fuel sc o lim = .ok (cut lim l)
  | none, l, lim, h => by
    have hl : l = [] := by
      rw [flatOptR] at h
      exact (Except.ok.inj h).symm
    rw [hl, flatOptB]
    rfl
  | some t, _, lim, h => by
    rw [flatOptR] at h
    rw [flatOptB]
    exact hR sc t _ lim h

/-- The cons step of `flatListB_of`, given the claim for the tail. -/
theorem flatListB_cons {fuel : Nat} (hR : RAgree ρ fuel) {sc : Scope} (t : Ty) (ts : List Ty)
    (ih : ∀ {l : List NumType} (lim : Nat), flatListR ρ fuel sc ts = .ok l →
      flatListB ρ fuel sc ts lim = .ok (cut lim l))
    {l : List NumType} (lim : Nat) (h : flatListR ρ fuel sc (t :: ts) = .ok l) :
    flatListB ρ fuel sc (t :: ts) lim = .ok (cut lim l) := by
  rw [flatListR] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  have hl : l = a ++ b := (Except.ok.inj h).symm
  have hta : flatB ρ fuel sc t lim = .ok (cut lim a) := hR sc t a lim ha
  rw [flatListB, hta, hl]
  by_cases hal : a.length ≤ lim
  · show _ = Except.ok (cut lim (a ++ b))
    have hc : cut lim a = some a := ite_eq_left hal
    have hts : flatListB ρ fuel sc ts (lim - a.length) = .ok (cut (lim - a.length) b) :=
      ih (lim - a.length) hb
    rw [hc]
    show (flatListB ρ fuel sc ts (lim - a.length) >>= fun r => pure (r.map (a ++ ·))) = _
    rw [hts, ← cut_append lim hal b]
    rfl
  · have hc : cut lim a = none := ite_eq_right hal
    rw [hc, cut_append_none hal b]
    rfl

theorem flatListB_of {fuel : Nat} (hR : RAgree ρ fuel) {sc : Scope} :
    ∀ (ts : List Ty) {l : List NumType} (lim : Nat), flatListR ρ fuel sc ts = .ok l →
      flatListB ρ fuel sc ts lim = .ok (cut lim l)
  | [], l, lim, h => by
    have hl : l = [] := by
      rw [flatListR] at h
      exact (Except.ok.inj h).symm
    rw [hl, flatListB]
    rfl
  | t :: ts, _, lim, h => flatListB_cons hR t ts (fun lim' h' => flatListB_of hR ts lim' h') lim h

theorem flatB_option {fuel : Nat} (hR : RAgree ρ fuel) (sc : Scope) (t : Ty) {l : List NumType}
    (lim : Nat) (h : flatR ρ (fuel + 1) sc (.option t) = .ok l) :
    flatB ρ (fuel + 1) sc (.option t) lim = .ok (cut lim l) := by
  rw [flatR] at h
  obtain ⟨f, hf, h⟩ := bind_eq_ok h
  have hl : l = ti32 :: f := (Except.ok.inj h).symm
  rw [flatB, hl]
  by_cases h0 : lim = 0
  · rw [ite_eq_left h0, h0, cut_cons_zero]
    rfl
  · have ht : flatB ρ fuel sc t (lim - 1) = .ok (cut (lim - 1) f) := hR sc t f (lim - 1) hf
    rw [ite_eq_right h0]
    show (flatB ρ fuel sc t (lim - 1) >>= fun r => pure (r.map (ti32 :: ·))) = _
    rw [ht, ← cut_cons h0]
    rfl

theorem cut_result (lim : Nat) (a b : List NumType) (h : ¬ a.length ≤ lim - 1 ∨ ¬ b.length ≤ lim - 1) :
    cut lim (ti32 :: joinList a b) = none := by
  unfold cut
  have hj : (ti32 :: joinList a b).length = max a.length b.length + 1 := by
    rw [List.length_cons, length_joinList]
  rw [ite_eq_right (by rw [hj]; omega)]

theorem cut_result_some {lim : Nat} (h0 : lim ≠ 0) {a b : List NumType} (ha : a.length ≤ lim - 1)
    (hb : b.length ≤ lim - 1) : cut lim (ti32 :: joinList a b) = some (ti32 :: joinList a b) := by
  unfold cut
  have hj : (ti32 :: joinList a b).length = max a.length b.length + 1 := by
    rw [List.length_cons, length_joinList]
  rw [ite_eq_left (by rw [hj]; omega)]

theorem flatB_result {fuel : Nat} (hR : RAgree ρ fuel) (sc : Scope) (ok err : Option Ty)
    {l : List NumType} (lim : Nat) (h : flatR ρ (fuel + 1) sc (.result ok err) = .ok l) :
    flatB ρ (fuel + 1) sc (.result ok err) lim = .ok (cut lim l) := by
  rw [flatR] at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  have hl : l = ti32 :: joinList a b := (Except.ok.inj h).symm
  rw [flatB, hl]
  by_cases h0 : lim = 0
  · rw [ite_eq_left h0, h0, cut_cons_zero]
    rfl
  · show _ = Except.ok (cut lim (ti32 :: joinList a b))
    have hoa : flatOptB ρ fuel sc ok (lim - 1) = .ok (cut (lim - 1) a) :=
      flatOptB_of hR ok (lim - 1) ha
    have hob : flatOptB ρ fuel sc err (lim - 1) = .ok (cut (lim - 1) b) :=
      flatOptB_of hR err (lim - 1) hb
    rw [ite_eq_right h0, hoa]
    by_cases hal : a.length ≤ lim - 1
    · rw [show cut (lim - 1) a = some a from ite_eq_left hal]
      show (flatOptB ρ fuel sc err (lim - 1) >>= _) = _
      rw [hob]
      by_cases hbl : b.length ≤ lim - 1
      · rw [show cut (lim - 1) b = some b from ite_eq_left hbl, cut_result_some h0 hal hbl]
        rfl
      · rw [show cut (lim - 1) b = none from ite_eq_right hbl, cut_result lim a b (Or.inr hbl)]
        rfl
    · rw [show cut (lim - 1) a = none from ite_eq_right hal, cut_result lim a b (Or.inl hal)]
      rfl

theorem flatB_ref {fuel : Nat} (hK : KAgree ρ fuel) (sc : Scope) (r : Silmaril.Wasm.Wit.Binary.TyRef)
    {l : List NumType} (lim : Nat) (h : flatR ρ (fuel + 1) sc (.ref r) = .ok l) :
    flatB ρ (fuel + 1) sc (.ref r) lim = .ok (cut lim l) := by
  rw [flatR] at h
  obtain ⟨p, hp, h⟩ := bind_eq_ok h
  have hk : flatKindB ρ fuel p.1 p.2 lim = .ok (cut lim l) := hK p.1 p.2 l lim h
  rw [flatB]
  show (ρ sc r >>= fun p => flatKindB ρ fuel p.1 p.2 lim) = _
  rw [hp]
  exact hk

/-- One more unit of fuel for `flatB`. -/
theorem flatB_succ {fuel : Nat} (hR : RAgree ρ fuel) (hK : KAgree ρ fuel) :
    RAgree ρ (fuel + 1) := by
  intro sc t l lim h
  match t with
  | .prim p => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .list _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .map _ _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .stream _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .future _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .own _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .borrow _ => rw [flatR] at h; rw [flatB, ← Except.ok.inj h]; rfl
  | .option t => exact flatB_option hR sc t lim h
  | .result a b => exact flatB_result hR sc a b lim h
  | .tuple ts => rw [flatR] at h; rw [flatB]; exact flatListB_of hR ts lim h
  | .fixedList _ _ => rw [flatR] at h; cases h
  | .ref r => exact flatB_ref hK sc r lim h

theorem flatKindB_variant {fuel : Nat} (hR : RAgree ρ fuel) (sc : Scope)
    (cs : List (Silmaril.Wasm.Wit.Binary.Labeled (Option Ty))) {l : List NumType} (lim : Nat)
    (h : flatKindR ρ (fuel + 1) sc (.variant cs) = .ok l) :
    flatKindB ρ (fuel + 1) sc (.variant cs) lim = .ok (cut lim l) := by
  rw [flatKindR] at h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok h
  have hl : l = ti32 :: fs.foldl joinList [] := (Except.ok.inj h).symm
  rw [flatKindB, hl]
  by_cases h0 : lim = 0
  · rw [ite_eq_left h0, h0, cut_cons_zero]
    rfl
  · show _ = Except.ok (cut lim (ti32 :: fs.foldl joinList []))
    have hgs : cs.mapM (fun c => flatOptB ρ fuel sc c.ty (lim - 1)) =
        .ok (fs.map (cut (lim - 1))) :=
      mapM_ok_map cs fs hfs fun c _ x hx => flatOptB_of hR c.ty (lim - 1) hx
    have hlen : (ti32 :: fs.foldl joinList []).length ≤ lim ↔ ∀ f ∈ fs, f.length ≤ lim - 1 := by
      rw [List.length_cons, ← Nat.le_sub_iff_add_le (Nat.pos_of_ne_zero h0),
        foldl_joinList_le, List.length_nil]
      exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le _, h⟩⟩
    rw [ite_eq_right h0]
    show (cs.mapM (fun c => flatOptB ρ fuel sc c.ty (lim - 1)) >>= _) = _
    rw [hgs]
    show Except.ok ((allSome (fs.map (cut (lim - 1)))).map _) = _
    rw [allSome_map_cut]
    unfold cut
    by_cases hall : ∀ f ∈ fs, f.length ≤ lim - 1
    · rw [ite_eq_left hall, ite_eq_left (hlen.mpr hall)]
      rfl
    · rw [ite_eq_right hall, ite_eq_right (fun h => hall (hlen.mp h))]
      rfl

/-- One more unit of fuel for `flatKindB`. -/
theorem flatKindB_succ {fuel : Nat} (hR : RAgree ρ fuel) : KAgree ρ (fuel + 1) := by
  intro sc k l lim h
  match k with
  | .record fs => rw [flatKindR] at h; rw [flatKindB]; exact flatListB_of hR _ lim h
  | .variant cs => exact flatKindB_variant hR sc cs lim h
  | .enum _ => rw [flatKindR] at h; rw [flatKindB, ← Except.ok.inj h]; rfl
  | .flags _ => rw [flatKindR] at h; rw [flatKindB, ← Except.ok.inj h]; rfl
  | .resource => rw [flatKindR] at h; rw [flatKindB, ← Except.ok.inj h]; rfl
  | .type t => rw [flatKindR] at h; rw [flatKindB]; exact hR sc t l lim h

/-- **Bounded flattening is the cut of full flattening**, at every fuel. -/
theorem agree_all : ∀ fuel, RAgree ρ fuel ∧ KAgree ρ fuel
  | 0 => by
    have hR : RAgree ρ 0 := by
      intro _ _ _ _ h
      rw [flatR] at h
      cases h
    have hK : KAgree ρ 0 := by
      intro _ _ _ _ h
      rw [flatKindR] at h
      cases h
    exact ⟨hR, hK⟩
  | fuel + 1 =>
    have ih : RAgree ρ fuel ∧ KAgree ρ fuel := agree_all fuel
    ⟨flatB_succ ih.1 ih.2, flatKindB_succ ih.1⟩

theorem flatB_eq {fuel : Nat} {sc : Scope} {t : Ty} {l : List NumType} (lim : Nat)
    (h : flatR ρ fuel sc t = .ok l) : flatB ρ fuel sc t lim = .ok (cut lim l) :=
  (agree_all fuel).1 sc t l lim h

theorem flatKindB_eq {fuel : Nat} {sc : Scope} {k : TyDefKind} {l : List NumType} (lim : Nat)
    (h : flatKindR ρ fuel sc k = .ok l) : flatKindB ρ fuel sc k lim = .ok (cut lim l) :=
  (agree_all fuel).2 sc k l lim h

theorem flatListB_eq {fuel : Nat} {sc : Scope} {ts : List Ty} {l : List NumType} (lim : Nat)
    (h : flatListR ρ fuel sc ts = .ok l) : flatListB ρ fuel sc ts lim = .ok (cut lim l) :=
  flatListB_of (agree_all fuel).1 ts lim h

theorem flatOptB_eq {fuel : Nat} {sc : Scope} {o : Option Ty} {l : List NumType} (lim : Nat)
    (h : flatOptR ρ fuel sc o = .ok l) : flatOptB ρ fuel sc o lim = .ok (cut lim l) :=
  flatOptB_of (agree_all fuel).1 o lim h

theorem spillB_cut (lim : Nat) (l : List NumType) : spillB (cut lim l) = spill lim l := by
  unfold cut spill
  by_cases h : l.length ≤ lim
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- **`liftCoreB` is `liftCoreR`** where the latter succeeds. -/
theorem liftCoreB_eq {sc : Scope} {f : Silmaril.Wasm.Wit.Binary.Func} {t : CoreFuncTy} (h : liftCoreR ρ sc f = .ok t) :
    liftCoreB ρ sc f = .ok t := by
  unfold liftCoreR at h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok h
  obtain ⟨rs, hrs, h⟩ := bind_eq_ok h
  have hps' := flatListB_eq maxFlatParams hps
  have hrs' := flatOptB_eq maxFlatResults hrs
  unfold liftCoreB
  rw [hps']
  show (flatOptB ρ flatFuel sc f.result maxFlatResults >>= _) = _
  rw [hrs', ← Except.ok.inj h]
  show Except.ok (⟨spillB (cut maxFlatParams ps), spillB (cut maxFlatResults rs)⟩ : CoreFuncTy) = _
  rw [spillB_cut, spillB_cut]
  rfl

/-- **`lowerCoreB` is `lowerCoreR`** where the latter succeeds. -/
theorem lowerCoreB_eq {sc : Scope} {f : Silmaril.Wasm.Wit.Binary.Func} {t : CoreFuncTy} (h : lowerCoreR ρ sc f = .ok t) :
    lowerCoreB ρ sc f = .ok t := by
  unfold lowerCoreR at h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok h
  obtain ⟨rs, hrs, h⟩ := bind_eq_ok h
  have hps' := flatListB_eq maxFlatParams hps
  have hrs' := flatOptB_eq maxFlatResults hrs
  unfold lowerCoreB
  rw [hps']
  show (flatOptB ρ flatFuel sc f.result maxFlatResults >>= _) = _
  rw [hrs', spillB_cut]
  unfold cut
  by_cases hr : rs.length ≤ maxFlatResults
  · rw [ite_eq_left hr] at h ⊢
    exact h
  · rw [ite_eq_right hr] at h ⊢
    exact h

end

/-! ## The dummy module -/

section
variable {ρ : Resolver} {m : Mangling}

/-- The core import of one function of an imported interface. -/
theorem importFn_eq {k : IfaceName ⊕ String} {f : Silmaril.Wasm.Wit.Binary.Func} {x : String × String × CoreFuncTy}
    (h : (do noAsync f; pure (importModule m (some k), fname f, ← lowerCoreR ρ (.iface k) f) :
      Except String _) = .ok x) :
    (do noAsync f; pure (importModule m (some k), fname f, ← lowerCoreB ρ (.iface k) f) :
      Except String _) = .ok x := by
  obtain ⟨u, hu, h⟩ := bind_eq_ok h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  rw [hu]
  show (lowerCoreB ρ (.iface k) f >>= _) = _
  rw [lowerCoreB_eq ht]
  exact h

/-- **`importsOfB` is `importsOf`** where the latter succeeds. -/
theorem importsOfB_eq : ∀ (is : List DItem) {r : List (String × String × CoreFuncTy)},
    importsOf ρ m is = .ok r → importsOfB ρ m is = .ok r
  | [], _, h => by rw [importsOf] at h; rw [importsOfB]; exact h
  | .func f :: is, r, h => by
    rw [importsOf] at h
    obtain ⟨u, hu, h⟩ := bind_eq_ok h
    obtain ⟨t, ht, h⟩ := bind_eq_ok h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok h
    rw [importsOfB, hu]
    show (lowerCoreB ρ .world f >>= _) = _
    rw [lowerCoreB_eq ht]
    show (importsOfB ρ m is >>= _) = _
    rw [importsOfB_eq is hrest]
    exact h
  | .iface k b :: is, r, h => by
    rw [importsOf] at h
    obtain ⟨fs, hfs, h⟩ := bind_eq_ok h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok h
    have hfsB : b.funcs.mapM (fun f => (do noAsync f; pure (importModule m (some k), fname f,
        ← lowerCoreB ρ (.iface k) f) : Except String _)) = .ok (fs.map id) :=
      mapM_ok_map b.funcs fs hfs fun _ _ x hx => importFn_eq hx
    rw [List.map_id] at hfsB
    rw [importsOfB, hfsB]
    show (importsOfB ρ m is >>= _) = _
    rw [importsOfB_eq is hrest]
    exact h
  | .type t :: is, r, h => by
    rw [importsOf] at h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok h
    rw [importsOfB]
    show (importsOfB ρ m is >>= _) = _
    rw [importsOfB_eq is hrest]
    exact h

/-- **`exportFuncB` is `exportFunc`** where the latter succeeds. -/
theorem exportFuncB_eq {k : Option (IfaceName ⊕ String)} {f : Silmaril.Wasm.Wit.Binary.Func} {r : List DFunc}
    (h : exportFunc ρ m k f = .ok r) : exportFuncB ρ m k f = .ok r := by
  unfold exportFunc at h
  obtain ⟨u, hu, h⟩ := bind_eq_ok h
  unfold exportFuncB
  rw [hu]
  cases k with
  | none =>
    obtain ⟨t, ht, h⟩ := bind_eq_ok h
    show (liftCoreB ρ .world f >>= _) = _
    rw [liftCoreB_eq ht]
    exact h
  | some k =>
    obtain ⟨t, ht, h⟩ := bind_eq_ok h
    show (liftCoreB ρ (.iface k) f >>= _) = _
    rw [liftCoreB_eq ht]
    exact h

/-- **`funcsOfB` is `funcsOf`** where the latter succeeds. -/
theorem funcsOfB_eq : ∀ (es : List DItem) {r : List DFunc},
    funcsOf ρ m es = .ok r → funcsOfB ρ m es = .ok r
  | [], _, h => by rw [funcsOf] at h; rw [funcsOfB]; exact h
  | .func f :: es, r, h => by
    rw [funcsOf] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok h
    rw [funcsOfB, exportFuncB_eq ha]
    show (funcsOfB ρ m es >>= _) = _
    rw [funcsOfB_eq es hrest]
    exact h
  | .iface k b :: es, r, h => by
    rw [funcsOf] at h
    obtain ⟨fs, hfs, h⟩ := bind_eq_ok h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok h
    have hfsB : b.funcs.mapM (exportFuncB ρ m (some k)) = .ok (fs.map id) :=
      mapM_ok_map b.funcs fs hfs fun _ _ x hx => exportFuncB_eq hx
    rw [List.map_id] at hfsB
    rw [funcsOfB, hfsB]
    show (funcsOfB ρ m es >>= _) = _
    rw [funcsOfB_eq es hrest]
    exact h
  | .type _ :: es, r, h => by
    rw [funcsOf] at h
    rw [funcsOfB]
    exact funcsOfB_eq es h

/-- **`dummyFast` is `Dummy.dummy`** where the latter succeeds. -/
theorem dummyFast_eq {wf : WorldFull} {d : Silmaril.Wasm.Tools.Component.Dummy.Module} (h : dummy wf m = .ok d) :
    dummyFast wf m = .ok d := by
  unfold dummy at h
  obtain ⟨is, his, h⟩ := bind_eq_ok h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok h
  unfold dummyFast
  show (importsOfB (JcoTool.NewI.rho wf) m wf.imports >>= _) = _
  rw [importsOfB_eq _ his]
  show (funcsOfB (JcoTool.NewI.rho wf) m wf.exports >>= _) = _
  rw [funcsOfB_eq _ hfs]
  exact h

/-- **`dummyOfPayloadFast` is `Dummy.dummyOfPayload`** where the latter succeeds. -/
theorem dummyOfPayloadFast_eq {pl out : ByteArray} (h : dummyOfPayload pl m = .ok out) :
    dummyOfPayloadFast pl m = .ok out := by
  unfold dummyOfPayload at h
  obtain ⟨wf, hwf, h⟩ := bind_eq_ok h
  obtain ⟨d, hd, h⟩ := bind_eq_ok h
  unfold dummyOfPayloadFast
  rw [hwf]
  show (dummyFast wf m >>= _) = _
  rw [dummyFast_eq hd]
  exact h

end

end Silmaril.Wasm.Tools.Component.DummyFast
