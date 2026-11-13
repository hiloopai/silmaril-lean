module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVCanon
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Floats in variant payloads: lifting

Reference `lift_flat` with floats at every type, variant payloads included:

* `coerceLiftSlots_canon`: the reference's coerced payload slots (`coerceLiftFlat`, decoding a
  float held in an integer slot with canonicalisation) agree with the IR's re-typed slots
  (`Flat.unfit`) up to the canonicalisation of their floats;
* `liftAtV`: reference `lift_flat` returns the IR lift with all floats canonicalised
  (`canonAtV`), or traps at its first operation where the IR lift fails. In a variant the
  reference lifts the payload from the coerced slots and the IR from the re-typed slots;
  `lift_canon` identifies the two after canonicalisation;
* `liftFlatTypes_liftArgs_floatV`: the direct lift path against `liftArgs`;
* `nanAtV_deterministic`: under the deterministic profile the admissible lowering is the
  canonicalisation `canonAtV`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Runtime (RtId)
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType IntType NumType)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Coerced payload slots -/

theorem reinterpret_ofNat (t : FloatType) {w : Nat} (b : BitVec w) :
    reinterpretIntAsFloat t (BitVec.ofNat (floatIntType t).width b.toNat) =
      b.setWidth t.width := by
  apply BitVec.eq_of_toNat_eq
  have hw : (floatIntType t).width = t.width := floatIntType_width t
  show (BitVec.ofNat (floatIntType t).width b.toNat).toNat = (b.setWidth t.width).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, hw]

/-- Decoding the integer bits of a float slot canonicalises the re-typed bits. -/
theorem decode_canon (f : FloatType) {w : Nat} (b : BitVec w) :
    CanonEq f (b.setWidth f.width)
      (decodeFloat f (BitVec.ofNat (floatIntType f).width b.toNat)) := by
  show _ = canonicalizeNaN f (canonicalizeNaN f _)
  rw [canonicalizeNaN_idem]
  exact congrArg _ (reinterpret_ofNat f b).symm

/-- One coerced slot is the IR's re-typed slot up to canonicalisation. -/
theorem coerceLiftFlat_canon {h w : NumType} {v : Flat} (hv : v.type = h)
    (hs : SlotOk w h = true) :
    FlatRel1 CanonEq (Flat.retype w v) (coerceLiftFlat h w v) := by
  obtain ⟨t, b⟩ := v
  simp only at hv
  subst hv
  have hrefl := FlatRel1.refl (R := CanonEq) canonEq_refl
  rcases t with (_ | _) | (_ | _) <;> rcases w with (_ | _) | (_ | _) <;>
    try first
      | (simp only [SlotOk, Bool.false_eq_true] at hs; done)
      | (rw [coerceLiftFlat_self, show Flat.retype _ ⟨_, b⟩ = ⟨_, b⟩ from retype_self ⟨_, b⟩]
         exact hrefl _)
  · exact .float .f32 _ _ (decode_canon .f32 b)
  · rw [coerceLiftFlat_eq (v := ⟨.int .i64, b⟩) rfl (.inr ⟨rfl, rfl⟩) (.inl rfl)]
    exact hrefl _
  · exact .float .f32 _ _ (decode_canon .f32 b)
  · exact .float .f64 _ _ (decode_canon .f64 b)

/-- **The coerced payload slots** are the IR's re-typed slots up to canonicalisation. -/
theorem coerceLiftSlots_canon : ∀ (ws hs : List NumType) (js : List Flat),
    js.map (·.type) = hs → JDom ws hs →
      FlatRel CanonEq (Flat.unfit ws js) (coerceLiftSlots hs ws js)
  | [], hs, _, _, _ => by cases hs <;> exact .nil
  | _ :: _, [], _, _, hd => hd.elim
  | w :: ws, h :: hs, [], hj, _ => by simp at hj
  | w :: ws, h :: hs, v :: js, hj, ⟨hwh, hd⟩ => by
    simp only [List.map_cons, List.cons.injEq] at hj
    exact .cons (coerceLiftFlat_canon hj.1 hwh) (coerceLiftSlots_canon ws hs js hj.2 hd)

/-! ## Lifting -/

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- `LiftRel` up to `canonAtV`. -/
def LiftRelCV (t : ValTy) (prog : P E σ (Value.Val × FlatCursor))
    (res : Option (IVal × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (w, r) => prog = pure (toRefVal (canonAtV t w), ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- `LiftsRel` up to `canonAtVList`. -/
def LiftsRelCV (ts : List ValTy) (prog : P E σ (List Value.Val × FlatCursor))
    (res : Option (List IVal × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (ws, r) => prog = pure (toRefVals (canonAtVList ts ws), ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- `CaseRel` up to `canonAtVOpt`. -/
def CaseRelCV (c : Option ValTy) (prog : P E σ (Option Value.Val × FlatCursor))
    (res : Option (Option IVal)) : Prop :=
  match res with
  | some o => ∃ cur, prog = pure (toRefOpt (canonAtVOpt c o), cur)
  | none => IsTrap prog

/-- `LiftRelC` is `LiftRelCV` where the two canonicalisations agree. -/
theorem liftRelCV_of {t : ValTy} {prog : P E σ (Value.Val × FlatCursor)}
    {res : Option (IVal × List Flat)} {ys : List Flat} {n' : Nat}
    (he : ∀ w, canonAt t w = canonAtV t w) (h : LiftRelC t prog res ys n') :
    LiftRelCV t prog res ys n' := by
  cases res with
  | none => exact h
  | some pr =>
    obtain ⟨w, r⟩ := pr
    obtain ⟨hp, hr⟩ := h
    exact ⟨by rw [hp, he], hr⟩

/-- A record lifts as its fields. -/
theorem liftRelCV_record {ts : List ValTy} {ys : List Flat} {n n' : Nat}
    {prog : P E σ (List Value.Val × FlatCursor)}
    (h : LiftsRelCV ts prog (ValTy.liftList ts (ys.drop n)) ys n') :
    LiftRelCV (.record ts) (prog >>= fun x => pure (Value.Val.record x.1, x.2))
      (ValTy.lift (.record ts) (ys.drop n)) ys n' := by
  simp only [ValTy.lift]
  revert h
  cases ValTy.liftList ts (ys.drop n) with
  | none => intro h; exact h.bind _
  | some pr =>
    intro h
    obtain ⟨hp, hr⟩ := h
    refine ⟨?_, hr⟩
    rw [hp]
    rfl

/-- One field more, after the first lifted. -/
theorem liftsRelCV_cons {t : ValTy} {ts : List ValTy} {ys : List Flat} {n : Nat} {w : IVal}
    {prog₂ : P E σ (List Value.Val × FlatCursor)}
    (ih₂ : LiftsRelCV ts prog₂ (ValTy.liftList ts (ys.drop (n + t.flat.length))) ys
      (n + t.flat.length + (ValTy.flatList ts).length)) :
    LiftsRelCV (t :: ts) (prog₂ >>= fun x => pure (toRefVal (canonAtV t w) :: x.1, x.2))
      ((ValTy.liftList ts (ys.drop (n + t.flat.length))).map fun p => (w :: p.1, p.2)) ys
      (n + (t.flat.length + (ValTy.flatList ts).length)) := by
  revert ih₂
  cases ValTy.liftList ts (ys.drop (n + t.flat.length)) with
  | none => intro ih₂; exact ih₂.bind _
  | some pr₂ =>
    intro ih₂
    obtain ⟨hp₂, hr₂⟩ := ih₂
    refine ⟨?_, by rw [hr₂, Nat.add_assoc]⟩
    rw [hp₂, pure_bind, Nat.add_assoc]
    rfl

variable (lim : Limits) (q : Quirks) (cx : Silmaril.Wasm.Component.Runtime.LiftLowerContext E)
  (p : Silmaril.Wasm.AddrType)

/-- A scalar other than a float: the plain lift. -/
theorem liftScalarV (t : ValTy) (ys : List Flat) (n : Nat) (hf : floatFree t = true)
    (h32 : t ≠ .f32) (h64 : t ≠ .f64) (hr : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs)
    (ht : Typed t.flat (ys.drop n)) :
    LiftRelCV (σ := σ) t (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + t.flat.length) := by
  refine liftRelCV_of (fun w => ?_) (liftRelC_of h32 h64 hr
    (liftFlatAt_toClosed lim q cx p t ys n hf ht))
  cases t <;> first
    | exact absurd rfl h32 | exact absurd rfl h64 | exact absurd rfl (hr _)
    | exact absurd rfl (hv _) | (cases w <;> rfl)

mutual
/-- **Reference `lift_flat` with floats at every type** is the IR lift with all floats
canonicalised, or traps where the IR lift fails. -/
theorem liftAtV : ∀ (t : ValTy) (ys : List Flat) (n : Nat), Typed t.flat (ys.drop n) →
    LiftRelCV (σ := σ) t (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + t.flat.length)
  | .f32, ys, n, ht => liftRelCV_of (fun w => by cases w <;> rfl) (liftAt_f32 lim q cx p ys n ht)
  | .f64, ys, n, ht => liftRelCV_of (fun w => by cases w <;> rfl) (liftAt_f64 lim q cx p ys n ht)
  | .record ts, ys, n, ht => by
    have ih := liftFieldsV ts (labels "f" (toClosedList ts)) ys n (labels_map_snd "f" _)
      (by simpa only [ValTy.flat] using ht)
    simp only [ValTy.flat]
    exact liftRelCV_record ih
  | .variant cs, ys, n, ht => liftVariantV cs ys n ht
  | .bool, ys, n, ht | .s8, ys, n, ht | .u8, ys, n, ht | .s16, ys, n, ht | .u16, ys, n, ht
  | .s32, ys, n, ht | .u32, ys, n, ht | .s64, ys, n, ht | .u64, ys, n, ht | .char, ys, n, ht =>
    liftScalarV lim q cx p _ ys n rfl (by simp) (by simp) (by simp) (by simp) ht

theorem liftVariantV : ∀ (cs : List (Option ValTy)) (ys : List Flat) (n : Nat),
    Typed (ValTy.flat (.variant cs)) (ys.drop n) →
      LiftRelCV (σ := σ) (.variant cs)
        (liftFlatAt (σ := σ) lim q cx p (toClosed (.variant cs)) ⟨ys, n⟩)
        (ValTy.lift (.variant cs) (ys.drop n)) ys (n + (ValTy.flat (.variant cs)).length)
  | cs, ys, n, ht => by
    simp only [ValTy.flat] at ht ⊢
    obtain ⟨d, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
    have hdty : d.type = .int .i32 := typed_head (hd ▸ ht)
    obtain ⟨dt, db⟩ := d
    simp only at hdty
    subst hdty
    have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
    have htr : Typed (ValTy.flatCases cs) rest := by
      have h' : Typed ([.int .i32] ++ ValTy.flatCases cs) (⟨.int .i32, db⟩ :: rest) := hd ▸ ht
      simpa only [List.length_singleton, List.drop_one, List.tail_cons] using h'.right
    have hlen : (labels "c" (toClosedCases cs)).length = cs.length := by
      simp only [labels, List.length_mapIdx, toClosedCases_length]
    have hjoin : variantPayload (flattenCases p (labels "c" (toClosedCases cs))) =
        ValTy.flatCases cs := flattenCases_toClosed p cs _ (labels_map_snd "c" _)
    rw [hd]
    simp only [ValTy.lift, flatTake_eq _ _ htr, toClosed, liftFlatAt, liftFlatVariantWith,
      next_eq hd, pure_bind, flatNat, hlen, hjoin]
    by_cases hlt : db.toNat < cs.length
    · obtain ⟨c, hc⟩ : ∃ c, cs[db.toNat]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hng : ¬ (db.toNat ≥ cs.length) := Nat.not_le.mpr hlt
      have hlen' : (ValTy.flatCases cs).length ≤ (ys.drop (n + 1)).length := by
        rw [← hrest]; exact htr.2
      have hxs : (rest.take (ValTy.flatCases cs).length).map (·.type) = ValTy.flatCases cs := htr.1
      have hdom : JDom (ValTy.flatOpt c) (ValTy.flatCases cs) := jdom_case cs _ c hc
      have hu := coerceLiftSlots_canon _ _ _ hxs hdom
      have hzs : (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length)).map
          (·.type) = ValTy.flatOpt c :=
        unfit_types _ _ (by
          have h₁ := congrArg List.length hxs
          rw [List.length_map] at h₁
          rw [h₁]
          exact hdom.length_le)
      have hzs' := (flatRel_types hu).trans hzs
      have ih := liftCaseV cs (labels "c" (toClosedCases cs)) db.toNat c _
        (labels_map_snd "c" _) hc hzs'
      have hcan := liftCase_canon cs db.toNat c _ _ hc hu
      simp only [hng, decide_false, trapIf, Bool.false_eq_true, ↓reduceIte, pure_bind,
        nextN_eq _ ys (n + 1) hlen', ← hrest, caseFlat_eq p (labels_map_snd "c" _) hc,
        liftCase_some cs _ c _ hc, FlatCursor.ofList]
      revert ih hcan
      cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length))
        with
      | none =>
        cases ValTy.liftOpt c (coerceLiftSlots (ValTy.flatCases cs) (ValTy.flatOpt c)
          (rest.take (ValTy.flatCases cs).length)) with
        | none => intro ih _; exact ih.bind _
        | some _ => intro _ hcan; exact (hcan : False).elim
      | some o =>
        cases ValTy.liftOpt c (coerceLiftSlots (ValTy.flatCases cs) (ValTy.flatOpt c)
          (rest.take (ValTy.flatCases cs).length)) with
        | none => intro _ hcan; exact (hcan : False).elim
        | some o' =>
          intro ih hcan
          obtain ⟨cur, hcur⟩ := ih
          refine ⟨?_, ?_⟩
          · rw [hcur, pure_bind]
            simp only [List.length_cons, toRefVal, canonAtV, canonAtVCase_some hc]
            congr 3
            · exact congrArg _ (hcan : canonAtVOpt c o = canonAtVOpt c o').symm
            · omega
          · rw [hrest, List.drop_drop]
            congr 1
            simp only [List.length_cons]
            omega
    · have hge : cs.length ≤ db.toNat := Nat.le_of_not_lt hlt
      simp only [ge_iff_le, hge, decide_true, trapIf, ↓reduceIte, liftCase_none _ _ _ hge,
        Option.map_none, LiftRelCV]
      exact (isTrap_trap _).bind _

theorem liftCaseV : ∀ (cs : List (Option ValTy))
    (fs : List (String × Option (WIT.ClosedType RtId))) (i : Nat) (c : Option ValTy)
    (zs : List Flat), fs.map Prod.snd = toClosedCases cs →
      cs[i]? = some c → zs.map (·.type) = ValTy.flatOpt c →
        CaseRelCV (σ := σ) c (liftFlatCaseAt (σ := σ) lim q cx p fs i ⟨zs, 0⟩)
          (ValTy.liftOpt c zs)
  | [], _, _, _, _, _, hc, _ => by simp at hc
  | none :: _, [], _, _, _, hfs, _, _ | some _ :: _, [], _, _, _, hfs, _, _ => by
    simp [toClosedCases] at hfs
  | none :: cs, (nm, u) :: fs, 0, c, zs, hfs, hc, _ => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    exact ⟨⟨zs, 0⟩, rfl⟩
  | some t :: cs, (nm, u) :: fs, 0, c, zs, hfs, hc, hz => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    simp only [ValTy.flatOpt] at hz
    have hlen : zs.length = t.flat.length := by rw [← hz, List.length_map]
    have ht : Typed t.flat (zs.drop 0) := by
      refine ⟨?_, by simp [hlen]⟩
      rw [List.drop_zero, ← hlen, List.take_length, hz]
    have ih := liftAtV t zs 0 ht
    rw [List.drop_zero] at ih
    simp only [liftFlatCaseAt, liftFlatOpt, ValTy.liftOpt]
    revert ih
    cases ValTy.lift t zs with
    | none => intro ih; exact ih.bind _
    | some pr =>
      intro ih
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih
      have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
      subst hr'
      exact ⟨_, by rw [hp, pure_bind]; rfl⟩
  | c' :: cs, (nm, u) :: fs, i + 1, c, zs, hfs, hc, hz => by
    have hfs' : fs.map Prod.snd = toClosedCases cs := by
      cases c' <;> simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs <;> exact hfs.2
    simp only [List.getElem?_cons_succ] at hc
    simp only [liftFlatCaseAt]
    exact liftCaseV cs fs i c zs hfs' hc hz

/-- `liftAtV` on record fields. -/
theorem liftFieldsV : ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType RtId))
    (ys : List Flat) (n : Nat), fs.map Prod.snd = toClosedList ts →
      Typed (ValTy.flatList ts) (ys.drop n) →
        LiftsRelCV (σ := σ) ts (liftFlatFields (σ := σ) lim q cx p fs ⟨ys, n⟩)
          (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | [], [], ys, n, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => by simp [toClosedList] at h
  | t :: ts, (nm, u) :: fs, ys, n, hfs, ht => by
    have hfs' : u = toClosed t ∧ fs.map Prod.snd = toClosedList ts := by
      simpa only [List.map_cons, toClosedList, List.cons.injEq] using hfs
    have ht' : Typed (t.flat ++ ValTy.flatList ts) (ys.drop n) := by
      simpa only [ValTy.flatList] using ht
    have ih₁ := liftAtV t ys n ht'.left
    rw [hfs'.1]
    simp only [liftFlatFields, ValTy.liftList, ValTy.flatList, List.length_append]
    revert ih₁
    cases ValTy.lift t (ys.drop n) with
    | none => intro ih₁; exact ih₁.bind _
    | some pr =>
      intro ih₁
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih₁
      have ht₂ : Typed (ValTy.flatList ts) (ys.drop (n + t.flat.length)) := by
        have h₂ := ht'.right
        rwa [List.drop_drop] at h₂
      have ih₂ := liftFieldsV ts fs ys (n + t.flat.length) hfs'.2 ht₂
      rw [hp, pure_bind, hr]
      exact liftsRelCV_cons ih₂
end

/-- `liftFieldsV` on argument lists. -/
theorem liftFlatTypesV (ts : List ValTy) (ys : List Flat) (n : Nat)
    (ht : Typed (ValTy.flatList ts) (ys.drop n)) :
    LiftsRelCV (σ := σ) ts (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, n⟩)
      (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length) := by
  have h := liftFieldsV (σ := σ) lim q cx p ts _ ys n (labels_map_snd "f" _) ht
  have heq : ∀ (fs : List (String × WIT.ClosedType RtId)) (c : FlatCursor),
      (liftFlatFields (σ := σ) lim q cx p fs c) = liftFlatTypes lim q cx p (fs.map Prod.snd) c := by
    intro fs
    induction fs with
    | nil => intro c; rfl
    | cons f fs ih =>
      intro c
      obtain ⟨nm, u⟩ := f
      simp only [liftFlatFields, liftFlatTypes, List.map_cons, ih]
  rwa [heq, labels_map_snd] at h

/-- **The direct lift path with floats at every type relates to `liftArgs`**: the
canonicalised results, or a trap at the first operation where `liftArgs` fails. -/
theorem liftFlatTypes_liftArgs_floatV {ts : List ValTy} {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList ts) :
    match liftArgs ts ys with
    | some ws => ∃ c, (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) =
        pure ((canonAtVList ts ws).map toRefVal, c)
    | none => IsTrap (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) := by
  have hlen : ys.length = (ValTy.flatList ts).length := by rw [← hys, List.length_map]
  have ht : Typed (ValTy.flatList ts) (ys.drop 0) := by
    refine ⟨?_, by simp [hlen]⟩
    rw [List.drop_zero, ← hlen, List.take_length, hys]
  have h := liftFlatTypesV (σ := σ) lim q cx p ts ys 0 ht
  rw [List.drop_zero] at h
  unfold liftArgs
  revert h
  cases ValTy.liftList ts ys with
  | none => intro h; exact h
  | some pr =>
    intro h
    obtain ⟨ws, r⟩ := pr
    obtain ⟨hp, hr⟩ := h
    have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
    subst hr'
    exact ⟨_, by rw [hp, toRefVals_eq]⟩

/-! ## The deterministic profile -/

mutual
/-- **Under the deterministic profile the admissible lowering is unique**: the
canonicalisation, at every type. -/
theorem nanAtV_deterministic : ∀ (t : ValTy) (v w : IVal), NanAtV .deterministic t v w →
    w = canonAtV t v
  | .f32, _, _, h => by
    obtain ⟨x, y, rfl, rfl, h⟩ := h
    exact congrArg _ (nanLower_deterministic h)
  | .f64, _, _, h => by
    obtain ⟨x, y, rfl, rfl, h⟩ := h
    exact congrArg _ (nanLower_deterministic h)
  | .record ts, _, _, h => by
    obtain ⟨vs, ws, rfl, rfl, h⟩ := h
    exact congrArg _ (nanAtVList_deterministic ts vs ws h)
  | .variant cs, _, _, h => by
    obtain ⟨i, pl, pl', rfl, rfl, h⟩ := h
    exact congrArg _ (nanAtVCase_deterministic cs i pl pl' h)
  | .bool, v, _, h | .s8, v, _, h | .u8, v, _, h | .s16, v, _, h | .u16, v, _, h
  | .s32, v, _, h | .u32, v, _, h | .s64, v, _, h | .u64, v, _, h | .char, v, _, h => by
    subst h
    cases v <;> rfl

theorem nanAtVList_deterministic : ∀ (ts : List ValTy) (vs ws : List IVal),
    NanAtVList .deterministic ts vs ws → ws = canonAtVList ts vs
  | [], _, _, h => by rw [h.1, h.2]; rfl
  | t :: ts, _, _, h => by
    obtain ⟨v, vs, w, ws, rfl, rfl, hv, hvs⟩ := h
    exact congrArg₂ List.cons (nanAtV_deterministic t v w hv)
      (nanAtVList_deterministic ts vs ws hvs)

theorem nanAtVCase_deterministic : ∀ (cs : List (Option ValTy)) (i : Nat) (pl pl' : Option IVal),
    FloatRelAtCase (NanLower .deterministic) cs i pl pl' → pl' = canonAtVCase cs i pl
  | [], _, _, _, h => h.symm
  | none :: _, 0, _, _, h => by rw [h.1, h.2]; rfl
  | some t :: _, 0, _, _, h => by
    obtain ⟨v, w, rfl, rfl, h⟩ := h
    exact congrArg some (nanAtV_deterministic t v w h)
  | _ :: cs, i + 1, pl, pl', h => nanAtVCase_deterministic cs i pl pl' h
end

end Silmaril.Proofs.Wasm.Component.Reference
