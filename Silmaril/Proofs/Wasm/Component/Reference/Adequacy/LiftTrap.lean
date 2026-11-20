module

public import Silmaril.Proofs.Wasm.Component.Reference.CallPath

/-!
# Lift traps of the reference flat ABI are specification traps

`Silmaril.Proofs.Wasm.Component.Reference.FlatABI` shows that the reference `lift_flat` on IR
types traps exactly where the IR lift fails (`IsTrap`: the program's first operation is a
trap). Here the same statements are proved with `IsSpecTrap`: the trap reason is not a model
fault (`TrapReason.internal`). This is what a terminating trap outcome of the reference machine
needs (`Calls` excludes internal traps). The proofs follow `FlatABI` line by line; the traps
of the lift are `invalidChar` and `invalidDiscriminant`.

`lrun_lift_trapS` is `lrun_lift_trap` (`CallPath`) with a specification trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Runtime (RtId)

section Lift

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- The program traps at its first operation, with a specification trap (not a model fault). -/
def IsSpecTrap {α : Type} (prog : P E σ α) : Prop :=
  ∃ (r : TrapReason) (k : Empty → P E σ α), (∀ msg, r ≠ .internal msg) ∧
    prog = .op (S := Eff E σ) (.trap r) k

theorem IsSpecTrap.bind {α β : Type} {prog : P E σ α} (h : IsSpecTrap prog)
    (f : α → P E σ β) : IsSpecTrap (prog >>= f) := by
  obtain ⟨r, k, hr, rfl⟩ := h
  exact ⟨r, fun e => k e >>= f, hr, rfl⟩

theorem isSpecTrap_trap {α : Type} (r : TrapReason) (hr : ∀ msg, r ≠ .internal msg) :
    IsSpecTrap (trap r : P E σ α) := ⟨r, _, hr, rfl⟩

variable (lim : Limits) (q : Quirks) (cx : Silmaril.Wasm.Component.Runtime.LiftLowerContext E)
  (p : Silmaril.Wasm.AddrType)

def LiftRelS (prog : P E σ (Value.Val × FlatCursor))
    (res : Option (Silmaril.Wasm.Component.Val × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (w, r) => prog = pure (toRefVal w, ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsSpecTrap prog

/-- `LiftRelS` for lists of values. -/
def LiftsRelS (prog : P E σ (List Value.Val × FlatCursor))
    (res : Option (List Silmaril.Wasm.Component.Val × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (ws, r) => prog = pure (toRefVals ws, ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsSpecTrap prog

/-- `LiftRelS` for an optional payload, whose cursor is discarded. -/
def CaseRelS (prog : P E σ (Option Value.Val × FlatCursor))
    (res : Option (Option Silmaril.Wasm.Component.Val)) : Prop :=
  match res with
  | some o => ∃ c, prog = pure (toRefOpt o, c)
  | none => IsSpecTrap prog

theorem liftCharS {ys : List Flat} {n : Nat} {rest : List Flat}
    (b : BitVec (Silmaril.Wasm.NumType.int .i32).width)
    (hd : ys.drop n = ⟨.int .i32, b⟩ :: rest) (hrest : rest = ys.drop (n + 1)) :
    LiftRelS (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed .char) ⟨ys, n⟩)
      (ValTy.lift .char (⟨.int .i32, b⟩ :: rest)) ys (n + 1) := by
  have hp : (liftFlatAt (σ := σ) lim q cx p (toClosed .char) ⟨ys, n⟩) =
      (do let c ← orTrap .invalidChar (charOfBits b); pure (Value.Val.char c, ⟨ys, n + 1⟩)) := by
    simp only [toClosed, liftFlatAt, liftFlatAtWith, FlatLoadCarrier.reference, liftFlatPrim,
      next_eq hd, pure_bind, wrap_i32,
      convertI32ToChar, convertI32ToChar?_eq]
  rw [hp]
  cases hc : charOfBits b with
  | none =>
    simp only [ValTy.lift, hc, Option.map_none, orTrap, LiftRelS]
    exact (isSpecTrap_trap _ (fun _ h => by cases h)).bind _
  | some c =>
    simp only [ValTy.lift, hc, Option.map_some, orTrap, LiftRelS, pure_bind]
    exact ⟨rfl, hrest⟩

/-- One scalar value. -/
theorem liftPrimS (t : ValTy) (ys : List Flat) (n : Nat) (y : Flat) (rest : List Flat)
    (hd : ys.drop n = y :: rest) (hty : t.flat = [y.type]) (hf : floatFree t = true)
    (hs : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs) :
    LiftRelS (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + 1) := by
  obtain ⟨ty, b⟩ := y
  rw [hd]
  have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
  cases t <;>
    first
      | exact absurd rfl (hs _)
      | exact absurd rfl (hv _)
      | (simp only [floatFree, Bool.false_eq_true] at hf; done)
      | (simp only [ValTy.flat, List.cons.injEq, and_true] at hty
         subst hty
         first
           | (refine ⟨?_, hrest⟩
              simp only [toClosed, liftFlatAt, liftFlatAtWith, FlatLoadCarrier.reference,
                liftFlatPrim, Value.IntKind.ofPrimitive, next_eq hd,
                pure_bind, toRefVal, intKindCore]
              first
                | (rw [liftFlatBool_eq])
                | (rw [liftFlatInt_unsigned rfl rfl]
                   simp only [BitVec.ofNat_toNat]
                   rfl)
                | (rw [liftFlatInt_signed rfl rfl (by decide)]
                   simp only [BitVec.ofNat_toNat]
                   rfl))
           | exact liftCharS lim q cx p b hd hrest)

/-- One scalar value, from a typed cursor. -/
theorem liftScalarS (t : ValTy) (ys : List Flat) (n : Nat) {f : Silmaril.Wasm.NumType}
    (hfl : t.flat = [f]) (hf : floatFree t = true) (ht : Typed t.flat (ys.drop n))
    (hs : ∀ ts, t ≠ .record ts) (hv : ∀ cs, t ≠ .variant cs) :
    LiftRelS (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
      (ValTy.lift t (ys.drop n)) ys (n + t.flat.length) := by
  rw [hfl] at ht ⊢
  obtain ⟨y, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
  have hy : y.type = f := typed_head (hd ▸ ht)
  exact liftPrimS lim q cx p t ys n y rest hd (by rw [hfl, hy]) hf hs hv

mutual
/-- **Reference `lift_flat` on IR types is the IR lift**, for float-free types and flat values of
the right types: the same values, or a trap where the IR traps. -/
theorem liftFlatAtS : ∀ (t : ValTy) (ys : List Flat) (n : Nat), floatFree t = true →
    Typed t.flat (ys.drop n) →
      LiftRelS (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
        (ValTy.lift t (ys.drop n)) ys (n + t.flat.length)
  | .record ts, ys, n, hf, ht => by
    have ih := liftFlatFieldsS ts (labels "f" (toClosedList ts)) ys n
      (labels_map_snd "f" _) (by simpa only [floatFree] using hf) (by simpa only [ValTy.flat] using ht)
    simp only [ValTy.flat]
    simp only [toClosed, liftFlatAt, liftFlatAtWith, ValTy.lift]
    revert ih
    cases ValTy.liftList ts (ys.drop n) with
    | none => intro ih; exact ih.bind _
    | some pr =>
      intro ih
      obtain ⟨hp, hr⟩ := ih
      refine ⟨?_, hr⟩
      unfold liftFlatFields at hp
      rw [hp]
      rfl
  | .variant cs, ys, n, hf, ht => liftVariantS cs ys n (by simpa only [floatFree] using hf) ht
  | .bool, ys, n, hf, ht => liftScalarS lim q cx p .bool ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s8, ys, n, hf, ht => liftScalarS lim q cx p .s8 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u8, ys, n, hf, ht => liftScalarS lim q cx p .u8 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s16, ys, n, hf, ht => liftScalarS lim q cx p .s16 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u16, ys, n, hf, ht => liftScalarS lim q cx p .u16 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s32, ys, n, hf, ht => liftScalarS lim q cx p .s32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u32, ys, n, hf, ht => liftScalarS lim q cx p .u32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .s64, ys, n, hf, ht => liftScalarS lim q cx p .s64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .u64, ys, n, hf, ht => liftScalarS lim q cx p .u64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .f32, ys, n, hf, ht => liftScalarS lim q cx p .f32 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .f64, ys, n, hf, ht => liftScalarS lim q cx p .f64 ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)
  | .char, ys, n, hf, ht => liftScalarS lim q cx p .char ys n rfl hf ht (fun _ h => by cases h) (fun _ h => by cases h)

theorem liftVariantS : ∀ (cs : List (Option ValTy)) (ys : List Flat) (n : Nat),
    floatFreeCases cs = true → Typed (ValTy.flat (.variant cs)) (ys.drop n) →
      LiftRelS (σ := σ) (liftFlatAt (σ := σ) lim q cx p (toClosed (.variant cs)) ⟨ys, n⟩)
        (ValTy.lift (.variant cs) (ys.drop n)) ys (n + (ValTy.flat (.variant cs)).length)
  | cs, ys, n, hf, ht => by
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
    simp only [ValTy.lift, flatTake_eq _ _ htr, toClosed, liftFlatAt, liftFlatAtWith,
      liftFlatVariantUsing, FlatLoadCarrier.reference, LoadCarrier.reference,
      next_eq hd, pure_bind, flatNat, hlen, hjoin]
    by_cases hlt : db.toNat < cs.length
    · obtain ⟨c, hc⟩ : ∃ c, cs[db.toNat]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hng : ¬ (db.toNat ≥ cs.length) := Nat.not_le.mpr hlt
      have hlen' : (ValTy.flatCases cs).length ≤ (ys.drop (n + 1)).length := by
        rw [← hrest]; exact htr.2
      have hxs : (rest.take (ValTy.flatCases cs).length).map (·.type) = ValTy.flatCases cs := htr.1
      have hdom : Dom (ValTy.flatOpt c) (ValTy.flatCases cs) := dom_case cs _ c hf hc
      have hint : IntFlat (ValTy.flatOpt c) := Dom.int hdom (flatCases_int cs hf)
      have hzs : (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length)).map
          (·.type) = ValTy.flatOpt c :=
        unfit_types _ _ (by
          have h₁ := congrArg List.length hxs
          rw [List.length_map] at h₁
          rw [h₁]
          exact hdom.length_le)
      have ih := liftFlatCaseS cs (labels "c" (toClosedCases cs)) db.toNat c _
        (labels_map_snd "c" _) hf hc hzs
      simp only [hng, decide_false, trapIf, Bool.false_eq_true, ↓reduceIte, pure_bind,
        nextN_eq _ ys (n + 1) hlen', ← hrest, caseFlat_eq p (labels_map_snd "c" _) hc,
        coerceLiftSlots_eq _ _ _ hdom hint hxs, liftCase_some cs _ c _ hc, FlatCursor.ofList]
      revert ih
      cases ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) (rest.take (ValTy.flatCases cs).length)) with
      | none => intro ih; exact ih.bind _
      | some o =>
        intro ih
        obtain ⟨cur, hcur⟩ := ih
        refine ⟨?_, ?_⟩
        · simp only [liftFlatCaseAt, FlatLoadCarrier.reference, LoadCarrier.reference] at hcur
          rw [hcur, pure_bind]
          simp only [List.length_cons, toRefVal]
          congr 3
          omega
        · rw [hrest, List.drop_drop]
          congr 1
          simp only [List.length_cons]
          omega
    · have hge : cs.length ≤ db.toNat := Nat.le_of_not_lt hlt
      simp only [ge_iff_le, hge, decide_true, trapIf, ↓reduceIte, liftCase_none _ _ _ hge,
        Option.map_none, LiftRelS]
      exact (isSpecTrap_trap _ (fun _ h => by cases h)).bind _

theorem liftFlatCaseS : ∀ (cs : List (Option ValTy))
    (fs : List (String × Option (WIT.ClosedType RtId))) (i : Nat) (c : Option ValTy)
    (zs : List Flat), fs.map Prod.snd = toClosedCases cs → floatFreeCases cs = true →
      cs[i]? = some c → zs.map (·.type) = ValTy.flatOpt c →
        CaseRelS (σ := σ) (liftFlatCaseAt (σ := σ) lim q cx p fs i ⟨zs, 0⟩) (ValTy.liftOpt c zs)
  | [], _, _, _, _, _, _, hc, _ => by simp at hc
  | none :: _, [], _, _, _, hfs, _, _, _ | some _ :: _, [], _, _, _, hfs, _, _, _ => by
    simp [toClosedCases] at hfs
  | none :: cs, (nm, u) :: fs, 0, c, zs, hfs, _, hc, _ => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    exact ⟨⟨zs, 0⟩, rfl⟩
  | some t :: cs, (nm, u) :: fs, 0, c, zs, hfs, hf, hc, hz => by
    simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs
    obtain ⟨rfl, -⟩ := hfs
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    simp only [floatFreeCases, Bool.and_eq_true] at hf
    simp only [ValTy.flatOpt] at hz
    have hlen : zs.length = t.flat.length := by rw [← hz, List.length_map]
    have ht : Typed t.flat (zs.drop 0) := by
      refine ⟨?_, by simp [hlen]⟩
      rw [List.drop_zero, ← hlen, List.take_length, hz]
    have ih := liftFlatAtS t zs 0 hf.1 ht
    rw [List.drop_zero] at ih
    simp only [liftFlatCaseAt, liftFlatCaseAtWith, liftFlatOptWith, ValTy.liftOpt]
    revert ih
    cases ValTy.lift t zs with
    | none => intro ih; exact ih.bind _
    | some pr =>
      intro ih
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih
      have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
      subst hr'
      unfold liftFlatAt at hp
      exact ⟨_, by rw [hp, pure_bind]; rfl⟩
  | c' :: cs, (nm, u) :: fs, i + 1, c, zs, hfs, hf, hc, hz => by
    have hfs' : fs.map Prod.snd = toClosedCases cs := by
      cases c' <;> simp only [List.map_cons, toClosedCases, List.cons.injEq] at hfs <;> exact hfs.2
    have hf' : floatFreeCases cs = true := by
      cases c' <;> simp only [floatFreeCases, Bool.and_eq_true] at hf <;> first | exact hf | exact hf.2
    simp only [List.getElem?_cons_succ] at hc
    simp only [liftFlatCaseAt, liftFlatCaseAtWith]
    exact liftFlatCaseS cs fs i c zs hfs' hf' hc hz

theorem liftFlatFieldsS : ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType RtId))
    (ys : List Flat) (n : Nat), fs.map Prod.snd = toClosedList ts → floatFreeList ts = true →
      Typed (ValTy.flatList ts) (ys.drop n) →
        LiftsRelS (σ := σ) (liftFlatFields (σ := σ) lim q cx p fs ⟨ys, n⟩)
          (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | [], [], ys, n, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp [toClosedList] at h
  | t :: ts, (nm, u) :: fs, ys, n, hfs, hf, ht => by
    simp only [List.map_cons, toClosedList, List.cons.injEq] at hfs
    obtain ⟨rfl, hfs⟩ := hfs
    simp only [floatFreeList, Bool.and_eq_true] at hf
    simp only [ValTy.flatList] at ht
    have ih₁ := liftFlatAtS t ys n hf.1 ht.left
    simp only [liftFlatFields, liftFlatFieldsWith, ValTy.liftList, ValTy.flatList, List.length_append]
    revert ih₁
    cases ValTy.lift t (ys.drop n) with
    | none => intro ih₁; exact ih₁.bind _
    | some pr =>
      intro ih₁
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih₁
      subst hr
      have ht₂ : Typed (ValTy.flatList ts) (ys.drop (n + t.flat.length)) := by
        have := ht.right
        rwa [List.drop_drop] at this
      have ih₂ := liftFlatFieldsS ts fs ys (n + t.flat.length) hfs hf.2 ht₂
      unfold liftFlatAt at hp
      rw [hp, pure_bind]
      dsimp only
      revert ih₂
      cases ValTy.liftList ts (ys.drop (n + t.flat.length)) with
      | none => intro ih₂; exact ih₂.bind _
      | some pr₂ =>
        intro ih₂
        obtain ⟨hp₂, hr₂⟩ := ih₂
        refine ⟨?_, by rw [hr₂, Nat.add_assoc]⟩
        unfold liftFlatFields at hp₂
        rw [hp₂, pure_bind, Nat.add_assoc]
        rfl
end

theorem liftFlatTypesS : ∀ (ts : List ValTy) (ys : List Flat) (n : Nat),
    floatFreeList ts = true → Typed (ValTy.flatList ts) (ys.drop n) →
      LiftsRelS (σ := σ) (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, n⟩)
        (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | ts, ys, n, hf, ht => by
    have hfs : (labels "f" (toClosedList ts)).map Prod.snd = toClosedList ts := labels_map_snd "f" _
    have h := liftFlatFieldsS (σ := σ) lim q cx p ts _ ys n hfs hf ht
    have heq : ∀ (fs : List (String × WIT.ClosedType RtId)) (c : FlatCursor),
        (liftFlatFields (σ := σ) lim q cx p fs c) = liftFlatTypes lim q cx p (fs.map Prod.snd) c := by
      intro fs
      induction fs with
      | nil => intro c; rfl
      | cons f fs ih =>
        intro c
        obtain ⟨nm, u⟩ := f
        simp only [liftFlatFields, liftFlatFieldsWith, liftFlatTypes, liftFlatTypesWith,
          List.map_cons, ih]
    rwa [heq, hfs] at h

/-- The direct lift path relates to `liftArgs`. -/
theorem liftFlatTypes_liftArgsS {ts : List ValTy} {ys : List Flat} (hf : floatFreeList ts = true)
    (hys : ys.map (·.type) = ValTy.flatList ts) :
    match liftArgs ts ys with
    | some ws => ∃ c, (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) =
        pure (ws.map toRefVal, c)
    | none => IsSpecTrap (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) := by
  have hlen : ys.length = (ValTy.flatList ts).length := by rw [← hys, List.length_map]
  have ht : Typed (ValTy.flatList ts) (ys.drop 0) := by
    refine ⟨?_, by simp [hlen]⟩
    rw [List.drop_zero, ← hlen, List.take_length, hys]
  have h := liftFlatTypesS (σ := σ) lim q cx p ts ys 0 hf ht
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

end Lift

section Run

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

theorem lrun_lift_trapS {α : Type} {th : Option ThreadId} (prof : ProfileKind) (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    (hnone : liftArgs x.ty.results ys = none)
    {cx : LiftLowerContext (E3 P)} {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) Unit α}
    {g : α → Canon.P (E3 P) Unit (Ret (E3 P))} {M : Machine.Config (E3 P) Unit}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    ∃ mT r, (∀ msg, r ≠ .internal msg) ∧ LRun prof (refHost P).hr (D P) M [.tau] mT ∧
      Live mT ∧ UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT) := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P (E3 P) Unit _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgsS (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn (CoreEngine.view _ M.core) cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hr, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) Unit) .readCore fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (refHost P).hr (D P) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn (CoreEngine.view _ M.core) cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.readCore hc'
  rw [hk] at s₁
  refine ⟨_, r, hr, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩

end Run

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
