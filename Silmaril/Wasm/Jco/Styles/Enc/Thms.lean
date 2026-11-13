module

public import Silmaril.Wasm.Jco.Styles.Enc.Defs
public import Silmaril.Wasm.Jco.Basic.Thms
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# The canonical ABI with string encodings: basic facts

* `canonCallE_utf8`: with `string-encoding=utf8`, `canonCallE` **is** `canonCall` of
  `Silmaril.Wasm.Jco.Canon` (`lowerParamsE_utf8`, `liftResultE_utf8`).
* `lowerParamsE_congr`: lowering calls the `realloc` only on `i32` argument lists, so two
  `realloc`s that agree there give the same lowering.
* `lowerParamsE_length`: lowering yields `(flatParams ps).length` flat values.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy)
open RM

variable (M : CoreInst)

theorem lowerParamsE_utf8 (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal), lowerParamsE M .utf8 R ps vs = lowerParams M R ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    have hp : lowerParamE M .utf8 R t v = lowerParam M R t v := by
      cases t <;> cases v <;> rfl
    simp only [lowerParamsE, lowerParams, hp, lowerParamsE_utf8 R ts vs]

theorem readPair_pairAt (rp : BitVec 32) :
    readPair M rp = (pairAt M rp >>= fun pl => M.load pl.1.toNat pl.2.toNat) := by
  simp only [readPair, pairAt, RM.bind_assoc, RM.pure_bind]

theorem liftResultE_utf8 (r : Option PTy) (xs : List Flat) :
    liftResultE M .utf8 r xs = liftResult M r xs := by
  match r, xs with
  | some .string, [x] =>
    show (RM.ofOption (asI32? x) >>= fun rp => pairAt M rp >>= fun pl =>
        liftStr M .utf8 pl.1 pl.2 >>= fun s => pure (some (PVal.string s))) = _
    simp only [liftResult, readPair_pairAt, liftStr, RM.bind_assoc]
  | none, _ => rfl
  | some (.val _), _ => rfl
  | some .bytes, _ => rfl
  | some .string, [] => rfl
  | some .string, _ :: _ :: _ => rfl

/-- **With `utf8`, the encoded canonical call is `canonCall`.** -/
theorem canonCallE_utf8 (R callee : List Flat → RM M.St (List Flat)) (sig : Sig)
    (vs : List PVal) : canonCallE M .utf8 R callee sig vs = canonCall M R callee sig vs := by
  simp only [canonCallE, canonCall, lowerParamsE_utf8]
  refine RM.bind_congr fun xs => RM.bind_congr fun rs => ?_
  exact liftResultE_utf8 M sig.result rs

/-! ## Congruence in the `realloc` -/

section congr
variable {R R' : List Flat → RM M.St (List Flat)}
  (hR : ∀ a b c d : Nat, R [i32n a, i32n b, i32n c, i32n d] = R' [i32n a, i32n b, i32n c, i32n d])
include hR

theorem reallocCall_congr (a b c d : Nat) : reallocCall M R a b c d = reallocCall M R' a b c d := by
  simp only [reallocCall, hR]

theorem shrinkTo_congr (p : BitVec 32) (w len : Nat) : shrinkTo M R p w len = shrinkTo M R' p w len := by
  simp only [shrinkTo, reallocCall_congr M hR]

theorem lowerStr_congr (enc : StrEnc) (s : String) : lowerStr M R enc s = lowerStr M R' enc s := by
  cases enc <;>
    simp only [lowerStr, lowerBytes, storeUtf16, storeLatin1Utf16, hR, reallocCall_congr M hR,
      shrinkTo_congr M hR]

theorem lowerParamE_congr (enc : StrEnc) (t : PTy) (v : PVal) :
    lowerParamE M enc R t v = lowerParamE M enc R' t v := by
  cases t <;> cases v <;>
    simp only [lowerParamE, lowerParam, lowerBytes, hR, lowerStr_congr M hR]

/-- Two `realloc`s that agree on `i32` arguments give the same lowering. -/
theorem lowerParamsE_congr (enc : StrEnc) :
    ∀ (ps : List PTy) (vs : List PVal), lowerParamsE M enc R ps vs = lowerParamsE M enc R' ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    simp only [lowerParamsE, lowerParamE_congr M hR enc t v, lowerParamsE_congr enc ts vs]

end congr

/-! ## Lengths -/

theorem lowerBytes_length (R : List Flat → RM M.St (List Flat)) (limit : Nat) (bs : List UInt8) :
    Returns (lowerBytes M R limit bs) fun xs => xs.length = 2 :=
  returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
    returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
      returns_pure rfl

theorem storeUtf16_length (R : List Flat → RM M.St (List Flat)) (s : String) :
    Returns (storeUtf16 M R s) fun xs => xs.length = 2 :=
  returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
    returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
      returns_bind (returns_true _) fun _ _ => returns_pure rfl

theorem storeLatin1Utf16_length (R : List Flat → RM M.St (List Flat)) (s : String) :
    Returns (storeLatin1Utf16 M R s) fun xs => xs.length = 2 := by
  refine returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
    returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ => ?_
  split
  · exact returns_bind (returns_true _) fun _ _ => returns_pure rfl
  · exact returns_bind returns_check fun _ _ => returns_bind (returns_true _) fun _ _ =>
      returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
        returns_bind (returns_true _) fun _ _ => returns_bind (returns_true _) fun _ _ =>
          returns_bind (returns_true _) fun _ _ => returns_pure rfl

theorem lowerStr_length (R : List Flat → RM M.St (List Flat)) (enc : StrEnc) (s : String) :
    Returns (lowerStr M R enc s) fun xs => xs.length = 2 := by
  cases enc
  · exact lowerBytes_length M R _ _
  · exact storeUtf16_length M R s
  · exact storeLatin1Utf16_length M R s

theorem lowerVal_length (t : ValTy) (v : Silmaril.Wasm.Component.Val) :
    Returns (do RM.check (t.check v); pure (t.lower v) : RM M.St (List Flat))
      fun xs => xs.length = t.flat.length := by
  by_cases hc : t.check v = true
  · have hl : (t.lower v).length = t.flat.length := by
      rw [← ValTy.lower_types t v hc, List.length_map]
    simp only [hc, RM.check_true, RM.pure_bind]
    exact returns_pure (P := fun xs : List Flat => xs.length = t.flat.length) hl
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, RM.check_false, RM.fail_bind]
    exact returns_fail

theorem lowerParamE_length (enc : StrEnc) (R : List Flat → RM M.St (List Flat)) (t : PTy)
    (v : PVal) : Returns (lowerParamE M enc R t v) fun xs => xs.length = t.flat.length := by
  cases t <;> cases v
  case val.val t v => exact lowerVal_length M t v
  case string.string s => exact lowerStr_length M R enc s
  case bytes.bytes bs => exact lowerBytes_length M R _ _
  all_goals exact returns_fail

/-- Lowering yields `(flatParams ps).length` flat values. -/
theorem lowerParamsE_length (enc : StrEnc) (R : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List PTy) (vs : List PVal),
      Returns (lowerParamsE M enc R ps vs) fun xs => xs.length = (flatParams ps).length
  | [], [] => returns_pure rfl
  | t :: ts, v :: vs => by
    refine returns_bind (lowerParamE_length M enc R t v) fun a ha =>
      returns_bind (lowerParamsE_length enc R ts vs) fun b hb => returns_pure ?_
    simp only [flatParams, List.length_append, ha, hb]
  | [], _ :: _ | _ :: _, [] => returns_fail

end Silmaril.Wasm.Jco
