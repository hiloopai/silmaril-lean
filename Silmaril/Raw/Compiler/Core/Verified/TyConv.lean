module

public import Silmaril.Compiler.Core.Verified.ConvInt.Defs
public import Silmaril.Compiler.Core.Verified.TyActions.Defs
public import Silmaril.Compiler.Core.Source.PureEvalExt.Defs
/-! # Conversions to every supported integer type

A conversion of the integer `n` to the supported type `ity` (`TyActions.supported`) is the
wrap-around `cv ity n = wrap lo hi n` into its bounds: `n` itself when the type holds it
(`cv_of_fits`), always a value of the type (`cv_fits`). Cerberus computes it in three places:

* the primitive `conv_int` (`PEconv_int`, the guards of `+` and `-`): `primitive_conv`;
* std.core's `conv_int(ty, n)`: `if ty = _Bool then … else if is_representable_integer(n, ty)
  then n else if is_unsigned(ty) then wrapI(ty, n) else
  Integer__conv_nonrepresentable_signed_integer(ty, n)`, where the implementation's rule is
  `wrapI(ty, n)` and std.core's `wrapI(ty, n)` is `let dlt = ivmax(ty) - ivmin(ty) + 1 in let
  r = n rem_f dlt in if r <= ivmax(ty) then r else r - dlt`;
* std.core's `conv_loaded_int(ty, v)`, which applies `conv_int` to a specified value.

`isConv file c` / `isConvLoaded file s` check syntactically that the functions named `c`, `s`
(and every callee) have std.core's shape, comparing symbols by key; `conv_ev` and
`convLoaded_ev` evaluate them (`PureEvalExt.Ev`) to `cv ity n`. Nothing is evaluated at
compile time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyConv

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (runtimeValue functionBody primitive extendEnv selectCase
  matchPattern integer boolean wrap)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open ConvInt (Pure Fun lookupFun isRepresentable functionBody_eq lookup_two_first
  lookup_two_second lookup_one lookup_one_other)
open TyActions (supported width signed bounds Fits)

/-! ## Values -/

/-- The conversion of `n` to `ity`: the wrap-around into its bounds. -/
def cv (ity : IntegerType) (n : Int) : Int := wrap (bounds ity).1 (bounds ity).2 n

/-- The modulus of a type. -/
abbrev modulus (ity : IntegerType) : Int := 256 ^ width ity

theorem modulus_pos (ity : IntegerType) : 0 < modulus ity := by positivity

theorem modulus_even {ity : IntegerType} (h : supported ity = true) :
    modulus ity / 2 * 2 = modulus ity := by
  have hw := TyActions.width_pos h
  obtain ⟨k, hk⟩ : ∃ k, width ity = k + 1 := ⟨width ity - 1, by omega⟩
  unfold modulus
  rw [hk, pow_succ]
  omega

theorem bounds_eq {ity : IntegerType} (h : supported ity = true) :
    bounds ity = if signed ity then (-(modulus ity / 2), modulus ity / 2 - 1)
      else (0, modulus ity - 1) := by
  have he := modulus_even h
  unfold bounds Mem.Concrete.representationBounds
  cases signed ity
  · rfl
  · simp only [↓reduceIte]
    change (-modulus ity / 2, modulus ity / 2 - 1) = _
    congr 1
    omega

theorem bounds_span {ity : IntegerType} (h : supported ity = true) :
    (bounds ity).2 - (bounds ity).1 + 1 = modulus ity := by
  have he := modulus_even h
  rw [bounds_eq h]
  cases signed ity <;> simp; omega

theorem bounds_lo_le {ity : IntegerType} (h : supported ity = true) : (bounds ity).1 ≤ 0 := by
  have := modulus_pos ity
  rw [bounds_eq h]
  cases signed ity <;> simp; omega

instance (ity : IntegerType) (n : Int) : Decidable (Fits ity n) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem fits_iff {ity : IntegerType} {n : Int} :
    Fits ity n ↔ (bounds ity).1 ≤ n ∧ n ≤ (bounds ity).2 := Iff.rfl

/-- The wrap-around is a value of the type. -/
theorem cv_fits {ity : IntegerType} (h : supported ity = true) (n : Int) : Fits ity (cv ity n) := by
  rw [fits_iff]
  have sp := bounds_span h
  have pos := modulus_pos ity
  have he := modulus_even h
  unfold cv wrap
  simp only [sp]
  have r0 := Int.emod_nonneg n (show modulus ity ≠ 0 by omega)
  have r1 := Int.emod_lt_of_pos n pos
  rw [bounds_eq h] at sp ⊢
  cases signed ity <;> simp only [Bool.false_eq_true, ↓reduceIte] at sp ⊢ <;> split <;> omega

/-- A value of the type is its own wrap-around. -/
theorem cv_of_fits {ity : IntegerType} (h : supported ity = true) {n : Int} (hn : Fits ity n) :
    cv ity n = n := by
  rw [fits_iff] at hn
  have sp := bounds_span h
  have pos := modulus_pos ity
  have he := modulus_even h
  unfold cv wrap
  simp only [sp]
  rw [bounds_eq h] at hn ⊢
  cases hsg : signed ity
  · simp only [hsg, Bool.false_eq_true, ↓reduceIte] at hn ⊢
    rw [Int.emod_eq_of_lt hn.1 (by omega)]
    simp only [ite_eq_left_iff, not_le]
    omega
  · simp only [hsg, ↓reduceIte] at hn ⊢
    by_cases hneg : n < 0
    · have e : n % modulus ity = n + modulus ity := by
        rw [Int.emod_eq_add_self_emod]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [e, ite_eq_right (by omega)]
      ring
    · have e : n % modulus ity = n := Int.emod_eq_of_lt (by omega) (by omega)
      rw [e, ite_eq_left (by omega)]

/-- The wrap-around is congruent to the value. -/
theorem cv_emod {ity : IntegerType} (h : supported ity = true) (n : Int) :
    cv ity n % modulus ity = n % modulus ity := by
  have sp := bounds_span h
  unfold cv wrap
  simp only [sp]
  split
  · exact Int.emod_emod_of_dvd _ (dvd_refl _)
  · rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _),
      Int.emod_emod_of_dvd _ (dvd_refl _)]

theorem fits_zero {ity : IntegerType} (h : supported ity = true) : Fits ity 0 := by
  rw [fits_iff, bounds_eq h]
  have he := modulus_even h
  have hm : 256 ≤ modulus ity := by
    have := TyActions.width_pos h
    unfold modulus
    calc (256 : Int) = 256 ^ 1 := by norm_num
      _ ≤ 256 ^ width ity := pow_le_pow_right₀ (by norm_num) this
  cases signed ity <;> simp <;> omega

/-! ## The primitive -/

theorem not_bool {ity : IntegerType} (h : supported ity = true) : ity ≠ .bool := by
  rintro rfl; simp [supported] at h

theorem primitive_conv {ity : IntegerType} (h : supported ity = true) (n : Int)
    (tags : Mem.Concrete.Tags) :
    primitive (.conv ity) [.object (.integer n)] tags = .ok (.object (.integer (cv ity n))) := by
  have hb := TyActions.registeredBounds h tags
  have nb := not_bool h
  simp only [primitive, hb]
  simp only [pure, Except.pure, integer]
  have : (ity == .bool) = false := by simpa using nb
  rw [this]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 3
  split
  · rename_i hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact (cv_of_fits h hr).symm
  · rfl

/-! ## std.core's functions -/

/-- std.core's `wrapI(ty, n)`. -/
def wrapFun : Fun → Bool
  | .function _ [(ty, _), (n, _)]
      (.mk _ () (.let_ (.mk _ (.base (some dlt, _)))
        (.mk _ () (.op .add
          (.mk _ () (.op .sub (.mk _ () (.ctor .ivMax [.mk _ () (.sym ty₁)]))
            (.mk _ () (.ctor .ivMin [.mk _ () (.sym ty₂)]))))
          (.mk _ () (.val (.object (.integer 1))))))
        (.mk _ () (.let_ (.mk _ (.base (some r, _)))
          (.mk _ () (.op .remF (.mk _ () (.sym n₁)) (.mk _ () (.sym dlt₁))))
          (.mk _ () (.if_ (.mk _ () (.op .le (.mk _ () (.sym r₁))
              (.mk _ () (.ctor .ivMax [.mk _ () (.sym ty₃)]))))
            (.mk _ () (.sym r₂))
            (.mk _ () (.op .sub (.mk _ () (.sym r₃)) (.mk _ () (.sym dlt₂)))))))))) =>
      decide (n.key ≠ ty.key ∧ ty₁.key = ty.key ∧ ty₂.key = ty.key ∧ ty₃.key = ty.key ∧
        n₁.key = n.key ∧ dlt₁.key = dlt.key ∧ dlt₂.key = dlt.key ∧ r₁.key = r.key ∧
        r₂.key = r.key ∧ r₃.key = r.key ∧ dlt.key ≠ ty.key ∧ dlt.key ≠ n.key ∧
        r.key ≠ ty.key ∧ r.key ≠ dlt.key)
  | _ => false

/-- The symbol `w` names std.core's `wrapI`. -/
def isWrap (file : File Codec.wireModel Unit Unit) (w : Sym) : Bool :=
  match lookupFun file w with
  | some d => wrapFun d
  | none => false

/-- The implementation constant `c` is a function `(ty, n) ↦ wrapI(ty, n)`. -/
def implWrap (file : File Codec.wireModel Unit Unit) (c : ImplementationConstant) : Bool :=
  match file.impl.lookup c with
  | some (.function _ [(ty, _), (n, _)]
      (.mk _ () (.call (.sym w) [.mk _ () (.sym ty₁), .mk _ () (.sym n₁)]))) =>
      decide (n.key ≠ ty.key ∧ ty₁.key = ty.key ∧ n₁.key = n.key) && isWrap file w
  | _ => false

/-- std.core's `conv_int(ty, n)`, every branch. -/
def convFun (file : File Codec.wireModel Unit Unit) : Fun → Bool
  | .function _ [(ty, _), (n, _)]
      (.mk _ () (.if_
        (.mk _ () (.op .eq (.mk _ () (.sym ty₁)) (.mk _ () (.val (.ctype (.mk _ (.basic (.integer .bool))))))))
        _
        (.mk _ () (.if_
          (.mk _ () (.call (.sym r) [.mk _ () (.sym n₁), .mk _ () (.sym ty₂)]))
          (.mk _ () (.sym n₂))
          (.mk _ () (.if_ (.mk _ () (.isUnsigned (.mk _ () (.sym ty₃))))
            (.mk _ () (.call (.sym w) [.mk _ () (.sym ty₄), .mk _ () (.sym n₃)]))
            (.mk _ () (.call (.impl c) [.mk _ () (.sym ty₅), .mk _ () (.sym n₄)])))))))) =>
      decide (n.key ≠ ty.key ∧ ty₁.key = ty.key ∧ ty₂.key = ty.key ∧ ty₃.key = ty.key ∧
        ty₄.key = ty.key ∧ ty₅.key = ty.key ∧ n₁.key = n.key ∧ n₂.key = n.key ∧
        n₃.key = n.key ∧ n₄.key = n.key) &&
      (match lookupFun file r with
       | some d => isRepresentable d
       | none => false) &&
      isWrap file w && implWrap file c
  | _ => false

/-- The symbol `c` names std.core's `conv_int`. -/
def isConv (file : File Codec.wireModel Unit Unit) (c : Sym) : Bool :=
  match lookupFun file c with
  | some d => convFun file d
  | none => false

/-- std.core's `conv_loaded_int(ty, v)` on a specified value. -/
def convLoadedFun (file : File Codec.wireModel Unit Unit) : Fun → Bool
  | .function _ [(ty, _), (v, _)]
      (.mk _ () (.case_ (.mk _ () (.sym v₁))
        ((.mk _ (.ctor .specified [.mk _ (.base (some n, _))]),
          .mk _ () (.ctor .specified
            [.mk _ () (.call (.sym c) [.mk _ () (.sym ty₁), .mk _ () (.sym n₁)])])) :: _))) =>
      decide (v.key ≠ ty.key ∧ n.key ≠ ty.key ∧ v₁.key = v.key ∧ ty₁.key = ty.key ∧
        n₁.key = n.key) && isConv file c
  | _ => false

/-- The symbol `s` names std.core's `conv_loaded_int`. -/
def isConvLoaded (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => convLoadedFun file d
  | none => false

/-! ## Evaluations -/

variable {file : Dynamics.Program} {tags : Mem.Concrete.Tags}

theorem lookup_ext {a : Sym} {x : Dynamics.Val} {env : Dynamics.Env} {s : Sym} (h : s.key = a.key) :
    (extendEnv [(a, x)] env).lookup s = some x := lookup_one h

theorem bound_eval {ity : IntegerType} (hs : supported ity = true) (ann : List Annot)
    (max : Bool) {env : Dynamics.Env} {ty : Sym} (hty : env.lookup ty = some (.ctype (Mem.Concrete.tyType ann ity)))
    {a b : List Annot} :
    Ev file tags env (.inl (.mk a () (.ctor (if max then .ivMax else .ivMin) [.mk b () (.sym ty)])))
      (.inl (.object (.integer (if max then (bounds ity).2 else (bounds ity).1)))) := by
  refine .ctor (.cons (.sym hty) .nil) ?_
  cases max <;>
    simp [primitive, Mem.Concrete.tyType, Dynamics.intType, TyActions.registeredBounds hs, integer] <;>
    rfl

/-- `wrapI(ty, n)` is the wrap-around. -/
theorem wrap_ev {w : Sym} (hw : isWrap file w = true) {ity : IntegerType} (hs : supported ity = true)
    {ann : List Annot} {n : Int} {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Ev file tags env (.inr args) (.inr [.ctype (Mem.Concrete.tyType ann ity), .object (.integer n)])) :
    Ev file tags env (.inl (.mk a () (.call (.sym w) args))) (.inl (.object (.integer (cv ity n)))) := by
  unfold isWrap at hw
  split at hw
  · rename_i d hl
    unfold wrapFun at hw
    split at hw
    · rename_i _ ty _ nn _ _ _ dlt _ _ _ _ _ ty₁ _ _ ty₂ _ _ _ r _ _ _ n₁ _ dlt₁ _ _ _ r₁ _ _ ty₃ _ r₂
        _ _ r₃ _ dlt₂
      simp only [decide_eq_true_eq] at hw
      obtain ⟨ne, e1, e2, e3, e4, e5, e6, e7, e8, e9, d1, d2, d3, d4⟩ := hw
      refine .call hargs (functionBody_eq hl rfl) ?_
      let T : Dynamics.Val := .ctype (Mem.Concrete.tyType ann ity)
      let env₀ : Dynamics.Env := extendEnv [(ty, T), (nn, .object (.integer n))] ∅
      have lty₀ : ∀ {s : Sym}, s.key = ty.key → env₀.lookup s = some T := fun h => lookup_two_first h
      have ln₀ : ∀ {s : Sym}, s.key = nn.key → env₀.lookup s = some (.object (.integer n)) :=
        fun h => lookup_two_second h ne
      let D : Int := (bounds ity).2 - (bounds ity).1 + 1
      have hD : D = modulus ity := bounds_span hs
      let env₁ : Dynamics.Env := extendEnv [(dlt, .object (.integer D))] env₀
      have lty₁ : ∀ {s : Sym}, s.key = ty.key → env₁.lookup s = some T := fun h => by
        rw [lookup_one_other (by rw [h]; exact Ne.symm d1)]; exact lty₀ h
      have ln₁ : ∀ {s : Sym}, s.key = nn.key → env₁.lookup s = some (.object (.integer n)) := fun h => by
        rw [lookup_one_other (by rw [h]; exact Ne.symm d2)]; exact ln₀ h
      have ld₁ : ∀ {s : Sym}, s.key = dlt.key → env₁.lookup s = some (.object (.integer D)) :=
        fun h => lookup_one h
      let R : Int := n % D
      let env₂ : Dynamics.Env := extendEnv [(r, .object (.integer R))] env₁
      have lty₂ : ∀ {s : Sym}, s.key = ty.key → env₂.lookup s = some T := fun h => by
        rw [lookup_one_other (by rw [h]; exact Ne.symm d3)]; exact lty₁ h
      have ld₂ : ∀ {s : Sym}, s.key = dlt.key → env₂.lookup s = some (.object (.integer D)) := fun h => by
        rw [lookup_one_other (by rw [h]; exact Ne.symm d4)]; exact ld₁ h
      have lr₂ : ∀ {s : Sym}, s.key = r.key → env₂.lookup s = some (.object (.integer R)) :=
        fun h => lookup_one h
      have hpos : 0 < D := by rw [hD]; exact modulus_pos ity
      refine .let_ (x := .object (.integer D)) ?_ rfl ?_
      · refine .op (vs := [.object (.integer ((bounds ity).2 - (bounds ity).1)), .object (.integer 1)])
          (.cons ?_ (.cons .val .nil)) (by simp [primitive, Dynamics.integerBin, integer]; rfl)
        refine .op (vs := [.object (.integer (bounds ity).2), .object (.integer (bounds ity).1)])
          (.cons (bound_eval hs ann true (lty₀ e1)) (.cons (bound_eval hs ann false (lty₀ e2)) .nil))
          (by simp [primitive, Dynamics.integerBin, integer]; rfl)
      · refine .let_ (x := .object (.integer R)) ?_ rfl ?_
        · refine .op (.cons (.sym (ln₁ e4)) (.cons (.sym (ld₁ e5)) .nil)) ?_
          simp [primitive, Dynamics.integerBin, integer, hpos, R]; rfl
        · have hv : cv ity n = if R ≤ (bounds ity).2 then R else R - D := rfl
          by_cases hle : R ≤ (bounds ity).2
          · rw [hv, ite_eq_left hle]
            refine .ifTrue (.op (.cons (.sym (lr₂ e7)) (.cons (bound_eval hs ann true (lty₂ e3)) .nil))
              ?_) (.sym (lr₂ e8))
            simp [primitive, Dynamics.integerBin, boolean, hle]; rfl
          · rw [hv, ite_eq_right hle]
            refine .ifFalse (.op (.cons (.sym (lr₂ e7)) (.cons (bound_eval hs ann true (lty₂ e3)) .nil))
              ?_) ?_
            · simp [primitive, Dynamics.integerBin, boolean, hle]; rfl
            refine .op (.cons (.sym (lr₂ e9)) (.cons (.sym (ld₂ e6)) .nil)) ?_
            simp [primitive, Dynamics.integerBin, integer]; rfl
    · cases hw
  · cases hw

theorem functionBody_impl {c : ImplementationConstant} {bt : BaseType}
    {params : List (Sym × BaseType)} {body : Pure} {vs : List Dynamics.Val}
    (h : file.impl.lookup c = some (.function bt params body)) (hl : params.length = vs.length) :
    functionBody file (.impl c) vs = .ok (body, extendEnv ((params.map Prod.fst).zip vs) ∅) := by
  simp [functionBody, h, hl, bind, Except.bind, pure, Except.pure]

/-- The implementation's rule for a signed type is the wrap-around. -/
theorem implWrap_ev {c : ImplementationConstant} (hc : implWrap file c = true) {ity : IntegerType}
    (hs : supported ity = true)
    {ann : List Annot} {n : Int} {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Ev file tags env (.inr args) (.inr [.ctype (Mem.Concrete.tyType ann ity), .object (.integer n)])) :
    Ev file tags env (.inl (.mk a () (.call (.impl c) args))) (.inl (.object (.integer (cv ity n)))) := by
  unfold implWrap at hc
  split at hc
  · rename_i _ ty _ nn _ _ w _ ty₁ _ n₁ hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨ne, e1, e2⟩, hw⟩ := hc
    refine .call hargs (functionBody_impl hl rfl) ?_
    exact wrap_ev hw hs (.cons (.sym (lookup_two_first e1)) (.cons (.sym (lookup_two_second e2 ne)) .nil))
  · cases hc

/-- `is_representable_integer(n, ty)` decides the bounds. -/
theorem isRepresentable_ev {r : Sym} {d : Fun} (hl : lookupFun file r = some d)
    (hd : isRepresentable d = true) {ity : IntegerType} (hs : supported ity = true) {n : Int}
    {ann : List Annot} {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Ev file tags env (.inr args) (.inr [.object (.integer n), .ctype (Mem.Concrete.tyType ann ity)]))
    {b : Bool} (hb : decide (Fits ity n) = b) :
    Ev file tags env (.inl (.mk a () (.call (.sym r) args))) (.inl (boolean b)) := by
  subst hb
  unfold isRepresentable at hd
  split at hd
  · rename_i _ _ nn _ ty _ _ _ _ _ ty₁ _ n₁ _ _ n₂ _ _ ty₂
    simp only [decide_eq_true_eq] at hd
    obtain ⟨ne, e1, e2, e3, e4⟩ := hd
    refine .call hargs (functionBody_eq hl rfl) ?_
    have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(nn, (.object (.integer n) : Dynamics.Val)),
        (ty, .ctype (Mem.Concrete.tyType ann ity))] ∅ : Dynamics.Env).lookup s =
          some (.ctype (Mem.Concrete.tyType ann ity)) :=
      fun h => lookup_two_second h (Ne.symm ne)
    have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(nn, (.object (.integer n) : Dynamics.Val)),
        (ty, .ctype (Mem.Concrete.tyType ann ity))] ∅ : Dynamics.Env).lookup s =
          some (.object (.integer n)) :=
      fun h => lookup_two_first h
    refine .op (vs := [boolean (decide ((bounds ity).1 ≤ n)), boolean (decide (n ≤ (bounds ity).2))])
      (.cons (.op (.cons (bound_eval hs ann false (lty e1)) (.cons (.sym (ln e3)) .nil)) ?_)
        (.cons (.op (.cons (.sym (ln e4)) (.cons (bound_eval hs ann true (lty e2)) .nil)) ?_) .nil)) ?_
    · simp [primitive, Dynamics.integerBin]; rfl
    · simp [primitive, Dynamics.integerBin]; rfl
    · have hf : decide (Fits ity n) = (decide ((bounds ity).1 ≤ n) && decide (n ≤ (bounds ity).2)) := by
        simp [fits_iff]
      rw [hf]
      by_cases ha : (bounds ity).1 ≤ n <;> by_cases hb : n ≤ (bounds ity).2 <;>
        simp [primitive, boolean, ha, hb] <;> rfl
  · cases hd

theorem tyType_ne_bool {ity : IntegerType} (hs : supported ity = true) (ann ann' : List Annot)
    (tags : Mem.Concrete.Tags) :
    primitive (.bin .eq) [.ctype (Mem.Concrete.tyType ann ity),
      .ctype (.mk ann' (.basic (.integer .bool)))] tags = .ok .false := by
  have nb := not_bool hs
  have : (ity == .bool) = false := by simpa using nb
  simp [primitive, Mem.Concrete.tyType, Dynamics.intType, TyActions.registeredBounds hs,
    ConvInt.bounds_bool, boolean, this]
  rfl

theorem isUnsigned_prim {ity : IntegerType} (hs : supported ity = true) (ann : List Annot)
    (tags : Mem.Concrete.Tags) :
    primitive (.isType 3) [.ctype (Mem.Concrete.tyType ann ity)] tags = .ok (boolean (!signed ity)) := by
  have hl := Mem.Concrete.registeredIntegerLayout_of (TyActions.layout_of hs) tags
  simp [primitive, Mem.Concrete.tyType, Dynamics.intType, TyActions.registeredBounds hs, hl]
  rfl

/-- **std.core's `conv_int(ty, n)`** is the wrap-around. -/
theorem conv_ev {c : Sym} (hc : isConv file c = true) {ity : IntegerType}
    (hs : supported ity = true) {ann : List Annot} {n : Int} {env : Dynamics.Env} {a : List Annot}
    {args : List Pure}
    (hargs : Ev file tags env (.inr args) (.inr [.ctype (Mem.Concrete.tyType ann ity), .object (.integer n)])) :
    Ev file tags env (.inl (.mk a () (.call (.sym c) args))) (.inl (.object (.integer (cv ity n)))) := by
  unfold isConv at hc
  split at hc
  · rename_i d hl
    unfold convFun at hc
    split at hc
    · rename_i _ ty _ nn _ _ _ _ ty₁ _ _ _ _ _ r _ n₁ _ ty₂ _ n₂ _ _ _ ty₃ _ w _ ty₄ _ n₃ _ ci _ ty₅ _ n₄
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨ne, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩, hr⟩, hw⟩, hi⟩ := hc
      refine .call hargs (functionBody_eq hl rfl) ?_
      let T : Dynamics.Val := .ctype (Mem.Concrete.tyType ann ity)
      have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(ty, T), (nn, .object (.integer n))] ∅ :
          Dynamics.Env).lookup s = some T := fun h => lookup_two_first h
      have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(ty, T), (nn, .object (.integer n))] ∅ :
          Dynamics.Env).lookup s = some (.object (.integer n)) := fun h => lookup_two_second h ne
      refine .ifFalse (.op (.cons (.sym (lty e1)) (.cons .val .nil)) (tyType_ne_bool hs ann _ tags)) ?_
      split at hr
      · rename_i dr hlr
        by_cases hf : Fits ity n
        · rw [cv_of_fits hs hf]
          exact .ifTrue (isRepresentable_ev (b := true) hlr hr hs
            (.cons (.sym (ln e6)) (.cons (.sym (lty e2)) .nil)) (by simp [hf])) (.sym (ln e7))
        · refine .ifFalse (isRepresentable_ev (b := false) hlr hr hs
            (.cons (.sym (ln e6)) (.cons (.sym (lty e2)) .nil)) (by simp [hf])) ?_
          cases hsg : signed ity
          · exact .ifTrue (.isUnsigned (.cons (.sym (lty e3)) .nil)
                (by rw [isUnsigned_prim hs ann tags, hsg]; rfl))
              (wrap_ev hw hs (.cons (.sym (lty e4)) (.cons (.sym (ln e8)) .nil)))
          · exact .ifFalse (.isUnsigned (.cons (.sym (lty e3)) .nil)
                (by rw [isUnsigned_prim hs ann tags, hsg]; rfl))
              (implWrap_ev hi hs (.cons (.sym (lty e5)) (.cons (.sym (ln e9)) .nil)))
      · cases hr
    · cases hc
  · cases hc

/-- **std.core's `conv_loaded_int(ty, Specified n)`** is `Specified` of the wrap-around. -/
theorem convLoaded_ev {s : Sym} (hs' : isConvLoaded file s = true) {ity : IntegerType}
    (hs : supported ity = true) {n : Int} {ann : List Annot} {env : Dynamics.Env} {a : List Annot}
    {args : List Pure}
    (hargs : Ev file tags env (.inr args)
      (.inr [.ctype (Mem.Concrete.tyType ann ity), .loaded (.specified (.integer n))])) :
    Ev file tags env (.inl (.mk a () (.call (.sym s) args)))
      (.inl (.loaded (.specified (.integer (cv ity n))))) := by
  unfold isConvLoaded at hs'
  split at hs'
  · rename_i d hl
    unfold convLoadedFun at hs'
    split at hs'
    · rename_i _ _ ty _ v _ _ _ v₁ _ _ nn _ _ _ c _ ty₁ _ n₁ _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs'
      obtain ⟨⟨ne, ne', e1, e2, e3⟩, hc⟩ := hs'
      refine .call hargs (functionBody_eq hl rfl) ?_
      let env' : Dynamics.Env := extendEnv [(ty, (.ctype (Mem.Concrete.tyType ann ity) : Dynamics.Val)),
        (v, .loaded (.specified (.integer n)))] ∅
      have lv : env'.lookup v₁ = some (.loaded (.specified (.integer n))) :=
        lookup_two_second e1 ne
      refine .case_ (.sym lv) (by simp [selectCase, matchPattern]; exact ⟨rfl, rfl⟩) ?_
      refine .ctor (vs := [.object (.integer (cv ity n))]) (.cons ?_ .nil) (by simp [primitive]; rfl)
      refine conv_ev (ann := ann) hc hs (.cons (.sym ?_) (.cons (.sym ?_) .nil))
      · rw [lookup_one_other (by rw [e2]; exact Ne.symm ne')]
        exact lookup_two_first e2
      · exact lookup_one e3
    · cases hs'
  · cases hs'

end Silmaril.Compile.Core.Verified.TyConv
