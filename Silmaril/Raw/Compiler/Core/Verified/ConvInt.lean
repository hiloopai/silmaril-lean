module

public import Silmaril.Compiler.Core.Source.PureEval.Defs

/-! # `conv_loaded_int(int, n)` on a representable `n`

Every C `int` store and `return` elaborates to a call of std.core's
`conv_loaded_int(ty, v)`, which calls `conv_int(ty, n)`, which calls
`is_representable_integer(n, ty)`. These are ordinary pure functions of the document
(`File.stdlib`), so the compiler cannot assume their meaning: `convLoadedInt? file s` checks,
syntactically, that the function named `s` has std.core's shape (the branch that matters for a
specified integer, through the two callees), comparing symbols by key as Core maps do. It
evaluates nothing.

`convLoadedInt_eval`: for such a document, `conv_loaded_int(int, Specified n)` evaluates to
`Specified n` when `n` is an `int` (`Eval`, hence a run of the Core machine by
`PureEval.Eval.sound`), in any environment that binds the operand symbol to `Specified n`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ConvInt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (runtimeValue functionBody primitive extendEnv selectCase
  matchPattern integer boolean)
open Silmaril.Cerberus.Core.PureEval

/-- Pure expressions and functions of decoded documents (spelled out: the compiler's closure
must not name the dynamics). -/
abbrev Pure := Pexpr Codec.wireModel Unit Sym
abbrev Fun := FunDecl Codec.wireModel Unit Unit

/-- std.core's `is_representable_integer(n, ty)`:
`ivmin(ty) <= n && n <= ivmax(ty)`. -/
def isRepresentable : Fun → Bool
  | .function _ [(n, _), (ty, _)]
      (.mk _ () (.op .and
        (.mk _ () (.op .le (.mk _ () (.ctor .ivMin [.mk _ () (.sym ty₁)])) (.mk _ () (.sym n₁))))
        (.mk _ () (.op .le (.mk _ () (.sym n₂)) (.mk _ () (.ctor .ivMax [.mk _ () (.sym ty₂)])))))) =>
      decide (n.key ≠ ty.key ∧ ty₁.key = ty.key ∧ ty₂.key = ty.key ∧ n₁.key = n.key ∧
        n₂.key = n.key)
  | _ => false

/-- The pure function a `Sym` names, as `functionBody` finds it (std.core first). -/
def lookupFun (file : File Codec.wireModel Unit Unit) (s : Sym) : Option Fun :=
  match file.stdlib.lookup s with
  | some d => some d
  | none => file.funs.lookup s

/-- std.core's `conv_int(ty, n)` on its non-`_Bool`, representable path:
`if ty = _Bool then … else if is_representable_integer(n, ty) then n else …`. -/
def convInt (file : File Codec.wireModel Unit Unit) : Fun → Bool
  | .function _ [(ty, _), (n, _)]
      (.mk _ () (.if_
        (.mk _ () (.op .eq (.mk _ () (.sym ty₁)) (.mk _ () (.val (.ctype (.mk _ (.basic (.integer .bool))))))))
        _
        (.mk _ () (.if_
          (.mk _ () (.call (.sym r) [.mk _ () (.sym n₁), .mk _ () (.sym ty₂)]))
          (.mk _ () (.sym n₂))
          _)))) =>
      decide (n.key ≠ ty.key ∧ ty₁.key = ty.key ∧ ty₂.key = ty.key ∧ n₁.key = n.key ∧
        n₂.key = n.key) &&
      (match lookupFun file r with
       | some d => isRepresentable d
       | none => false)
  | _ => false

/-- std.core's `conv_loaded_int(ty, v)` on a specified value:
`case v of Specified(n) => Specified(conv_int(ty, n)) | …`. -/
def convLoadedInt (file : File Codec.wireModel Unit Unit) : Fun → Bool
  | .function _ [(ty, _), (v, _)]
      (.mk _ () (.case_ (.mk _ () (.sym v₁))
        ((.mk _ (.ctor .specified [.mk _ (.base (some n, _))]),
          .mk _ () (.ctor .specified
            [.mk _ () (.call (.sym c) [.mk _ () (.sym ty₁), .mk _ () (.sym n₁)])])) :: _))) =>
      decide (v.key ≠ ty.key ∧ n.key ≠ ty.key ∧ v₁.key = v.key ∧ ty₁.key = ty.key ∧
        n₁.key = n.key) &&
      (match lookupFun file c with
       | some d => convInt file d
       | none => false)
  | _ => false

/-- The symbol `s` names std.core's `conv_loaded_int`. -/
def isConvLoadedInt (file : File Codec.wireModel Unit Unit) (s : Sym) : Bool :=
  match lookupFun file s with
  | some d => convLoadedInt file d
  | none => false

/-! ## Proofs -/

/-- `int`, with any annotations. -/
def intTy (ann : List Annot) : Ctype := .mk ann (.basic (.integer (.signed .int)))

/-- `int` is representable on 32 bits. -/
def IsInt (n : Int) : Prop := -2147483648 ≤ n ∧ n ≤ 2147483647

theorem functionBody_eq {file : Dynamics.Program} {s : Sym} {bt : BaseType}
    {params : List (Sym × BaseType)} {body : Pure} {vs : List Dynamics.Val}
    (h : lookupFun file s = some (.function bt params body)) (hl : params.length = vs.length) :
    functionBody file (.sym s) vs = .ok (body, extendEnv ((params.map Prod.fst).zip vs) ∅) := by
  unfold lookupFun at h
  cases hs : file.stdlib.lookup s with
  | none =>
    simp only [hs] at h
    simp [functionBody, hs, h, hl, bind, Except.bind, pure, Except.pure]
  | some d' =>
    simp only [hs, Option.some.injEq] at h
    subst h
    simp [functionBody, hs, hl, bind, Except.bind, pure, Except.pure]

theorem lookup_two_first {a b : Sym} {x y : Dynamics.Val} {s : Sym} (h : s.key = a.key) :
    (extendEnv [(a, x), (b, y)] ∅ : Dynamics.Env).lookup s = some x := by
  have : MapKey.key s = MapKey.key a := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [this, Finmap.lookup_insert]

theorem lookup_two_second {a b : Sym} {x y : Dynamics.Val} {s : Sym} (h : s.key = b.key)
    (ne : b.key ≠ a.key) : (extendEnv [(a, x), (b, y)] ∅ : Dynamics.Env).lookup s = some y := by
  have hs : MapKey.key s ≠ MapKey.key a := by
    change s.key ≠ a.key
    rw [h]; exact ne
  have : MapKey.key s = MapKey.key b := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [Finmap.lookup_insert_of_ne _ hs, this, Finmap.lookup_insert]

theorem lookup_one {a : Sym} {x : Dynamics.Val} {env : Dynamics.Env} {s : Sym} (h : s.key = a.key) :
    (extendEnv [(a, x)] env).lookup s = some x := by
  have : MapKey.key s = MapKey.key a := h
  simp only [extendEnv, List.foldr, Map.lookup, Map.insert]
  rw [this, Finmap.lookup_insert]

theorem lookup_one_other {a : Sym} {x : Dynamics.Val} {env : Dynamics.Env} {s : Sym}
    (h : s.key ≠ a.key) : (extendEnv [(a, x)] env).lookup s = env.lookup s := by
  have : MapKey.key s ≠ MapKey.key a := h
  simp [extendEnv, Map.lookup, Map.insert, Finmap.lookup_insert_of_ne _ this]

variable {file : Dynamics.Program} {tags : Mem.Concrete.Tags}

/-- The bounds of `int` do not depend on the tag environment. -/
theorem bounds_int (tags : Mem.Concrete.Tags) :
    Mem.Concrete.registeredIntegerBounds tags (.signed .int) = some (-2147483648, 2147483647) := by
  simp [Mem.Concrete.registeredIntegerBounds, Mem.Concrete.registeredInteger,
    Mem.Concrete.integerBounds, Mem.Concrete.integerLayout, Mem.Concrete.baseWidth]

theorem bounds_bool (tags : Mem.Concrete.Tags) :
    Mem.Concrete.registeredIntegerBounds tags .bool = some (0, 255) := by
  simp [Mem.Concrete.registeredIntegerBounds, Mem.Concrete.registeredInteger,
    Mem.Concrete.integerBounds, Mem.Concrete.integerLayout]

/-- `is_representable_integer(n, int)` is `true` for an `int` `n`. -/
theorem isRepresentable_eval {r : Sym} {d : Fun} (hl : lookupFun file r = some d)
    (hd : isRepresentable d = true) {n : Int} (hn : IsInt n) {ann : List Annot}
    {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Eval file tags env (.inr args) (.inr [.object (.integer n), .ctype (intTy ann)])) :
    Eval file tags env (.inl (.mk a () (.call (.sym r) args))) (.inl .true) := by
  unfold isRepresentable at hd
  split at hd
  · rename_i _ _ nn _ ty _ _ _ _ _ ty₁ _ n₁ _ _ n₂ _ _ ty₂
    simp only [decide_eq_true_eq] at hd
    obtain ⟨ne, e1, e2, e3, e4⟩ := hd
    refine .call hargs (functionBody_eq hl rfl) ?_
    have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(nn, Value.object (.integer n)),
        (ty, .ctype (intTy ann))] ∅ : Dynamics.Env).lookup s = some (.ctype (intTy ann)) :=
      fun h => lookup_two_second h (Ne.symm ne)
    have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(nn, Value.object (.integer n)),
        (ty, .ctype (intTy ann))] ∅ : Dynamics.Env).lookup s = some (.object (.integer n)) :=
      fun h => lookup_two_first h
    obtain ⟨lo, hi⟩ := hn
    refine .op (vs := [.true, .true]) (.cons ?_ (.cons ?_ .nil)) (by simp [primitive]; rfl)
    · refine .op (vs := [.object (.integer (-2147483648)), .object (.integer n)])
        (.cons (.ctor (.cons (.sym (lty e1)) .nil) ?_) (.cons (.sym (ln e3)) .nil)) ?_
      · simp [primitive, intTy, Dynamics.intType, bounds_int, integer]; rfl
      · simp [primitive, Dynamics.integerBin, boolean, lo]; rfl
    · refine .op (vs := [.object (.integer n), .object (.integer 2147483647)])
        (.cons (.sym (ln e4)) (.cons (.ctor (.cons (.sym (lty e2)) .nil) ?_) .nil)) ?_
      · simp [primitive, intTy, Dynamics.intType, bounds_int, integer]; rfl
      · simp [primitive, Dynamics.integerBin, boolean, hi]; rfl
  · cases hd

/-- `conv_int(int, n)` is `n` for an `int` `n`. -/
theorem convInt_eval {c : Sym} {d : Fun} (hl : lookupFun file c = some d)
    (hd : convInt file d = true) {n : Int} (hn : IsInt n) {ann : List Annot}
    {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Eval file tags env (.inr args) (.inr [.ctype (intTy ann), .object (.integer n)])) :
    Eval file tags env (.inl (.mk a () (.call (.sym c) args))) (.inl (.object (.integer n))) := by
  unfold convInt at hd
  split at hd
  · rename_i _ _ ty _ nn _ _ _ _ ty₁ _ _ _ _ _ r _ n₁ _ ty₂ _ n₂ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨ne, e1, e2, e3, e4⟩, hr⟩ := hd
    split at hr
    · rename_i d' hlr
      refine .call hargs (functionBody_eq hl rfl) ?_
      have lty : ∀ {s : Sym}, s.key = ty.key → (extendEnv [(ty, Value.ctype (intTy ann)),
          (nn, .object (.integer n))] ∅ : Dynamics.Env).lookup s = some (.ctype (intTy ann)) :=
        fun h => lookup_two_first h
      have ln : ∀ {s : Sym}, s.key = nn.key → (extendEnv [(ty, Value.ctype (intTy ann)),
          (nn, .object (.integer n))] ∅ : Dynamics.Env).lookup s = some (.object (.integer n)) :=
        fun h => lookup_two_second h ne
      refine .ifFalse ?_ (.ifTrue (isRepresentable_eval hlr hr hn
        (.cons (.sym (ln e3)) (.cons (.sym (lty e2)) .nil))) (.sym (ln e4)))
      refine .op (vs := [.ctype (intTy ann), .ctype (.mk _ (.basic (.integer .bool)))])
        (.cons (.sym (lty e1)) (.cons .val .nil)) ?_
      simp [primitive, intTy, Dynamics.intType, bounds_int, bounds_bool, boolean]; rfl
    · cases hr
  · cases hd

/-- `conv_loaded_int(int, Specified n)` is `Specified n` for an `int` `n`. -/
theorem convLoadedInt_eval {s : Sym} (hs : isConvLoadedInt file s = true) {n : Int} (hn : IsInt n)
    {ann : List Annot} {env : Dynamics.Env} {a : List Annot} {args : List Pure}
    (hargs : Eval file tags env (.inr args)
      (.inr [.ctype (intTy ann), .loaded (.specified (.integer n))])) :
    Eval file tags env (.inl (.mk a () (.call (.sym s) args)))
      (.inl (.loaded (.specified (.integer n)))) := by
  unfold isConvLoadedInt at hs
  split at hs
  · rename_i d hl
    unfold convLoadedInt at hs
    split at hs
    · rename_i _ _ ty _ v _ _ _ v₁ _ _ nn _ _ _ c _ ty₁ _ n₁ _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨ne, ne', e1, e2, e3⟩, hc⟩ := hs
      split at hc
      · rename_i d' hlc
        refine .call hargs (functionBody_eq hl rfl) ?_
        let env' : Dynamics.Env := extendEnv [(ty, Value.ctype (intTy ann)),
          (v, .loaded (.specified (.integer n)))] ∅
        have lv : env'.lookup v₁ = some (.loaded (.specified (.integer n))) :=
          lookup_two_second e1 ne
        refine .case_ (.sym lv) (by simp [selectCase, matchPattern]; exact ⟨rfl, rfl⟩) ?_
        refine .ctor (vs := [.object (.integer n)]) (.cons ?_ .nil) (by simp [primitive]; rfl)
        refine convInt_eval (ann := ann) hlc hc hn (.cons (.sym ?_) (.cons (.sym ?_) .nil))
        · rw [lookup_one_other (by rw [e2]; exact Ne.symm ne')]
          exact lookup_two_first e2
        · exact lookup_one e3
      · cases hc
    · cases hs
  · cases hs

end Silmaril.Compile.Core.Verified.ConvInt
