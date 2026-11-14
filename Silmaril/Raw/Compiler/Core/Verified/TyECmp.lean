module

public import Silmaril.Compiler.Core.Verified.TyGuard.Defs
public import Silmaril.Compiler.Core.Verified.Cond.Defs
/-! # Relational comparisons as effect-level cases

Cerberus elaborates `e₁ < e₂` (and `<=`, `>`, `>=`) to the `unseq` of the operands bound to
`(a, b)`, then the effect-level case

```
case (a, b) of
| (Specified(x), Specified(y)) => pure(if conv_int(T, x) rel conv_int(T, y) then Specified(1)
                                        else Specified(0))
| _ => pure(Unspecified(int))
```

(where `==` and `!=` use a pure case, `TyGuard.tguard`). `eguard file a b e = some g` recognises
it, `g` a comparison of `TyGuard` (`bodyG`); `eguard_runs` runs it by local steps to
`Specified (g.val n₁ n₂)`, touching only the current location. No arm is undefined
(`eguard_ok`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyECmp

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ReturnLit (Eff)
open ConvInt (Pure)
open TyGuard (G bodyG)
open Guard (operands lookup_pair_first lookup_pair_second)
open IntExpr (spec)
open LoadTask (Touched)

/-- The effect-level comparison over the operand tuple `(a, b)`. -/
def eguard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Eff → Option G
  | .mk _ (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      [(.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]), .mk _ (.pure body)),
        (_, .mk _ (.pure _))]) =>
      if a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key then
        match bodyG file x y body with
        | some (.cmp ity r c₁ c₂) => some (.cmp ity r c₁ c₂)
        | _ => none
      else none
  | _ => none

theorem eguard_ok {file : File Codec.wireModel Unit Unit} {a b : Sym} {e : Eff} {g : G}
    (h : eguard file a b e = some g) (x y : Int) : g.Ok x y := by
  unfold eguard at h
  split at h
  · split at h
    · split at h
      · cases h; trivial
      · cases h
    · cases h
  · cases h

theorem eguard_parts {file : File Codec.wireModel Unit Unit} {a b : Sym} {e : Eff} {g : G}
    (h : eguard file a b e = some g) :
    ∃ (an ann₁ pa pb : List Annot) (a' b' : Sym) (p₁ p₂ : Pattern Sym) (ann₂ ann₃ : List Annot)
      (body q : Pure),
      e = .mk an (.case_ (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')]))
        [(p₁, .mk ann₂ (.pure body)), (p₂, .mk ann₃ (.pure q))]) ∧
      a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧
      ∃ (x y : Sym), y.key ≠ x.key ∧ bodyG file x y body = some g ∧
        ∀ (n₁ n₂ : Int), selectCase (.tuple [spec n₁, spec n₂])
          ([(p₁, .mk ann₂ (.pure body)), (p₂, .mk ann₃ (.pure q))] : List (Pattern Sym × Eff)) =
          some ([(x, .object (.integer n₁)), (y, .object (.integer n₂))], .mk ann₂ (.pure body)) := by
  unfold eguard at h
  split at h
  · rename_i an ann₁ pa a' pb b' tann tx bs x bx ty sann y cy bann body p₂ ann₃ q
    split at h
    · rename_i cond
      obtain ⟨e1, e2, ne, ne'⟩ := cond
      split at h
      · rename_i ity r c₁ c₂ hb
        cases h
        exact ⟨an, ann₁, pa, pb, a', b', _, p₂, bann, ann₃, body, q, rfl, e1, e2, ne, x, y, ne', hb,
          fun n₁ n₂ => by simp [selectCase, matchPattern, matchPatterns]⟩
      · cases h
    · cases h
  · cases h

variable {file : Program} {labels : Labels}

/-- **The comparison** runs by local steps to `Specified (g.val n₁ n₂)`. -/
theorem eguard_runs {a b : Sym} {e : Eff} {g : G} (h : eguard file a b e = some g) (env : Env)
    (n₁ n₂ : Int) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ m', Touched m m' ∧ LocalReaches file labels false
      ⟨.effectExpr e (operands a b n₁ n₂ env), k, m⟩ ⟨.value (spec (g.val n₁ n₂)), k, m'⟩ := by
  obtain ⟨an, ann₁, pa, pb, a', b', p₁, p₂, bann, ann₃, body, q, rfl, e1, e2, ne, x, y, ne', hb, hsel⟩ :=
    eguard_parts h
  let bs : List (Pattern Sym × Eff) := [(p₁, .mk bann (.pure body)), (p₂, .mk ann₃ (.pure q))]
  let env₁ := operands a b n₁ n₂ env
  let SCR : Pure := .mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')])
  obtain ⟨l, hr⟩ := Cond.requestAux_case (file := file) (labels := labels) m an SCR bs env₁ k false
  obtain ⟨l₁, s₁⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr _ env₁) (by simpa using hr)
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  have scrut : Ev file (tagsOf file m₁) env₁ (.inl SCR) (.inl (.tuple [spec n₁, spec n₂])) :=
    .ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne)) .nil))
      (by simp [primitive]; rfl)
  have s₂ := PureEvalExt.ev_local file (tagsOf file m₁) (wc := false) (labels := labels) scrut
    (.effectCase bs env₁ :: k) m₁ rfl
  let env₂ := TyGuard.armEnv x y n₁ n₂ env₁
  have s₃ : LocalReaches file labels false ⟨.value (.tuple [spec n₁, spec n₂]), .effectCase bs env₁ :: k, m₁⟩
      ⟨.effectExpr (.mk bann (.pure body)) env₂, k, m₁⟩ :=
    .single (.next (Cond.requestAux_effectCase m₁ _ bs env₁ k false (hsel n₁ n₂))
      (LoadTask.plain_effectExpr _ _))
  obtain ⟨l₂, s₄⟩ := IntExpr.guard_local (file := file) (labels := labels) bann body env₂ k m₁
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have s₅ := PureEvalExt.ev_local file (tagsOf file m₂) (wc := false) (labels := labels)
    (TyGuard.bodyG_eval hb ne' env₁ (eguard_ok h n₁ n₂)) (.diagnosticLocation m₁.currentLocation :: k)
    m₂ rfl
  refine ⟨m₂, ⟨l₂, m.lastUsed, rfl⟩, s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
    (LoadTask.plain_value _)

end Silmaril.Compile.Core.Verified.TyECmp
