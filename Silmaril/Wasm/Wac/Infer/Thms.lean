module

public import Silmaril.Wasm.Wac.Infer.Defs

/-!
# WAC name inference: each function computes the unique name its relation allows

`matchIface_iff`, `tailOrSelf_iff`, `inferArg_iff`, `namedArg_iff`,
`exportName?_iff`, `pickExport_iff`: soundness and completeness of every naming
function of the elaborator against the precedence rules of `LANGUAGE.md`, stated as
relations in `Silmaril.Wasm.Wac.Infer.Defs`. Each relation is functional (`*_unique`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

theorem matchIface_iff {x : String} {names : List String} {n : String} :
    matchIface x names = some n ↔ MatchIface x names n := by
  unfold matchIface MatchIface
  by_cases hx : x ∈ names
  · simp [hx]
  · simp only [hx, ite_false, not_false_eq_true, true_and]
    cases h : tailMatches x names with
    | nil => simp
    | cons a l => cases l <;> simp

theorem tailOrSelf_iff {x : String} {names : List String} {n : String} :
    tailOrSelf x names = n ↔ TailOrSelf x names n := by
  unfold tailOrSelf
  cases h : matchIface x names with
  | some m =>
    have hm : MatchIface x names m := matchIface_iff.1 h
    refine ⟨fun e => e ▸ .tail hm, fun t => ?_⟩
    cases t with
    | tail hn => exact Option.some.inj (h.symm.trans (matchIface_iff.2 hn))
    | self hn => exact absurd hm (hn m)
  | none =>
    have hn : ∀ m, ¬ MatchIface x names m := fun m hm => by
      rw [matchIface_iff.2 hm] at h; cases h
    refine ⟨fun e => e ▸ .self hn, fun t => ?_⟩
    cases t with
    | tail hm => exact absurd hm (hn n)
    | self _ => rfl

theorem TailOrSelf.unique {x : String} {names : List String} {n n' : String}
    (h : TailOrSelf x names n) (h' : TailOrSelf x names n') : n = n' :=
  (tailOrSelf_iff.2 h).symm.trans (tailOrSelf_iff.2 h')

/-! ## Inferred arguments -/

theorem inferArgOrigin_spec {g : CGraph} {imps : List String} {x : String} {i : Nat}
    (h1 : ∀ p, ¬ ByIdApplies g imps i p) :
    InferArg g imps x i (inferArg.inferArgOrigin g imps x i) := by
  unfold inferArg.inferArgOrigin
  have hfall : (∀ m, ¬ ByOriginApplies g imps i m) → InferArg g imps x i (tailOrSelf x imps) :=
    fun h2 => match tailOrSelf_iff.1 (rfl : tailOrSelf x imps = _) with
      | .tail hm => .byTail h1 h2 hm
      | .self hn => .byLocal h1 h2 hn
  cases ho : g.origin? i with
  | none => exact hfall fun m hm => nomatch ho.symm.trans hm.1
  | some m =>
    by_cases hm : m ∈ imps
    · simpa [hm] using InferArg.byOrigin h1 ⟨ho, hm⟩
    · simpa [hm] using hfall fun m' hm' =>
        hm ((Option.some.inj (ho.symm.trans hm'.1)) ▸ hm'.2)

/-- The inferred argument name satisfies the rules. -/
theorem inferArg_spec (g : CGraph) (imps : List String) (x : String) (i : Nat) :
    InferArg g imps x i (inferArg g imps x i) := by
  unfold inferArg
  cases hk : (g.kindOf i).instId with
  | none => exact inferArgOrigin_spec fun p hp => nomatch hk.symm.trans hp.1
  | some p =>
    by_cases hp : p ∈ imps
    · simpa [hp] using InferArg.byId ⟨hk, hp⟩
    · simpa [hp] using inferArgOrigin_spec fun p' hp' =>
        hp ((Option.some.inj (hk.symm.trans hp'.1)) ▸ hp'.2)

theorem ByIdApplies.unique {g : CGraph} {imps : List String} {i : Nat} {p q : String}
    (h : ByIdApplies g imps i p) (h' : ByIdApplies g imps i q) : p = q :=
  Option.some.inj (h.1.symm.trans h'.1)

theorem ByOriginApplies.unique {g : CGraph} {imps : List String} {i : Nat} {p q : String}
    (h : ByOriginApplies g imps i p) (h' : ByOriginApplies g imps i q) : p = q :=
  Option.some.inj (h.1.symm.trans h'.1)

theorem MatchIface.unique {x : String} {names : List String} {n n' : String}
    (h : MatchIface x names n) (h' : MatchIface x names n') : n = n' := by
  have e : [n] = [n'] := h.2.symm.trans h'.2
  simpa using e

/-- **The rules determine the inferred name.** -/
theorem InferArg.unique {g : CGraph} {imps : List String} {x : String} {i : Nat} {n n' : String}
    (h : InferArg g imps x i n) (h' : InferArg g imps x i n') : n = n' := by
  cases h with
  | byId a => cases h' with
    | byId b => exact a.unique b
    | byOrigin n1 _ | byTail n1 _ _ | byLocal n1 _ _ => exact absurd a (n1 _)
  | byOrigin n1 a => cases h' with
    | byId b => exact absurd b (n1 _)
    | byOrigin _ b => exact a.unique b
    | byTail _ n2 _ | byLocal _ n2 _ => exact absurd a (n2 _)
  | byTail n1 n2 a => cases h' with
    | byId b => exact absurd b (n1 _)
    | byOrigin _ b => exact absurd b (n2 _)
    | byTail _ _ b => exact a.unique b
    | byLocal _ _ n3 => exact absurd a (n3 _)
  | byLocal n1 n2 n3 => cases h' with
    | byId b => exact absurd b (n1 _)
    | byOrigin _ b => exact absurd b (n2 _)
    | byTail _ _ b => exact absurd b (n3 _)
    | byLocal _ _ _ => rfl

/-- **Inferred arguments: sound and complete.** -/
theorem inferArg_iff {g : CGraph} {imps : List String} {x : String} {i : Nat} {n : String} :
    inferArg g imps x i = n ↔ InferArg g imps x i n :=
  ⟨fun e => e ▸ inferArg_spec g imps x i, fun h => (inferArg_spec g imps x i).unique h⟩

/-! ## Named arguments, exports, spreads -/

theorem namedArg_iff {imps : List String} {a : Syntax.ArgName} {n : String} :
    namedArg imps a = n ↔ NamedArg imps a n := by
  cases a with
  | ident x =>
    refine ⟨fun e => .ident (tailOrSelf_iff.1 e), fun h => ?_⟩
    cases h with | ident t => exact tailOrSelf_iff.2 t
  | str s =>
    refine ⟨fun e => e ▸ .str s, fun h => ?_⟩
    cases h; rfl

theorem exportName?_iff {g : CGraph} {i : Nat} {n : String} :
    exportName? g i = some n ↔ ExportName g i n := by
  unfold exportName?
  cases hk : (g.kindOf i).instId with
  | some p =>
    refine ⟨fun e => (Option.some.inj e) ▸ .byId hk, fun h => ?_⟩
    cases h with
    | byId h' => rw [hk] at h'; exact h'
    | byOrigin h' _ => rw [hk] at h'; cases h'
  | none =>
    refine ⟨fun e => .byOrigin hk e, fun h => ?_⟩
    cases h with
    | byId h' => rw [hk] at h'; cases h'
    | byOrigin _ h' => exact h'

theorem pickExport_iff {exps : List String} {n e : String} :
    pickExport exps n = some e ↔ PickExport exps n e := by
  unfold pickExport
  by_cases hn : n ∈ exps
  · simp only [hn, ite_true, Option.some.injEq]
    refine ⟨fun h => h ▸ .exact hn, fun h => ?_⟩
    cases h with
    | exact _ => rfl
    | semver _ _ hn' => exact absurd hn hn'
  · simp only [hn, ite_false, List.find?_eq_some_iff_append, Bool.not_eq_true']
    constructor
    · rintro ⟨hc, pre, post, rfl, hpre⟩
      exact .semver pre post hn rfl hc hpre
    · intro h
      cases h with
      | exact h' => exact absurd h' hn
      | semver pre post _ he hc hpre => exact ⟨hc, pre, post, he, hpre⟩

end Silmaril.Wasm.Wac
