module

public import Silmaril.Logic.Metamath.SetMM.Grammar

@[expose] public section

/-!
# The axioms of set.mm's ZFC as tree assertions

The `PropCalc`, `PredCalc`, `ZF` and `ZFC` fragments of the committed CC0
file `data/metamath/set-axioms.mm`, as tree assertions over `SetMM.grammar`, with the definitions of `<->`, `/\`, `\/` and
`E.` (`df-bi`, `df-an`, `df-or`, `df-ex`) that `ZF` and `ZFC` use. Each
assertion keeps the source's mandatory hypotheses in database order and its
disjoint-variable pairs in the order the checker lists them, so its flattening
is exactly the checker's assertion (tested in
`Silmaril.Logic.Metamath.SetMM.Regression`).

The axiom sets are given as labelled lists (`propCalcList`, ...), each
extending the previous one, and as sets of tree assertions (`propCalc`,
`predCalc`, `zf`, `zfc`). All their members are well formed
(`wellFormed_zfc`).

The string axiom sets (`strAxioms`) add each fragment's syntax axioms to the
flattened axioms. They lie inside the string axioms of the grammar (`strAxioms_subset_axioms`), whose consistency
the models give.
-/

namespace Silmaril.Logic.Metamath.SetMM

open Silmaril.Logic.Metamath Grammar

/-- All pairs of distinct members of a list, in order: the pairs of a `$d`
statement. -/
def dvAll : List String → List (String × String)
  | [] => []
  | a :: l => l.map (a, ·) ++ dvAll l

/-! ## Propositional calculus -/

/-- `ax-mp`: from `|- ph` and `|- ( ph -> ps )` infer `|- ps`. -/
def axMp : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps", .ess (pf (wv "ph")), .ess (pf (wi (wv "ph") (wv "ps")))], pf (wv "ps")⟩

/-- `ax-1`: `|- ( ph -> ( ps -> ph ) )`. -/
def ax1 : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps"], pf (wi (wv "ph") (wi (wv "ps") (wv "ph")))⟩

/-- `ax-2`: `|- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )`. -/
def ax2 : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps", fw "ch"], pf (wi (wi (wv "ph") (wi (wv "ps") (wv "ch")))
    (wi (wi (wv "ph") (wv "ps")) (wi (wv "ph") (wv "ch"))))⟩

/-- `ax-3`: `|- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )`. -/
def ax3 : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps"], pf (wi (wi (wn (wv "ph")) (wn (wv "ps"))) (wi (wv "ps") (wv "ph")))⟩

/-! ## Predicate calculus -/

/-- `ax-gen`: from `|- ph` infer `|- A. x ph`. -/
def axGen : TAssertion L String String :=
  ⟨[], [fw "ph", fs "x", .ess (pf (wv "ph"))], pf (wal "x" (wv "ph"))⟩

/-- `ax-4`: `|- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )`. -/
def ax4 : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps", fs "x"], pf (wi (wal "x" (wi (wv "ph") (wv "ps")))
    (wi (wal "x" (wv "ph")) (wal "x" (wv "ps"))))⟩

/-- `ax-5`: `|- ( ph -> A. x ph )`, with `$d x ph`. -/
def ax5 : TAssertion L String String :=
  ⟨[("x", "ph")], [fw "ph", fs "x"], pf (wi (wv "ph") (wal "x" (wv "ph")))⟩

/-- `ax-6`: `|- -. A. x -. x = y`. -/
def ax6 : TAssertion L String String :=
  ⟨[], [fs "x", fs "y"], pf (wn (wal "x" (wn (weq "x" "y"))))⟩

/-- `ax-7`: `|- ( x = y -> ( x = z -> y = z ) )`. -/
def ax7 : TAssertion L String String :=
  ⟨[], [fs "x", fs "y", fs "z"], pf (wi (weq "x" "y") (wi (weq "x" "z") (weq "y" "z")))⟩

/-- `ax-8`: `|- ( x = y -> ( x e. z -> y e. z ) )`. -/
def ax8 : TAssertion L String String :=
  ⟨[], [fs "x", fs "y", fs "z"], pf (wi (weq "x" "y") (wi (wel "x" "z") (wel "y" "z")))⟩

/-- `ax-9`: `|- ( x = y -> ( z e. x -> z e. y ) )`. -/
def ax9 : TAssertion L String String :=
  ⟨[], [fs "x", fs "y", fs "z"], pf (wi (weq "x" "y") (wi (wel "z" "x") (wel "z" "y")))⟩

/-- `ax-10`: `|- ( -. A. x ph -> A. x -. A. x ph )`. -/
def ax10 : TAssertion L String String :=
  ⟨[], [fw "ph", fs "x"], pf (wi (wn (wal "x" (wv "ph"))) (wal "x" (wn (wal "x" (wv "ph")))))⟩

/-- `ax-11`: `|- ( A. x A. y ph -> A. y A. x ph )`. -/
def ax11 : TAssertion L String String :=
  ⟨[], [fw "ph", fs "x", fs "y"],
    pf (wi (wal "x" (wal "y" (wv "ph"))) (wal "y" (wal "x" (wv "ph"))))⟩

/-- `ax-12`: `|- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )`. -/
def ax12 : TAssertion L String String :=
  ⟨[], [fw "ph", fs "x", fs "y"], pf (wi (weq "x" "y")
    (wi (wal "y" (wv "ph")) (wal "x" (wi (weq "x" "y") (wv "ph")))))⟩

/-- `ax-13`: `|- ( -. x = y -> ( y = z -> A. x y = z ) )`. -/
def ax13 : TAssertion L String String :=
  ⟨[], [fs "x", fs "y", fs "z"],
    pf (wi (wn (weq "x" "y")) (wi (weq "y" "z") (wal "x" (weq "y" "z"))))⟩

/-! ## Definitions -/

/-- `df-bi`: `|- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) ->
-. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) )`. -/
def dfBi : TAssertion L String String :=
  let i := wi (wi (wv "ph") (wv "ps")) (wn (wi (wv "ps") (wv "ph")))
  ⟨[], [fw "ph", fw "ps"], pf (wn (wi (wi (wb (wv "ph") (wv "ps")) (wn i))
    (wn (wi (wn i) (wb (wv "ph") (wv "ps"))))))⟩

/-- `df-an`: `|- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )`. -/
def dfAn : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps"],
    pf (wb (wa (wv "ph") (wv "ps")) (wn (wi (wv "ph") (wn (wv "ps")))))⟩

/-- `df-or`: `|- ( ( ph \/ ps ) <-> ( -. ph -> ps ) )`. -/
def dfOr : TAssertion L String String :=
  ⟨[], [fw "ph", fw "ps"], pf (wb (wo (wv "ph") (wv "ps")) (wi (wn (wv "ph")) (wv "ps")))⟩

/-- `df-ex`: `|- ( E. x ph <-> -. A. x -. ph )`. -/
def dfEx : TAssertion L String String :=
  ⟨[], [fw "ph", fs "x"], pf (wb (wex "x" (wv "ph")) (wn (wal "x" (wn (wv "ph")))))⟩

/-! ## Set theory -/

/-- `ax-ext`: `|- ( A. z ( z e. x <-> z e. y ) -> x = y )`. -/
def axExt : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z"], [fs "x", fs "y", fs "z"],
    pf (wi (wal "z" (wb (wel "z" "x") (wel "z" "y"))) (weq "x" "y"))⟩

/-- `ax-rep`: `|- ( A. w E. y A. z ( A. y ph -> z = y ) ->
E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) )`. -/
def axRep : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z", "w"], [fw "ph", fs "x", fs "y", fs "z", fs "w"],
    pf (wi (wal "w" (wex "y" (wal "z" (wi (wal "y" (wv "ph")) (weq "z" "y")))))
      (wex "y" (wal "z" (wb (wel "z" "y") (wex "w" (wa (wel "w" "x") (wal "y" (wv "ph"))))))))⟩

/-- `ax-sep`: `|- E. y A. x ( x e. y <-> ( x e. z /\ ph ) )`. -/
def axSep : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z"] ++ dvAll ["y", "z", "ph"], [fw "ph", fs "x", fs "y", fs "z"],
    pf (wex "y" (wal "x" (wb (wel "x" "y") (wa (wel "x" "z") (wv "ph")))))⟩

/-- `ax-nul`: `|- E. x A. y -. y e. x`. -/
def axNul : TAssertion L String String :=
  ⟨dvAll ["x", "y"], [fs "x", fs "y"], pf (wex "x" (wal "y" (wn (wel "y" "x"))))⟩

/-- `ax-pow`: `|- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )`. -/
def axPow : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z", "w"], [fs "x", fs "y", fs "z", fs "w"],
    pf (wex "y" (wal "z" (wi (wal "w" (wi (wel "w" "z") (wel "w" "x"))) (wel "z" "y"))))⟩

/-- `ax-pr`: `|- E. z A. w ( ( w = x \/ w = y ) -> w e. z )`. -/
def axPr : TAssertion L String String :=
  ⟨dvAll ["x", "z", "w"] ++ dvAll ["y", "z", "w"], [fs "x", fs "y", fs "z", fs "w"],
    pf (wex "z" (wal "w" (wi (wo (weq "w" "x") (weq "w" "y")) (wel "w" "z"))))⟩

/-- `ax-un`: `|- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y )`. -/
def axUn : TAssertion L String String :=
  ⟨dvAll ["w", "x", "y", "z"], [fs "x", fs "y", fs "z", fs "w"],
    pf (wex "y" (wal "z" (wi (wex "w" (wa (wel "z" "w") (wel "w" "x"))) (wel "z" "y"))))⟩

/-- `ax-reg`: `|- ( E. y y e. x -> E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) )`. -/
def axReg : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z"], [fs "x", fs "y", fs "z"],
    pf (wi (wex "y" (wel "y" "x"))
      (wex "y" (wa (wel "y" "x") (wal "z" (wi (wel "z" "y") (wn (wel "z" "x")))))))⟩

/-- `ax-inf`: `|- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )`. -/
def axInf : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z", "w"], [fs "x", fs "y", fs "z", fs "w"],
    pf (wex "y" (wa (wel "x" "y")
      (wal "z" (wi (wel "z" "y") (wex "w" (wa (wel "z" "w") (wel "w" "y")))))))⟩

/-- `ax-ac`: `|- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t
( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )`. -/
def axAc : TAssertion L String String :=
  ⟨dvAll ["x", "y", "z", "w", "v", "u", "t"],
    [fs "x", fs "y", fs "z", fs "w", fs "v", fs "u", fs "t"],
    pf (wex "y" (wal "z" (wal "w" (wi (wa (wel "z" "w") (wel "w" "x"))
      (wex "v" (wal "u" (wb (wex "t" (wa (wa (wel "u" "w") (wel "w" "t"))
        (wa (wel "u" "t") (wel "t" "y")))) (weq "u" "v"))))))))⟩

/-! ## The axiom sets -/

/-- A labelled list of tree assertions. -/
abbrev LList := List (String × TAssertion L String String)

/-- The tree assertions of a labelled list. -/
def ofList (l : LList) : Set (TAssertion L String String) := {A | ∃ p ∈ l, p.2 = A}

theorem mem_ofList {l : LList} {A : TAssertion L String String} {s : String} (h : (s, A) ∈ l) :
    A ∈ ofList l := ⟨_, h, rfl⟩

theorem ofList_mono {l l' : LList} (h : ∀ p ∈ l, p ∈ l') : ofList l ⊆ ofList l' :=
  fun _ ⟨p, hp, e⟩ => ⟨p, h p hp, e⟩

theorem ofList_append_left (l l' : LList) : ofList l ⊆ ofList (l ++ l') :=
  ofList_mono fun _ hp => List.mem_append_left _ hp

/-- Classical propositional calculus: `ax-mp`, `ax-1`, `ax-2`, `ax-3`. -/
def propCalcList : LList := [("ax-mp", axMp), ("ax-1", ax1), ("ax-2", ax2), ("ax-3", ax3)]

/-- Predicate calculus with equality and membership: `ax-gen` and `ax-4` to `ax-13`. -/
def predCalcList : LList := propCalcList ++
  [("ax-gen", axGen), ("ax-4", ax4), ("ax-5", ax5), ("ax-6", ax6), ("ax-7", ax7), ("ax-8", ax8),
    ("ax-9", ax9), ("ax-10", ax10), ("ax-11", ax11), ("ax-12", ax12), ("ax-13", ax13)]

/-- The definitions used by `ZF`: `df-bi`, `df-an`, `df-or`, `df-ex`. -/
def defsList : LList := [("df-bi", dfBi), ("df-an", dfAn), ("df-or", dfOr), ("df-ex", dfEx)]

/-- The set-theoretic axioms of `ZF`. -/
def zfAxList : LList :=
  [("ax-ext", axExt), ("ax-rep", axRep), ("ax-sep", axSep), ("ax-nul", axNul), ("ax-pow", axPow),
    ("ax-pr", axPr), ("ax-un", axUn), ("ax-reg", axReg), ("ax-inf", axInf)]

/-- Zermelo-Fraenkel set theory with its definitions. -/
def zfList : LList := predCalcList ++ defsList ++ zfAxList

/-- `ZF` with the axiom of choice `ax-ac`. -/
def zfcList : LList := zfList ++ [("ax-ac", axAc)]

/-- Classical propositional calculus. -/
abbrev propCalc : Set (TAssertion L String String) := ofList propCalcList

/-- Predicate calculus. -/
abbrev predCalc : Set (TAssertion L String String) := ofList predCalcList

/-- `ZF` with `df-bi`, `df-an`, `df-or`, `df-ex`. -/
abbrev zf : Set (TAssertion L String String) := ofList zfList

/-- `ZFC` with `df-bi`, `df-an`, `df-or`, `df-ex`. -/
abbrev zfc : Set (TAssertion L String String) := ofList zfcList

theorem propCalc_subset_predCalc : propCalc ⊆ predCalc := ofList_append_left _ _

theorem predCalc_subset_zf : predCalc ⊆ zf :=
  (ofList_append_left _ defsList).trans (ofList_append_left _ _)

theorem zf_subset_zfc : zf ⊆ zfc := ofList_append_left _ _

/-! ## Well-formedness -/

/-- Every member of a labelled list passes the well-formedness check. -/
def checkList (l : LList) : Bool := l.all fun p => TAssertion.checkWF grammar p.2

theorem wellFormed_of_checkList {l : LList} (h : checkList l = true) :
    ∀ A ∈ ofList l, A.WellFormed grammar := by
  rintro A ⟨p, hp, rfl⟩
  exact .of_checkWF (List.all_eq_true.1 h p hp)

theorem checkList_zfc : checkList zfcList = true := by decide

theorem wellFormed_zfc : ∀ A ∈ zfc, A.WellFormed grammar :=
  wellFormed_of_checkList checkList_zfc

theorem wellFormed_zf : ∀ A ∈ zf, A.WellFormed grammar :=
  fun A hA => wellFormed_zfc A (zf_subset_zfc hA)

theorem wellFormed_predCalc : ∀ A ∈ predCalc, A.WellFormed grammar :=
  fun A hA => wellFormed_zf A (predCalc_subset_zf hA)

theorem wellFormed_propCalc : ∀ A ∈ propCalc, A.WellFormed grammar :=
  fun A hA => wellFormed_predCalc A (propCalc_subset_predCalc hA)

/-! ## String axiom sets -/

/-- The syntax axioms of `PropCalc`. -/
def propCalcSyntax : List L := [.wn, .wi]

/-- The syntax axioms of `PredCalc`. -/
def predCalcSyntax : List L := [.wn, .wi, .wal, .cv, .wceq, .wcel]

/-- The syntax axioms of `ZF` and `ZFC`. -/
def zfSyntax : List L := [.wn, .wi, .wb, .wa, .wo, .wal, .cv, .wceq, .wex, .wcel]

/-- The string axioms of a system: the listed syntax axioms and the flattened
tree axioms. -/
def strAxioms (S : List L) (l : LList) : Set (Assertion String String) :=
  {A | ∃ r ∈ S, (rules r).toAssertion = A} ∪ {A | ∃ p ∈ l, p.2.flatten grammar = A}

theorem strAxioms_mono {S S' : List L} {l l' : LList} (hS : ∀ r ∈ S, r ∈ S')
    (hl : ∀ p ∈ l, p ∈ l') : strAxioms S l ⊆ strAxioms S' l' := by
  rintro A (⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩)
  · exact Or.inl ⟨r, hS r hr, rfl⟩
  · exact Or.inr ⟨p, hl p hp, rfl⟩

/-- The string axioms of a system lie among the string axioms of the grammar. -/
theorem strAxioms_subset_axioms (S : List L) (l : LList) :
    strAxioms S l ⊆ grammar.axioms (ofList l) := by
  rintro A (⟨r, -, rfl⟩ | ⟨p, hp, rfl⟩)
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩

end Silmaril.Logic.Metamath.SetMM
