module

public import Silmaril.Logic.Metamath.Grammar.Derivation
public import Silmaril.Logic.Metamath.Grammar.Examples
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The data of `z2.mm`

Generated from the CC0 database `data/metamath/z2.mm`. The constants, variables and syntax axioms of
the database, and each logical axiom and theorem as a tree assertion with
the frame a Metamath verifier computes. `SecondOrder.Tests` checks the
flattened data against the verified checker's reading of the file.
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Silmaril.Logic.Metamath Grammar

/-- The constants. -/
inductive C
  | lp | rp | imp | not | bi | and | all | ex | eq | lt | el | zero | succ | lb | rb | plus
  | times | wff | term | nvar | svar | turnstile | bnd | sig1 | pi1 | arith
  deriving DecidableEq, Repr

instance : Fintype C :=
  .ofList [.lp, .rp, .imp, .not, .bi, .and, .all, .ex, .eq, .lt, .el, .zero, .succ, .lb, .rb,
    .plus, .times, .wff, .term, .nvar, .svar, .turnstile, .bnd, .sig1, .pi1, .arith]
    (by intro c; cases c <;> simp)

/-- The Metamath token of a constant. -/
def C.token : C → String
  | .lp => "("
  | .rp => ")"
  | .imp => "->"
  | .not => "-."
  | .bi => "<->"
  | .and => "/\\"
  | .all => "A."
  | .ex => "E."
  | .eq => "="
  | .lt => "<"
  | .el => "e."
  | .zero => "0"
  | .succ => "S"
  | .lb => "["
  | .rb => "]"
  | .plus => "+"
  | .times => "x."
  | .wff => "wff"
  | .term => "term"
  | .nvar => "nvar"
  | .svar => "svar"
  | .turnstile => "|-"
  | .bnd => "bnd"
  | .sig1 => "sig1"
  | .pi1 => "pi1"
  | .arith => "arith"

/-- The variables: those of the database, and infinitely many more. -/
inductive V
  | ph | ps | ch | th | x | y | z | w | X | Y | Z | t | u | v
  | aux (n : ℕ)
  deriving DecidableEq, Repr

instance : Infinite V := Infinite.of_injective V.aux fun _ _ h => V.aux.inj h

/-- The Metamath token of a variable. -/
def V.token : V → String
  | .ph => "ph"
  | .ps => "ps"
  | .ch => "ch"
  | .th => "th"
  | .x => "x"
  | .y => "y"
  | .z => "z"
  | .w => "w"
  | .X => "X"
  | .Y => "Y"
  | .Z => "Z"
  | .t => "t"
  | .u => "u"
  | .v => "v"
  | .aux n => s!"aux.{n}"

/-- The labels of the syntax axioms. -/
inductive L
  | tvar | t0 | tS | tpl | tmu | wn | wi | wb | wa | wal | wex | wsal | wsex | weq | wlt | wel
  | wseq
  deriving DecidableEq, Repr

instance : Fintype L :=
  .ofList [.tvar, .t0, .tS, .tpl, .tmu, .wn, .wi, .wb, .wa, .wal, .wex, .wsal, .wsex, .weq, .wlt,
    .wel, .wseq]
    (by intro l; cases l <;> simp)

/-- The Metamath label of a syntax axiom. -/
def L.label : L → String
  | .tvar => "tvar"
  | .t0 => "t0"
  | .tS => "tS"
  | .tpl => "tpl"
  | .tmu => "tmu"
  | .wn => "wn"
  | .wi => "wi"
  | .wb => "wb"
  | .wa => "wa"
  | .wal => "wal"
  | .wex => "wex"
  | .wsal => "wsal"
  | .wsex => "wsex"
  | .weq => "weq"
  | .wlt => "wlt"
  | .wel => "wel"
  | .wseq => "wseq"

/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .tvar => Grammar.Examples.rule .term [(.nvar, .x)] [.var .x]
  | .t0 => Grammar.Examples.rule .term [] [.const .zero] .nil .nil
  | .tS => Grammar.Examples.rule .term [(.term, .t)] [.const .succ, .var .t]
  | .tpl => Grammar.Examples.rule .term [(.term, .t), (.term, .u)]
      [.const .lb, .var .t, .const .plus, .var .u, .const .rb]
  | .tmu => Grammar.Examples.rule .term [(.term, .t), (.term, .u)]
      [.const .lb, .var .t, .const .times, .var .u, .const .rb]
  | .wn => Grammar.Examples.rule .wff [(.wff, .ph)] [.const .not, .var .ph]
  | .wi => Grammar.Examples.rule .wff [(.wff, .ph), (.wff, .ps)]
      [.const .lp, .var .ph, .const .imp, .var .ps, .const .rp]
  | .wb => Grammar.Examples.rule .wff [(.wff, .ph), (.wff, .ps)]
      [.const .lp, .var .ph, .const .bi, .var .ps, .const .rp]
  | .wa => Grammar.Examples.rule .wff [(.wff, .ph), (.wff, .ps)]
      [.const .lp, .var .ph, .const .and, .var .ps, .const .rp]
  | .wal => Grammar.Examples.rule .wff [(.wff, .ph), (.nvar, .x)] [.const .all, .var .x, .var .ph]
  | .wex => Grammar.Examples.rule .wff [(.wff, .ph), (.nvar, .x)] [.const .ex, .var .x, .var .ph]
  | .wsal => Grammar.Examples.rule .wff [(.wff, .ph), (.svar, .X)] [.const .all, .var .X, .var .ph]
  | .wsex => Grammar.Examples.rule .wff [(.wff, .ph), (.svar, .X)] [.const .ex, .var .X, .var .ph]
  | .weq => Grammar.Examples.rule .wff [(.term, .t), (.term, .u)] [.var .t, .const .eq, .var .u]
  | .wlt => Grammar.Examples.rule .wff [(.term, .t), (.term, .u)] [.var .t, .const .lt, .var .u]
  | .wel => Grammar.Examples.rule .wff [(.svar, .X), (.term, .t)] [.var .t, .const .el, .var .X]
  | .wseq => Grammar.Examples.rule .wff [(.svar, .X), (.svar, .Y)] [.var .X, .const .eq, .var .Y]

/-- The syntax typecodes. -/
def isSort : C → Bool
  | .wff => true
  | .term => true
  | .nvar => true
  | .svar => true
  | _ => false

/-- The syntax typecode of each provable typecode. -/
def provOf : C → Option C
  | .turnstile => some .wff
  | .bnd => some .wff
  | .sig1 => some .wff
  | .pi1 => some .wff
  | .arith => some .wff
  | _ => none

/-! ## Logical axioms -/

/-- `ax-mp`: `|- ps`. Modus ponens. -/
def axMp : TAssertion L C V where
  dv := []
  hyps := [
    .float .wff .ph,
    .float .wff .ps,
    .ess ⟨.turnstile, .var .ph⟩,
    .ess ⟨.turnstile, .node .wi [.var .ph, .var .ps]⟩
  ]
  concl := ⟨.turnstile, .var .ps⟩

/-- `ax-1`: `|- ( ph -> ( ps -> ph ) )`. Axiom Simp. -/
def ax1 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile, .node .wi [.var .ph, .node .wi [.var .ps, .var .ph]]⟩

/-- `ax-2`: `|- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )`. Axiom Frege. -/
def ax2 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .float .wff .ch]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wi [.var .ph, .node .wi [.var .ps, .var .ch]],
      .node .wi [.node .wi [.var .ph, .var .ps], .node .wi [.var .ph, .var .ch]]
    ]⟩

/-- `ax-3`: `|- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )`. Axiom Transp. -/
def ax3 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wi [.node .wn [.var .ph], .node .wn [.var .ps]],
      .node .wi [.var .ps, .var .ph]
    ]⟩

/-- `df-bi1`: `|- ( ( ph <-> ps ) -> ( ph -> ps ) )`. The biconditional implies the forward
implication. -/
def dfBi1 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile, .node .wi [.node .wb [.var .ph, .var .ps], .node .wi [.var .ph, .var .ps]]⟩

/-- `df-bi2`: `|- ( ( ph <-> ps ) -> ( ps -> ph ) )`. The biconditional implies the reverse
implication. -/
def dfBi2 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile, .node .wi [.node .wb [.var .ph, .var .ps], .node .wi [.var .ps, .var .ph]]⟩

/-- `df-bi3`: `|- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) )`. Two implications give
the biconditional. -/
def dfBi3 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wi [.var .ph, .var .ps],
      .node .wi [.node .wi [.var .ps, .var .ph], .node .wb [.var .ph, .var .ps]]
    ]⟩

/-- `df-an`: `|- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )`. Conjunction. -/
def dfAn : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps]
  concl := ⟨.turnstile,
    .node .wb [
      .node .wa [.var .ph, .var .ps],
      .node .wn [.node .wi [.var .ph, .node .wn [.var .ps]]]
    ]⟩

/-- `ax-gen`: `|- A. x ph`. Generalization. -/
def axGen : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .ess ⟨.turnstile, .var .ph⟩]
  concl := ⟨.turnstile, .node .wal [.var .ph, .var .x]⟩

/-- `ax-4`: `|- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )`. Quantified implication. -/
def ax4 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .float .nvar .x]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wi [.var .ph, .var .ps], .var .x],
      .node .wi [.node .wal [.var .ph, .var .x], .node .wal [.var .ps, .var .x]]
    ]⟩

/-- `ax-5`: `|- ( ph -> A. x ph )`. Vacuous quantification. -/
def ax5 : TAssertion L C V where
  dv := [(.x, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x]
  concl := ⟨.turnstile, .node .wi [.var .ph, .node .wal [.var .ph, .var .x]]⟩

/-- `ax-6`: `|- -. A. x -. x = y`. Existence of a number equal to a variable. -/
def ax6 : TAssertion L C V where
  dv := []
  hyps := [.float .nvar .x, .float .nvar .y]
  concl := ⟨.turnstile,
    .node .wn [
      .node .wal [.node .wn [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]]], .var .x]
    ]⟩

/-- `ax-7`: `|- ( t = u -> ( t = v -> u = v ) )`. Equality is transitive and symmetric. -/
def ax7 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .wi [.node .weq [.var .t, .var .v], .node .weq [.var .u, .var .v]]
    ]⟩

/-- `ax-10`: `|- ( -. A. x ph -> A. x -. A. x ph )`. Quantified negation. -/
def ax10 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wn [.node .wal [.var .ph, .var .x]],
      .node .wal [.node .wn [.node .wal [.var .ph, .var .x]], .var .x]
    ]⟩

/-- `ax-11`: `|- ( A. x A. y ph -> A. y A. x ph )`. Quantifier commutation. -/
def ax11 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .float .nvar .y]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wal [.var .ph, .var .y], .var .x],
      .node .wal [.node .wal [.var .ph, .var .x], .var .y]
    ]⟩

/-- `ax-12`: `|- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )`. Substitution. -/
def ax12 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .float .nvar .y]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.node .tvar [.var .x], .node .tvar [.var .y]],
      .node .wi [
        .node .wal [.var .ph, .var .y],
        .node .wal [
          .node .wi [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]], .var .ph],
          .var .x
        ]
      ]
    ]⟩

/-- `ax-13`: `|- ( -. x = y -> ( y = z -> A. x y = z ) )`. Quantified equality. -/
def ax13 : TAssertion L C V where
  dv := []
  hyps := [.float .nvar .x, .float .nvar .y, .float .nvar .z]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wn [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]]],
      .node .wi [
        .node .weq [.node .tvar [.var .y], .node .tvar [.var .z]],
        .node .wal [.node .weq [.node .tvar [.var .y], .node .tvar [.var .z]], .var .x]
      ]
    ]⟩

/-- `ax-tex`: `|- -. A. x -. x = t`. Every term denotes a number. -/
def axTex : TAssertion L C V where
  dv := [(.x, .t)]
  hyps := [.float .nvar .x, .float .term .t]
  concl := ⟨.turnstile,
    .node .wn [.node .wal [.node .wn [.node .weq [.node .tvar [.var .x], .var .t]], .var .x]]⟩

/-- `df-ex`: `|- ( E. x ph <-> -. A. x -. ph )`. Existential quantification. -/
def dfEx : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x]
  concl := ⟨.turnstile,
    .node .wb [
      .node .wex [.var .ph, .var .x],
      .node .wn [.node .wal [.node .wn [.var .ph], .var .x]]
    ]⟩

/-- `ax-sgen`: `|- A. X ph`. Generalization. -/
def axSgen : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .svar .X, .ess ⟨.turnstile, .var .ph⟩]
  concl := ⟨.turnstile, .node .wsal [.var .ph, .var .X]⟩

/-- `ax-s4`: `|- ( A. X ( ph -> ps ) -> ( A. X ph -> A. X ps ) )`. Quantified implication. -/
def axS4 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wsal [.node .wi [.var .ph, .var .ps], .var .X],
      .node .wi [.node .wsal [.var .ph, .var .X], .node .wsal [.var .ps, .var .X]]
    ]⟩

/-- `ax-s5`: `|- ( ph -> A. X ph )`. Vacuous quantification. -/
def axS5 : TAssertion L C V where
  dv := [(.X, .ph)]
  hyps := [.float .wff .ph, .float .svar .X]
  concl := ⟨.turnstile, .node .wi [.var .ph, .node .wsal [.var .ph, .var .X]]⟩

/-- `ax-s6`: `|- -. A. X -. X = Y`. Existence of a set equal to a variable. -/
def axS6 : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .svar .Y]
  concl := ⟨.turnstile,
    .node .wn [.node .wsal [.node .wn [.node .wseq [.var .X, .var .Y]], .var .X]]⟩

/-- `ax-s7`: `|- ( X = Y -> ( X = Z -> Y = Z ) )`. Set equality is transitive and symmetric. -/
def axS7 : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .svar .Y, .float .svar .Z]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wseq [.var .X, .var .Y],
      .node .wi [.node .wseq [.var .X, .var .Z], .node .wseq [.var .Y, .var .Z]]
    ]⟩

/-- `ax-s10`: `|- ( -. A. X ph -> A. X -. A. X ph )`. Quantified negation. -/
def axS10 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wn [.node .wsal [.var .ph, .var .X]],
      .node .wsal [.node .wn [.node .wsal [.var .ph, .var .X]], .var .X]
    ]⟩

/-- `ax-s11`: `|- ( A. X A. Y ph -> A. Y A. X ph )`. Quantifier commutation. -/
def axS11 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .svar .X, .float .svar .Y]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wsal [.node .wsal [.var .ph, .var .Y], .var .X],
      .node .wsal [.node .wsal [.var .ph, .var .X], .var .Y]
    ]⟩

/-- `ax-s12`: `|- ( X = Y -> ( A. Y ph -> A. X ( X = Y -> ph ) ) )`. Substitution. -/
def axS12 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .svar .X, .float .svar .Y]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wseq [.var .X, .var .Y],
      .node .wi [
        .node .wsal [.var .ph, .var .Y],
        .node .wsal [.node .wi [.node .wseq [.var .X, .var .Y], .var .ph], .var .X]
      ]
    ]⟩

/-- `ax-s13`: `|- ( -. X = Y -> ( Y = Z -> A. X Y = Z ) )`. Quantified equality. -/
def axS13 : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .svar .Y, .float .svar .Z]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wn [.node .wseq [.var .X, .var .Y]],
      .node .wi [
        .node .wseq [.var .Y, .var .Z],
        .node .wsal [.node .wseq [.var .Y, .var .Z], .var .X]
      ]
    ]⟩

/-- `ax-ns11`: `|- ( A. x A. X ph -> A. X A. x ph )`. Commutation of a number and a set
quantifier. -/
def axNs11 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wsal [.var .ph, .var .X], .var .x],
      .node .wsal [.node .wal [.var .ph, .var .x], .var .X]
    ]⟩

/-- `ax-sn11`: `|- ( A. X A. x ph -> A. x A. X ph )`. Commutation of a set and a number
quantifier. -/
def axSn11 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wsal [.node .wal [.var .ph, .var .x], .var .X],
      .node .wal [.node .wsal [.var .ph, .var .X], .var .x]
    ]⟩

/-- `df-sex`: `|- ( E. X ph <-> -. A. X -. ph )`. Existential set quantification. -/
def dfSex : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wb [
      .node .wsex [.var .ph, .var .X],
      .node .wn [.node .wsal [.node .wn [.var .ph], .var .X]]
    ]⟩

/-- `df-seq`: `|- ( X = Y <-> A. x ( x e. X <-> x e. Y ) )`. Extensionality: sets with the same
members are equal. -/
def dfSeq : TAssertion L C V where
  dv := []
  hyps := [.float .nvar .x, .float .svar .X, .float .svar .Y]
  concl := ⟨.turnstile,
    .node .wb [
      .node .wseq [.var .X, .var .Y],
      .node .wal [
        .node .wb [
          .node .wel [.var .X, .node .tvar [.var .x]],
          .node .wel [.var .Y, .node .tvar [.var .x]]
        ],
        .var .x
      ]
    ]⟩

/-- `ax-eqS`: `|- ( t = u -> S t = S u )`. Successor respects equality. -/
def axEqS : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .weq [.node .tS [.var .t], .node .tS [.var .u]]
    ]⟩

/-- `ax-eqpl1`: `|- ( t = u -> [ t + v ] = [ u + v ] )`. Addition respects equality on the left. -/
def axEqpl1 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .weq [.node .tpl [.var .t, .var .v], .node .tpl [.var .u, .var .v]]
    ]⟩

/-- `ax-eqpl2`: `|- ( t = u -> [ v + t ] = [ v + u ] )`. Addition respects equality on the right. -/
def axEqpl2 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .weq [.node .tpl [.var .v, .var .t], .node .tpl [.var .v, .var .u]]
    ]⟩

/-- `ax-eqmu1`: `|- ( t = u -> [ t x. v ] = [ u x. v ] )`. Multiplication respects equality on
the left. -/
def axEqmu1 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .weq [.node .tmu [.var .t, .var .v], .node .tmu [.var .u, .var .v]]
    ]⟩

/-- `ax-eqmu2`: `|- ( t = u -> [ v x. t ] = [ v x. u ] )`. Multiplication respects equality on
the right. -/
def axEqmu2 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .weq [.node .tmu [.var .v, .var .t], .node .tmu [.var .v, .var .u]]
    ]⟩

/-- `ax-eqlt1`: `|- ( t = u -> ( t < v -> u < v ) )`. Order respects equality on the left. -/
def axEqlt1 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .wi [.node .wlt [.var .t, .var .v], .node .wlt [.var .u, .var .v]]
    ]⟩

/-- `ax-eqlt2`: `|- ( t = u -> ( v < t -> v < u ) )`. Order respects equality on the right. -/
def axEqlt2 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u, .float .term .v]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .wi [.node .wlt [.var .v, .var .t], .node .wlt [.var .v, .var .u]]
    ]⟩

/-- `ax-eqel1`: `|- ( t = u -> ( t e. X -> u e. X ) )`. Membership respects equality of numbers. -/
def axEqel1 : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.var .t, .var .u],
      .node .wi [.node .wel [.var .X, .var .t], .node .wel [.var .X, .var .u]]
    ]⟩

/-- `ax-eqel2`: `|- ( X = Y -> ( t e. X -> t e. Y ) )`. Membership respects equality of sets. -/
def axEqel2 : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .svar .Y, .float .term .t]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wseq [.var .X, .var .Y],
      .node .wi [.node .wel [.var .X, .var .t], .node .wel [.var .Y, .var .t]]
    ]⟩

/-- `ax-S0`: `|- -. S t = 0`. Zero is not a successor. -/
def axS0 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t]
  concl := ⟨.turnstile, .node .wn [.node .weq [.node .tS [.var .t], .node .t0 []]]⟩

/-- `ax-Sinj`: `|- ( S t = S u -> t = u )`. Successor is injective. -/
def axSinj : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .wi [
      .node .weq [.node .tS [.var .t], .node .tS [.var .u]],
      .node .weq [.var .t, .var .u]
    ]⟩

/-- `ax-pl0`: `|- [ t + 0 ] = t`. Addition of zero. -/
def axPl0 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t]
  concl := ⟨.turnstile, .node .weq [.node .tpl [.var .t, .node .t0 []], .var .t]⟩

/-- `ax-plS`: `|- [ t + S u ] = S [ t + u ]`. Addition of a successor. -/
def axPlS : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .weq [
      .node .tpl [.var .t, .node .tS [.var .u]],
      .node .tS [.node .tpl [.var .t, .var .u]]
    ]⟩

/-- `ax-mu0`: `|- [ t x. 0 ] = 0`. Multiplication by zero. -/
def axMu0 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t]
  concl := ⟨.turnstile, .node .weq [.node .tmu [.var .t, .node .t0 []], .node .t0 []]⟩

/-- `ax-muS`: `|- [ t x. S u ] = [ [ t x. u ] + t ]`. Multiplication by a successor. -/
def axMuS : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .weq [
      .node .tmu [.var .t, .node .tS [.var .u]],
      .node .tpl [.node .tmu [.var .t, .var .u], .var .t]
    ]⟩

/-- `ax-lt0`: `|- -. t < 0`. Nothing is below zero. -/
def axLt0 : TAssertion L C V where
  dv := []
  hyps := [.float .term .t]
  concl := ⟨.turnstile, .node .wn [.node .wlt [.var .t, .node .t0 []]]⟩

/-- `ax-ltS`: `|- ( t < S u <-> ( -. t < u -> t = u ) )`. Below a successor: ` t < S u ` exactly
when ` t < u ` or ` t = u ` . -/
def axLtS : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.turnstile,
    .node .wb [
      .node .wlt [.var .t, .node .tS [.var .u]],
      .node .wi [.node .wn [.node .wlt [.var .t, .var .u]], .node .weq [.var .t, .var .u]]
    ]⟩

/-- `bnd-eq`: `bnd t = u`. An equation is bounded. -/
def bndEq : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.bnd, .node .weq [.var .t, .var .u]⟩

/-- `bnd-lt`: `bnd t < u`. An inequality is bounded. -/
def bndLt : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.bnd, .node .wlt [.var .t, .var .u]⟩

/-- `bnd-el`: `bnd t e. X`. A membership is bounded. -/
def bndEl : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .term .t]
  concl := ⟨.bnd, .node .wel [.var .X, .var .t]⟩

/-- `bnd-n`: `bnd -. ph`. Bounded formulas are closed under negation. -/
def bndN : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.bnd, .node .wn [.var .ph]⟩

/-- `bnd-i`: `bnd ( ph -> ps )`. Bounded formulas are closed under implication. -/
def bndI : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.bnd, .var .ph⟩, .ess ⟨.bnd, .var .ps⟩]
  concl := ⟨.bnd, .node .wi [.var .ph, .var .ps]⟩

/-- `bnd-b`: `bnd ( ph <-> ps )`. Bounded formulas are closed under the biconditional. -/
def bndB : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.bnd, .var .ph⟩, .ess ⟨.bnd, .var .ps⟩]
  concl := ⟨.bnd, .node .wb [.var .ph, .var .ps]⟩

/-- `bnd-a`: `bnd ( ph /\ ps )`. Bounded formulas are closed under conjunction. -/
def bndA : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.bnd, .var .ph⟩, .ess ⟨.bnd, .var .ps⟩]
  concl := ⟨.bnd, .node .wa [.var .ph, .var .ps]⟩

/-- `bnd-ral`: `bnd A. x ( x < t -> ph )`. Bounded universal quantification. -/
def bndRal : TAssertion L C V where
  dv := [(.x, .t)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .term .t, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.bnd,
    .node .wal [.node .wi [.node .wlt [.node .tvar [.var .x], .var .t], .var .ph], .var .x]⟩

/-- `bnd-rex`: `bnd E. x ( x < t /\ ph )`. Bounded existential quantification. -/
def bndRex : TAssertion L C V where
  dv := [(.x, .t)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .term .t, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.bnd,
    .node .wex [.node .wa [.node .wlt [.node .tvar [.var .x], .var .t], .var .ph], .var .x]⟩

/-- `sig1-bnd`: `sig1 ph`. A bounded formula is Sigma^0_1. -/
def sig1Bnd : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.sig1, .var .ph⟩

/-- `sig1-ex`: `sig1 E. x ph`. An existentially quantified bounded formula is Sigma^0_1. -/
def sig1Ex : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.sig1, .node .wex [.var .ph, .var .x]⟩

/-- `pi1-bnd`: `pi1 ph`. A bounded formula is Pi^0_1. -/
def pi1Bnd : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.pi1, .var .ph⟩

/-- `pi1-al`: `pi1 A. x ph`. A universally quantified bounded formula is Pi^0_1. -/
def pi1Al : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .ess ⟨.bnd, .var .ph⟩]
  concl := ⟨.pi1, .node .wal [.var .ph, .var .x]⟩

/-- `arith-eq`: `arith t = u`. An equation is arithmetical. -/
def arithEq : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.arith, .node .weq [.var .t, .var .u]⟩

/-- `arith-lt`: `arith t < u`. An inequality is arithmetical. -/
def arithLt : TAssertion L C V where
  dv := []
  hyps := [.float .term .t, .float .term .u]
  concl := ⟨.arith, .node .wlt [.var .t, .var .u]⟩

/-- `arith-el`: `arith t e. X`. A membership is arithmetical. -/
def arithEl : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .term .t]
  concl := ⟨.arith, .node .wel [.var .X, .var .t]⟩

/-- `arith-seq`: `arith X = Y`. An equality of sets is arithmetical. -/
def arithSeq : TAssertion L C V where
  dv := []
  hyps := [.float .svar .X, .float .svar .Y]
  concl := ⟨.arith, .node .wseq [.var .X, .var .Y]⟩

/-- `arith-n`: `arith -. ph`. Arithmetical formulas are closed under negation. -/
def arithN : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.arith, .var .ph⟩]
  concl := ⟨.arith, .node .wn [.var .ph]⟩

/-- `arith-al`: `arith A. x ph`. Arithmetical formulas are closed under number quantification. -/
def arithAl : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .ess ⟨.arith, .var .ph⟩]
  concl := ⟨.arith, .node .wal [.var .ph, .var .x]⟩

/-- `arith-ex`: `arith E. x ph`. Arithmetical formulas are closed under existential number
quantification. -/
def arithEx : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .nvar .x, .ess ⟨.arith, .var .ph⟩]
  concl := ⟨.arith, .node .wex [.var .ph, .var .x]⟩

/-- `arith-i`: `arith ( ph -> ps )`. Arithmetical formulas are closed under implication. -/
def arithI : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.arith, .var .ph⟩, .ess ⟨.arith, .var .ps⟩]
  concl := ⟨.arith, .node .wi [.var .ph, .var .ps]⟩

/-- `arith-b`: `arith ( ph <-> ps )`. Arithmetical formulas are closed under the biconditional. -/
def arithB : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.arith, .var .ph⟩, .ess ⟨.arith, .var .ps⟩]
  concl := ⟨.arith, .node .wb [.var .ph, .var .ps]⟩

/-- `arith-a`: `arith ( ph /\ ps )`. Arithmetical formulas are closed under conjunction. -/
def arithA : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.arith, .var .ph⟩, .ess ⟨.arith, .var .ps⟩]
  concl := ⟨.arith, .node .wa [.var .ph, .var .ps]⟩

/-- `arith-sig1`: `arith ph`. A Sigma^0_1 formula is arithmetical. -/
def arithSig1 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.sig1, .var .ph⟩]
  concl := ⟨.arith, .var .ph⟩

/-- `arith-pi1`: `arith ph`. A Pi^0_1 formula is arithmetical. -/
def arithPi1 : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .ess ⟨.pi1, .var .ph⟩]
  concl := ⟨.arith, .var .ph⟩

/-- `ax-ind-sig1`: `|- ( A. x ( x = 0 -> ph ) -> ( A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y
-> ph ) ) -> A. x ph ) )`. Sigma^0_1 induction: ` A. x ( x = y -> ph ) ` is ` ph ` at ` y ` . -/
def axIndSig1 : TAssertion L C V where
  dv := [(.x, .y), (.y, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .nvar .y, .ess ⟨.sig1, .var .ph⟩]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wi [.node .weq [.node .tvar [.var .x], .node .t0 []], .var .ph], .var .x],
      .node .wi [
        .node .wal [
          .node .wi [
            .node .wal [
              .node .wi [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]], .var .ph],
              .var .x
            ],
            .node .wal [
              .node .wi [
                .node .weq [.node .tvar [.var .x], .node .tS [.node .tvar [.var .y]]],
                .var .ph
              ],
              .var .x
            ]
          ],
          .var .y
        ],
        .node .wal [.var .ph, .var .x]
      ]
    ]⟩

/-- `ax-dcomp`: `|- ( A. x ( ph <-> ps ) -> E. X A. x ( x e. X <-> ph ) )`. Delta^0_1
comprehension. -/
def axDcomp : TAssertion L C V where
  dv := [(.X, .ph), (.X, .ps)]
  hyps := [
    .float .wff .ph,
    .float .wff .ps,
    .float .nvar .x,
    .float .svar .X,
    .ess ⟨.sig1, .var .ph⟩,
    .ess ⟨.pi1, .var .ps⟩
  ]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wb [.var .ph, .var .ps], .var .x],
      .node .wsex [
        .node .wal [.node .wb [.node .wel [.var .X, .node .tvar [.var .x]], .var .ph], .var .x],
        .var .X
      ]
    ]⟩

/-- `ax-sep1`: `|- ( A. x -. ( ph /\ ps ) -> E. X A. x ( ( ph -> x e. X ) /\ ( ps -> -. x e. X )
) )`. Sigma^0_1 separation, the form of weak Koenig's lemma used here. -/
def axSep1 : TAssertion L C V where
  dv := [(.X, .ph), (.X, .ps)]
  hyps := [
    .float .wff .ph,
    .float .wff .ps,
    .float .nvar .x,
    .float .svar .X,
    .ess ⟨.sig1, .var .ph⟩,
    .ess ⟨.sig1, .var .ps⟩
  ]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wn [.node .wa [.var .ph, .var .ps]], .var .x],
      .node .wsex [
        .node .wal [
          .node .wa [
            .node .wi [.var .ph, .node .wel [.var .X, .node .tvar [.var .x]]],
            .node .wi [.var .ps, .node .wn [.node .wel [.var .X, .node .tvar [.var .x]]]]
          ],
          .var .x
        ],
        .var .X
      ]
    ]⟩

/-- `ax-acomp`: `|- E. X A. x ( x e. X <-> ph )`. Arithmetical comprehension. -/
def axAcomp : TAssertion L C V where
  dv := [(.X, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .svar .X, .ess ⟨.arith, .var .ph⟩]
  concl := ⟨.turnstile,
    .node .wsex [
      .node .wal [.node .wb [.node .wel [.var .X, .node .tvar [.var .x]], .var .ph], .var .x],
      .var .X
    ]⟩

/-- `ax-ind`: `|- ( A. x ( x = 0 -> ph ) -> ( A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph
) ) -> A. x ph ) )`. Full induction. -/
def axInd : TAssertion L C V where
  dv := [(.x, .y), (.y, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .nvar .y]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wi [.node .weq [.node .tvar [.var .x], .node .t0 []], .var .ph], .var .x],
      .node .wi [
        .node .wal [
          .node .wi [
            .node .wal [
              .node .wi [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]], .var .ph],
              .var .x
            ],
            .node .wal [
              .node .wi [
                .node .weq [.node .tvar [.var .x], .node .tS [.node .tvar [.var .y]]],
                .var .ph
              ],
              .var .x
            ]
          ],
          .var .y
        ],
        .node .wal [.var .ph, .var .x]
      ]
    ]⟩

/-- `ax-comp`: `|- E. X A. x ( x e. X <-> ph )`. Full comprehension. -/
def axComp : TAssertion L C V where
  dv := [(.X, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .svar .X]
  concl := ⟨.turnstile,
    .node .wsex [
      .node .wal [.node .wb [.node .wel [.var .X, .node .tvar [.var .x]], .var .ph], .var .x],
      .var .X
    ]⟩

/-! ## Theorems -/

/-- `a1i`: `|- ( ps -> ph )`. Inference form of ~ ax-1 . -/
def a1i : TAssertion L C V where
  dv := []
  hyps := [.float .wff .ph, .float .wff .ps, .ess ⟨.turnstile, .var .ph⟩]
  concl := ⟨.turnstile, .node .wi [.var .ps, .var .ph]⟩

/-- `dcomp-aca`: `|- ( A. x ( ph <-> ps ) -> E. X A. x ( x e. X <-> ph ) )`. Delta^0_1
comprehension holds in ACA0: ~ ax-dcomp follows from ~ ax-acomp by the coercion ~ arith-sig1 . -/
def dcompAca : TAssertion L C V where
  dv := [(.X, .ph), (.X, .ps)]
  hyps := [
    .float .wff .ph,
    .float .wff .ps,
    .float .nvar .x,
    .float .svar .X,
    .ess ⟨.sig1, .var .ph⟩,
    .ess ⟨.pi1, .var .ps⟩
  ]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wb [.var .ph, .var .ps], .var .x],
      .node .wsex [
        .node .wal [.node .wb [.node .wel [.var .X, .node .tvar [.var .x]], .var .ph], .var .x],
        .var .X
      ]
    ]⟩

/-- `ind-sig1-ind`: `|- ( A. x ( x = 0 -> ph ) -> ( A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y
-> ph ) ) -> A. x ph ) )`. Sigma^0_1 induction is an instance of full induction ~ ax-ind . -/
def indSig1Ind : TAssertion L C V where
  dv := [(.x, .y), (.y, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .nvar .y, .ess ⟨.sig1, .var .ph⟩]
  concl := ⟨.turnstile,
    .node .wi [
      .node .wal [.node .wi [.node .weq [.node .tvar [.var .x], .node .t0 []], .var .ph], .var .x],
      .node .wi [
        .node .wal [
          .node .wi [
            .node .wal [
              .node .wi [.node .weq [.node .tvar [.var .x], .node .tvar [.var .y]], .var .ph],
              .var .x
            ],
            .node .wal [
              .node .wi [
                .node .weq [.node .tvar [.var .x], .node .tS [.node .tvar [.var .y]]],
                .var .ph
              ],
              .var .x
            ]
          ],
          .var .y
        ],
        .node .wal [.var .ph, .var .x]
      ]
    ]⟩

/-- `acomp-comp`: `|- E. X A. x ( x e. X <-> ph )`. Arithmetical comprehension is an instance of
full comprehension ~ ax-comp . -/
def acompComp : TAssertion L C V where
  dv := [(.X, .ph)]
  hyps := [.float .wff .ph, .float .nvar .x, .float .svar .X, .ess ⟨.arith, .var .ph⟩]
  concl := ⟨.turnstile,
    .node .wsex [
      .node .wal [.node .wb [.node .wel [.var .X, .node .tvar [.var .x]], .var .ph], .var .x],
      .var .X
    ]⟩

/-- The logical axioms, labelled, in database order. -/
def axiomList : List (String × TAssertion L C V) := [
  ("ax-mp", axMp),
  ("ax-1", ax1),
  ("ax-2", ax2),
  ("ax-3", ax3),
  ("df-bi1", dfBi1),
  ("df-bi2", dfBi2),
  ("df-bi3", dfBi3),
  ("df-an", dfAn),
  ("ax-gen", axGen),
  ("ax-4", ax4),
  ("ax-5", ax5),
  ("ax-6", ax6),
  ("ax-7", ax7),
  ("ax-10", ax10),
  ("ax-11", ax11),
  ("ax-12", ax12),
  ("ax-13", ax13),
  ("ax-tex", axTex),
  ("df-ex", dfEx),
  ("ax-sgen", axSgen),
  ("ax-s4", axS4),
  ("ax-s5", axS5),
  ("ax-s6", axS6),
  ("ax-s7", axS7),
  ("ax-s10", axS10),
  ("ax-s11", axS11),
  ("ax-s12", axS12),
  ("ax-s13", axS13),
  ("ax-ns11", axNs11),
  ("ax-sn11", axSn11),
  ("df-sex", dfSex),
  ("df-seq", dfSeq),
  ("ax-eqS", axEqS),
  ("ax-eqpl1", axEqpl1),
  ("ax-eqpl2", axEqpl2),
  ("ax-eqmu1", axEqmu1),
  ("ax-eqmu2", axEqmu2),
  ("ax-eqlt1", axEqlt1),
  ("ax-eqlt2", axEqlt2),
  ("ax-eqel1", axEqel1),
  ("ax-eqel2", axEqel2),
  ("ax-S0", axS0),
  ("ax-Sinj", axSinj),
  ("ax-pl0", axPl0),
  ("ax-plS", axPlS),
  ("ax-mu0", axMu0),
  ("ax-muS", axMuS),
  ("ax-lt0", axLt0),
  ("ax-ltS", axLtS),
  ("bnd-eq", bndEq),
  ("bnd-lt", bndLt),
  ("bnd-el", bndEl),
  ("bnd-n", bndN),
  ("bnd-i", bndI),
  ("bnd-b", bndB),
  ("bnd-a", bndA),
  ("bnd-ral", bndRal),
  ("bnd-rex", bndRex),
  ("sig1-bnd", sig1Bnd),
  ("sig1-ex", sig1Ex),
  ("pi1-bnd", pi1Bnd),
  ("pi1-al", pi1Al),
  ("arith-eq", arithEq),
  ("arith-lt", arithLt),
  ("arith-el", arithEl),
  ("arith-seq", arithSeq),
  ("arith-n", arithN),
  ("arith-al", arithAl),
  ("arith-ex", arithEx),
  ("arith-i", arithI),
  ("arith-b", arithB),
  ("arith-a", arithA),
  ("arith-sig1", arithSig1),
  ("arith-pi1", arithPi1),
  ("ax-ind-sig1", axIndSig1),
  ("ax-dcomp", axDcomp),
  ("ax-sep1", axSep1),
  ("ax-acomp", axAcomp),
  ("ax-ind", axInd),
  ("ax-comp", axComp)]

/-- The theorems, labelled, in database order. -/
def theoremList : List (String × TAssertion L C V) := [
  ("a1i", a1i),
  ("dcomp-aca", dcompAca),
  ("ind-sig1-ind", indSig1Ind),
  ("acomp-comp", acompComp)]

end Silmaril.Logic.Metamath.SecondOrder
