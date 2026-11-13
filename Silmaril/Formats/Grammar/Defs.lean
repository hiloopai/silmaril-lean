module
public import Silmaril.Formats.Category.Thms

/-! Context-free EBNF with independent inductive semantics. Alternatives are
nondeterministic, repetition denotes finite concatenations, and references may
be mutually or left recursive. No executable decoder occurs in the definition
of grammatical validity. -/
@[expose] public section
namespace Silmaril.Formats.Grammar
inductive Symbol (Terminal Nonterminal : Type) where
  | terminal (value : Terminal)
  | nonterminal (value : Nonterminal)
  deriving DecidableEq, Repr, Inhabited

structure Rule (Terminal Nonterminal : Type) where
  lhs : Nonterminal
  rhs : List (Symbol Terminal Nonterminal)
  deriving DecidableEq, Repr

structure Cfg (Terminal Nonterminal : Type) where
  start : Nonterminal
  rules : Array (Rule Terminal Nonterminal)

namespace Ebnf
inductive Expr (Terminal Nonterminal : Type) where
  | empty
  | epsilon
  | terminal (value : Terminal)
  | reference (name : Nonterminal)
  | sequence (left right : Expr Terminal Nonterminal)
  | alternative (left right : Expr Terminal Nonterminal)
  | repetition (body : Expr Terminal Nonterminal)
  deriving DecidableEq, Repr

namespace Expr
variable {T N U M : Type}
def optional (body : Expr T N) : Expr T N := .alternative .epsilon body
def oneOrMore (body : Expr T N) : Expr T N := .sequence body (.repetition body)
def map (terminal : T → U) (nonterminal : N → M) : Expr T N → Expr U M
  | .empty => .empty
  | .epsilon => .epsilon
  | .terminal t => .terminal (terminal t)
  | .reference n => .reference (nonterminal n)
  | .sequence a b => .sequence (a.map terminal nonterminal) (b.map terminal nonterminal)
  | .alternative a b => .alternative (a.map terminal nonterminal) (b.map terminal nonterminal)
  | .repetition a => .repetition (a.map terminal nonterminal)
def ofSymbol : Symbol T N → Expr T N
  | .terminal t => .terminal t | .nonterminal n => .reference n
def word (symbols : List (Symbol T N)) : Expr T N :=
  symbols.foldr (fun s rest => .sequence (ofSymbol s) rest) .epsilon
end Expr

/-- Finite derivations are the semantics, including for nullable and
left-recursive grammars. Repetition is not a greedy parsing instruction. -/
inductive Derives {T N : Type} (body : N → Expr T N) : Expr T N → List T → Prop
  | epsilon : Derives body .epsilon []
  | terminal (t : T) : Derives body (.terminal t) [t]
  | reference {n xs} : Derives body (body n) xs → Derives body (.reference n) xs
  | sequence {a b xs ys} : Derives body a xs → Derives body b ys →
      Derives body (.sequence a b) (xs ++ ys)
  | left {a b xs} : Derives body a xs → Derives body (.alternative a b) xs
  | right {a b xs} : Derives body b xs → Derives body (.alternative a b) xs
  | nil {e} : Derives body (.repetition e) []
  | cons {e xs ys} : Derives body e xs → Derives body (.repetition e) ys →
      Derives body (.repetition e) (xs ++ ys)

structure System where
  Terminal : Type
  Nonterminal : Type
  start : Nonterminal
  body : Nonterminal → Expr Terminal Nonterminal

def System.Accepts (grammar : System) (input : List grammar.Terminal) : Prop :=
  Derives grammar.body (.reference grammar.start) input

/-- A structural grammar morphism renames terminals and nonterminals while
commuting with productions and preserving the distinguished start symbol. -/
@[ext] structure Hom (G H : System) where
  onTerminal : G.Terminal → H.Terminal
  onNonterminal : G.Nonterminal → H.Nonterminal
  start_commute : onNonterminal G.start = H.start
  body_commute : ∀ n, (G.body n).map onTerminal onNonterminal = H.body (onNonterminal n)
end Ebnf

namespace Cfg
variable {T N : Type}
/-- Finite production tables have the same independent EBNF semantics, with
all matching productions as alternatives. Ordering is immaterial to validity. -/
def body [DecidableEq N] (cfg : Cfg T N) (name : N) : Ebnf.Expr T N :=
  cfg.rules.toList.foldr (fun rule rest =>
    if rule.lhs = name then .alternative (.word rule.rhs) rest else rest) .empty
def toEbnf [DecidableEq N] (cfg : Cfg T N) : Ebnf.System :=
  ⟨T,N,cfg.start,cfg.body⟩
def Accepts [DecidableEq N] (cfg : Cfg T N) (input : List T) : Prop := cfg.toEbnf.Accepts input
end Cfg
end Silmaril.Formats.Grammar
