module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceSemantics.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs

/-! # The two direct diamonds through the source square

The two direct φ diamonds of the atom regressions, with their registers
and labels in the universe of the tree semantics. They differ in the
operand that the φ of `join` takes from `reply`. For each, the checks on
the original graph give the semantic square: its φ run at the two
ordered exits is the run of the typed packed program of its compiled
lowering, in every model of the four primitives. Nothing is evaluated on
the normalized, lowered or elaborated graph. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics.Tests

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

private abbrev SortName := ULift.{1} Unit

private instance : AtomValues SortName := ⟨fun _ => ULift.{1} Nat⟩

private inductive Op | pick | test | echo | mark
  deriving DecidableEq

private abbrev tok : Ty SortName := .base ⟨()⟩
private abbrev pairTy : Ty SortName := .product tok tok
private abbrev sumTy : Ty SortName := .coprod pairTy tok
private abbrev testTy : Ty SortName := .coprod tok tok

/-- `pick` replies with a pair or one atom, `test` with one of two atoms,
`echo` and `mark` with one atom. -/
private instance : HasTy Op (Ty SortName) where
  src _ := tok
  trg
    | .pick => sumTy
    | .test => testTy
    | .echo => tok
    | .mark => tok

private instance : HasEff Op Bool := ⟨fun _ => true⟩

private abbrev signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Op

private inductive Reg : Type 1 | later | earlier | s | a | b | e | j | f | u | q | x | z
  deriving DecidableEq

private inductive Lbl : Type 1 | classify | reply | payload | join | leaf | done | other
  deriving DecidableEq

/-- The direct diamond: `reply`, `payload` and `leaf` read the registers of
earlier blocks, and only `join` has a φ, with its operand on the edge
from `reply`. -/
private def direct (incoming : Reg) : Phi.Graph Reg Lbl Op where
  entry := .let1 .s (.app .pick (.var .later)) (.term (Phi.br .classify))
  blocks :=
    [(.classify, ⟨[], .term (.case (.app .test (.var .earlier))
        .a (Phi.br .reply) .b (Phi.br .payload))⟩),
     (.reply, ⟨[], .let1 .e (.app .echo (.var .a)) (.term (Phi.br .join))⟩),
     (.payload, ⟨[], .term (Phi.br .join)⟩),
     (.join, ⟨[⟨.j, [(some .reply, .var incoming), (some .payload, .var .b)]⟩],
        .let1 .f (.app .mark (.var .j))
          (.term (.case (.val (.var .s)) .u (Phi.br .leaf)
            .q (.br (some .done) (.pair (.var .q) (.var .j)))))⟩),
     (.leaf, ⟨[], .let2 .x .z (.val (.var .u))
        (.term (.br (some .done) (.pair (.var .x) (.var .f))))⟩)]

private abbrev exits : List (Option Lbl) := [some .done, some .other]
private abbrev inputs : List Reg := [.later, .earlier]

private abbrev arrivals : Phi.GlobalSSA.Certificate Reg Lbl :=
  [(.classify, [.earlier, .s]), (.reply, [.s, .a]), (.payload, [.s, .b]), (.join, [.s]),
    (.leaf, [.u, .f])]

private def rank : Lbl → Nat
  | .classify => 4
  | .reply => 3
  | .payload => 3
  | .join => 2
  | .leaf => 1
  | _ => 0

private def types : Reg → Ty SortName
  | .s => sumTy
  | .u => pairTy
  | _ => tok

private def exitType : Option Lbl → Ty SortName
  | some .done => pairTy
  | _ => tok

private abbrev context : BoundCtx (Ty SortName) 2 := (BoundCtx.snoc .nil tok).snoc tok

/-- The two captures of the entry. -/
private def captures : Captures (Phi.Forward.Name Reg Lbl) context where
  names := ![some (.inl .later), some (.inl .earlier)]
  distinct := by decide
  privateUnit := by decide

/-- The source square for both diamonds, from checks on the direct graph
only: the scope check with its arrival claims, the condition on claims,
the rank, the fragment, the typing certificate, and the two captures at
their declared types. -/
example (incoming : Reg) (h : incoming = .e ∨ incoming = .a) :
    ∃ (code : FiniteCFG Op (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward (direct incoming)
            (Phi.Forward.infer (direct incoming) exits inputs)))).blocks.length exits.length 2)
      (typed : code.HasType context
        (internal (Phi.Forward.forward (direct incoming)
          (Phi.Forward.infer (direct incoming) exits inputs)) (forwardTypes types))
        (external exits exitType)),
      NamedFlat.compile (Phi.OrderedExits.lower (Phi.Forward.forward (direct incoming)
          (Phi.Forward.infer (direct incoming) exits inputs))) exits captures.names = some code ∧
      ∀ {Events : Type → Type} (M : Model (κ := SortName) Events signature.Instr)
        (record : Input context) (ambient : Env (Sigma (AtomValues.carrier (κ := SortName)))),
        (Phi.OrderedExits.run (treeModel M.raw) (direct incoming)
            (captures.store record ∘ Sum.inl) >>= fun p =>
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          region M.raw (extend ambient (encodeValue _ _ record))
            (Program.ofCFGEntry typed).code :=
  source_square_infer (P := signature) (direct incoming) exits inputs arrivals rank types exitType
    captures (by rcases h with rfl | rfl <;> decide +kernel)
    (by rcases h with rfl | rfl <;> decide +kernel) (by rcases h with rfl | rfl <;> decide +kernel)
    (by rcases h with rfl | rfl <;> decide +kernel) (by decide)
    (by rcases h with rfl | rfl <;> decide +kernel) (by decide)

/-- The same square for a table written by hand, which is not the inferred
one: it lists the same registers in another order, so the φ rows and the
packets of the normalized graph are ordered differently. The table is
checked on the original graph: no block defines a register it receives,
and the table is closed. -/
private abbrev handTable : Phi.Forward.Table Reg Lbl :=
  [(.classify, [.s]), (.reply, [.s, .a]), (.payload, [.s, .b]), (.join, [.s]), (.leaf, [.f, .u])]

example (incoming : Reg) (h : incoming = .e ∨ incoming = .a) :
    ∃ (code : FiniteCFG Op (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward (direct incoming) handTable))).blocks.length exits.length 2)
      (typed : code.HasType context
        (internal (Phi.Forward.forward (direct incoming) handTable) (forwardTypes types))
        (external exits exitType)),
      NamedFlat.compile (Phi.OrderedExits.lower (Phi.Forward.forward (direct incoming) handTable))
          exits captures.names = some code ∧
      ∀ {Events : Type → Type} (M : Model (κ := SortName) Events signature.Instr)
        (record : Input context) (ambient : Env (Sigma (AtomValues.carrier (κ := SortName)))),
        (Phi.OrderedExits.run (treeModel M.raw) (direct incoming)
            (captures.store record ∘ Sum.inl) >>= fun p =>
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          region M.raw (extend ambient (encodeValue _ _ record))
            (Program.ofCFGEntry typed).code :=
  source_square (P := signature) (direct incoming) handTable exits inputs types exitType captures
    (by rcases h with rfl | rfl <;> decide +kernel) (by rcases h with rfl | rfl <;> decide +kernel)
    (by rcases h with rfl | rfl <;> decide +kernel) (by decide)
    (by rcases h with rfl | rfl <;> decide +kernel) (by decide)

/-- The two diamonds are different graphs with the same checks; the square
holds for each with its own run on the left. -/
example : direct .e ≠ direct .a := by decide

example : Phi.Forward.infer (direct .e) exits inputs ≠ handTable := by decide +kernel

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceSemantics.Tests
