import Lean.Data.Json
import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms

open Lean
open Silmaril.Logic.Smt (SE)
open Silmaril.ProofFormats
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.ProofFormats.DaslSyntax.Database

namespace NamedLogicExport

mutual
def tree : SE → Json
  | .atom text => .str text
  | .list children => .arr (trees children).toArray

def trees : List SE → List Json
  | [] => []
  | child :: children => tree child :: trees children
end

def block {Item : Type} (grammar : Syntax Item) (item : Item) : Json :=
  tree (grammar.codec.encode item)

def evidencePath := "Silmaril/ProofFormats/DaslSyntax/Database/Examples/Thms.lean"

def step {Checked : Prop} (_checked : Checked) (declaration : Name)
    (id rule judgment : String) (premises : List String := []) : Json :=
  Json.mkObj [("id", toJson id), ("rule", toJson rule), ("judgment", toJson judgment),
    ("premises", toJson premises), ("declaration", toJson declaration.toString)]

def row {Checked : Prop} (_checked : Checked) (declaration : Name)
    (id logic judgment scope : String) (roots : List (String × String))
    (assumptions : List String := []) (steps : List Json := []) : Json :=
  Json.mkObj [("id", toJson id), ("logic", toJson logic), ("judgment", toJson judgment),
    ("scope", toJson scope), ("roots", Json.mkObj (roots.map fun (role, key) => (role, toJson key))),
    ("assumptions", toJson assumptions), ("evidence", Json.mkObj [("declaration", toJson declaration.toString),
      ("path", toJson evidencePath), ("steps", toJson steps)])]

def plan (revision : String) : Json :=
  let holScope := "HOL Light initialSignature; empty added theory"
  let mlttScope := "Extensional MLTT; empty context; Sigma formation at U₀"
  let sigmaText := "Σ n : ℕ, Id ℕ n n"
  let pairText := "(zero, refl zero)"
  let holAssume := step Examples.HOL.assumed ``Examples.HOL.assumed "assume" "assume" "{p} ⊢ p"
  let sigmaForm := step Examples.MLTT.sigmaFormation ``Examples.MLTT.sigmaFormation
    "sigma" "dependent sum formation" s!"⊢ {sigmaText} : U₀"
  let pairTyping := step Examples.MLTT.pairTyping ``Examples.MLTT.pairTyping
    "pair" "dependent pair" s!"⊢ {pairText} : {sigmaText}" ["sigma"]
  Json.mkObj [
    ("format", "silmaril.named-logic.plan.v1"),
    ("source", Json.mkObj [("repo", "hiloopai/silmaril-lean"), ("revision", toJson revision)]),
    ("blocks", Json.mkObj [
      ("hol.closed", block DaslSyntax.HOL.tm Examples.HOL.closed),
      ("hol.assumptions", block DaslSyntax.HOL.assumptions [Examples.HOL.premise]),
      ("hol.premise", block DaslSyntax.HOL.tm Examples.HOL.premise),
      ("hol.consequence", block DaslSyntax.HOL.tm Examples.HOL.consequence),
      ("mltt.context", block DaslSyntax.MLTT.ctx .nil),
      ("mltt.sigma", block DaslSyntax.MLTT.ty Examples.MLTT.sigma),
      ("mltt.pair", block (DaslSyntax.MLTT.tm 0) Examples.MLTT.pair),
      ("mltt.first", block (DaslSyntax.MLTT.tm 0) (.fst Examples.MLTT.pair)),
      ("mltt.second", block (DaslSyntax.MLTT.tm 0) (.snd Examples.MLTT.pair)),
      ("mltt.nat", block DaslSyntax.MLTT.ty .nats),
      ("mltt.zero-fiber", block DaslSyntax.MLTT.ty (Examples.MLTT.fiber.lst .zero))]),
    ("rows", toJson [
      row Examples.HOL.closedRow ``Examples.HOL.closedRow "hol.closed" "HOL" "∅ ⊢ truth ⇒ truth"
        holScope [("conclusion", "hol.closed")] []
        [step Examples.HOL.closedProof ``Examples.HOL.closedProof "closed" "implication introduction"
          "∅ ⊢ truth ⇒ truth"],
      row Examples.HOL.contextRow ``Examples.HOL.contextRow "hol.named-assumption" "HOL" "{p} ⊢ truth ⇒ p"
        holScope [("context", "hol.assumptions"), ("conclusion", "hol.consequence")] ["hol.premise"]
        [holAssume, step Examples.HOL.consequenceProof ``Examples.HOL.consequenceProof "consequence"
          "weakening and implication introduction" "{p} ⊢ truth ⇒ p" ["assume"]],
      row Examples.MLTT.formationRow ``Examples.MLTT.formationRow "mltt.sigma-form" "MLTT"
        s!"⊢ {sigmaText} : U₀" mlttScope [("context", "mltt.context"), ("type", "mltt.sigma")] [] [sigmaForm],
      row Examples.MLTT.inhabitanceRow ``Examples.MLTT.inhabitanceRow "mltt.sigma-inhabited" "MLTT"
        s!"∃ term, ⊢ term : {sigmaText}" mlttScope
        [("context", "mltt.context"), ("type", "mltt.sigma")] [] [sigmaForm, pairTyping],
      row Examples.MLTT.typingRow ``Examples.MLTT.typingRow "mltt.sigma-typing" "MLTT"
        s!"⊢ {pairText} : {sigmaText}" mlttScope
        [("context", "mltt.context"), ("term", "mltt.pair"), ("type", "mltt.sigma")] [] [sigmaForm, pairTyping],
      row Examples.MLTT.firstProjection ``Examples.MLTT.firstProjection "mltt.sigma-first" "MLTT"
        s!"⊢ fst {pairText} ≡ zero : ℕ" mlttScope
        [("context", "mltt.context"), ("term", "mltt.first"), ("type", "mltt.nat")] []
        [step Examples.MLTT.firstProjection ``Examples.MLTT.firstProjection "fst" "first projection beta"
          s!"⊢ fst {pairText} ≡ zero : ℕ"],
      row Examples.MLTT.secondProjection ``Examples.MLTT.secondProjection "mltt.sigma-second" "MLTT"
        s!"⊢ snd {pairText} ≡ refl zero : Id ℕ zero zero" mlttScope
        [("context", "mltt.context"), ("term", "mltt.second"), ("type", "mltt.zero-fiber")] []
        [step Examples.MLTT.secondProjection ``Examples.MLTT.secondProjection "snd" "second projection beta"
          s!"⊢ snd {pairText} ≡ refl zero : Id ℕ zero zero"]])]

end NamedLogicExport

def main (args : List String) : IO Unit := do
  let [revision] := args | throw (IO.userError "expected the exact Git revision of the checked example sources")
  IO.println (NamedLogicExport.plan revision).compress
