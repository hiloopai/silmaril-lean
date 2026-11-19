module

public meta import Lean

public meta section
namespace Cerberus.RuntimeShard

/-- No arguments retains all original seeds; the harness partitions exactly these three. -/
def seeds (args : List String) : IO (List (Fin 3)) := do
  match args with
  | [] => pure (List.finRange 3)
  | ["--seed", text] =>
    match text.toNat? with
    | some n =>
      if h : n < 3 then pure [⟨n, h⟩]
      else throw <| IO.userError "seed must be 0, 1 or 2"
    | none => throw <| IO.userError "seed must be 0, 1 or 2"
  | _ => throw <| IO.userError "expected no arguments or --seed {0|1|2}"

def report (suite : String) (selected : List (Fin 3)) (cases : Nat) : IO Unit :=
  IO.println <| "CERBERUS_SHARD " ++ (Lean.Json.mkObj [
    ("schema", Lean.toJson "silmaril.cerberus.runtime-shard/1"),
    ("suite", Lean.toJson suite),
    ("seeds", Lean.toJson (selected.map Fin.val)),
    ("cases", Lean.toJson cases)]).compress
