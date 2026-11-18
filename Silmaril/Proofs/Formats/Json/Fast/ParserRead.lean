module

public import Silmaril.Formats.Json.Fast.Parser.Wire.Defs
import Silmaril.Formats.JsonWire.Defs

public section
namespace Silmaril.Proofs.Json.Fast.ParserRead

open Silmaril.Formats
open Silmaril.Formats.Json.Fast (Value)
open Silmaril.Formats.Json.Fast.Parser
open Silmaril.Formats.JsonWire Internal

@[expose] def arrayAst (children : List (Ast Decimal)) : Syn Decimal .arr := children.foldr .cons .nil

@[expose] def objectAst (entries : List (Units × Ast Decimal)) : Syn Decimal .obj :=
  entries.foldr (fun (key, child) rest => .objCons key child rest) .objNil

@[expose] def projectMember (depth : Nat) (entry : String × Value) : Option (Units × Ast Decimal) := do
  return (stringUnits entry.1, ← entry.2.toWire? depth)

private def arrayContinue (fuel : Nat) (ast : Ast Number) :
    List Token → Option (Syn Number .arr × List Token)
  | .arrayClose :: rest => some (.cons ast .nil, rest)
  | .comma :: rest => do
    let (tail, rest) ← array? .rfc8259 fuel false rest
    pure (.cons ast tail, rest)
  | _ => none

private theorem array_notClose {fuel : Nat} {tokens : List Token} {ast : Ast Number} {rest : List Token}
    (readHead : value? .rfc8259 fuel tokens = some (ast, rest)) (allowEmpty : Bool) :
    array? .rfc8259 (fuel + 1) allowEmpty tokens = arrayContinue fuel ast rest := by
  simp only [array?]
  split
  · cases fuel <;> simp_all [value?]
  · rw [readHead]
    cases rest with
    | nil => rfl
    | cons token _ => cases token <;> rfl

theorem arrayTail_read {depth : Nat} {tokens : List Token} {items : List Value}
    (trace : WireTail .arrayClose (MatchesValue depth) tokens items) :
    ∃ children, items.mapM (Value.toWire? depth) = some children ∧
      ∀ fuel, tokens.length < fuel → ∀ allowEmpty suffix,
        array? .rfc8259 fuel allowEmpty (tokens ++ suffix) =
          some ((arrayAst children).mapScalar liftScalar, suffix) := by
  induction trace with
  | @last head _ accepted =>
    obtain ⟨ast, projected, read⟩ := accepted
    refine ⟨[ast], by simp [List.mapM_cons, projected], ?_⟩
    intro fuel enough allowEmpty suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      have readHead := read fuel (by simp only [List.length_append, List.length_singleton] at enough; omega)
        (.arrayClose :: suffix)
      simpa [List.append_assoc, arrayContinue, arrayAst, RawSyn.mapScalar] using array_notClose readHead allowEmpty
  | @next head tail _ _ accepted _ ih =>
    obtain ⟨ast, projected, read⟩ := accepted
    obtain ⟨children, projectedTail, readTail⟩ := ih
    refine ⟨ast :: children, by simp [List.mapM_cons, projected, projectedTail], ?_⟩
    intro fuel enough allowEmpty suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_append, List.length_cons] at enough
      have readHead := read fuel (by omega) (.comma :: (tail ++ suffix))
      rw [List.append_assoc, List.cons_append, array_notClose readHead allowEmpty]
      simp [arrayContinue, readTail fuel (by omega) false suffix, arrayAst]

theorem objectTail_read {depth : Nat} {tokens : List Token} {items : List (String × Value)}
    (trace : WireTail .objectClose (MatchesMember depth) tokens items) :
    ∃ entries, items.mapM (projectMember depth) = some entries ∧
      ∀ fuel, tokens.length < fuel → ∀ allowEmpty suffix,
        object? .rfc8259 fuel allowEmpty (tokens ++ suffix) =
          some ((objectAst entries).mapScalar liftScalar, suffix) := by
  induction trace with
  | @last head entry accepted =>
    obtain ⟨childTokens, rfl, ast, projected, read⟩ := accepted
    refine ⟨[(stringUnits entry.1, ast)], by simp [List.mapM_cons, projectMember, projected], ?_⟩
    intro fuel enough allowEmpty suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_append, List.length_cons] at enough
      have readHead := read fuel (by omega) (.objectClose :: suffix)
      simp only [List.cons_append, List.append_assoc, List.nil_append, object?, bind, Option.bind,
        readHead, objectAst, List.foldr, RawSyn.mapScalar]
  | @next head tail entry _ accepted _ ih =>
    obtain ⟨childTokens, rfl, ast, projected, read⟩ := accepted
    obtain ⟨entries, projectedTail, readTail⟩ := ih
    refine ⟨(stringUnits entry.1, ast) :: entries,
      by simp [List.mapM_cons, projectMember, projected, projectedTail], ?_⟩
    intro fuel enough allowEmpty suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_append, List.length_cons] at enough
      have readHead := read fuel (by omega) (.comma :: (tail ++ suffix))
      simp only [List.cons_append, List.append_assoc, object?, bind, Option.bind, readHead]
      change (do
        let (children, left) ← object? .rfc8259 fuel false (tail ++ suffix)
        pure (RawSyn.objCons (stringUnits entry.1) (ast.mapScalar liftScalar) children, left)) = _
      rw [readTail fuel (by omega) false suffix]
      rfl

theorem lower_lift {sort : JsonIx} (ast : Syn Decimal sort) :
    mapNumbers? (fun | .finite decimal => some decimal | _ => none) (ast.mapScalar liftScalar) = some ast := by
  induction ast with
  | scalar atom =>
    cases atom with
    | none => rfl
    | some atom => cases atom <;> rfl
  | list _ ih | map _ ih => simp [RawSyn.mapScalar, mapNumbers?, ih]
  | nil | objNil => rfl
  | cons _ _ ih tail | objCons _ _ _ ih tail => simp [RawSyn.mapScalar, mapNumbers?, ih, tail]

end Silmaril.Proofs.Json.Fast.ParserRead
