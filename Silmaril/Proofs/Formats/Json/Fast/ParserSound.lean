module

public import Silmaril.Formats.Json.Fast.Wire.Defs
public import Silmaril.Formats.Json.Fast.Parser.Defs
public import Silmaril.Formats.JsonWire.Thms
import Silmaril.Proofs.Formats.Json.Fast.ParserLex
import Silmaril.Proofs.Formats.Json.Fast.ParserRead
import Silmaril.Formats.JsonWire.Grammar.Thms

public section
namespace Silmaril.Proofs.Json.Fast.ParserSound

open Silmaril.Formats
open Silmaril.Formats.Json.Fast (Error Value Limits parseText parseBytes)
open Silmaril.Formats.Json.Fast.Parser
open Silmaril.Formats.JsonWire Internal
open ParserLex ParserRead

private theorem bind_ok {Input Output : Type} {run : Except Error Input}
    {next : Input → Except Error Output} {out : Output} (ok : run.bind next = .ok out) :
    ∃ item, run = .ok item ∧ next item = .ok out := by
  cases run with
  | error => cases ok
  | ok item => exact ⟨item, rfl, ok⟩

private theorem expect_with_next {pos start : Pos} {char : Char}
    (ok : expect pos char = .ok start) : start = pos.next ∧ pos.get = char := by
  unfold expect at ok
  split at ok
  · rename_i allowed
    exact ⟨(Except.ok.inj ok).symm, beq_iff_eq.mp (Bool.and_eq_true_iff.mp allowed).2⟩
  · cases ok

private theorem member_lex {depth size : Nat} {parseValue : Pos → Except Error (Value × Pos)}
    (soundValue : ∀ {input stop out}, parseValue input = .ok (out, stop) → Follows stop.rest →
      ∃ tokens, LexedPrefix input.rest stop.rest tokens ∧ MatchesValue depth tokens out)
    {pos stop : Pos} {entry : String × Value} (ok : member size parseValue pos = .ok (entry, stop))
    (follows : Follows stop.rest) :
    ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ MatchesMember depth tokens entry := by
  obtain ⟨⟨key, keyStop⟩, keyRead, rest⟩ := bind_ok (run := quoted size pos) ok
  obtain ⟨start, colonRead, rest⟩ := bind_ok (run := expect (skip keyStop) ':') rest
  obtain ⟨⟨child, after⟩, childRead, rest⟩ := bind_ok (run := parseValue start) rest
  change Except.ok ((key, child), after) = .ok (entry, stop) at rest
  cases rest
  obtain ⟨rfl, colon⟩ := expect_with_next colonRead
  have colonLex : LexedPrefix (skip keyStop).rest (skip keyStop).next.rest [.colon] := by
    unfold LexedPrefix
    rw [char_step (by decide) colon]
    exact tokensOf_punct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) _
  obtain ⟨tokens, read, sound⟩ := soundValue childRead follows
  have stringLex : LexedPrefix pos.rest keyStop.rest [.string (stringUnits key)] := quoted_tokens keyRead
  exact ⟨_, lex_append stringLex (lex_append (skip_lex keyStop) (lex_append colonLex read)), ⟨tokens, rfl, sound⟩⟩

private theorem array_matches {depth size : Nat} {parseValue : Pos → Except Error (Value × Pos)}
    (soundValue : ∀ {pos stop out}, parseValue pos = .ok (out, stop) → Follows stop.rest →
      ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ MatchesValue depth tokens out)
    {start stop : Pos} {items : Array Value} (openArray : start.get = '[')
    (parsed : series size ']' parseValue start.next = .ok (items, stop)) :
    ∃ tokens, LexedPrefix start.rest stop.rest tokens ∧ MatchesValue (depth + 1) tokens (Value.ofArray items) := by
  have openLex : LexedPrefix start.rest start.next.rest [.arrayOpen] := by
    unfold LexedPrefix
    rw [char_step (by decide) openArray]
    exact tokensOf_punct (Or.inl ⟨rfl, rfl⟩) _
  obtain ⟨tokens, lex, tail⟩ := series_lex (Or.inl ⟨rfl, rfl⟩) soundValue parsed
  refine ⟨_, lex_append openLex lex, ?_⟩
  obtain ⟨children, projected, read⟩ : ∃ children, items.toList.mapM (Value.toWire? depth) = some children ∧
      ∀ fuel, tokens.length < fuel → ∀ suffix,
        array? .rfc8259 fuel true (tokens ++ suffix) = some ((arrayAst children).mapScalar liftScalar, suffix) := by
    rcases tail with ⟨rfl, isEmpty⟩ | nonempty
    · refine ⟨[], by rw [isEmpty]; rfl, ?_⟩
      intro fuel enough suffix
      cases fuel with
      | zero => omega
      | succ => rfl
    · obtain ⟨children, projected, read⟩ := arrayTail_read nonempty
      exact ⟨children, projected, fun fuel enough => read fuel enough true⟩
  refine ⟨.list (arrayAst children), ?_, ?_⟩
  · rw [Value.toWire?_ofArray, projected]; rfl
  · intro fuel enough suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.singleton_append, List.length_cons] at enough
      simp only [List.cons_append, List.nil_append, value?, read fuel (by omega) suffix,
        bind, Option.bind, RawSyn.mapScalar]
      rfl

private theorem object_matches {depth size : Nat} {parseValue : Pos → Except Error (Value × Pos)}
    (soundValue : ∀ {pos stop out}, parseValue pos = .ok (out, stop) → Follows stop.rest →
      ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ MatchesValue depth tokens out)
    {start stop : Pos} {items : Array (String × Value)} (openObject : start.get = '{')
    (parsed : series size '}' (member size parseValue) start.next = .ok (items, stop)) :
    ∃ tokens, LexedPrefix start.rest stop.rest tokens ∧ MatchesValue (depth + 1) tokens (Value.ofObject items) := by
  have openLex : LexedPrefix start.rest start.next.rest [.objectOpen] := by
    unfold LexedPrefix
    rw [char_step (by decide) openObject]
    exact tokensOf_punct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _
  obtain ⟨tokens, lex, tail⟩ := series_lex (Or.inr ⟨rfl, rfl⟩) (member_lex soundValue) parsed
  refine ⟨_, lex_append openLex lex, ?_⟩
  obtain ⟨children, projected, read⟩ : ∃ children, items.toList.mapM (projectMember depth) = some children ∧
      ∀ fuel, tokens.length < fuel → ∀ suffix,
        object? .rfc8259 fuel true (tokens ++ suffix) = some ((objectAst children).mapScalar liftScalar, suffix) := by
    rcases tail with ⟨rfl, isEmpty⟩ | nonempty
    · refine ⟨[], by rw [isEmpty]; rfl, ?_⟩
      intro fuel enough suffix
      cases fuel with
      | zero => omega
      | succ => rfl
    · obtain ⟨children, projected, read⟩ := objectTail_read nonempty
      exact ⟨children, projected, fun fuel enough => read fuel enough true⟩
  refine ⟨.map (objectAst children), ?_, ?_⟩
  · rw [Value.toWire?_ofObject]
    change (do let children ← items.toList.mapM (projectMember depth); pure (RawSyn.map (objectAst children) : Ast Decimal)) = _
    rw [projected]; rfl
  · intro fuel enough suffix
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.singleton_append, List.length_cons] at enough
      simp only [List.cons_append, List.nil_append, value?, read fuel (by omega) suffix,
        bind, Option.bind, RawSyn.mapScalar]
      rfl

private def scalarToken : Scalar Decimal → Token
  | none => .null
  | some (.bool flag) => .bool flag
  | some (.string text) => .string text
  | some (.number number) => .number (.finite number)

private theorem scalar_matches {depth : Nat} {out : Value} {scalar : Scalar Decimal}
    (projected : out.toWire? depth = some (.scalar scalar)) : MatchesValue depth [scalarToken scalar] out := by
  refine ⟨.scalar scalar, projected, ?_⟩
  intro fuel enough suffix
  cases fuel with
  | zero => omega
  | succ => cases scalar with
    | none => rfl
    | some atom => cases atom <;> rfl

private theorem value_lex (size numberBytes depth : Nat) {pos stop : Pos} {out : Value}
    (ok : value size numberBytes depth pos = .ok (out, stop)) (follows : Follows stop.rest) :
    ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ MatchesValue depth tokens out := by
  induction depth using Nat.strong_induction_on generalizing pos stop out with
  | ind depth ih =>
    rw [value.eq_def] at ok
    dsimp only at ok
    have prepend {tokens : List Token} (lex : LexedPrefix (skip pos).rest stop.rest tokens)
        (matched : MatchesValue depth tokens out) :
        ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ MatchesValue depth tokens out :=
      ⟨tokens, by simpa using lex_append (skip_lex pos) lex, matched⟩
    split at ok
    · rename_i found
      cases depth with
      | zero => cases ok
      | succ depth =>
        obtain ⟨⟨items, after⟩, parsed, ret⟩ := bind_ok (run := series size ']' (value size numberBytes depth) (skip pos).next) ok
        change Except.ok (Value.ofArray items, after) = .ok (out, stop) at ret
        cases ret
        obtain ⟨_, read, matched⟩ := array_matches (ih depth (Nat.lt_succ_self _)) found parsed
        exact prepend read matched
    · rename_i found
      cases depth with
      | zero => cases ok
      | succ depth =>
        obtain ⟨⟨items, after⟩, parsed, ret⟩ := bind_ok
          (run := series size '}' (member size (value size numberBytes depth)) (skip pos).next) ok
        change Except.ok (Value.ofObject items, after) = .ok (out, stop) at ret
        cases ret
        obtain ⟨_, read, matched⟩ := object_matches (ih depth (Nat.lt_succ_self _)) found parsed
        exact prepend read matched
    · obtain ⟨⟨text, after⟩, parsed, ret⟩ := bind_ok (run := quoted size (skip pos)) ok
      change Except.ok (Value.string text, after) = .ok (out, stop) at ret
      cases ret
      exact prepend (tokens := [.string (stringUnits text)]) (quoted_tokens parsed)
        (scalar_matches (scalar := some (.string (stringUnits text))) (by cases depth <;> rfl))
    · obtain ⟨after, parsed, ret⟩ := bind_ok (run := literal ['n', 'u', 'l', 'l'] (skip pos)) ok
      change Except.ok (Value.null, after) = .ok (out, stop) at ret
      cases ret
      apply prepend (tokens := [.null]) _ (scalar_matches (scalar := none) (by cases depth <;> rfl))
      rw [LexedPrefix, literal_consumes parsed]
      exact tokensOf_literal (Or.inr (Or.inr ⟨rfl, rfl⟩)) follows
    · obtain ⟨after, parsed, ret⟩ := bind_ok (run := literal ['t', 'r', 'u', 'e'] (skip pos)) ok
      change Except.ok (Value.bool true, after) = .ok (out, stop) at ret
      cases ret
      apply prepend (tokens := [.bool true]) _ (scalar_matches (scalar := some (.bool true)) (by cases depth <;> rfl))
      rw [LexedPrefix, literal_consumes parsed]
      exact tokensOf_literal (Or.inl ⟨rfl, rfl⟩) follows
    · obtain ⟨after, parsed, ret⟩ := bind_ok (run := literal ['f', 'a', 'l', 's', 'e'] (skip pos)) ok
      change Except.ok (Value.bool false, after) = .ok (out, stop) at ret
      cases ret
      apply prepend (tokens := [.bool false]) _ (scalar_matches (scalar := some (.bool false)) (by cases depth <;> rfl))
      rw [LexedPrefix, literal_consumes parsed]
      exact tokensOf_literal (Or.inr (Or.inl ⟨rfl, rfl⟩)) follows
    · split at ok
      · obtain ⟨digits, number, span, rfl, _, decoded⟩ := numberLoop_sound ok
        apply prepend (tokens := [.number (.finite number)]) _
          (scalar_matches (scalar := some (.number number)) (by cases depth <;> rfl))
        rw [LexedPrefix, span]
        exact tokensOf_number_exact decoded follows
      · cases ok

theorem parseBytes_sound {bytes : ByteArray} {limits : Limits} {result : Value}
    (parsed : parseBytes bytes limits = .ok result) :
    ∃ ast, result.toWire? limits.depth = some ast ∧ JsonWire.parse? ⟨bytes⟩ = some ast := by
  cases utf8 : String.fromUTF8? bytes with
  | none => simp [parseBytes, utf8] at parsed
  | some text =>
    simp only [parseBytes, utf8, parseText] at parsed
    let pos : Pos := ⟨0, text.toList⟩
    obtain ⟨⟨out, stop⟩, read, rest⟩ := bind_ok (run := value text.utf8ByteSize limits.numberBytes limits.depth pos) parsed
    change (if (skip stop).atEnd then Except.ok out else fail (skip stop) .trailingInput) = .ok result at rest
    split at rest
    · rename_i eof
      have endRest : (skip stop).rest = [] := List.isEmpty_iff.mp eof
      cases rest
      have follows : Follows stop.rest := ParserLex.follows_skip (pos := stop) (by simp [endRest, Follows])
      obtain ⟨tokens, lex, ast, projected, readWire⟩ := value_lex _ _ _ read follows
      have whole := lex_append lex (skip_lex stop)
      have tokensOfText : tokensOf text.toList = some tokens := by
        simpa [LexedPrefix, pos, endRest, tokensOf, Internal.lex] using whole
      have lexed := lex_tokens_eq (off := 0) (Nat.lt_succ_self text.toList.length)
      rw [tokensOfText] at lexed
      obtain ⟨lexed, lexedResult, tokenResult⟩ := Option.map_eq_some_iff.mp lexed
      have readAll := readWire (2 * tokens.length + 1) (by omega) []
      refine ⟨ast, projected, ?_⟩
      simp [JsonWire.parse?, parseDecimal?, Internal.decode, utf8, lexedResult, tokenResult,
        show value? .rfc8259 (2 * tokens.length + 1) tokens = _ from by simpa using readAll]
      exact lower_lift ast
    · cases rest

end Silmaril.Proofs.Json.Fast.ParserSound
