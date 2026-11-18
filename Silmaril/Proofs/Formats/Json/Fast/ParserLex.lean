module

public import Silmaril.Formats.Json.Fast.Parser.Thms
public import Silmaril.Formats.Json.Fast.Parser.Wire.Defs
import Silmaril.Formats.JsonWire.Grammar.Thms

public section
namespace Silmaril.Proofs.Json.Fast.ParserLex

open Silmaril.Formats
open Silmaril.Formats.Json.Fast (Error Value)
open Silmaril.Formats.Json.Fast.Parser
open Silmaril.Formats.JsonWire Internal

theorem skip_lex (pos : Pos) : LexedPrefix pos.rest (skip pos).rest [] := by
  obtain ⟨white, before, allWhite⟩ := whitespace_consumes pos.byteIdx pos.rest
  change pos.rest = white ++ (skip pos).rest at before
  rw [LexedPrefix, before, tokensOf_white_append allWhite]
  simp

theorem lex_append {input mid suffix : List Char} {left right : List Token}
    (first : LexedPrefix input mid left) (second : LexedPrefix mid suffix right) :
    LexedPrefix input suffix (left ++ right) := by
  unfold LexedPrefix at *
  rw [first, second, Option.map_map]
  simp only [Function.comp_def, List.append_assoc]

theorem char_step {pos : Pos} {char : Char} (notSentinel : char ≠ Char.ofNat 0) (found : pos.get = char) :
    pos.rest = char :: pos.next.rest := by
  cases pos with
  | mk offset rest =>
    cases rest with
    | nil => exact False.elim (notSentinel found.symm)
    | cons head tail => simpa [Pos.get, Pos.next] using found

private theorem follows_cons {char : Char} {tail : List Char}
    (delimiterChar : delimiter .rfc8259 char = true) : Follows (char :: tail) := by
  simp [Follows, delimiterChar]

theorem follows_skip {pos : Pos} (follows : Follows (skip pos).rest) : Follows pos.rest := by
  obtain ⟨white, before, allWhite⟩ := whitespace_consumes pos.byteIdx pos.rest
  change pos.rest = white ++ (skip pos).rest at before
  rw [before]
  cases white with
  | nil => exact follows
  | cons first tail =>
    have whiteFirst := allWhite first (by simp)
    exact follows_cons (by simp [delimiter, whiteFirst])

@[expose] def IsCloser (close : Char) (token : Token) : Prop :=
  close = ']' ∧ token = .arrayClose ∨ close = '}' ∧ token = .objectClose

private theorem closer_nonsentinel {close : Char} {token : Token} (closer : IsCloser close token) :
    close ≠ Char.ofNat 0 := by
  rcases closer with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

private theorem closer_delimiter {close : Char} {token : Token} (closer : IsCloser close token) :
    delimiter .rfc8259 close = true := by
  rcases closer with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

private theorem lex_closer {pos : Pos} {close : Char} {token : Token}
    (closer : IsCloser close token) (found : pos.get = close) : LexedPrefix pos.rest pos.next.rest [token] := by
  unfold LexedPrefix
  rw [char_step (closer_nonsentinel closer) found]
  rcases closer with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tokensOf_punct (Or.inr (Or.inl ⟨rfl, rfl⟩)) _
  · exact tokensOf_punct (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) _

theorem lex_comma {pos : Pos} (found : pos.get = ',') : LexedPrefix pos.rest pos.next.rest [.comma] := by
  unfold LexedPrefix
  rw [char_step (by decide) found]
  exact tokensOf_punct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) _

theorem more_lex {Item : Type} {close : Char} {token : Token} {Accept : List Token → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)} (closer : IsCloser close token)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) → Follows stop.rest →
      ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ Accept tokens item)
    {fuel : Nat} {pos stop : Pos} {acc output : Array Item}
    (result : more close parseItem fuel pos acc = .ok (output, stop)) :
    ∃ tokens items, LexedPrefix pos.rest stop.rest tokens ∧
      output.toList = acc.toList ++ items ∧ WireTail token Accept tokens items := by
  induction fuel generalizing pos acc with
  | zero => simp [more, fail] at result
  | succ fuel ih =>
    simp only [more] at result
    split at result
    · cases result
    · rename_i item itemStop parsed
      have prefixTokens (follows : Follows (skip itemStop).rest) :
          ∃ tokens, LexedPrefix pos.rest (skip itemStop).rest tokens ∧ Accept tokens item := by
        obtain ⟨tokens, read, accepted⟩ := soundItem parsed (follows_skip follows)
        have joined := lex_append (lex_append (skip_lex pos) read) (skip_lex itemStop)
        exact ⟨tokens, by simpa using joined, accepted⟩
      split at result
      · rename_i closeFound
        have closeFound := beq_iff_eq.mp closeFound
        have readClose := lex_closer closer closeFound
        have follows : Follows (skip itemStop).rest := by
          rw [char_step (closer_nonsentinel closer) closeFound]
          exact follows_cons (closer_delimiter closer)
        obtain ⟨tokens, read, accepted⟩ := prefixTokens follows
        cases result
        exact ⟨_, _, lex_append read readClose, Array.toList_push, .last accepted⟩
      · split at result
        · rename_i commaFound
          have commaFound := beq_iff_eq.mp commaFound
          have follows : Follows (skip itemStop).rest := by
            rw [char_step (by decide) commaFound]
            exact follows_cons (by decide)
          obtain ⟨tokens, read, accepted⟩ := prefixTokens follows
          obtain ⟨tail, items, readTail, allItems, acceptedTail⟩ := ih result
          refine ⟨_, _, lex_append read (lex_append (lex_comma commaFound) readTail), ?_, .next accepted acceptedTail⟩
          simpa [List.append_assoc] using allItems
        · simp [fail] at result

theorem series_lex {Item : Type} {close : Char} {token : Token} {Accept : List Token → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)} (closer : IsCloser close token)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) → Follows stop.rest →
      ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧ Accept tokens item)
    {size : Nat} {pos stop : Pos} {output : Array Item}
    (result : series size close parseItem pos = .ok (output, stop)) :
    ∃ tokens, LexedPrefix pos.rest stop.rest tokens ∧
      (tokens = [token] ∧ output.toList = [] ∨ WireTail token Accept tokens output.toList) := by
  simp only [series] at result
  split at result
  · rename_i closed
    have read := lex_append (skip_lex pos) (lex_closer closer (beq_iff_eq.mp closed))
    cases result
    exact ⟨_, read, .inl ⟨rfl, rfl⟩⟩
  · obtain ⟨tokens, items, read, order, realized⟩ := more_lex closer soundItem result
    refine ⟨_, lex_append (skip_lex pos) read, .inr ?_⟩
    simpa [order] using realized

end Silmaril.Proofs.Json.Fast.ParserLex
