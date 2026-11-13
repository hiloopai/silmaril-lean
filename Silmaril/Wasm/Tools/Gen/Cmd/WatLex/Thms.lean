module

public import Silmaril.Wasm.Tools.Gen.Cmd.WatLex.Defs
public import Silmaril.Raw.Wasm.Tools.Gen.Cmd.WatLex

/-!
# The linear-time WAT lexer: specification

* `lexF_eq` (proof in `Silmaril.Raw.Wasm.Tools.Gen.Cmd.WatLex`): `lexF p n N cs = lexGoFull p n
  cs` whenever `cs.length < N`;
* `lexFull?_eq`: `lexFull? p s` is the last stage of silmaril's `sexpWatFullExec? p s` (its
  full lexer at the same fuel, then the bracket matcher);
* `lexFull?_sound`: **the tree is one the WAT S-expression grammar gives the text**
  (`sexpWat p s tree`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WatLex

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat

theorem lexFull?_eq (p : Profile) (s : String) :
    lexFull? p s = (lexGoFull p (s.toList.length + 1) s.toList).bind bracketExec? := by
  simp only [lexFull?, lexF_eq p _ _ s.toList (Nat.lt_succ_self _)]

/-- **The linear-time lexer is sound for the WAT S-expression grammar.** -/
theorem lexFull?_sound {p : Profile} {s : String} {tree}
    (h : lexFull? p s = some tree) : sexpWat p s tree := by
  rw [lexFull?_eq] at h
  cases hl : lexGoFull p (s.toList.length + 1) s.toList with
  | none => simp [hl] at h
  | some tokens =>
    have hb : bracketExec? tokens = some tree := by simpa [hl] using h
    exact ⟨tokens, lexGoFull_sound p _ _ _ hl, bracketExec?_sound hb⟩

end Silmaril.Wasm.Tools.Gen.Cmd.WatLex
