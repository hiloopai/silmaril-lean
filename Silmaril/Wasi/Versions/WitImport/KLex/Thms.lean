module

public import Silmaril.Wasi.Versions.WitImport.KLex.Defs

@[expose] public section

/-!
# The kernel-reducible WIT lexer is the lexer

PROVED (standard axioms): `takeLineK_eq`, `takeNumK_eq` (in `KLex.Defs`), `lex_eq_body` (the
well-founded `lex` unfolds to one `lexBody` step), **`lexK_eq`** (`lexK n cs = lex cs` when
`cs.length < n`) and **`parseCharsK_eq`** (`parseCharsK cs = (lex cs).bind Parse.document`).
The per-file kernel checks are in `WitImport/KParse/*`.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit.Text

theorem lex_eq_body (cs : List Char) : lex cs = lexBody cs fun cs' _ => lex cs' := by
  rw [lex.eq_def]
  simp only [← takeLineK_eq, ← takeNumK_eq]
  split <;> simp_all [lexBody]
  split <;> split <;> simp_all

/-- The fuelled step agrees for equal recursive calls. -/
theorem lexBody_congr (cs : List Char)
    (r₁ r₂ : (cs' : List Char) → cs'.length < cs.length → Option (List Tok))
    (h : ∀ cs' hc, r₁ cs' hc = r₂ cs' hc) : lexBody cs r₁ = lexBody cs r₂ := by
  have hr : r₁ = r₂ := funext fun cs' => funext fun hc => h cs' hc
  rw [hr]

/-- **The fuelled lexer is the lexer** when the fuel exceeds the length. -/
theorem lexK_eq : ∀ n cs, cs.length < n → lexK n cs = lex cs
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, cs, h => by
    rw [lexK, lex_eq_body cs]
    exact lexBody_congr cs _ _ fun cs' hc => lexK_eq n cs' (by omega)

/-- **The fuelled parser is the parser** of `Silmaril.Wasm.Wit.Text` on characters. -/
theorem parseCharsK_eq (cs : List Char) : parseCharsK cs = (lex cs).bind Parse.document := by
  rw [parseCharsK, lexK_eq _ cs (Nat.lt_succ_self _)]

end Silmaril.Wasi.Versions.WitImport
