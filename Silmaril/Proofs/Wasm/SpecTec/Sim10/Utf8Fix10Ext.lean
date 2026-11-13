module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Env
public import Silmaril.Wasm.SpecTec.Sim10.Round7Host.Thms

/-!
# The 1.0 `$utf8` erratum extends `simEnv10T` at `$utf8`

Round 6's 2.0 argument (`Sim20.Utf8Mono.utf8_le20`), with the 1.0 clauses of `$utf8`
(`Name10.utf8Clauses10`): at every fuel and on every argument list, the 1.0 `$utf8` answers at
most what the erratum's primitive answers (`utf8_le10`). On `[]` the four one-character clauses
are peeled and the last clause answers `[]`; on a non-empty list the clauses are out of fuel
(`Name10.tryClauses_utf8_ne10`); on any other argument list no pattern matches.

* **`envExt10T`**: `Utf8Mono.EnvExt (simEnv10T B) (utf8Env10T B) "utf8"` when `B` leaves `$utf8`
  uninterpreted. So every positive derivation of `simEnv10T B` is one of `utf8Env10T B`, with
  round 6's `Utf8Mono` lemmas.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (utf8Clause1 chsDom)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res concatClause1 clausePats BadArgs
  tryClauses_bad utf8Call_bad)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (utf8Call)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Name10 (utf8Clauses10 utf8Clauses10_split chPat_take4_10
  findDef_utf8_10T tryClauses_utf8_single10 tryClauses_utf8_long10)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (EnvExt tryClauses_peelCh tryClauses_last_nil bind_ok
  matchTypV_eq matchSymV_eq argSubOk_eq callAt)

set_option maxRecDepth 100000

variable {env : Env}

/-- On `[[]]` the 1.0 clauses answer `[]` or are out of fuel. -/
theorem tryClauses_utf8_nil10
    (hc : ∃ ps t rest, env.findDef? "concat_" = some (ps, t, concatClause1 :: rest))
    (hX : env.memTyp "X" = false) (n : Nat) :
    tryClauses n env utf8Clauses10 [.val (.list [])] = .error .outOfFuel ∨
      tryClauses n env utf8Clauses10 [.val (.list [])] = .ok (.list []) := by
  rw [utf8Clauses10_split]
  rcases tryClauses_peelCh (env := env) [] (by simp) [utf8Clause1] _ chPat_take4_10 n
    with h' | ⟨m, -, h'⟩
  · exact Or.inl h'
  · rw [h']
    exact tryClauses_last_nil hc hX m

theorem utf8Clauses10_pats : ∀ c ∈ utf8Clauses10,
    clausePats c = [.expA (.iterE (.varE "ch") chsDom)] ∨
      clausePats c = [.expA (.listE [.varE "ch"])] := by
  intro c hc
  rw [utf8Clauses10_split] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact Or.inr (chPat_take4_10 c hc)
  · obtain rfl := List.mem_singleton.1 hc
    exact Or.inl rfl

/-- **`$utf8` in the 1.0 script is below the erratum's primitive**, at every fuel and on every
argument list. -/
theorem utf8_le10 {env₂ : Env}
    (hd : env.findDef? "utf8" = some (utf8Params, utf8Res, utf8Clauses10))
    (hc : ∃ ps t rest, env.findDef? "concat_" = some (ps, t, concatClause1 :: rest))
    (hX : env.memTyp "X" = false) (hB : ∀ ws, env.builtins.call "utf8" ws = none)
    (h₂ : env₂.findDef? "utf8" = some (utf8Params, utf8Res, []))
    (hc₂ : ∀ ws, env₂.builtins.call "utf8" ws = utf8Call ws) (n : Nat) (ws : List ArgV) :
    callAt n env "utf8" ws ⊑ callAt n env₂ "utf8" ws := by
  simp only [callAt, hd, h₂, hc₂, hB, Res.ofOption, bind_ok]
  rcases n with _ | n
  · simp only [tryClauses, Res.elimUndef]; exact Res.oof_le _
  rw [show tryClauses (n + 1) env₂ [] ws = .error .undef by simp [tryClauses]]
  simp only [Res.elimUndef]
  by_cases hw : ∃ L, ws = [.val (.list L)]
  · obtain ⟨L, rfl⟩ := hw
    rcases L with _ | ⟨u, _ | ⟨u', us⟩⟩
    · rcases tryClauses_utf8_nil10 hc hX (n + 1) with h' | h' <;> simp only [h']
      · exact Res.oof_le _
      · exact Res.Le.refl _
    · simp only [tryClauses_utf8_single10 hd u]; exact Res.oof_le _
    · simp only [tryClauses_utf8_long10 hd]; exact Res.oof_le _
  · have hb : BadArgs ws := fun L h' => hw ⟨L, h'⟩
    rcases tryClauses_bad env ws hb _ utf8Clauses10_pats (n + 1) with h' | h' <;>
      simp only [h', utf8Call_bad hb]
    · exact Res.oof_le _
    · exact Res.Le.refl _

variable (B : Builtins)

set_option maxRecDepth 8000000 in
theorem findDef_concat_10T : ∃ ps t rest,
    (simEnv10T B).findDef? "concat_" = some (ps, t, concatClause1 :: rest) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 8000000 in
theorem memX_10T : (simEnv10T B).memTyp "X" = false := rfl

/-- **`utf8Env10T B` extends `simEnv10T B` at `$utf8`.** -/
theorem envExt10T (hB : ∀ ws, B.call "utf8" ws = none) :
    EnvExt (simEnv10T B) (utf8Env10T B) "utf8" where
  defs _ hx := findDef?_utf8Env10T_of_ne B hx
  rels x := findRel?_utf8Env10T B x
  typs x := findTyp?_utf8Env10T B x
  call _ hx ws := call_utf8Env10T_of_ne B hx ws
  typV := matchTypV_eq (findTyp?_utf8Env10T B)
  symV := matchSymV_eq (findGram?_utf8Env10T B)
  sub := argSubOk_eq (findTyp?_utf8Env10T B)
  at0 n ws := utf8_le10 (findDef_utf8_10T B) (findDef_concat_10T B) (memX_10T B) hB
    (findDef?_utf8Env10T B) (call_utf8Env10T_utf8 B) n ws

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
