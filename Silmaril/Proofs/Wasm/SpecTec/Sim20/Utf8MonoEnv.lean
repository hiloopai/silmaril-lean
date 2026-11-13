module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8MonoCall
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Mono.Defs

/-!
# The two 2.0 pairs of environments, each across `$utf8`

* `utf8Env20T B` agrees with `simEnv20T B` on every type, relation and grammar, on every
  definition but `$utf8` and on every primitive but `$utf8` (`findDef?_utf8Env20T_of_ne`,
  `findRel?_utf8Env20T`, `findTyp?_utf8Env20T`, `call_utf8Env20T_of_ne`), as an earlier
  `utf8Env20 B` agrees with `simEnv20 B`.
* `utf8Script20_simEnv20`, `utf8Script20_simEnv20T`: both scripts have the 2.0 `$utf8` and the
  first clause of `$concat_`, so `utf8_le20` applies to them.
* **`envExt20`**, **`envExt20T`**: each pair is an `EnvExt` at `$utf8`, when `B` leaves `$utf8`
  uninterpreted. `storeB_utf8`: the primitives of the forward invariant do.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res concatClause1)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (withUtf8 utf8Call)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 utf8BaseEnv20 utf8Clauses20)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## `utf8Env20T` against `simEnv20T` -/

@[simp] theorem findDef?_utf8Env20T :
    (utf8Env20T B).findDef? "utf8" = some (utf8Params, utf8Res, []) := by
  simp [utf8Env20T, utf8BaseEnv20T]

theorem findDef?_utf8Env20T_of_ne {x : IL.Id} (hx : x ≠ "utf8") :
    (utf8Env20T B).findDef? x = (simEnv20T B).findDef? x := by
  simp [utf8Env20T, utf8BaseEnv20T, simEnv20T, Ne.symm hx]

theorem findTyp?_utf8Env20T (x : IL.Id) : (utf8Env20T B).findTyp? x = (simEnv20T B).findTyp? x := by
  simp only [utf8Env20T, utf8BaseEnv20T, simEnv20T, Env.findTyp?, Env.bindDef, Env.withBuiltins]

theorem findRel?_utf8Env20T (x : IL.Id) : (utf8Env20T B).findRel? x = (simEnv20T B).findRel? x := by
  simp only [utf8Env20T, utf8BaseEnv20T, simEnv20T, Env.findRel?, Env.bindDef, Env.withBuiltins]

theorem findGram?_utf8Env20T (x : IL.Id) :
    (utf8Env20T B).findGram? x = (simEnv20T B).findGram? x := by
  simp only [utf8Env20T, utf8BaseEnv20T, simEnv20T, Env.findGram?, Env.bindDef, Env.withBuiltins]

theorem call_utf8Env20T_of_ne {x : IL.Id} (hx : x ≠ "utf8") (ws : List ArgV) :
    (utf8Env20T B).builtins.call x ws = B.call x ws := by
  simp [utf8Env20T, withUtf8, hx]

theorem call_utf8Env20T_utf8 (ws : List ArgV) :
    (utf8Env20T B).builtins.call "utf8" ws = utf8Call ws := by
  simp [utf8Env20T, withUtf8]

/-! ## `utf8Env20` against `simEnv20` (an earlier erratum) -/

theorem findTyp?_utf8Env20 (x : IL.Id) : (utf8Env20 B).findTyp? x = (simEnv20 B).findTyp? x := by
  simp only [utf8Env20, utf8BaseEnv20, simEnv20, Env.findTyp?, Env.bindDef, Env.withBuiltins]

theorem findGram?_utf8Env20 (x : IL.Id) : (utf8Env20 B).findGram? x = (simEnv20 B).findGram? x := by
  simp only [utf8Env20, utf8BaseEnv20, simEnv20, Env.findGram?, Env.bindDef, Env.withBuiltins]

/-! ## Matchers that read only the type and grammar tables -/

theorem matchTypV_eq {e₁ e₂ : Env} (h : ∀ x, e₂.findTyp? x = e₁.findTyp? x) :
    matchTypV e₂ = matchTypV e₁ := by
  have hm : ∀ x, e₂.memTyp x = e₁.memTyp x := fun x => by
    simp only [Env.memTyp, Map.mem]
    exact congrArg Option.isSome (h x)
  funext ρ pat t
  simp only [matchTypV, hm]

theorem matchSymV_eq {e₁ e₂ : Env} (h : ∀ x, e₂.findGram? x = e₁.findGram? x) :
    matchSymV e₂ = matchSymV e₁ := by
  have hm : ∀ x, e₂.memGram x = e₁.memGram x := fun x => by
    simp only [Env.memGram, Map.mem]
    exact congrArg Option.isSome (h x)
  funext ρ pat g
  simp only [matchSymV, hm]

theorem argSubOk_eq {e₁ e₂ : Env} (h : ∀ x, e₂.findTyp? x = e₁.findTyp? x) :
    argSubOk e₂ = argSubOk e₁ := by
  have hs : subCaseOk e₂ = subCaseOk e₁ := by
    funext ρ t v
    simp only [subCaseOk, h]
  funext ρ e v
  simp only [argSubOk, hs]

/-! ## The 2.0 `$utf8` in both scripts -/

theorem findDef_utf8_20T : (simEnv20T B).findDef? "utf8" =
    some (utf8Params, utf8Res, utf8Clauses20) := rfl

theorem findDef_concat_20 : ∃ ps t rest,
    (simEnv20 B).findDef? "concat_" = some (ps, t, concatClause1 :: rest) := ⟨_, _, _, rfl⟩

theorem findDef_concat_20T : ∃ ps t rest,
    (simEnv20T B).findDef? "concat_" = some (ps, t, concatClause1 :: rest) := ⟨_, _, _, rfl⟩

theorem utf8Script20_simEnv20 (hB : ∀ ws, B.call "utf8" ws = none) :
    Utf8Script20 (simEnv20 B) where
  utf8 := StoreBulk.findDef_utf8_20 B
  concat := findDef_concat_20 B
  memX := rfl
  call := hB

theorem utf8Script20_simEnv20T (hB : ∀ ws, B.call "utf8" ws = none) :
    Utf8Script20 (simEnv20T B) where
  utf8 := findDef_utf8_20T B
  concat := findDef_concat_20T B
  memX := rfl
  call := hB

/-! ## Both pairs extend across `$utf8` -/

/-- **`utf8Env20 B` extends `simEnv20 B` at `$utf8`.** -/
theorem envExt20 (hB : ∀ ws, B.call "utf8" ws = none) :
    EnvExt (simEnv20 B) (utf8Env20 B) "utf8" where
  defs _ hx := StoreBulk.findDef?_utf8Env20_of_ne B hx
  rels x := StoreBulk.findRel?_utf8Env20 B x
  typs x := findTyp?_utf8Env20 B x
  call _ hx ws := StoreBulk.call_utf8Env20_of_ne B hx ws
  typV := matchTypV_eq (findTyp?_utf8Env20 B)
  symV := matchSymV_eq (findGram?_utf8Env20 B)
  sub := argSubOk_eq (findTyp?_utf8Env20 B)
  at0 n ws := utf8_le20 (utf8Script20_simEnv20 B hB) (StoreBulk.findDef?_utf8Env20 B)
    (StoreBulk.call_utf8Env20_utf8 B) n ws

/-- **`utf8Env20T B` extends `simEnv20T B` at `$utf8`.** -/
theorem envExt20T (hB : ∀ ws, B.call "utf8" ws = none) :
    EnvExt (simEnv20T B) (utf8Env20T B) "utf8" where
  defs _ hx := findDef?_utf8Env20T_of_ne B hx
  rels x := findRel?_utf8Env20T B x
  typs x := findTyp?_utf8Env20T B x
  call _ hx ws := call_utf8Env20T_of_ne B hx ws
  typV := matchTypV_eq (findTyp?_utf8Env20T B)
  symV := matchSymV_eq (findGram?_utf8Env20T B)
  sub := argSubOk_eq (findTyp?_utf8Env20T B)
  at0 n ws := utf8_le20 (utf8Script20_simEnv20T B hB) (findDef?_utf8Env20T B)
    (call_utf8Env20T_utf8 B) n ws

/-! ## The primitives of the forward invariant leave `$utf8` uninterpreted -/

theorem floatIntB_utf8 (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    (Sim.Floats.floatIntB P).call "utf8" ws = none := by
  simp only [Sim.Floats.floatIntB, Sim.Floats.floatNames]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact Sim.Round7.intCall_utf8 ws

/-- **`Whole.storeB P` leaves `$utf8` uninterpreted.** -/
theorem storeB_utf8 (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    (Whole.storeB P).call "utf8" ws = none := by
  simp only [Whole.storeB, Whole.laneB, Whole.vbytesB, Whole.growB]
  simp only [ite_false, String.reduceEq, or_self]
  exact floatIntB_utf8 P ws

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
