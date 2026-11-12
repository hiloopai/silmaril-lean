module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Script.Agree

/-!
# Round 7: `simEnv B` and `utf8Env B` agree away from `$utf8`

Pass 5's `Round7.envMonoAt` says `utf8Env B` answers at least what `simEnv B` answers;
`Round7.Script.agreeAt` says the converse on well-behaved inputs. Together, at every fuel, the two
environments give the same answer to every term whose definition references are reachable and
not `$utf8`, whose relation references are reachable, in a scope whose definition variables are
such definitions (`DefsOk`), with `ArgOk` arguments. The closure facts say which terms those are:
every reachable definition, relation and type other than `$utf8` and the type `name`
(`goodEvs_of_reach`).

This is the evaluator half of `Round7.Task.envAgreeNE`'s converse direction; the typing half
(`name`) and the quantifier values remain (see `docs/projects/spectec/README.md`).
The hypothesis on `B` is that it leaves `$utf8` uninterpreted, as round 6's `BI` does
(`Round7.BI_utf8`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {B : Builtins}

/-- **Expressions evaluate alike** in `utf8Env B` and `simEnv B`, away from `$utf8`. -/
theorem evalExp_utf8Env_eq (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {e : Exp} (hD : DefsOk ρ) (hG : GoodEvs (evExp e)) :
    evalExp n (utf8Env B) ρ e = evalExp n (simEnv B) ρ e :=
  le_antisymm' ((agreeAt B n).exp ρ e hD hG) ((Round7.envMonoAt B hB n).exp ρ e)

/-- **Patterns match alike.** -/
theorem matchExp_utf8Env_eq (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {e : Exp} {v : Value} (hD : DefsOk ρ) (hG : GoodEvs (evExp e)) :
    matchExp n (utf8Env B) ρ e v = matchExp n (simEnv B) ρ e v :=
  le_antisymm' ((agreeAt B n).matchExp ρ e v hD hG) ((Round7.envMonoAt B hB n).matchExp ρ e v)

/-- **Premises hold alike.** -/
theorem premsHold_utf8Env_eq (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {prs : List Prem} (hD : DefsOk ρ) (hG : GoodEvs (evPrems prs)) :
    premsHold n (utf8Env B) ρ prs = premsHold n (simEnv B) ρ prs :=
  le_antisymm' ((agreeAt B n).premsHold ρ prs hD hG) ((Round7.envMonoAt B hB n).premsHold ρ prs)

/-- **Calls answer alike**, for a reachable callee other than `$utf8`. -/
theorem callDef_utf8Env_eq (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {x : IL.Id} {ags : List Arg} (hD : DefsOk ρ) (hx : GoodName x) (hG : GoodEvs (evArgs ags)) :
    callDef n (utf8Env B) ρ x ags = callDef n (simEnv B) ρ x ags :=
  le_antisymm' ((agreeAt B n).callDef ρ x ags hD hx hG) ((Round7.envMonoAt B hB n).callDef ρ x ags)

/-- **Reachable relations derive alike.** -/
theorem derives_utf8Env_eq (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {x : IL.Id}
    {op : MixopS} {ags : List ArgV} {v : Value} (hx : (0, x) ∈ stepReach)
    (hW : ∀ w ∈ ags, ArgOk w) :
    derives n (utf8Env B) x op ags v = derives n (simEnv B) x op ags v := by
  apply Bool.eq_iff_iff.2
  exact ⟨(agreeAt B n).derives x op ags v hx hW, (Round7.envMonoAt B hB n).derives x op ags v⟩

/-- `EvalExp` in the two environments, away from `$utf8`. -/
theorem evalExp_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {e : Exp}
    {v : Value} (hD : DefsOk ρ) (hG : GoodEvs (evExp e)) :
    EvalExp (utf8Env B) ρ e v ↔ EvalExp (simEnv B) ρ e v := by
  simp only [EvalExp, evalExp_utf8Env_eq hB _ hD hG]

/-- `Derives` in the two environments, for a reachable relation. -/
theorem derives_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id} {op : MixopS}
    {ags : List ArgV} {v : Value} (hx : (0, x) ∈ stepReach) (hW : ∀ w ∈ ags, ArgOk w) :
    Derives (utf8Env B) x op ags v ↔ Derives (simEnv B) x op ags v := by
  simp only [Derives, derives_utf8Env_eq hB _ hx hW]

/-- **The `Step` relation derives alike** in the two environments (fuelled reading), at
argument-free calls. -/
theorem derives_step_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {op : MixopS} {v : Value} :
    Derives (utf8Env B) "Step" op [] v ↔ Derives (simEnv B) "Step" op [] v :=
  derives_utf8Env_iff hB step_mem_stepReach (by simp)

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
