module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.VAgree.Agree
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs

/-!
# Round 7, memory SIMD: `simEnv B₁` and `simEnv B₂` evaluate alike away from `$vbytes_`

`AgreeOff` is symmetric, so `VAgree.agreeAt` gives both inequalities, and `Script.le_antisymm'`
turns them into equalities. At every fuel, on `GoodEvs` syntax with a `DefsOk` scope:

* expressions, arguments, patterns, premises and calls answer alike (`evalExp_eq`,
  `evalArgs_eq`, `matchExp_eq`, `premsHold_eq`, `callDef_eq`);
* a `GoodRel` relation derives alike (`derives_eq`), and so does a list of `GoodEvs` rules
  (`anyRule_eq`), in particular one `GoodRule` of `Step_pure`, `Step_read` or `Step`
  (`anyRule_goodRule_eq`).

The fuel-free forms are `evalExp_iff`, `evalArgs_iff` and `derives_iff`. `withVBytes B` and `B`
agree off `$vbytes_` (`agreeOff_withVBytes`), which is the pair `BM`/`BI` of round 7.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evExp evArgs evPrems evRule le_antisymm')

variable {B₁ B₂ : Builtins}

theorem agreeOff_symm (h : AgreeOff B₁ B₂) : AgreeOff B₂ B₁ :=
  fun x ws hx => (h x ws hx).symm

/-- **`withVBytes B` and `B` agree off `$vbytes_`.** -/
theorem agreeOff_withVBytes (B : Builtins) : AgreeOff (MemSimd.withVBytes B) B := by
  intro x ws hx
  simp [MemSimd.withVBytes, hx]

theorem evalExp_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {e : Exp} (hD : DefsOk ρ)
    (hG : GoodEvs (evExp e)) : evalExp n (simEnv B₁) ρ e = evalExp n (simEnv B₂) ρ e :=
  le_antisymm' ((agreeAt B₁ B₂ hB n).exp ρ e hD hG)
    ((agreeAt B₂ B₁ (agreeOff_symm hB) n).exp ρ e hD hG)

theorem evalArgs_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {ags : List Arg}
    (hD : DefsOk ρ) (hG : GoodEvs (evArgs ags)) :
    evalArgs n (simEnv B₁) ρ ags = evalArgs n (simEnv B₂) ρ ags :=
  le_antisymm' ((agreeAt B₁ B₂ hB n).args ρ ags hD hG)
    ((agreeAt B₂ B₁ (agreeOff_symm hB) n).args ρ ags hD hG)

theorem matchExp_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {e : Exp} {v : Value}
    (hD : DefsOk ρ) (hG : GoodEvs (evExp e)) :
    matchExp n (simEnv B₁) ρ e v = matchExp n (simEnv B₂) ρ e v :=
  le_antisymm' ((agreeAt B₁ B₂ hB n).matchExp ρ e v hD hG)
    ((agreeAt B₂ B₁ (agreeOff_symm hB) n).matchExp ρ e v hD hG)

theorem premsHold_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {prs : List Prem}
    (hD : DefsOk ρ) (hG : GoodEvs (evPrems prs)) :
    premsHold n (simEnv B₁) ρ prs = premsHold n (simEnv B₂) ρ prs :=
  le_antisymm' ((agreeAt B₁ B₂ hB n).premsHold ρ prs hD hG)
    ((agreeAt B₂ B₁ (agreeOff_symm hB) n).premsHold ρ prs hD hG)

theorem callDef_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {x : IL.Id} {ags : List Arg}
    (hD : DefsOk ρ) (hx : GoodName x) (hG : GoodEvs (evArgs ags)) :
    callDef n (simEnv B₁) ρ x ags = callDef n (simEnv B₂) ρ x ags :=
  le_antisymm' ((agreeAt B₁ B₂ hB n).callDef ρ x ags hD hx hG)
    ((agreeAt B₂ B₁ (agreeOff_symm hB) n).callDef ρ x ags hD hx hG)

/-- **A `GoodRel` relation derives alike.** -/
theorem derives_eq (hB : AgreeOff B₁ B₂) (n : Nat) {x : IL.Id} {op : MixopS} {ags : List ArgV}
    {v : Value} (hx : GoodRel x) (hW : ∀ w ∈ ags, ArgOk w) :
    derives n (simEnv B₁) x op ags v = derives n (simEnv B₂) x op ags v :=
  Bool.eq_iff_iff.2 ⟨(agreeAt B₁ B₂ hB n).derives x op ags v hx hW,
    (agreeAt B₂ B₁ (agreeOff_symm hB) n).derives x op ags v hx hW⟩

/-- **`GoodEvs` rules fire alike.** -/
theorem anyRule_eq (hB : AgreeOff B₁ B₂) (n : Nat) {op : MixopS} {ps : List Param}
    {ags : List ArgV} {v : Value} {rs : List Rule} (hrs : ∀ r ∈ rs, GoodEvs (evRule r))
    (hW : ∀ w ∈ ags, ArgOk w) :
    anyRule n (simEnv B₁) op ps ags v rs = anyRule n (simEnv B₂) op ps ags v rs :=
  Bool.eq_iff_iff.2 ⟨(agreeAt B₁ B₂ hB n).anyRule op ps ags v rs hrs hW,
    (agreeAt B₂ B₁ (agreeOff_symm hB) n).anyRule op ps ags v rs hrs hW⟩

/-- **One `GoodRule` of a relation fires alike**: rule `i` of `x`, tried on its own. With
`goodRule_pure`, `goodRule_read` and `goodRule_step`, this covers every rule of `Step_pure`, every
rule of `Step_read` but 43 and every rule of `Step` but 1–5 and 23. -/
theorem anyRule_goodRule_eq (hB : AgreeOff B₁ B₂) (n : Nat) {x : IL.Id} {i : Nat}
    (hx : GoodRule x i) {B : Builtins} {d : RelDef} {r : Rule} (hd : (simEnv B).findRel? x = some d)
    (hr : d.2.2.2[i]? = some r) {op : MixopS} {ags : List ArgV} {v : Value}
    (hW : ∀ w ∈ ags, ArgOk w) :
    anyRule n (simEnv B₁) op d.1 ags v [r] = anyRule n (simEnv B₂) op d.1 ags v [r] :=
  anyRule_eq hB n (fun r' hr' => by
    rw [List.mem_singleton] at hr'
    rw [hr']
    exact hx B d r hd hr) hW

/-! ## Fuel-free forms -/

theorem evalExp_iff (hB : AgreeOff B₁ B₂) {ρ : VarEnv} {e : Exp} {v : Value} (hD : DefsOk ρ)
    (hG : GoodEvs (evExp e)) : EvalExp (simEnv B₁) ρ e v ↔ EvalExp (simEnv B₂) ρ e v := by
  simp only [EvalExp, evalExp_eq hB _ hD hG]

theorem evalArgs_iff (hB : AgreeOff B₁ B₂) {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (hD : DefsOk ρ) (hG : GoodEvs (evArgs ags)) :
    EvalArgs (simEnv B₁) ρ ags ws ↔ EvalArgs (simEnv B₂) ρ ags ws := by
  simp only [EvalArgs, evalArgs_eq hB _ hD hG]

/-- **`Derives` of a `GoodRel` relation, fuel-free.** -/
theorem derives_iff (hB : AgreeOff B₁ B₂) {x : IL.Id} {op : MixopS} {ags : List ArgV} {v : Value}
    (hx : GoodRel x) (hW : ∀ w ∈ ags, ArgOk w) :
    Derives (simEnv B₁) x op ags v ↔ Derives (simEnv B₂) x op ags v := by
  simp only [Derives, derives_eq hB _ hx hW]

/-- `derives_iff` at round 7's pair: `withVBytes B` against `B`. -/
theorem derives_withVBytes_iff (B : Builtins) {x : IL.Id} {op : MixopS} {ags : List ArgV}
    {v : Value} (hx : GoodRel x) (hW : ∀ w ∈ ags, ArgOk w) :
    Derives (simEnv (MemSimd.withVBytes B)) x op ags v ↔ Derives (simEnv B) x op ags v :=
  derives_iff (agreeOff_withVBytes B) hx hW

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
