module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Closed
public import Silmaril.Wasm.SpecTec.Scripts.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x

/-!
# Errata locality: the wasm-3.0 errata change the grammar table only at their targets

`Scripts.fixedPatch_eq_self` says a definition that declares none of the thirteen targets comes
through the errata unchanged. This module lifts that to the lookup environment and the grammar
theory:

* `gramBinds_fixedPatch`: for a name `y` outside the targets, `fixedPatch` changes no grammar
  binding of `y` in **any** definition. This includes a recursion group that also declares a
  target. The proof is structural: each patch is a `replaceDef` that swaps one declaration for
  another with the same name (`gramBinds_replaceDef`).
* `findGram_fixed_eq`: the fixed and original environments agree on every grammar name outside
  the targets.
* `errata_locality`: with the evaluation environment `E` held fixed, the fixed and original
  production tables give the same theory outside the targets.
* `entails_local_iff`: about a closed set of nonterminals avoiding the targets, the two tables
  have the same consequences. `bsn_errata_local` instantiates it at the LEB128 grammars.

The function errata (#655 `$cont`, #656 `$utf8`) change the evaluation environment, not the
table. The statements therefore fix `E`. With `E` the fixed environment on one side and the
original on the other, the attribute actions can differ wherever a production calls `$cont` or
`$utf8`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-! ## The grammar bindings of a definition -/

mutual

/-- The grammar bindings a definition makes for the name `y`, in order (`envOfDef`'s
`bindGram`, which ignores the wildcard `_`). -/
def gramBinds (y : IL.Id) : Def → List GramDef
  | .gramD x ps t prods => if x ≠ "_" ∧ x = y then [(ps, t, prods)] else []
  | .recD ds => gramBindsL y ds
  | .typD .. => []
  | .relD .. => []
  | .decD .. => []

/-- `gramBinds` over a list of definitions. -/
def gramBindsL (y : IL.Id) : List Def → List GramDef
  | [] => []
  | d :: ds => gramBinds y d ++ gramBindsL y ds

end

/-- The lookup after a sequence of bindings: the last one, or the old value. -/
def lastOr (l : List GramDef) (o : Option GramDef) : Option GramDef :=
  l.foldl (fun _ v => some v) o

theorem lastOr_append (l₁ l₂ : List GramDef) (o : Option GramDef) :
    lastOr (l₁ ++ l₂) o = lastOr l₂ (lastOr l₁ o) := List.foldl_append ..

theorem findGram_bindGram (env : Env) (x y : IL.Id) (v : GramDef) :
    (env.bindGram x v).findGram? y = lastOr (if x ≠ "_" ∧ x = y then [v] else []) (env.findGram? y) := by
  rw [Env.findGram?_bindGram]
  by_cases h : x ≠ "_" ∧ x = y
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    rfl

mutual

/-- What a definition does to the lookup of `y`. -/
theorem findGram_envOfDef (y : IL.Id) :
    ∀ (env : Env) (d : Def), (envOfDef env d).findGram? y = lastOr (gramBinds y d) (env.findGram? y)
  | env, .gramD x ps t prods => findGram_bindGram env x y (ps, t, prods)
  | env, .recD ds => findGram_envOfDefs y env ds
  | _, .typD .. => rfl
  | _, .relD .. => rfl
  | _, .decD .. => rfl

/-- What a list of definitions does to the lookup of `y`. -/
theorem findGram_envOfDefs (y : IL.Id) :
    ∀ (env : Env) (ds : List Def),
      (envOfDefs env ds).findGram? y = lastOr (gramBindsL y ds) (env.findGram? y)
  | _, [] => rfl
  | env, d :: ds => by
    show (envOfDefs (envOfDef env d) ds).findGram? y = lastOr (gramBinds y d ++ gramBindsL y ds) _
    rw [findGram_envOfDefs y (envOfDef env d) ds, findGram_envOfDef y env d, lastOr_append]

end

theorem gramBindsL_map {y : IL.Id} {f : Def → Def} (hf : ∀ d, gramBinds y (f d) = gramBinds y d) :
    ∀ ds : List Def, gramBindsL y (ds.map f) = gramBindsL y ds
  | [] => rfl
  | d :: ds => by
    show gramBinds y (f d) ++ gramBindsL y (ds.map f) = gramBinds y d ++ gramBindsL y ds
    rw [hf d, gramBindsL_map hf ds]

/-! ## A replacement leaves the other names alone -/

theorem gramBinds_eq_nil {y : IL.Id} {d : Def} (hr : isRecD d = false)
    (h : declName? d ≠ some y) : gramBinds y d = [] := by
  cases d with
  | gramD x ps t prods =>
    have hxy : x ≠ y := fun e => h (by rw [e]; rfl)
    simp [gramBinds, hxy]
  | recD _ => cases hr
  | typD _ _ _ => rfl
  | relD _ _ _ _ _ => rfl
  | decD _ _ _ _ => rfl

theorem isRecD_of_declName {d : Def} {x : IL.Id} (h : declName? d = some x) : isRecD d = false := by
  cases d with
  | recD _ => cases h
  | _ => rfl

theorem gramBinds_replaceDef_aux {new d : Def} {x y : IL.Id} (hname : declName? new = some x)
    (hy : y ≠ x) (hr : isRecD d = false) : gramBinds y (replaceDef new d) = gramBinds y d := by
  rw [replaceDef_of_not_isRecD hr]
  by_cases hm : matchesDecl new d = true
  · obtain ⟨kx, hk, hn⟩ := declKind?_of_matchesDecl hm
    have hd : declName? d = some x := (declName?_eq_of_declKind? (hk.trans hn.symm)).trans hname
    have hne : ∀ e : Def, declName? e = some x → declName? e ≠ some y :=
      fun e he h => hy (Option.some_inj.mp (h.symm.trans he))
    rw [ite_eq_left_of_eq_true _ _ (eq_true hm), gramBinds_eq_nil (isRecD_of_declName hname) (hne new hname),
      gramBinds_eq_nil hr (hne d hd)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]

mutual

/-- **A patch changes no grammar binding of another name.** -/
theorem gramBinds_replaceDef {new : Def} {x y : IL.Id} (hname : declName? new = some x)
    (hy : y ≠ x) : ∀ d : Def, gramBinds y (replaceDef new d) = gramBinds y d
  | .recD ds => gramBindsL_replaceDefs hname hy ds
  | .gramD .. => gramBinds_replaceDef_aux hname hy rfl
  | .typD .. => gramBinds_replaceDef_aux hname hy rfl
  | .relD .. => gramBinds_replaceDef_aux hname hy rfl
  | .decD .. => gramBinds_replaceDef_aux hname hy rfl

/-- `gramBinds_replaceDef` on lists. -/
theorem gramBindsL_replaceDefs {new : Def} {x y : IL.Id} (hname : declName? new = some x)
    (hy : y ≠ x) : ∀ ds : List Def, gramBindsL y (replaceDefs new ds) = gramBindsL y ds
  | [] => rfl
  | d :: ds => by
    show gramBinds y (replaceDef new d) ++ gramBindsL y (replaceDefs new ds) =
      gramBinds y d ++ gramBindsL y ds
    rw [gramBinds_replaceDef hname hy d, gramBindsL_replaceDefs hname hy ds]

end

/-! ## The thirteen wasm-3.0 targets -/

/-- The names the thirteen wasm-3.0 patches declare: the grammars `Bi32`, `Bi64` and nine text
grammars, and the functions `$cont` and `$utf8`. -/
def wasm30Targets : List IL.Id :=
  ["Bi32", "Bi64", "cont", "utf8", "Tstringchar", "Tfloat", "Thexfloat", "Talign_", "Ttypeuse_",
    "Tblockcomment", "Tblockchar", "Texporttabledots_", "Treserved"]

set_option maxRecDepth 100000 in
/-- **No grammar binding outside the targets changes**, in any definition. -/
theorem gramBinds_fixedPatch {y : IL.Id} (hy : y ∉ wasm30Targets) (d : Def) :
    gramBinds y (Wasm30.fixedPatch d) = gramBinds y d := by
  simp only [wasm30Targets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := hy
  rw [Wasm30.fixedPatch, IL.Text6x.text6xPatch, IL.Binary51.binary51Patch,
    gramBinds_replaceDef rfl h₁₃, gramBinds_replaceDef rfl h₁₂, gramBinds_replaceDef rfl h₁₁,
    gramBinds_replaceDef rfl h₁₀, gramBinds_replaceDef rfl h₉, gramBinds_replaceDef rfl h₈,
    gramBinds_replaceDef rfl h₇, gramBinds_replaceDef rfl h₆, gramBinds_replaceDef rfl h₅,
    gramBinds_replaceDef rfl h₄, gramBinds_replaceDef rfl h₃, gramBinds_replaceDef rfl h₂,
    gramBinds_replaceDef rfl h₁]

/-- **The fixed and original environments agree on every grammar outside the targets.** -/
theorem findGram_fixed_eq {y : IL.Id} (hy : y ∉ wasm30Targets) :
    Wasm30.envFixed.findGram? y = Wasm30.envOriginal.findGram? y := by
  rw [Wasm30.envFixed, Wasm30.envOriginal, envOfScript, envOfScript, findGram_envOfDefs,
    findGram_envOfDefs, fixed_eq_map, gramBindsL_map (gramBinds_fixedPatch hy)]

/-- The production tables agree outside the targets, whatever evaluation environment `E`
supplies the attribute actions. -/
theorem prodsOf_fixed_eq (E : Env) {n : NT} (hn : n.1 ∉ wasm30Targets) :
    prodsOf E Wasm30.envFixed n = prodsOf E Wasm30.envOriginal n := by
  unfold prodsOf
  rw [findGram_fixed_eq hn]

/-- **Errata locality**: with the evaluation environment held fixed, the fixed and original
wasm-3.0 grammar theories have the same productions outside the thirteen targets. -/
theorem errata_locality (E : Env) :
    prodAxiomsWhere (fun n : NT => n.1 ∉ wasm30Targets) (prodsOf E Wasm30.envFixed) =
      prodAxiomsWhere (fun n : NT => n.1 ∉ wasm30Targets) (prodsOf E Wasm30.envOriginal) := by
  ext φ
  constructor
  · rintro ⟨x, g, hx, hg, rfl⟩
    exact ⟨x, g, hx, prodsOf_fixed_eq E hx ▸ hg, rfl⟩
  · rintro ⟨x, g, hx, hg, rfl⟩
    exact ⟨x, g, hx, (prodsOf_fixed_eq E hx).symm ▸ hg, rfl⟩

/-- **About a closed set of nonterminals that avoids the targets, the fixed and original tables
have the same consequences** (actions from the same `E`). -/
theorem entails_local_iff (E : Env) {R : NT → Prop}
    (hR : ClosedUnder R (prodsOf E Wasm30.envOriginal)) (hRt : ∀ n, R n → n.1 ∉ wasm30Targets)
    {g : Grammar.Sym NT Act} (hg : SymIn R g) (bs : Grammar.Bytes) (Q : Act → Prop) :
    Entails (prodAxioms (prodsOf E Wasm30.envFixed)) (.derives g bs Q) ↔
      Entails (prodAxioms (prodsOf E Wasm30.envOriginal)) (.derives g bs Q) := by
  have hR' : ClosedUnder R (prodsOf E Wasm30.envFixed) := fun n hn g hg =>
    hR n hn g (prodsOf_fixed_eq E (hRt n hn) ▸ hg)
  show (room actAlg NT).Entails _ _ ↔ (room actAlg NT).Entails _ _
  rw [← entails_fragment_iff actAlg hR' hRt hg, ← entails_fragment_iff actAlg hR hRt hg,
    errata_locality]

/-! ## An instance: the LEB128 grammars -/

/-- The LEB128 grammars `Bbyte`, `BuN` and `BsN`. -/
def isLeb (x : IL.Id) : Bool := x == "Bbyte" || x == "BuN" || x == "BsN"

theorem isLeb_not_target {x : IL.Id} (h : isLeb x = true) : x ∉ wasm30Targets := by
  simp only [isLeb, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl <;> decide

set_option maxRecDepth 100000 in
theorem checkLeb_original : checkGrams isLeb Wasm30.envOriginal.grams = true := by
  decide +kernel

/-- **The LEB128 consequences are local**: for every evaluation environment, the fixed and
original tables entail the same `BsN` facts. So #803 is untouched by the errata for a structural
reason, not only by the computation in `bsn_FF7E_not_entailed_fixed`. -/
theorem bsn_errata_local (E : Env) (W : Nat) (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    Entails (prodAxioms (prodsOf E Wasm30.envFixed)) (derivesNT "BsN" (argW W) ρ bs v) ↔
      Entails (prodAxioms (prodsOf E Wasm30.envOriginal)) (derivesNT "BsN" (argW W) ρ bs v) :=
  entails_local_iff E (closedUnder_ntOver checkLeb_original)
    (fun _ hn => isLeb_not_target hn.1) (g := .nt ("BsN", argW W)) ⟨rfl, rfl⟩ bs _

end Silmaril.Wasm.SpecTec.GrammarInst
