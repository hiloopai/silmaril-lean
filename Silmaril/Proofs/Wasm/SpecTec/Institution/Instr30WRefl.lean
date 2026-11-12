module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30W.Defs

/-!
# Module typing of the wasm-3.0 script, `Module_ok` reflected at memory-only modules

`Instr30Z` proved that `Module_ok` holds at `memModuleV mts` whenever Core validates
every memory type in `mts`. This file proves the converse, by inverting `Module_ok`'s one rule:

* `moduleOk_memL_inv`: in every evaluator `simEnv B` and under every reading of `otherwise`, a
  `Module_ok(memModuleV mts, v)` fact gives `mt.Valid` for every `mt ∈ mts`, and `v` is the answer
  of the primitives to `$clos_moduletype(C, [] -> [])` at some context `C`;
* `moduleOk_memL_iff`: at the repaired primitives `withClosMod B`, `Module_ok(memModuleV mts, v)`
  holds **exactly** when `v = [] -> []` and Core validates every `mt ∈ mts`.

The inversion reads, from the conclusion, `import* = []`, `mem* = MEMORY mt*` and `export* = []`,
and the arguments of `$clos_moduletype`; from premise 1 (`Import_ok` over `import*` and `xt_I*`)
and premise 10 (`Export_ok` over `export*`, `nm*` and `xt_E*`), that `xt_I*` and `xt_E*` are empty
(the domains of an iterated premise have one length); and from premise 4 (`Mem_ok` over `mem*`
and `mt*`), through `Instr30Z.memOk_inv`, that every memory type is valid.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff not_tryClauses_and_undef)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (modConcl modPrems modPrem1 modPrem4 modPrem10 mtNil
  withClosMod moduleOkRule findDef_closMod tryClausesUndef_closMod)
open Silmaril.Wasm.SpecTec.Institution.Instr30Z (memV memModuleV memOk_inv dd_oneRule_inv)

variable {B : Builtins}

/-! ## Generic inversions -/

/-- A list of expressions evaluated, read componentwise. -/
theorem evalExps_forall₂ {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → List.Forall₂ (EvalExp env ρ) es vs
  | [], _, h => by
    obtain rfl := Equiv.Validation.evalExps_nil_iff.1 h
    exact .nil
  | _ :: _, _, h => by
    obtain ⟨w, ws, rfl, hw, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 h
    exact .cons hw (evalExps_forall₂ hws)

/-- A tuple expression evaluated to a tuple, read componentwise. -/
theorem evalExp_tupE_forall₂ {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExp env ρ (.tupE es) (.tuple vs)) : List.Forall₂ (EvalExp env ρ) es vs := by
  obtain ⟨ws, hws, he⟩ := evalExp_tupE_iff.1 h
  obtain rfl := Value.tuple.inj he
  exact evalExps_forall₂ hws

/-- `evalDoms`'s body, read one domain at a time. -/
theorem mapM_doms_forall₂ {env : Env} {ρ : VarEnv} {n : Nat} :
    ∀ {ds : List Dom} {xvs : List (IL.Id × Value)},
    ds.mapM (fun d => (fun v => (domVar d, v)) <$> evalExp n env ρ (domSrc d)) = .ok xvs →
      List.Forall₂ (fun d q => q.1 = domVar d ∧ EvalExp env ρ (domSrc d) q.2) ds xvs
  | [], xvs, h => by
    have hx : xvs = [] := by simpa [List.mapM_nil, Pure.pure, Except.pure] using h.symm
    exact hx ▸ .nil
  | d :: ds, xvs, h => by
    cases h₁ : evalExp n env ρ (domSrc d) with
    | error e => simp [List.mapM_cons, h₁, Bind.bind, Except.bind] at h
    | ok v =>
      cases h₂ : ds.mapM (fun d => (fun v => (domVar d, v)) <$> evalExp n env ρ (domSrc d)) with
      | error e => simp [List.mapM_cons, h₁, h₂, Bind.bind, Except.bind] at h
      | ok ws =>
        have hx : xvs = (domVar d, v) :: ws := by simpa [List.mapM_cons, h₁, h₂] using h.symm
        exact hx ▸ .cons ⟨rfl, n, h₁⟩ (mapM_doms_forall₂ h₂)

/-- The domains of an iteration, read one by one: each value is its domain's source, evaluated. -/
theorem evalDoms_forall₂ {env : Env} {ρ : VarEnv} {ds : List Dom} {xvs : List (IL.Id × Value)}
    (h : EvalDoms env ρ ds xvs) :
    List.Forall₂ (fun d q => q.1 = domVar d ∧ EvalExp env ρ (domSrc d) q.2) ds xvs := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [evalDoms] at hn
  | succ n => exact mapM_doms_forall₂ (by simpa only [evalDoms] using hn)

/-- `domLists` keeps every list-valued domain, under its name. -/
theorem mem_domLists {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
    (h : domLists xvs = some dls) {x : IL.Id} {l : List Value} (hx : (x, Value.list l) ∈ xvs) :
    (x, l) ∈ dls := by
  induction xvs generalizing dls with
  | nil => cases hx
  | cons q xvs ih =>
    simp only [domLists, List.mapM_cons] at h ih
    cases h₁ : q.2.asList? with
    | none => simp [h₁] at h
    | some l₁ =>
      cases h₂ : xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) with
      | none => simp [h₁, h₂] at h
      | some ls =>
        simp [h₁, h₂] at h
        subst h
        rcases List.mem_cons.1 hx with rfl | hx
        · simp only [Value.asList?, Option.some.injEq] at h₁
          subst h₁
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h₂ hx)

/-- A related element of a member. -/
theorem forall₂_exists_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => by cases ha
  | _, _, .cons hab hs, _, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_of_mem hs ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- **One length for all domains**: in an iteration over `k` rounds, a domain `x <- y` with `y`
bound to a list has that list's length `k`. -/
theorem iterLen_of_dom {env : Env} {ρ : VarEnv} {ds : List Dom} {xvs : List (IL.Id × Value)}
    {dls : List (IL.Id × List Value)} {k : Nat} (hd : EvalDoms env ρ ds xvs)
    (hdl : domLists xvs = some dls) (hk : ∀ d ∈ dls, d.2.length = k) {x y : IL.Id}
    {l : List Value} (hmem : Dom.mk x (.varE y) ∈ ds) (hy : ρ.findVal? y = some (.list l)) :
    l.length = k := by
  obtain ⟨⟨x', w⟩, hq, hq₁, hq₂⟩ := forall₂_exists_of_mem (evalDoms_forall₂ hd) hmem
  obtain rfl : x' = x := hq₁
  obtain rfl : w = .list l := Option.some.inj ((evalExp_varE_iff.1 hq₂).symm.trans hy)
  exact hk _ (mem_domLists hdl hq)

/-- `x*` over `x <- xs`, inverted: `xs` is bound to the result. -/
theorem star_inv {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_") {w : Value}
    (h : EvalExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) w) :
    ∃ l, ρ.findVal? xs = some (.list l) ∧ w = .list l :=
  Round5.Target.evalExp_iterList_inv
    (fun _ _ _ hw hu => Option.some.inj ((evalExp_varE_iff.1 hu).symm.trans hw)) hx h

/-- `%(x*)` evaluated to `%(w)`, inverted: `xs` is bound to `w`. -/
theorem pctStar_inv {env : Env} {ρ : VarEnv} {x xs : IL.Id} (hx : x ≠ "_") {w : Value}
    (h : EvalExp env ρ (.caseE "%" (.tupE [.iterE (.varE x) (.mk .list [.mk x (.varE xs)])]))
      (.case "%" (.tuple [w]))) : ρ.findVal? xs = some w := by
  have h₁ := evalExp_tupE_forall₂ (Instr30Z.evalExp_case_inv h)
  simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at h₁
  obtain ⟨l, hl, rfl⟩ := star_inv hx h₁
  exact hl

/-! ## The conclusion -/

set_option maxRecDepth 100000 in
/-- `Module_ok` is the one rule `moduleOkRule`. -/
theorem rel_moduleOk : ∃ t, (simEnv B).findRel? "Module_ok" = some ([], "|-%:%", t, [moduleOkRule]) :=
  ⟨_, rfl⟩

/-- `Module_ok`'s conclusion has no empty-domain option iteration. -/
theorem conclAlts_modConcl : conclAlts modConcl = [modConcl] := rfl

/-- The module part of `Module_ok`'s conclusion. -/
def modModE : Exp := match modConcl with | .tupE (e :: _) => e | e => e

/-- The type part of `Module_ok`'s conclusion, `$clos_moduletype(C, %->%(xt_I*, xt_E*))`. -/
def closE : Exp := match modConcl with | .tupE [_, e] => e | e => e

/-- `Module_ok`'s conclusion is the pair of its two parts. -/
theorem modConcl_eq : modConcl = .tupE [modModE, closE] := rfl

/-- **The module part, read back** at a module without imports and exports: `import*` and
`export*` are empty and `mem*` is bound to the memory list `M`. -/
theorem modModE_inv {env : Env} {ρ : VarEnv} {a₀ a₂ a₃ M a₅ a₆ a₇ a₈ a₉ : Value}
    (h : EvalExp env ρ modModE
      (.case "MODULE" (.tuple [a₀, pctNil, a₂, a₃, .case "%" (.tuple [M]), a₅, a₆, a₇, a₈, a₉,
        pctNil]))) :
    ρ.findVal? "import*" = some (.list []) ∧ ρ.findVal? "mem*" = some M ∧
      ρ.findVal? "export*" = some (.list []) := by
  have hc := evalExp_tupE_forall₂ (Instr30Z.evalExp_case_inv h)
  have hc' := List.forall₂_cons.1 hc
  have hc₁ := List.forall₂_cons.1 hc'.2
  have hc₄ := List.forall₂_cons.1 (List.forall₂_cons.1 (List.forall₂_cons.1 hc₁.2).2).2
  have hc₁₀ := List.forall₂_cons.1 (List.forall₂_cons.1 (List.forall₂_cons.1
    (List.forall₂_cons.1 (List.forall₂_cons.1 (List.forall₂_cons.1 hc₄.2).2).2).2).2).2
  exact ⟨pctStar_inv (by decide) hc₁.1, pctStar_inv (by decide) hc₄.1,
    pctStar_inv (by decide) hc₁₀.1⟩

/-- The argument `%->%(xt_I*, xt_E*)` of `$clos_moduletype`, read back. -/
theorem mtArg_inv {env : Env} {ρ : VarEnv} {m : Value}
    (h : EvalExp env ρ (.caseE "%->%" (.tupE [
      .iterE (.varE "xt_I") (.mk .list [.mk "xt_I" (.varE "xt_I*")]),
      .iterE (.varE "xt_E") (.mk .list [.mk "xt_E" (.varE "xt_E*")])])) m) :
    ∃ xI xE, ρ.findVal? "xt_I*" = some (.list xI) ∧ ρ.findVal? "xt_E*" = some (.list xE) ∧
      m = .case "%->%" (.tuple [.list xI, .list xE]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  have hf := evalExps_forall₂ hus
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, us = [a, b] ∧ EvalExp env ρ (.iterE (.varE "xt_I")
      (.mk .list [.mk "xt_I" (.varE "xt_I*")])) a ∧ EvalExp env ρ (.iterE (.varE "xt_E")
      (.mk .list [.mk "xt_E" (.varE "xt_E*")])) b := by
    rcases hf with _ | ⟨g₁, _ | ⟨g₂, gn⟩⟩
    cases gn
    exact ⟨_, _, rfl, g₁, g₂⟩
  obtain ⟨xI, fI, haI⟩ := star_inv (by decide) ha
  obtain ⟨xE, fE, hbE⟩ := star_inv (by decide) hb
  exact ⟨xI, xE, fI, fE, by rw [hab, haI, hbE]⟩

/-- **The type part, read back**: `v` is the primitives' answer to `$clos_moduletype` at some
context and at `%->%(xt_I*, xt_E*)`. -/
theorem closE_inv {ρ : VarEnv} (hρ : ρ.findDef? "clos_moduletype" = none) {v : Value}
    (h : EvalExp (simEnv B) ρ closE v) :
    ∃ c xI xE, ρ.findVal? "xt_I*" = some (.list xI) ∧ ρ.findVal? "xt_E*" = some (.list xE) ∧
      B.call "clos_moduletype" [.val c, .val (.case "%->%" (.tuple [.list xI, .list xE]))] =
        some v := by
  obtain ⟨ws, ps, t, cs, ha, hd, hcs⟩ := callDef_iff.1 (evalExp_callE_iff.1 h)
  obtain ⟨c, ws₁, -, ha₁, hws⟩ := Round5.BwdStep.evalArgs_cons_inv ha
  obtain ⟨m, ws₂, hm, ha₂, hws₁⟩ := Round5.BwdStep.evalArgs_cons_inv ha₁
  have hws₂ : ws₂ = [] := evalArgs_nil_iff.1 ha₂
  obtain ⟨xI, xE, fI, fE, hmv⟩ := mtArg_inv hm
  have hargs : ws = [.val c, .val (.case "%->%" (.tuple [.list xI, .list xE]))] := by
    rw [hws, hws₁, hws₂, hmv]
  have hcs' : cs = Instr30X.closModClauses := by
    obtain ⟨ps', t', hd'⟩ := findDef_closMod (B := B)
    rw [hρ, Option.getD_none, hd'] at hd
    cases hd
    rfl
  rw [hρ, Option.getD_none, hcs', hargs] at hcs
  rcases hcs with hcs | ⟨-, hb⟩
  · exact (not_tryClauses_and_undef hcs (tryClausesUndef_closMod _ _)).elim
  · exact ⟨c, xI, xE, fI, fE, by rwa [simEnv, Env.builtins_withBuiltins] at hb⟩

/-! ## The premises -/

/-- An iterated premise over `x₁ <- y₁` and `x₂ <- y₂`, at `y₁` bound to `[]`: `y₂`, bound to a
list, is empty. -/
theorem iterNil_two {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ y₁ x₂ y₂ : IL.Id} {l : List Value}
    (h : DPremB env O els ρ (.iterPr pr (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)])))
    (h₁ : ρ.findVal? y₁ = some (.list [])) (h₂ : ρ.findVal? y₂ = some (.list l)) : l = [] := by
  cases h with
  | iterList _ hd _ hdl hk _ =>
    have e₁ := iterLen_of_dom hd hdl hk List.mem_cons_self h₁
    have e₂ := iterLen_of_dom hd hdl hk (List.mem_cons_of_mem _ List.mem_cons_self) h₂
    exact List.eq_nil_of_length_eq_zero (e₂.trans e₁.symm)

/-- An iterated premise over three domains, at the first bound to `[]`: the third, bound to a
list, is empty. -/
theorem iterNil_three {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ y₁ x₂ y₂ x₃ y₃ : IL.Id} {l : List Value}
    (h : DPremB env O els ρ
      (.iterPr pr (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂), .mk x₃ (.varE y₃)])))
    (h₁ : ρ.findVal? y₁ = some (.list [])) (h₃ : ρ.findVal? y₃ = some (.list l)) : l = [] := by
  cases h with
  | iterList _ hd _ hdl hk _ =>
    have e₁ := iterLen_of_dom hd hdl hk List.mem_cons_self h₁
    have e₃ := iterLen_of_dom hd hdl hk
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h₃
    exact List.eq_nil_of_length_eq_zero (e₃.trans e₁.symm)

/-- Two variable domains, read back. -/
theorem doms_two_inv {env : Env} {ρ : VarEnv} {x₁ y₁ x₂ y₂ : IL.Id} {xvs : List (IL.Id × Value)}
    (h : List.Forall₂ (fun d q => q.1 = domVar d ∧ EvalExp env ρ (domSrc d) q.2)
      [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)] xvs) :
    ∃ w₁ w₂, xvs = [(x₁, w₁), (x₂, w₂)] ∧ ρ.findVal? y₁ = some w₁ ∧ ρ.findVal? y₂ = some w₂ := by
  rcases h with _ | ⟨⟨e₁, g₁⟩, _ | ⟨⟨e₂, g₂⟩, gn⟩⟩
  cases gn
  rename_i q₁ q₂
  obtain ⟨n₁, w₁⟩ := q₁
  obtain ⟨n₂, w₂⟩ := q₂
  have hn₁ : n₁ = x₁ := e₁
  have hn₂ : n₂ = x₂ := e₂
  exact ⟨w₁, w₂, by rw [hn₁, hn₂], evalExp_varE_iff.1 g₁, evalExp_varE_iff.1 g₂⟩

/-- `domLists` at two domains, the first a list. -/
theorem domLists_two {x₁ x₂ : IL.Id} {l₁ : List Value} {w₂ : Value}
    {dls : List (IL.Id × List Value)} (h : domLists [(x₁, .list l₁), (x₂, w₂)] = some dls) :
    ∃ l₂, w₂ = .list l₂ ∧ dls = [(x₁, l₁), (x₂, l₂)] := by
  cases w₂ with
  | list l₂ => exact ⟨l₂, rfl, by simpa [domLists, Value.asList?] using h.symm⟩
  | _ => simp [domLists, Value.asList?] at h

/-- Round `i` of a two-domain iteration over lists of length `k`. -/
theorem row_mem_iterRows {x₁ x₂ : IL.Id} {l₁ l₂ : List Value} {k i : Nat} (hi : i < k)
    (h₁ : l₁.length = k) (h₂ : l₂.length = k) :
    [(x₁, l₁[i]'(h₁ ▸ hi)), (x₂, l₂[i]'(h₂ ▸ hi))] ∈ iterRows [(x₁, l₁), (x₂, l₂)] none k := by
  simp only [iterRows, List.mem_map, List.mem_range]
  exact ⟨i, hi, by simp [iterRow, h₁ ▸ hi, h₂ ▸ hi]⟩

/-- **A two-domain iterated premise, unrolled**: with `y₁` bound to `l₁`, `y₂` is bound to a list
`l₂` of the same length, and the premise holds in every round. -/
theorem iterList_two_rows {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ y₁ x₂ y₂ : IL.Id} {l₁ : List Value}
    (h : DPremB env O els ρ (.iterPr pr (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)])))
    (hy : ρ.findVal? y₁ = some (.list l₁)) :
    ∃ l₂ : List Value, ∃ hl : l₂.length = l₁.length, ∀ i (hi : i < l₁.length),
      DPremB env O els (ρ.bindVals [(x₁, l₁[i]), (x₂, l₂[i]'(hl ▸ hi))]) pr := by
  cases h with
  | @iterList _ _ _ _ _ xvs dls k _ hd _ hdl hk hrows =>
    obtain ⟨w₁, w₂, hx, f₁, -⟩ := doms_two_inv (evalDoms_forall₂ hd)
    have hw₁ : w₁ = .list l₁ := Option.some.inj (f₁.symm.trans hy)
    obtain ⟨l₂, -, hdls⟩ := domLists_two (x₁ := x₁) (x₂ := x₂) (w₂ := w₂) (by rwa [hx, hw₁] at hdl)
    have hk₁ : l₁.length = k := hk _ (by rw [hdls]; exact List.mem_cons_self)
    have hk₂ : l₂.length = k := hk _ (by rw [hdls]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨l₂, hk₂.trans hk₁.symm, fun i hi => hrows _ ?_⟩
    rw [hdls]
    exact row_mem_iterRows (hk₁ ▸ hi) hk₁ hk₂

/-- One round of premise 4, `Mem_ok(C', MEMORY mt, u)`, gives `mt.Valid`. -/
theorem memRow_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {mt : Silmaril.Wasm.MemoryType}
    {u : Value} (h : DPremB (simEnv B) O els (ρ.bindVals [("mem", memV mt), ("mt", u)])
      (.rulePr "Mem_ok" [] "%|-%:%" (.tupE [.varE "C'", .varE "mem", .varE "mt"]))) :
    mt.Valid := by
  cases h with
  | rulePr hargs hw hdd =>
    obtain rfl := evalArgs_nil_iff.1 hargs
    obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hw
    rcases evalExps_forall₂ hus with _ | ⟨-, _ | ⟨hb, _ | ⟨-, hn⟩⟩⟩
    cases hn
    have hmem : (ρ.bindVals [("mem", memV mt), ("mt", u)]).findVal? "mem" = some (memV mt) := by
      simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind]
    obtain rfl := Option.some.inj ((evalExp_varE_iff.1 hb).symm.trans hmem)
    exact (memOk_inv hdd).2

/-- **Premise 4 at `mem* = MEMORY mt*`, inverted**: every `mt ∈ mts` is valid. -/
theorem prem4_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {mts : List Silmaril.Wasm.MemoryType}
    (hm : ρ.findVal? "mem*" = some (.list (mts.map memV)))
    (h : DPremB (simEnv B) O els ρ modPrem4) : ∀ mt ∈ mts, mt.Valid := by
  intro mt hmt
  obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hmt
  obtain ⟨l₂, hl, hrows⟩ := iterList_two_rows h hm
  have hi' : i < (mts.map memV).length := by simpa using hi
  have hr := hrows i hi'
  rw [List.getElem_map, hmi] at hr
  exact memRow_inv hr

/-! ## Reflection -/

/-- **`Module_ok` inverted at a module without imports and exports**: the memory list `M` of the
module is bound to `mem*` in a scope where premise 4 holds, and `v` is the primitives' answer to
`$clos_moduletype(C, [] -> [])` at some `C`. -/
theorem moduleOk_noImpExp_inv {O : ElseI} {a₀ a₂ a₃ M a₅ a₆ a₇ a₈ a₉ v : Value}
    (h : DDerivesB (simEnv B) O "Module_ok" "|-%:%" []
      (.tuple [.case "MODULE" (.tuple [a₀, pctNil, a₂, a₃, .case "%" (.tuple [M]), a₅, a₆, a₇, a₈,
        a₉, pctNil]), v])) :
    (∃ ρ els, ρ.findVal? "mem*" = some M ∧ DPremB (simEnv B) O els ρ modPrem4) ∧
      ∃ c, B.call "clos_moduletype" [.val c, .val mtNil] = some v := by
  obtain ⟨t, hrel⟩ := rel_moduleOk (B := B)
  obtain ⟨σ, he, hp⟩ := dd_oneRule_inv hrel conclAlts_modConcl h
  have hρ : (VarEnv.empty.bindVals σ).findDef? "clos_moduletype" = none :=
    Memory.findDef_bindVals_empty _ _
  obtain ⟨hmod, hcl⟩ := Instr30Z.evalExp_tup2_inv' (modConcl_eq ▸ he)
  obtain ⟨fimp, fmem, fexp⟩ := modModE_inv hmod
  obtain ⟨c, xI, xE, fI, fE, hB⟩ := closE_inv hρ hcl
  have hp1 : DPremB (simEnv B) O _ _ modPrem1 := hp _ (by simp [modPrems])
  have hp10 : DPremB (simEnv B) O _ _ modPrem10 := hp _ (by simp [modPrems])
  have hxI : xI = [] := iterNil_two hp1 fimp fI
  have hxE : xE = [] := iterNil_three hp10 fexp fE
  refine ⟨⟨_, _, fmem, hp _ (by simp [modPrems])⟩, c, ?_⟩
  rw [hxI, hxE] at hB
  exact hB

/-- **`Module_ok` is reflected at memory-only modules**: in every evaluator `simEnv B`, under every
reading of `otherwise`, a `Module_ok(memModuleV mts, v)` fact gives `mt.Valid` for every
`mt ∈ mts`, and `v` is the primitives' answer to `$clos_moduletype(C, [] -> [])` at some `C`. -/
theorem moduleOk_memL_inv {O : ElseI} {mts : List Silmaril.Wasm.MemoryType} {v : Value}
    (h : DDerivesB (simEnv B) O "Module_ok" "|-%:%" [] (.tuple [memModuleV mts, v])) :
    (∀ mt ∈ mts, mt.Valid) ∧ ∃ c, B.call "clos_moduletype" [.val c, .val mtNil] = some v :=
  let ⟨⟨_, _, fmem, hp4⟩, hB⟩ := moduleOk_noImpExp_inv h
  ⟨prem4_inv fmem hp4, hB⟩

/-- **`Module_ok` is exact at memory-only modules, at the repaired primitives**: in
`simEnv (withClosMod B)`, under every reading of `otherwise`, `Module_ok(memModuleV mts, v)` holds
exactly when `v = [] -> []` and Core validates every `mt ∈ mts`. -/
theorem moduleOk_memL_iff (O : ElseI) (mts : List Silmaril.Wasm.MemoryType) (v : Value) :
    DDerivesB (simEnv (withClosMod B)) O "Module_ok" "|-%:%" [] (.tuple [memModuleV mts, v]) ↔
      v = mtNil ∧ ∀ mt ∈ mts, mt.Valid := by
  constructor
  · intro h
    obtain ⟨hv, c, hB⟩ := moduleOk_memL_inv h
    exact ⟨(Option.some.inj hB).symm, hv⟩
  · rintro ⟨rfl, hv⟩
    exact Instr30Z.moduleOk_memL O hv rfl

/-- **The satisfaction condition is exact on memory-only modules**: for every host and profile,
`stepModel (withClosMod BI)` has the fact `Module_ok(memModuleV mts, v)` exactly when Core
validates `memModule mts` at some module type `τ` and `v` is `[] -> []`, the image of `τ` (Core's
only type for such a module, `Instr30Z.memModule_ok_iff`). -/
theorem memModule_sat_iff {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (mts : List Silmaril.Wasm.MemoryType)
    (v : Value) :
    (Wasm30.stepModel (withClosMod (Round4Int.BI P hn host))).D "Module_ok" "|-%:%" []
        (.tuple [memModuleV mts, v]) ↔
      ∃ τ, Silmaril.Wasm.Validation.ModuleOk (Instr30Z.memModule mts) τ ∧ τ = ⟨[], []⟩ ∧
        v = mtNil := by
  constructor
  · intro h
    obtain ⟨rfl, hv⟩ := (moduleOk_memL_iff _ mts v).1 h
    exact ⟨⟨[], []⟩, (Instr30Z.memModule_ok_iff mts _).2 ⟨rfl, hv⟩, rfl, rfl⟩
  · rintro ⟨τ, hτ, -, rfl⟩
    exact (moduleOk_memL_iff _ mts _).2 ⟨rfl, ((Instr30Z.memModule_ok_iff mts τ).1 hτ).2⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30W
