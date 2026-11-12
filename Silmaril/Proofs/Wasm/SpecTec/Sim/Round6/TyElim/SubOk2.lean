module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.OkInv
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Guard

/-!
# Round 6: what `Subtype_ok2` says about a declared supertype

`subtypeOk2_facts`: under `DDerivesB`, on the concrete `B`, `Subtype_ok2` at
`SUB final? typeuse* comptype` in a context `ctxR L` at position `j` gives, for each declared
supertype (`SupFact`):

* `REC k`: `k < j` (`$before`), and `L[k]` is a non-final subtype whose body has the head of
  `comptype` (`$unrollht_` reads `C.RECS[k]`, and `Comptype_sub` keeps the head constructor);
* a defined type `dt`: `Deftype_ok` at `dt` (through `Typeuse_ok`), and Core's `unrolldt dt` is
  a non-final subtype whose body has the head of `comptype`.

Only `Subtype_ok2`'s supertype premises and the head constructor of `Comptype_sub` are read.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV headV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.RefOkB (ctxR)

variable {B : Builtins}

/-! ## Scopes -/

/-- Binding names other than `y` leaves `y`'s value. -/
theorem findVal_binds_other {y : IL.Id} {v : Value} :
    ∀ (r : List (IL.Id × Value)) {ρ : VarEnv}, ρ.findVal? y = some v → (∀ p ∈ r, p.1 ≠ y) →
      (ρ.bindVals r).findVal? y = some v
  | [], ρ, hy, _ => by simpa [VarEnv.bindVals, Map.binds] using hy
  | (x, a) :: r, ρ, hy, hr => by
    have hx : x ≠ y := hr _ (List.mem_cons_self ..)
    have h₁ : (ρ.bindVal x a).findVal? y = some v := by
      simp only [VarEnv.findVal?, VarEnv.bindVal, Map.bind] at hy ⊢
      split <;> simp [Map.find?, hx, hy]
    have := findVal_binds_other r h₁ fun p hp => hr p (List.mem_cons_of_mem _ hp)
    simpa [VarEnv.bindVals, VarEnv.bindVal, Map.binds] using this

/-! ## Iterated premises, one row at a time -/

/-- An iterated premise over one domain `x ← y`: every row. -/
theorem iterRow1 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem} {x y : IL.Id}
    {l : List Value} (hy : ρ.findVal? y = some (.list l))
    (h : DPremB env O els ρ (.iterPr pr (.mk .list [.mk x (.varE y)]))) :
    ∀ (p : Nat) (a : Value), l[p]? = some a → DPremB env O els (ρ.bindVals [(x, a)]) pr := by
  intro p a hp
  cases h with
  | iterList _ hdoms _ hdl hlen hrows =>
    obtain ⟨n, hn⟩ := hdoms
    obtain ⟨yv, hy', rfl⟩ := Exn.evalDoms_one hn
    rw [hy] at hy'
    obtain rfl := Option.some.inj hy'
    obtain rfl : _ = [(x, l)] := by simpa [domLists, Value.asList?] using hdl.symm
    have hk := hlen _ (List.mem_singleton_self _)
    have hpl : p < l.length := (List.getElem?_eq_some_iff.1 hp).1
    have hr := hrows _ (List.mem_map.2 ⟨p, List.mem_range.2 (by simp at hk; omega), rfl⟩)
    have e : iterRow [(x, l)] none p = [(x, a)] := by simp [iterRow, hp]
    rwa [e] at hr

/-- Three variable domains, evaluated. -/
theorem evalDoms_three {env : Env} {n : Nat} {ρ : VarEnv} {x₁ y₁ x₂ y₂ x₃ y₃ : IL.Id}
    {xvs : List (IL.Id × Value)}
    (h : evalDoms n env ρ [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂), .mk x₃ (.varE y₃)] = .ok xvs) :
    ∃ v₁ v₂ v₃, ρ.findVal? y₁ = some v₁ ∧ ρ.findVal? y₂ = some v₂ ∧ ρ.findVal? y₃ = some v₃ ∧
      xvs = [(x₁, v₁), (x₂, v₂), (x₃, v₃)] := by
  cases n with
  | zero => simp [evalDoms] at h
  | succ n =>
    simp only [evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc] at h
    cases h₁ : evalExp n env ρ (.varE y₁) with
    | error e => simp [h₁] at h
    | ok v₁ =>
      cases h₂ : evalExp n env ρ (.varE y₂) with
      | error e => simp [h₁, h₂] at h
      | ok v₂ =>
        cases h₃ : evalExp n env ρ (.varE y₃) with
        | error e => simp [h₁, h₂, h₃] at h
        | ok v₃ =>
          simp [h₁, h₂, h₃] at h
          exact ⟨v₁, v₂, v₃, evalExp_varE_iff.1 ⟨n, h₁⟩, evalExp_varE_iff.1 ⟨n, h₂⟩,
            evalExp_varE_iff.1 ⟨n, h₃⟩, h.symm⟩

/-- Three domain values read as lists, the middle one known. -/
theorem domLists3_inv {x₁ x₂ x₃ : IL.Id} {v₁ v₃ : Value} {l₂ : List Value}
    {dls : List (IL.Id × List Value)}
    (h : domLists [(x₁, v₁), (x₂, .list l₂), (x₃, v₃)] = some dls) :
    ∃ l₁ l₃, v₁ = .list l₁ ∧ v₃ = .list l₃ ∧ dls = [(x₁, l₁), (x₂, l₂), (x₃, l₃)] := by
  obtain ⟨l₁, rfl⟩ : ∃ l, v₁ = .list l := by cases v₁ <;> simp_all [domLists, Value.asList?]
  obtain ⟨l₃, rfl⟩ : ∃ l, v₃ = .list l := by cases v₃ <;> simp_all [domLists, Value.asList?]
  exact ⟨l₁, l₃, rfl, rfl, by simpa [domLists, Value.asList?] using h.symm⟩

/-- The rows of an iteration over three list domains. -/
theorem iterRow3_rows {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ x₂ x₃ : IL.Id} {l₁ l₂ l₃ : List Value} {k : Nat}
    (hlen : ∀ d ∈ [(x₁, l₁), (x₂, l₂), (x₃, l₃)], d.2.length = k)
    (hrows : ∀ r ∈ iterRows [(x₁, l₁), (x₂, l₂), (x₃, l₃)] none k,
      DPremB env O els (ρ.bindVals r) pr) :
    l₁.length = l₂.length ∧ l₃.length = l₂.length ∧ ∀ (p : Nat) (a₁ a₂ a₃ : Value),
      l₁[p]? = some a₁ → l₂[p]? = some a₂ → l₃[p]? = some a₃ →
        DPremB env O els (ρ.bindVals [(x₁, a₁), (x₂, a₂), (x₃, a₃)]) pr := by
  have k₁ : l₁.length = k := hlen _ (List.mem_cons_self ..)
  have k₂ : l₂.length = k := hlen _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have k₃ : l₃.length = k :=
    hlen _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨by omega, by omega, fun p a₁ a₂ a₃ ha₁ ha₂ ha₃ => ?_⟩
  have hp : p < l₂.length := (List.getElem?_eq_some_iff.1 ha₂).1
  have hr := hrows _ (List.mem_map.2 ⟨p, List.mem_range.2 (by omega), rfl⟩)
  have e : iterRow [(x₁, l₁), (x₂, l₂), (x₃, l₃)] none p = [(x₁, a₁), (x₂, a₂), (x₃, a₃)] := by
    simp [iterRow, ha₁, ha₂, ha₃]
  exact e ▸ hr

/-- An iterated premise over three domains, the middle one known: every row. -/
theorem iterRow3 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ y₁ x₂ y₂ x₃ y₃ : IL.Id} {l₂ : List Value} (hy : ρ.findVal? y₂ = some (.list l₂))
    (h : DPremB env O els ρ (.iterPr pr (.mk .list
      [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂), .mk x₃ (.varE y₃)]))) :
    ∃ l₁ l₃ : List Value, ρ.findVal? y₁ = some (.list l₁) ∧ l₁.length = l₂.length ∧
      l₃.length = l₂.length ∧ ∀ (p : Nat) (a₁ a₂ a₃ : Value), l₁[p]? = some a₁ →
        l₂[p]? = some a₂ → l₃[p]? = some a₃ →
          DPremB env O els (ρ.bindVals [(x₁, a₁), (x₂, a₂), (x₃, a₃)]) pr := by
  cases h with
  | iterList _ hdoms _ hdl hlen hrows =>
    obtain ⟨n, hn⟩ := hdoms
    obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩ := evalDoms_three hn
    have e₂ : v₂ = .list l₂ := Option.some.inj (h₂.symm.trans hy)
    obtain ⟨l₁, l₃, rfl, rfl, rfl⟩ := domLists3_inv (e₂ ▸ hdl)
    exact ⟨l₁, l₃, h₁, iterRow3_rows hlen hrows⟩

/-! ## `Comptype_sub` keeps the head constructor -/

/-- **`Comptype_sub` relates composite types with the same head constructor.** -/
theorem comptypeSub_head {O : ElseI} {c x y : Value}
    (hd : DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" [] (.tuple [c, x, y])) :
    headV x = headV y := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, -⟩ := dderivesB_inv findRel_comptypeSub hd
  rcases i with _ | _ | _ | i
  all_goals simp only [comptypeSubRules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  all_goals rw [conclAlts_of_not rfl, List.mem_singleton] at halt
  all_goals subst halt
  all_goals obtain ⟨-, h₂, h₃⟩ := ev3 he
  all_goals obtain ⟨w, -, rfl⟩ := evalExp_caseE_iff.1 h₂
  all_goals obtain ⟨w', -, rfl⟩ := evalExp_caseE_iff.1 h₃
  all_goals rfl

/-- The heads of two composite types' images agree only at the same kind. -/
theorem compAbs_of_head {c₁ c₂ : CCompType} (h : headV (tyV c₁) = headV (tyV c₂)) :
    compAbs c₁ = compAbs c₂ := by
  cases c₁ <;> cases c₂ <;> simp_all [tyV, headV, compAbs]

/-! ## `Subtype_ok2` -/

/-- What `Subtype_ok2` says of one declared supertype, in `ctxR L`, at position `j`, for a
subtype with body `ct`. -/
def SupFact (B : Builtins) (O : ElseI) (L : List Value) (j : Nat) (ct : CCompType) :
    CTypeUse → Prop
  | .recv k => k < j ∧ ∃ X c', L[k]? = some (.case "SUB" (.tuple [.opt none, X, c'])) ∧
      headV (tyV ct) = headV c'
  | .dt d₀ => DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [ctxR L, tyV d₀]) ∧
      ∃ st X c', unrolldt d₀ = some st ∧ tyV st = .case "SUB" (.tuple [.opt none, X, c']) ∧
        headV (tyV ct) = headV c'
  | .idx _ => True

/-- The scope of a row binding names other than `C` and `i`. -/
theorem row_C {ρ : VarEnv} {c : Value} (r : List (IL.Id × Value)) (hC : ρ.findVal? "C" = some c)
    (hr : ∀ p ∈ r, p.1 ≠ "C" := by simp) : (ρ.bindVals r).findVal? "C" = some c :=
  findVal_binds_other r hC hr

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}

/-- A call in a scope binding term variables only, inverted. -/
theorem applies_of_call {ρ : VarEnv} (hρ : ValsOnly ρ) {f : IL.Id} {args : List Arg}
    {ws : List ArgV} {v : Value} (ha : EvalArgs (simEnv (Prims.builtins prof hn host)) ρ args ws)
    (h : EvalExp (simEnv (Prims.builtins prof hn host)) ρ (.callE f args) v) :
    Applies (simEnv (Prims.builtins prof hn host)) f ws v :=
  (Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
    ha).2 (evalExp_callE_iff.1 h)

/-- `Subtype_ok2`'s iteration over its `$unrollht_` premise. -/
def unrollPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.callE "unrollht_" [.expA (.varE "C"),
    .expA (.subE (.varE "typeuse") (.varT "typeuse" []) (.varT "heaptype" []))])
    (.caseE "SUB" (.tupE [.optE none, .iterE (.varE "typeuse'")
      (.mk .list [.mk "typeuse'" (.varE "typeuse'*")]), .varE "comptype'"])))

/-- `SUB eps typeuse'* comptype'`, evaluated: its last component is `comptype'`. -/
theorem ev_subNone {env : Env} {ρ : VarEnv} {E : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE "SUB" (.tupE [.optE none, E, .varE "comptype'"])) v) :
    ∃ X c', v = .case "SUB" (.tuple [.opt none, X, c']) ∧ ρ.findVal? "comptype'" = some c' := by
  obtain ⟨w₀, hw₀, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨b₁, b₂, b₃, rfl, hb₁, -, hb₃⟩ := RefOkV.evalExp_tup3_ex hw₀
  have e₁ : b₁ = .opt none := evalExp_optE_none_iff.1 hb₁
  exact ⟨b₂, b₃, by rw [e₁], evalExp_varE_iff.1 hb₃⟩

/-- One round of the `$unrollht_` premise. -/
theorem unroll_row {L : List Value} {ρ : VarEnv} (hρ : ValsOnly ρ) {u : CTypeUse} {a₁ : Value}
    (hC : ρ.findVal? "C" = some (ctxR L)) (hU : ρ.findVal? "typeuse" = some (tyV u))
    (hK : ρ.findVal? "comptype'" = some a₁) {O : ElseI} {els : Prop}
    (h : DPremB (simEnv (Prims.builtins prof hn host)) O els ρ unrollPrem) :
    ∃ X, Applies (simEnv (Prims.builtins prof hn host)) "unrollht_" [.val (ctxR L), .val (tyV u)]
      (.case "SUB" (.tuple [.opt none, X, a₁])) := by
  cases h with
  | ifPr hc =>
    obtain ⟨v₁, v₂, hv₁, hv₂, hcv⟩ := evalExp_cmpE_iff.1 hc
    have e₁₂ := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcv
    obtain ⟨X, c', hv, hc'⟩ := ev_subNone hv₂
    have ec : c' = a₁ := Option.some.inj (hc'.symm.trans hK)
    refine ⟨X, ?_⟩
    rw [← ec, ← hv, ← e₁₂]
    exact applies_of_call hρ (Equiv.evalArgs_cons (evalExp_var hC)
      (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_var hU)) Equiv.evalArgs_nil)) hv₁

/-- One round of the `$before` premise, at `REC k`. -/
theorem before_row {ρ : VarEnv} (hρ : ValsOnly ρ) {k j : Nat}
    (hU : ρ.findVal? "typeuse" = some (tyV (Ty.recv k : CTypeUse)))
    (hI : ρ.findVal? "i" = some (natV j)) {O : ElseI} {els : Prop}
    (h : DPremB (simEnv (Prims.builtins prof hn host)) O els ρ
      (.ifPr (.callE "before" [.expA (.varE "typeuse"), .expA (.varE "i")]))) : k < j := by
  cases h with
  | ifPr hb =>
    exact applies_before_rec hn host (applies_of_call hρ (Equiv.evalArgs_cons (evalExp_var hU)
      (Equiv.evalArgs_cons (evalExp_var hI) Equiv.evalArgs_nil)) hb)

/-- `Subtype_ok2`'s conclusion, read: the context, the supertypes, the body, the position. -/
theorem subOk2_concl {env : Env} {ρ : VarEnv} {e' : Exp} {L : List Value} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {j : Nat}
    (halt : e' ∈ conclAlts Reading.subtypeOk2Concl)
    (he : EvalExp env ρ e' (.tuple [ctxR L, tyV (Ty.sub fin sups ct), .case "OK" (natV j)])) :
    ρ.findVal? "C" = some (ctxR L) ∧
      ρ.findVal? "typeuse*" = some (.list (sups.toList.map tyV)) ∧
      ρ.findVal? "comptype" = some (tyV ct) ∧ ρ.findVal? "i" = some (natV j) := by
  simp [Reading.subtypeOk2Concl, conclAlts, hasOptNil, hasOptNilL, optAlts, optAltsL,
    prod2] at halt
  obtain ⟨X, rfl⟩ : ∃ X, e' = .tupE [.varE "C", .caseE "SUB" (.tupE [X, .iterE (.varE "typeuse")
      (.mk .list [.mk "typeuse" (.varE "typeuse*")]), .varE "comptype"]), .caseE "OK" (.varE "i")] := by
    rcases halt with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := ev3 he
  obtain ⟨-, hIt, hCt⟩ := ev3 (evCase h₂).2
  obtain ⟨ws, hU, hws⟩ := Round5.Target.evalExp_iterList_inv
    (Round5.Target.bodyReads_sound (x := "typeuse") (b := .varE "typeuse") rfl) (by decide) hIt
  have e : ws = sups.toList.map tyV := (Value.list.inj (hws.symm.trans (Equiv.Validation.tyV_list _)))
  exact ⟨evalExp_varE_iff.1 h₁, e ▸ hU, evalExp_varE_iff.1 hCt,
    evalExp_varE_iff.1 (evCase h₃).2⟩

/-- A singleton row's own name. -/
theorem fv_row1 {ρ : VarEnv} {x : IL.Id} {a : Value} (hx : x ≠ "_") :
    (ρ.bindVals [(x, a)]).findVal? x = some a := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]

/-- The facts for one declared supertype, from the four iterated premises' rounds at it. -/
theorem supFact_of_rows {O : ElseI} {els : Prop} {L : List Value} {j : Nat} {ct : CCompType}
    {ρ : VarEnv} (hρ : ValsOnly ρ) (hC : ρ.findVal? "C" = some (ctxR L))
    (hI : ρ.findVal? "i" = some (natV j)) {u : CTypeUse} {X a₁ : Value}
    (hw : Applies (simEnv (Prims.builtins prof hn host)) "unrollht_" [.val (ctxR L), .val (tyV u)]
      (.case "SUB" (.tuple [.opt none, X, a₁])))
    (hsub : headV (tyV ct) = headV a₁)
    (hp₁ : DPremB (simEnv (Prims.builtins prof hn host)) O els (ρ.bindVals [("typeuse", tyV u)])
      (.rulePr "Typeuse_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "typeuse"])))
    (hp₂ : DPremB (simEnv (Prims.builtins prof hn host)) O els (ρ.bindVals [("typeuse", tyV u)])
      (.ifPr (.callE "before" [.expA (.varE "typeuse"), .expA (.varE "i")]))) :
    SupFact (Prims.builtins prof hn host) O L j ct u := by
  cases u with
  | idx x => trivial
  | recv k =>
    have hU₂ : (ρ.bindVals [("typeuse", tyV (Ty.recv k : CTypeUse))]).findVal? "typeuse" =
        some (tyV (Ty.recv k : CTypeUse)) := fv_row1 (by decide)
    have hI₂ : (ρ.bindVals [("typeuse", tyV (Ty.recv k : CTypeUse))]).findVal? "i" =
        some (natV j) := findVal_binds_other _ hI (by simp)
    exact ⟨before_row (ρ := ρ.bindVals [("typeuse", tyV (Ty.recv k : CTypeUse))])
      ⟨hρ.1, hρ.2.1, hρ.2.2⟩ hU₂ hI₂ hp₂, X, a₁,
      applies_unrollht_rec hn host hw, hsub⟩
  | dt d₀ =>
    obtain ⟨st, hst, hw'⟩ := applies_unrollht_def hn host hw
    have hU₁ : (ρ.bindVals [("typeuse", tyV (Ty.dt d₀ : CTypeUse))]).findVal? "typeuse" =
        some (tyV d₀) := fv_row1 (by decide)
    exact ⟨typeuseOk_def (prem_rule2 (row_C _ hC) hU₁ hp₁), st, X, a₁, hst, hw'.symm, hsub⟩

/-- `Typeuse_ok`, `$before`, `$unrollht_` and `Comptype_sub`, iterated over the supertypes. -/
structure SupPrems (env : Env) (O : ElseI) (els : Prop) (ρ : VarEnv) : Prop where
  typeuse : DPremB env O els ρ (.iterPr (.rulePr "Typeuse_ok" [] "%|-%:OK"
    (.tupE [.varE "C", .varE "typeuse"])) RefOkB.usesIt)
  before : DPremB env O els ρ (.iterPr (.ifPr (.callE "before"
    [.expA (.varE "typeuse"), .expA (.varE "i")])) RefOkB.usesIt)
  unroll : DPremB env O els ρ (.iterPr unrollPrem RefOkB.unrollIt)
  sub : DPremB env O els ρ (.iterPr (.rulePr "Comptype_sub" [] "%|-%<:%"
    (.tupE [.varE "C", .varE "comptype", .varE "comptype'"])) RefOkB.supsIt)

/-- The four iterated premises, out of `Subtype_ok2`'s premise list. -/
theorem supPrems_of {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv}
    (hp : ∀ pr ∈ RefOkB.subtypeOk2Prems, DPremB env O els ρ pr) : SupPrems env O els ρ :=
  ⟨hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
   hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
   hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
     (List.mem_cons_self ..)))),
   hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
     (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))⟩

/-- **What `Subtype_ok2` says of the declared supertypes**, from its premises at `ρ`. -/
theorem subOk2_body {O : ElseI} {els : Prop} {L : List Value} {sups : Ty (.list .use)}
    {ct : CCompType} {j : Nat} {ρ : VarEnv} (hρ : ValsOnly ρ)
    (hC : ρ.findVal? "C" = some (ctxR L))
    (hU : ρ.findVal? "typeuse*" = some (.list (sups.toList.map tyV)))
    (hT : ρ.findVal? "comptype" = some (tyV ct)) (hI : ρ.findVal? "i" = some (natV j))
    (P : SupPrems (simEnv (Prims.builtins prof hn host)) O els ρ) :
    ∀ u ∈ sups.toList, SupFact (Prims.builtins prof hn host) O L j ct u := by
  obtain ⟨l₁, l₃, hCs, hl₁, hl₃, hrow₃⟩ := iterRow3 hU P.unroll
  intro u hu
  obtain ⟨p, hpu⟩ := List.mem_iff_getElem?.1 hu
  have hpw : (sups.toList.map tyV)[p]? = some (tyV u) := by simp [hpu]
  have hpl : p < (sups.toList.map tyV).length := (List.getElem?_eq_some_iff.1 hpw).1
  obtain ⟨a₁, ha₁⟩ : ∃ a, l₁[p]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a, l₃[p]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hsub := comptypeSub_head (prem_rule3 (row_C [("comptype'", a₁)] hC)
    (findVal_binds_other [("comptype'", a₁)] hT (by simp)) (fv_row1 (by decide))
    (iterRow1 hCs P.sub p a₁ ha₁))
  obtain ⟨X, hw⟩ := unroll_row (ρ := ρ.bindVals [("comptype'", a₁), ("typeuse", tyV u),
    ("typeuse'*", a₃)]) (u := u) (a₁ := a₁) ⟨hρ.1, hρ.2.1, hρ.2.2⟩ (row_C _ hC)
    (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind])
    (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]) (hrow₃ p a₁ _ a₃ ha₁ hpw ha₃)
  exact supFact_of_rows hρ hC hI hw hsub (iterRow1 hU P.typeuse p _ hpw)
    (iterRow1 hU P.before p _ hpw)

/-- **What `Subtype_ok2` says of the declared supertypes**, on the concrete `B`. -/
theorem subtypeOk2_facts {O : ElseI} {L : List Value} {fin : Bool} {sups : Ty (.list .use)}
    {ct : CCompType} {j : Nat}
    (hd : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxR L, tyV (Ty.sub fin sups ct), .case "OK" (natV j)])) :
    ∀ u ∈ sups.toList, SupFact (Prims.builtins prof hn host) O L j ct u := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_subtypeOk2 hd
  rcases i with _ | i
  all_goals simp only [subtypeOk2Rules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  obtain ⟨hC, hU, hT, hI⟩ := subOk2_concl halt he
  exact subOk2_body (valsOnly_bind σ) hC hU hT hI (supPrems_of hp)

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
