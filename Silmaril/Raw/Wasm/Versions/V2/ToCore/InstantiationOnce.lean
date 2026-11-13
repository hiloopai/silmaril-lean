module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Instantiation
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

@[expose] public section

/-! # Wasm 2.0 instantiation with defined globals, against single allocation

New (not copied). `instantiate_sim` (`V2/ToCore/Instantiation.lean`) needs
`InstantiationBounds.noGlobals`: Core 3.0's spec `$instantiate` allocates every global twice.
This module drops that hypothesis by changing the Core side to **single allocation**:

* `Core.InstantiateOnce`: the relational form of silmaril-lean's `instantiateOnce?` (what the
  component engine `core3` runs): `$evalglobals` allocates each global once, then the
  global-free residue (`Module.globalResidue`) is instantiated against the imports followed by
  the new global addresses (`globalAddrs`);
* the 2.0 side is reduced to the global-free case: `allocModule?_dropGlobals` shows that 2.0's
  `$allocmodule` of `m` is the one of `m` without globals in the store that already holds them
  (`withGlobals`), against the imports followed by the new addresses;
* `constInstr_core'`/`constExpr_core'`/`evalExprss_core'`: the constant-expression lemmas of the
  copy, for Core stores and frames that *extend* the 2.0 ones in their globals;
* **`instantiate_sim_once`**: every 2.0 instantiation is simulated (`Sim`) by a Core
  `InstantiateOnce` of the image, with no `noGlobals`.

The relation to the spec's double allocation is a renaming of global addresses (the spec store
has `n` unreachable copies); see `docs/projects/spectec/README.md` ("component").
-/

namespace Silmaril.Wasm.V2.Execution.Once

open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Validation (ModuleOk)

variable {H : Type}

/-! ## The 2.0 side: allocation of the globals first -/

/-- The global instances `$allocmodule` allocates for `m` with initial values `vs`. -/
def globalsOf (m : Module) (vs : List Val) : List GlobalInst :=
  ((m.globals.map Global.type).zip vs).map fun p => ⟨p.1, p.2⟩

/-- A 2.0 store with global instances appended. -/
def withGlobals (s : Store H) (gis : List GlobalInst) : Store H :=
  { s with globals := s.globals ++ gis }

/-- A 2.0 module without its defined globals. -/
def dropGlobals (m : Module) : Module := { m with globals := [] }

/-- The 2.0 external addresses of `k` globals from address `n`. -/
def newGlobals (n k : Nat) : List ExternAddr := (List.range k).map fun i => .global (n + i)

theorem newGlobals_funcs (n k : Nat) : ExternAddr.funcs (newGlobals n k) = [] := by
  simp [newGlobals, ExternAddr.funcs, List.filterMap_map]

theorem newGlobals_tables (n k : Nat) : ExternAddr.tables (newGlobals n k) = [] := by
  simp [newGlobals, ExternAddr.tables, List.filterMap_map]

theorem newGlobals_mems (n k : Nat) : ExternAddr.mems (newGlobals n k) = [] := by
  simp [newGlobals, ExternAddr.mems, List.filterMap_map]

theorem newGlobals_globals (n k : Nat) :
    ExternAddr.globals (newGlobals n k) = (List.range k).map (n + ·) := by
  simp [newGlobals, ExternAddr.globals, List.filterMap_map]


/-- **2.0's `$allocmodule` with the globals allocated first.** Allocating `m` with global values
`vs` is allocating `m` without globals in the store that already holds the global instances,
against the imports followed by the addresses of those instances. -/
theorem allocModule?_dropGlobals {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    allocModule? (withGlobals s (globalsOf m vs)) (dropGlobals m)
      (xas ++ newGlobals s.globals.length m.globals.length) [] rss = some (s', mi) := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h ⊢
  obtain ⟨fts, hfts, hv, hr, xi, hxi, hs, hmi⟩ := h
  refine ⟨fts, hfts, rfl, hr, xi, ?_, ?_⟩
  · simpa [dropGlobals, newGlobals_funcs, newGlobals_tables, newGlobals_mems,
      newGlobals_globals, withGlobals] using hxi
  · subst hs hmi
    simp [allocFuncs_closed, allocGlobals_closed, allocTables_closed, allocMems_closed,
      allocElems_closed, allocDatas_closed, dropGlobals, newGlobals_funcs,
      newGlobals_tables, newGlobals_mems, newGlobals_globals, withGlobals, globalsOf]


/-! ## Constant expressions in extended Core states

The copy's `constInstr_core` asks for the Core globals to be exactly the images of the 2.0
ones and for the Core frame to be `ModuleInstSim`. During single allocation the Core store and
frame have *more* globals (those already allocated by `$evalglobals`); a 2.0 constant
expression reads only an imported global, so prefix agreement is enough. -/

/-- The image of a 2.0 constant instruction evaluates to the image of its denotation in every
Core state whose frame agrees on the functions and extends the globals, and whose store extends
the globals of the 2.0 store. -/
theorem constInstr_core' {P : Profile} {tgt : ToCore.CHostSemantics H} {s : Store H}
    {S : ToCore.CStore H} {F : ToCore.CFrame} {mi : ModuleInst}
    (hgs : ∀ (a : Nat) (gi : GlobalInst), s.globals[a]? = some gi →
      S.globals[a]? = some gi.toCore)
    (hfuncs : F.module.funcs = mi.funcs)
    (hglob : ∀ (x a : Nat), mi.globals[x]? = some a → F.module.globals[x]? = some a)
    {i : Instr} {ci : Wasm.Instr} (hi : Instr.toCore i = some ci)
    {v : Val} (hv : constInstr? s mi i = some v) :
    Silmaril.Wasm.Execution.Core.EvalExpr P tgt S F [ci] S F [v.toCore] := by
  cases i with
  | intConst t c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | floatConst t c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | vecConst c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | refNull rt =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.reference
        (Silmaril.Wasm.Execution.Core.RefStep.refNull _))
  | refFunc x =>
    simp only [constInstr?, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hi
    refine Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.reference
        (Silmaril.Wasm.Execution.Core.RefStep.refFunc ?_))
    rw [hfuncs]
    exact ha
  | globalGet x =>
    simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, gi, hgi, rfl⟩ := hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hi
    refine Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.variable
        (Silmaril.Wasm.Execution.Core.VariableStep.globalGet
          (a := a) (g := gi.toCore) ?_))
    rw [ModuleInst.globalAddr?] at ha
    rw [Store.globalInst?] at hgi
    simp [Silmaril.Wasm.Execution.Core.Store.global?, hglob _ _ ha, hgs _ _ hgi]
  | _ => simp [constInstr?] at hv

/-- `constInstr_core'` for constant expressions. -/
theorem constExpr_core' {P : Profile} {tgt : ToCore.CHostSemantics H} {s : Store H}
    {S : ToCore.CStore H} {F : ToCore.CFrame} {mi : ModuleInst}
    (hgs : ∀ (a : Nat) (gi : GlobalInst), s.globals[a]? = some gi →
      S.globals[a]? = some gi.toCore)
    (hfuncs : F.module.funcs = mi.funcs)
    (hglob : ∀ (x a : Nat), mi.globals[x]? = some a → F.module.globals[x]? = some a)
    {e : Expr} {ce : Wasm.Expr} (hce : Expr.toCore e = some ce)
    {v : Val} (hv : constExpr? s mi e = some v) :
    Silmaril.Wasm.Execution.Core.EvalExpr P tgt S F ce S F [v.toCore] := by
  match e with
  | [] => simp [constExpr?] at hv
  | _ :: _ :: _ => simp [constExpr?] at hv
  | [i] =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hce
    obtain ⟨c, hc, cs, hcs, rfl⟩ := hce
    simp only [Option.some.injEq] at hcs
    subst hcs
    exact constInstr_core' hgs hfuncs hglob hc hv


/-- The agreement of a Core state with a 2.0 one that constant evaluation needs. -/
structure ConstAgree (s : Store H) (mi : ModuleInst) (S : ToCore.CStore H) (F : ToCore.CFrame) :
    Prop where
  globals : ∀ (a : Nat) (gi : GlobalInst), s.globals[a]? = some gi →
    S.globals[a]? = some gi.toCore
  funcs : F.module.funcs = mi.funcs
  frameGlobals : ∀ (x a : Nat), mi.globals[x]? = some a → F.module.globals[x]? = some a

/-- `$evalexprs` on the images of 2.0 constant expressions, in an agreeing Core state. -/
theorem evalExprs_core' {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {F : ToCore.CFrame} {f : Frame}
    (hA : ConstAgree s f.module S F) {exs : List Expr} :
    ∀ {cexs : List Wasm.Expr} {rs : List Ref}, exs.mapM Expr.toCore = some cexs →
      (∀ ex ∈ exs, (constExpr? s f.module ex).isSome) →
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        EvalExpr P src s f ex s f [Val.ref r]) exs rs →
      Silmaril.Wasm.Execution.Core.EvalExprs P tgt S F cexs S F (rs.map Ref.toCore) := by
  induction exs with
  | nil =>
    intro cexs rs hc _ hrs
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    cases hrs
    exact .nil
  | cons ex exs ih =>
    intro cexs rs hc hconst hrs
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hc
    obtain ⟨cex, hcex, cexs', hcexs, rfl⟩ := hc
    cases hrs with
    | cons hr hrs =>
      refine .cons ?_ (ih hcexs (fun e' he' => hconst e' (by simp [he'])) hrs)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hconst ex (by simp))
      obtain ⟨-, -, hw⟩ := evalExpr_const_eq hv hr
      have hvr : v = Val.ref _ := (List.cons.injEq .. ▸ hw).1.symm
      rw [hvr] at hv
      exact constExpr_core' hA.globals hA.funcs hA.frameGlobals hcex hv

/-- `$evalexprss` on the images of the element initialisers, in an agreeing Core state. -/
theorem evalExprss_core' {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {F : ToCore.CFrame} {f : Frame}
    (hA : ConstAgree s f.module S F) {es : List Elem} :
    ∀ {ces : List Wasm.Elem} {rss : List (List Ref)}, es.mapM Elem.toCore = some ces →
      (∀ e ∈ es, ∀ ex ∈ e.init, (constExpr? s f.module ex).isSome) →
      List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
        List.Forall₂ (fun (ex : Expr) (r : Ref) =>
          EvalExpr P src s f ex s f [Val.ref r]) e.init rs) es rss →
      Silmaril.Wasm.Execution.Core.EvalExprss P tgt S F (ces.map Silmaril.Wasm.Elem.init) S F
        (rss.map (List.map Ref.toCore)) := by
  induction es with
  | nil =>
    intro ces rss hc _ hrs
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    cases hrs
    exact .nil
  | cons e es ih =>
    intro ces rss hc hconst hrs
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hc
    obtain ⟨ce, hce, ces', hces, rfl⟩ := hc
    cases hrs with
    | cons hr hrs =>
      simp only [List.map_cons]
      refine .cons ?_ (ih hces (fun e' he' => hconst e' (by simp [he'])) hrs)
      simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hce
      obtain ⟨is, his, md, -, rfl⟩ := hce
      exact evalExprs_core' hA his (hconst e (by simp)) hr


/-! ## `$evalglobals` on the Core side -/

theorem getElem?_append_of_some {α : Type} {l : List α} (l' : List α) {a : Nat} {x : α}
    (h : l[a]? = some x) : (l ++ l')[a]? = some x := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hlt, h]

/-- Agreement survives allocating a Core global (the 2.0 side reads only earlier globals). -/
theorem ConstAgree.alloc {s : Store H} {mi : ModuleInst} {S : ToCore.CStore H}
    {F : ToCore.CFrame} (hA : ConstAgree s mi S F) (g : Silmaril.Wasm.Validation.CGlobalType)
    (v : Silmaril.Wasm.Execution.Core.Val) :
    ConstAgree s mi (Silmaril.Wasm.Execution.Core.allocGlobal S g v).1
      { F with module := { F.module with globals := F.module.globals ++
        [(Silmaril.Wasm.Execution.Core.allocGlobal S g v).2] } } where
  globals a gi h := getElem?_append_of_some _ (hA.globals a gi h)
  funcs := hA.funcs
  frameGlobals x a h := getElem?_append_of_some _ (hA.frameGlobals x a h)

/-- **Core 3.0's `$evalglobals` on the image of 2.0 global initialisers**: each initialiser
evaluates, in the Core state extended by the earlier globals, to the image of the value 2.0
gives it in its fixed state; the store ends with the globals appended once. -/
theorem evalGlobals_core {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    {s : Store H} {f : Frame} :
    ∀ {gs : List Global} {cgs : List Wasm.Global} {vs : List Val} {cts : List Silmaril.Wasm.Validation.CGlobalType}
      {S : ToCore.CStore H} {F : ToCore.CFrame},
      gs.mapM Global.toCore = some cgs → ConstAgree s f.module S F →
      (∀ g ∈ gs, (constExpr? s f.module g.init).isSome) →
      List.Forall₂ (fun (g : Global) (v : Val) =>
        EvalExpr P src s f (Global.init g) s f [v]) gs vs →
      cts.length = gs.length →
      ∃ F', Silmaril.Wasm.Execution.Core.EvalGlobals P tgt S F cts
        (cgs.map Silmaril.Wasm.Global.init)
        { S with globals := S.globals ++ (cts.zip (vs.map Val.toCore)).map (fun p =>
            (⟨p.1, p.2⟩ : ToCore.CGlobalInst)) } F' (vs.map Val.toCore)
  | [], cgs, vs, cts, S, F, hc, _, _, hvs, hlen => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    cases hvs
    cases cts with
    | nil => exact ⟨F, by simpa using Silmaril.Wasm.Execution.Core.EvalGlobals.nil⟩
    | cons _ _ => simp at hlen
  | g :: gs, cgs, vs, cts, S, F, hc, hA, hconst, hvs, hlen => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hc
    obtain ⟨cg, hcg, cgs', hcgs, rfl⟩ := hc
    cases hvs with
    | @cons _ v _ vs' hv hvs' =>
    cases cts with
    | nil => simp at hlen
    | cons ct cts' =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hconst g (by simp))
      obtain ⟨-, -, hwv⟩ := evalExpr_const_eq hw hv
      have hwv' : w = v := by simpa using hwv.symm
      subst hwv'
      have hcinit : Expr.toCore g.init = some cg.init := by
        simp only [Global.toCore, Option.map_eq_some_iff] at hcg
        obtain ⟨init, hinit, rfl⟩ := hcg
        exact hinit
      have he := constExpr_core' (P := P) (tgt := tgt) hA.globals hA.funcs hA.frameGlobals
        hcinit hw
      obtain ⟨F', hF'⟩ := evalGlobals_core (P := P) (src := src) (tgt := tgt) hcgs
        (hA.alloc ct w.toCore) (fun g' hg' => hconst g' (by simp [hg'])) hvs'
        (by simpa using hlen)
      refine ⟨F', ?_⟩
      obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = (Silmaril.Wasm.Execution.Core.allocGlobal S ct w.toCore).1 :=
        ⟨_, rfl⟩
      have hS : ({ S₁ with globals := (S₁.globals ++
            (cts'.zip (vs'.map Val.toCore)).map (fun p => (⟨p.1, p.2⟩ : ToCore.CGlobalInst))) } :
            ToCore.CStore H) =
          { S with globals := (S.globals ++ ((ct :: cts').zip ((w :: vs').map Val.toCore)).map
            (fun p => (⟨p.1, p.2⟩ : ToCore.CGlobalInst))) } := by
        subst hS₁
        simp [Silmaril.Wasm.Execution.Core.allocGlobal]
      rw [← hS]
      subst hS₁
      exact .cons he hF'


/-- **Every global initialiser of a valid module is a constant expression whose denotation is
defined in the initial state** (`Global_ok`, `6-typing:597`, with `Expr_ok_const`): the global
analogue of the copy's `elemInit_const_isSome`. -/
theorem globalInit_const_isSome (P : Profile) (host : HostSemantics H) {s : Store H}
    {m : Module} {xas : List ExternAddr} {ixt xt : List ExternType} (hok : ModuleOk m ixt xt)
    (himp : List.Forall₂ (ExternAddrOk s) xas ixt) :
    ∀ g ∈ m.globals, (constExpr? s (ModuleInst.initial s m xas) g.init).isSome := by
  obtain ⟨hlf, hlg, -, hga⟩ := externAddrOk_kinds himp
  obtain ⟨-, -, hglobals, -, -, -, -, hfuncs, -, -, -, -, -, rfl⟩ := hok
  intro g hg
  obtain ⟨gt, -, hGok⟩ := Silmaril.Wasm.V2.Validation.forall₂_exists_of_mem hglobals hg
  have hden := Silmaril.Wasm.V2.Execution.exprOkConst_evalExpr (P := P) (host := host)
    (f := Frame.initial s m xas) hGok.2.2
    (by
      intro x hx
      have hl := List.Forall₂.length_eq hfuncs
      have hlt : x.toNat < (ModuleInst.initial s m xas).funcs.length := by
        simp only [ModuleInst.initial, List.length_append, List.length_map, List.length_range]
        simp only [List.length_append] at hx
        omega
      simp [Frame.initial, ModuleInst.funcAddr?, List.getElem?_eq_getElem hlt])
    (by
      intro x hx
      have hlt : x.toNat < (ExternAddr.globals xas).length := by rw [hlg]; exact hx
      exact ⟨(ExternAddr.globals xas)[x.toNat],
        by simp [Frame.initial, ModuleInst.globalAddr?, ModuleInst.initial,
          List.getElem?_eq_getElem hlt],
        hga _ (List.getElem_mem hlt)⟩)
  obtain ⟨v, hv, -⟩ := hden
  have hv' : constExpr? s (ModuleInst.initial s m xas) g.init = some v := hv
  simp [hv']


/-! ## Single allocation on the Core side -/

/-- The run of Core 3.0's `$instantiate` without its validity premise: the fields `bounded` and
`run` of `Silmaril.Wasm.Execution.Core.Instantiate`. -/
def CoreRun (P : Profile) (host : ToCore.CHostSemantics H) (s : ToCore.CStore H)
    (m : Wasm.Module) (xas : List ToCore.CExternAddr) (c : ToCore.CConfig H) : Prop :=
  (m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
    (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32)) ∧
  ∃ (s₁ s₂ s₃ s₄ : ToCore.CStore H) (f₁ f₂ f₃ : ToCore.CFrame)
      (valsG : List Silmaril.Wasm.Execution.Core.Val)
      (refsT : List Silmaril.Wasm.Execution.Core.Ref)
      (refsE : List (List Silmaril.Wasm.Execution.Core.Ref))
      (mi : Silmaril.Wasm.Execution.Core.ModuleInst),
    Silmaril.Wasm.Execution.Core.EvalGlobals P host s
      ⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial s m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (Silmaril.Wasm.Validation.liftVal g.type.value).substAll
          ((Silmaril.Wasm.Execution.Core.allocTypes m.types).map .dt)⟩)
      (m.globals.map Silmaril.Wasm.Global.init) s₁ f₁ valsG ∧
    Silmaril.Wasm.Execution.Core.EvalExprs P host s₁ f₁
      (m.tables.map Silmaril.Wasm.Table.init) s₂ f₂ refsT ∧
    Silmaril.Wasm.Execution.Core.EvalExprss P host s₂ f₂
      (m.elems.map Silmaril.Wasm.Elem.init) s₃ f₃ refsE ∧
    Silmaril.Wasm.Execution.Core.allocModule? s₃ m xas valsG refsT refsE = some (s₄, mi) ∧
    c = ⟨s₄, { module := mi },
      Silmaril.Wasm.Execution.Core.expression ((List.range m.elems.length).zip m.elems |>.flatMap
        fun (i, e) => Silmaril.Wasm.Execution.Core.runElem i e) ++
      Silmaril.Wasm.Execution.Core.expression ((List.range m.data.length).zip m.data |>.flatMap
        fun (i, d) => Silmaril.Wasm.Execution.Core.runData i d) ++
      (match m.start with | some x => [.plain (.call x)] | none => [])⟩

/-- `$instantiate` is validity followed by its run. -/
theorem instantiate_iff {P : Profile} {host : ToCore.CHostSemantics H} {s : ToCore.CStore H}
    {m : Wasm.Module} {xas : List ToCore.CExternAddr} {c : ToCore.CConfig H} :
    Silmaril.Wasm.Execution.Core.Instantiate P host s m xas c ↔
      (∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
        List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk s) xas xtI) ∧
      CoreRun P host s m xas c :=
  ⟨fun h => ⟨h.valid, h.bounded, h.run⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **Core 3.0 instantiation with every global allocated once**, the relational form of
silmaril-lean's `instantiateOnce?` (the instantiation of the component engine `core3`): the
module is valid against the imports; `$evalglobals` allocates the globals once; the global-free
residue (`Module.globalResidue`, whose trailing imports are those globals) is then run as by
`$instantiate` against the imports followed by the new global addresses. -/
def CoreInstantiateOnce (P : Profile) (host : ToCore.CHostSemantics H) (s : ToCore.CStore H)
    (m : Wasm.Module) (xas : List ToCore.CExternAddr) (c : ToCore.CConfig H) : Prop :=
  (∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
    List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk s) xas xtI) ∧
  ∃ (s₁ : ToCore.CStore H) (f₁ : ToCore.CFrame) (vs : List Silmaril.Wasm.Execution.Core.Val),
    Silmaril.Wasm.Execution.Core.EvalGlobals P host s
      ⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial s m xas⟩
      (Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes m) (m.globals.map Silmaril.Wasm.Global.init)
      s₁ f₁ vs ∧
    CoreRun P host s₁ m.globalResidue
      (xas ++ Silmaril.Wasm.Execution.Core.globalAddrs s.globals.length m.globals.length) c

/-- On a module without globals, single allocation is the spec's `$instantiate`. -/
theorem coreInstantiateOnce_of_nil {P : Profile} {host : ToCore.CHostSemantics H}
    {s : ToCore.CStore H} {m : Wasm.Module} {xas : List ToCore.CExternAddr}
    {c : ToCore.CConfig H} (hg : m.globals = []) :
    CoreInstantiateOnce P host s m xas c ↔
      Silmaril.Wasm.Execution.Core.Instantiate P host s m xas c := by
  rw [instantiate_iff, CoreInstantiateOnce, Silmaril.Wasm.Module.globalResidue_of_nil hg]
  simp only [Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes, hg, List.map_nil, List.length_nil,
    Silmaril.Wasm.Execution.Core.globalAddrs, List.range_zero, List.append_nil]
  constructor
  · rintro ⟨hv, s₁, f₁, vs, hE, hr⟩
    cases hE
    exact ⟨hv, hr⟩
  · rintro ⟨hv, hr⟩
    exact ⟨hv, s, _, [], .nil, hr⟩


/-! ## Images -/

/-- The image of a module without its globals is the image without globals. -/
theorem module_toCore_dropGlobals {m : Module} {cm : Wasm.Module}
    (hcm : Module.toCore m = some cm) :
    Module.toCore (dropGlobals m) = some { cm with globals := [] } := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨gs, -, fs, hfs, es, hes, ds, hds, rfl⟩ := hcm
  simp [Module.toCore, dropGlobals, hfs, hes, hds]

/-- A 2.0 value type is closed in Core 3.0. -/
theorem valType_substAll (t : ValType) (tus : List Silmaril.Wasm.Validation.CTypeUse) :
    (Silmaril.Wasm.Validation.liftVal t.toCore).substAll tus = t.toC :=
  Silmaril.Wasm.Validation.Ty.substAll_closed
    (by cases t <;> first | rfl | (rename_i r; cases r <;> rfl)) _

/-- The closed global types of the image are the images of the 2.0 global types. -/
theorem closedGlobalTypes_toCore {m : Module} {cm : Wasm.Module}
    (hcm : Module.toCore m = some cm) :
    Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes cm =
      (m.globals.map Global.type).map ToCore.globalToC := by
  obtain ⟨-, -, -, -, -, -, -, hgs, -⟩ := module_toCore_shape hcm
  unfold Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes
  have hf := Silmaril.Wasm.V2.Validation.forall₂_of_mapM hgs
  clear hgs
  generalize cm.globals = cgs at hf ⊢
  generalize m.globals = gs at hf ⊢
  induction hf with
  | nil => rfl
  | cons hg _ ih =>
    rename_i g cg _ _
    simp only [Global.toCore, Option.map_eq_some_iff] at hg
    obtain ⟨init, -, rfl⟩ := hg
    simp only [List.map_cons, ih, ToCore.globalToC, GlobalType.toCore, valType_substAll]

/-- The images of the global instances `$allocmodule` allocates. -/
theorem globalsOf_toCore (m : Module) (vs : List Val) :
    (globalsOf m vs).map GlobalInst.toCore =
      (((m.globals.map Global.type).map ToCore.globalToC).zip (vs.map Val.toCore)).map
        fun p => (⟨p.1, p.2⟩ : ToCore.CGlobalInst) := by
  unfold globalsOf
  generalize m.globals.map Global.type = ts
  induction ts generalizing vs with
  | nil => simp
  | cons t ts ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      simp only [List.zip_cons_cons, List.map_cons, List.map_map] at ih ⊢
      exact congrArg _ (by simpa [List.map_map] using ih vs)

/-- The Core store after single allocation of the globals is the image of the 2.0 store that
already holds them. -/
theorem store_toCore_withGlobals {s : Store H} {S : ToCore.CStore H} {m : Module}
    {vs : List Val} (hS : Store.toCore s = some (ToCore.Store.erase S)) :
    Store.toCore (withGlobals s (globalsOf m vs)) =
      some (ToCore.Store.erase { S with globals := (S.globals ++
        (((m.globals.map Global.type).map ToCore.globalToC).zip (vs.map Val.toCore)).map
          (fun p => (⟨p.1, p.2⟩ : ToCore.CGlobalInst))) }) := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hS ⊢
  obtain ⟨fs, hfs, hSe⟩ := hS
  refine ⟨fs, hfs, ?_⟩
  have hg := congrArg (fun t : ToCore.CStore H => t.globals) hSe
  simp only [ToCore.Store.erase] at hg hSe ⊢
  rw [← globalsOf_toCore]
  simp only [withGlobals, List.map_append]
  rw [← hg]
  injection hSe with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  congr

/-- The images of the imports followed by new global addresses. -/
theorem externAddrs_toCore_newGlobals (xas : List ExternAddr) (n k : Nat) :
    (xas ++ newGlobals n k).map ExternAddr.toCore =
      xas.map ExternAddr.toCore ++ Silmaril.Wasm.Execution.Core.globalAddrs n k := by
  simp [newGlobals, Silmaril.Wasm.Execution.Core.globalAddrs, Function.comp_def,
    ExternAddr.toCore]

/-- Appending globals keeps 2.0 store well-formedness. -/
theorem storeWF_withGlobals {s : Store H} (gis : List GlobalInst) (h : StoreWF s) :
    StoreWF (withGlobals s gis) :=
  ⟨fun i fi hi a ha => h.1 i fi hi a ha, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Core's `$allocmodule` does not read the imports. -/
theorem allocModule?_residue (S : ToCore.CStore H) (cm : Wasm.Module)
    (xas : List ToCore.CExternAddr) (vs : List Silmaril.Wasm.Execution.Core.Val)
    (rs : List Silmaril.Wasm.Execution.Core.Ref)
    (rss : List (List Silmaril.Wasm.Execution.Core.Ref)) :
    Silmaril.Wasm.Execution.Core.allocModule? S cm.globalResidue xas vs rs rss =
      Silmaril.Wasm.Execution.Core.allocModule? S { cm with globals := [] } xas vs rs rss :=
  rfl


/-- Agreement of an exact image. -/
theorem ConstAgree.of_sim {s : Store H} {mi : ModuleInst} {S : ToCore.CStore H}
    {F : ToCore.CFrame} (hg : S.globals = s.globals.map GlobalInst.toCore)
    (hF : ToCore.ModuleInstSim mi F.module) : ConstAgree s mi S F where
  globals a gi h := by simp [hg, h]
  funcs := by
    have := congrArg (fun m : ToCore.CModuleInst => m.funcs) hF
    simpa [ToCore.ModuleInst.erase, ModuleInst.toCore] using this
  frameGlobals x a h := by
    have := congrArg (fun m : ToCore.CModuleInst => m.globals) hF
    have hglob : F.module.globals = mi.globals := by
      simpa [ToCore.ModuleInst.erase, ModuleInst.toCore] using this
    rw [hglob]
    exact h

/-- Agreement is kept by extending the Core store's and the frame's globals. -/
theorem ConstAgree.mono {s : Store H} {mi : ModuleInst} {S S' : ToCore.CStore H}
    {F F' : ToCore.CFrame} (hA : ConstAgree s mi S F)
    (hS : ∃ l, S'.globals = S.globals ++ l) (hf : F'.module.funcs = F.module.funcs)
    (hF : ∃ l, F'.module.globals = F.module.globals ++ l) : ConstAgree s mi S' F' where
  globals a gi h := by
    obtain ⟨l, hl⟩ := hS
    rw [hl]
    exact getElem?_append_of_some _ (hA.globals a gi h)
  funcs := hf.trans hA.funcs
  frameGlobals x a h := by
    obtain ⟨l, hl⟩ := hF
    rw [hl]
    exact getElem?_append_of_some _ (hA.frameGlobals x a h)


/-! ## The simulation -/

/-- **Wasm 2.0 instantiation is simulated by Core 3.0 single-allocation instantiation, with
defined globals.** `instantiate_sim` without `InstantiationBounds.noGlobals`: the target is
`CoreInstantiateOnce` (each global allocated once, as in silmaril-lean's `instantiateOnce?`)
instead of the spec's double-allocating `$instantiate`. -/
theorem instantiate_sim_once {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {c : Config H}
    (hwf : StoreWF s) (hS : Store.toCore s = some S)
    (hcm : Module.toCore m = some cm) (h : Instantiate P src s m xas c) :
    ∃ C : ToCore.CConfig H,
      CoreInstantiateOnce P tgt S cm (xas.map ExternAddr.toCore) C ∧
      Sim c C ∧ C.frame.locals = [] ∧ C.code = coreInstantiateCode cm ∧
      ToCore.ModuleInstSim c.frame.module C.frame.module := by
  have hSe : Store.toCore s = some (ToCore.Store.erase S) := by
    rw [Store.erase_toCore hS]; exact hS
  obtain ⟨hvalid, hbounded, hrun⟩ := h
  obtain ⟨ixt, xt, hok, himp⟩ := hvalid
  obtain ⟨valsG, refsE, s', mi, hgl, hel, halloc, hc⟩ := hrun
  subst hc
  obtain ⟨hlenf, hleng, hxfuncs, -⟩ := externAddrOk_kinds himp
  obtain ⟨-, -, -, -, -, -, -, hgsM, -⟩ := module_toCore_shape hcm
  have hcgl : cm.globals.length = m.globals.length := mapM_length hgsM
  have hSg : S.globals = s.globals.map GlobalInst.toCore := store_toCore_globals hSe
  have hSgl : S.globals.length = s.globals.length := by rw [hSg, List.length_map]
  -- the globals, allocated once on both sides
  let cts := Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes cm
  have hcts : cts = (m.globals.map Global.type).map ToCore.globalToC :=
    closedGlobalTypes_toCore hcm
  let S₁ : ToCore.CStore H := { S with globals := (S.globals ++
    (cts.zip (valsG.map Val.toCore)).map (fun p => (⟨p.1, p.2⟩ : ToCore.CGlobalInst))) }
  have hS₁ : Store.toCore (withGlobals s (globalsOf m valsG)) = some (ToCore.Store.erase S₁) := by
    have := store_toCore_withGlobals (m := m) (vs := valsG) hSe
    simpa only [S₁, hcts] using this
  have hFsim := moduleInst_initial_toCore (S := S) hSe hcm xas
  have hA₀' : ConstAgree s (Frame.initial s m xas).module S
      ⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial S cm
        (xas.map ExternAddr.toCore)⟩ := ConstAgree.of_sim (F := ⟨[], _⟩) hSg hFsim
  obtain ⟨F₁, hEG⟩ := evalGlobals_core (P := P) (src := src) (tgt := tgt) (cts := cts) hgsM
    hA₀' (globalInit_const_isSome P src hok himp) hgl
    (by simp only [cts, Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes, List.length_map,
      hcgl])
  -- the residue, on both sides
  let xas' := xas ++ newGlobals s.globals.length m.globals.length
  have halloc' := allocModule?_dropGlobals halloc
  have hxfuncs' : ∀ a ∈ ExternAddr.funcs xas',
      a < (withGlobals s (globalsOf m valsG)).funcs.length := by
    simpa [xas', newGlobals_funcs, withGlobals] using hxfuncs
  obtain ⟨Sa, miC, hallocC, hsim, hstore', hwf'⟩ :=
    allocModule_core (m := dropGlobals m) (cm := { cm with globals := [] }) rfl
      (storeWF_withGlobals _ hwf) (fun mt hmt => ModuleOk.memories_min_le hok mt hmt) hxfuncs' hS₁
      (module_toCore_dropGlobals hcm) halloc'
  have hxas' : xas'.map ExternAddr.toCore = xas.map ExternAddr.toCore ++
      Silmaril.Wasm.Execution.Core.globalAddrs S.globals.length cm.globals.length := by
    rw [externAddrs_toCore_newGlobals, hSgl, hcgl]
  rw [hxas', ← allocModule?_residue] at hallocC
  let F₂ : ToCore.CFrame := ⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial S₁
    cm.globalResidue (xas.map ExternAddr.toCore ++
      Silmaril.Wasm.Execution.Core.globalAddrs S.globals.length cm.globals.length)⟩
  have hA₂ : ConstAgree s (Frame.initial s m xas).module S₁ F₂ := by
    refine hA₀'.mono ⟨_, rfl⟩ ?_ ?_
    · simp [F₂, S₁, Silmaril.Wasm.Execution.Core.ModuleInst.initial,
        Silmaril.Wasm.Execution.Core.ExternAddr.funcs_append,
        Silmaril.Wasm.Execution.Core.ExternAddr.funcs_globalAddrs, Silmaril.Wasm.Module.globalResidue]
    · refine ⟨Silmaril.Wasm.Execution.Core.ExternAddr.globals
        (Silmaril.Wasm.Execution.Core.globalAddrs S.globals.length cm.globals.length), ?_⟩
      simp [F₂, Silmaril.Wasm.Execution.Core.ModuleInst.initial,
        Silmaril.Wasm.Execution.Core.ExternAddr.globals_append]
  have helemsM := (module_toCore_sections hcm).1
  have hdatasM := (module_toCore_sections hcm).2
  have hcelen : cm.elems.length = m.elems.length := mapM_length helemsM
  have hcdlen : cm.data.length = m.data.length := mapM_length hdatasM
  have hEE := evalExprss_core' (P := P) (src := src) (tgt := tgt) hA₂ helemsM
    (elemInit_const_isSome P src hok himp) hel
  refine ⟨⟨Sa, { module := miC }, coreInstantiateCode cm⟩,
    ⟨instantiate_valid hSe hcm hok himp, S₁, F₁, valsG.map Val.toCore, hEG, ⟨?_, ?_, ?_, ?_⟩,
      ⟨S₁, S₁, S₁, Sa, F₂, F₂, F₂, [], _, _, miC, .nil,
        evalExprs_tables (module_toCore_dropGlobals hcm) S₁ F₂, hEE, hallocC, rfl⟩⟩,
    ⟨?_, hwf', allocModule_modWF hxfuncs halloc, listWF_expression s' _⟩, rfl, rfl, hsim⟩
  · rw [show cm.globalResidue.elems = cm.elems from rfl, hcelen]; exact hbounded.1
  · rw [show cm.globalResidue.data = cm.data from rfl, hcdlen]; exact hbounded.2.1
  · intro cd hcd
    obtain ⟨d, hd, hdc⟩ := forall₂_exists_of_mem_right
      (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hdatasM) hcd
    rw [data_toCore_bytes hdc]
    exact hbounded.2.2.1 d hd
  · intro ce hce
    obtain ⟨e, he, hec⟩ := forall₂_exists_of_mem_right
      (Silmaril.Wasm.V2.Validation.forall₂_of_mapM helemsM) hce
    rw [mapM_length (elem_toCore_parts hec).2]
    exact hbounded.2.2.2 e he
  · -- the two configurations are related
    have hstart : Expr.toCore (startInstrs m) =
        some (match cm.start with | some x => [Wasm.Instr.call x] | none => []) :=
      startInstrs_toCore hcm
    have hbig : Expr.toCore (runElems m ++ runDatas m ++ startInstrs m) =
        some (coreRunElems cm ++ coreRunDatas cm ++
          (match cm.start with | some x => [Wasm.Instr.call x] | none => [])) :=
      expr_toCore_append
        (expr_toCore_append (runElems_toCore hcm)
          (runDatas_toCore hcm (ModuleOk.data_active_zero hok))) hstart
    have hnorm : ToCore.Admin.normList miC (coreInstantiateCode cm) =
        (coreRunElems cm ++ coreRunDatas cm ++
          (match cm.start with | some x => [Wasm.Instr.call x] | none => [])).map
            (ToCore.normPlain miC) := by
      simp only [coreInstantiateCode, Silmaril.Wasm.Execution.Core.expression,
        ToCore.Admin.normList_eq_map, List.map_append, List.map_map, Function.comp_def,
        ToCore.Admin.norm_plain, coreStartCode]
      cases cm.start <;> simp [ToCore.Admin.norm_plain]
    have hpn : (coreRunElems cm ++ coreRunDatas cm ++
        (match cm.start with | some x => [Wasm.Instr.call x] | none => [])).map
          ToCore.plainOrNull =
        ToCore.Admin.normList miC (coreInstantiateCode cm) := by
      rw [hnorm]
      exact List.map_congr_left fun ci hci =>
        (ToCore.normPlain_eq_plainOrNull miC fun x => Expr.toCore_ne_callRef hbig ci hci x).symm
    have hsimEq : ToCore.ModuleInst.erase miC = ModuleInst.toCore mi := hsim
    have hfr : Frame.toCore { module := mi } = ToCore.Frame.erase { module := miC } := by
      simp [Frame.toCore, ToCore.Frame.erase, hsimEq]
    show Config.toCore _ = some (ToCore.Config.norm _)
    simp only [Config.toCore, ToCore.Config.norm, hstore', Option.bind_some]
    show (Admin.listToCore s' (expression (runElems m ++ runDatas m ++ startInstrs m))).map _
      = some _
    rw [expression_toCore, hbig]
    simp only [Option.map_some, Option.some.injEq]
    rw [hfr, hpn]


/-! ## The relational form is silmaril-lean's `instantiateOnce?` -/

set_option linter.unusedTactic false in
/-- The computable `$instantiate` gives the run of the relational one (no validity needed). -/
theorem coreRun_of_instantiate? {P : Profile} {host : ToCore.CHostSemantics H}
    {ev : ToCore.CStore H → ToCore.CFrame → Wasm.Expr →
      Option (ToCore.CStore H × Silmaril.Wasm.Execution.Core.Val)}
    (hev : Silmaril.Wasm.Execution.Core.EvalSound P host ev) {s : ToCore.CStore H}
    {m : Wasm.Module} {xas : List ToCore.CExternAddr} {c : ToCore.CConfig H}
    (h : Silmaril.Wasm.Execution.Core.instantiate? ev s m xas = some c) :
    CoreRun P host s m xas c := by
  unfold Silmaril.Wasm.Execution.Core.instantiate? at h
  split at h <;> try cases h
  rename_i hb
  split at h <;> try cases h
  rename_i s₁ f₁ valsG hG
  split at h <;> try cases h
  rename_i s₂ f₂ refsT hT
  split at h <;> try cases h
  rename_i s₃ f₃ refsE hE
  split at h <;> try cases h
  rename_i s₄ mi hM
  exact ⟨hb, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi,
    Silmaril.Wasm.Execution.Core.evalGlobals?_sound hev hG,
    Silmaril.Wasm.Execution.Core.evalExprs?_sound hev hT,
    Silmaril.Wasm.Execution.Core.evalExprss?_sound hev hE, hM, rfl⟩

/-- **silmaril-lean's `instantiateOnce?` is a run of `CoreInstantiateOnce`**: on a valid module,
its configuration (with the start call) is a single-allocation instantiation, which runs the
segment initialisation to the store and frame `instantiateOnce?` returns, at every profile and
host. -/
theorem instantiateOnce?_once {P : Profile} {host : ToCore.CHostSemantics H}
    {s s' : ToCore.CStore H} {m : Wasm.Module} {xas : List ToCore.CExternAddr}
    {f' : ToCore.CFrame} {st : Option Wasm.FuncIdx}
    (hvalid : ∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk s) xas xtI)
    (h : Silmaril.Wasm.Execution.Core.instantiateOnce? s m xas = some (s', f', st)) :
    ∃ C, CoreInstantiateOnce P host s m xas C ∧
      Silmaril.Wasm.Execution.Core.Steps P host C ⟨s', f', Silmaril.Wasm.Execution.Core.startCode st⟩ := by
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ :=
    Silmaril.Wasm.Execution.Core.instantiateOnce?_steps (P := P) (host := host) h
  have hi : Silmaril.Wasm.Execution.Core.instantiate? Silmaril.Wasm.Execution.Core.evalConst? s₁
      m.globalResidue (xas ++ Silmaril.Wasm.Execution.Core.globalAddrs s.globals.length
        m.globals.length) = some (c.withStart st) := by
    rw [Silmaril.Wasm.Execution.Core.prepare?_instantiate?, hp]
    rfl
  refine ⟨c.withStart st, ⟨hvalid, s₁, f₁, vs,
    Silmaril.Wasm.Execution.Core.evalGlobals?_sound
      Silmaril.Wasm.Execution.Core.evalConst?_evalSound hg,
    coreRun_of_instantiate? Silmaril.Wasm.Execution.Core.evalConst?_evalSound hi⟩, ?_⟩
  rw [← Silmaril.Wasm.Execution.Core.Config.withStart_nil]
  exact Silmaril.Wasm.Execution.Core.Steps.withStart hS

end Silmaril.Wasm.V2.Execution.Once
