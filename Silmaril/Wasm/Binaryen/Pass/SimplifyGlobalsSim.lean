module

public import Silmaril.Wasm.Binaryen.GlobReadRun
public import Silmaril.Wasm.Binaryen.InlUnwrap
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobals

@[expose] public section

/-! # SimplifyGlobals as a global-read simulation

The rewrite of one function body (`SimplifyGlobals.exprs m`) lowers to code related by
`GIL (lookup m) mi mi` for every instance `mi` (`exprs_rel`): each rewritten `global.get x`
is a site of the global-read simulation (`Binaryen/GlobReadSim.lean`).

* **Typing** (`exprs_tyRepl`): a site may replace `global.get x` in every context whose
  global `x` has the literal's type, and the module context of a valid module is such a
  context (`moduleCtx_globals`): `constant?` checks the declared type.
* **Instantiation** (`inst_ginv`): every instantiation of a module establishes the
  invariant `GInv (lookup m)`: the global initialiser `t.const b` evaluates to `b`, and the
  module's globals follow the imported ones.
-/

namespace Silmaril.Wasm.Binaryen.SimplifyGlobals

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.GlobRead

/-! ## Lookups -/

theorem constant?_intConst {g : Global} {i : Instr} (h : constant? g = some i) :
    g.type.mutability = .const ∧ g.init = [i] ∧ ∃ t b, i = .intConst t b ∧
      g.type.value = .num (.int t) := by
  unfold constant? at h
  split at h
  · next t b hm hi =>
    split at h
    · next hv =>
      cases h
      exact ⟨hm, hi, t, b, rfl, hv⟩
    · cases h
  · cases h

/-- A successful lookup: a defined immutable global with a literal initialiser of the
declared type. -/
theorem lookup_intConst {m : BModule} {x : GlobalIdx} {i : Instr} (h : lookup m x = some i) :
    m.numImportedGlobals ≤ x.toNat ∧ ∃ g, m.base.globals[x.toNat - m.numImportedGlobals]? = some g ∧
      g.type.mutability = .const ∧ g.init = [i] ∧ ∃ t b, i = .intConst t b ∧
        g.type.value = .num (.int t) := by
  unfold lookup at h
  split at h
  · cases h
  · next hx =>
    obtain ⟨g, hg, hi⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨by omega, g, hg, constant?_intConst hi⟩

/-- The lookup reads only the module's imports and globals. -/
theorem lookup_congr {m m' : BModule} (h : m'.base = m.base) : lookup m' = lookup m := by
  funext x
  simp only [lookup, BModule.numImportedGlobals, h]
  rfl

/-! ## The rewrite is a relation of the global-read simulation -/

theorem instr_rel (m : BModule) (mi : ModuleInst) (i : Instr) :
    GI (lookup m) mi mi i (instr m i) := by
  cases i with
  | globalGet x =>
    cases hl : lookup m x with
    | none => simpa [instr, hl] using GI.flat (lk := lookup m) (mi := mi) (cur := mi) (.globalGet x)
    | some c =>
      obtain ⟨-, -, -, -, -, t, b, rfl, -⟩ := lookup_intConst hl
      simpa [instr, hl] using GI.site (lk := lookup m) (mi := mi) (cur := mi) rfl hl
  | _ => exact .flat _

mutual
/-- The lowering of a rewritten tree is related to the original lowering. -/
theorem expr_rel (m : BModule) (mi : ModuleInst) :
    ∀ e : BExpr, GIL (lookup m) mi mi e.lower (expr m e).lower
  | .op i args => by
    simp only [expr, BExpr.lower_op]
    exact GIL.append (exprs_rel m mi args) (.cons (instr_rel m mi i) .nil)
  | .block bt b => by
    simp only [expr, BExpr.lower]
    exact .cons (.block (exprs_rel m mi b)) .nil
  | .loop bt b => by
    simp only [expr, BExpr.lower]
    exact .cons (.loop (exprs_rel m mi b)) .nil
  | .if_ bt c t e => by
    simp only [expr, BExpr.lower]
    exact GIL.append (exprs_rel m mi c) (.cons (.if_ (exprs_rel m mi t) (exprs_rel m mi e)) .nil)
  | .tryTable bt cs b => by
    simp only [expr, BExpr.lower]
    exact .cons (.tryTable (exprs_rel m mi b)) .nil
/-- The lowering of a rewritten list of trees is related to the original lowering. -/
theorem exprs_rel (m : BModule) (mi : ModuleInst) :
    ∀ es : List BExpr, GIL (lookup m) mi mi (BExpr.lowerList es) (BExpr.lowerList (exprs m es))
  | [] => .nil
  | e :: es => by
    simp only [exprs, BExpr.lowerList_cons]
    exact GIL.append (expr_rel m mi e) (exprs_rel m mi es)
end

/-! ## Typing in contexts that type the resolved globals -/

/-- Contexts whose resolved globals have the literal's type. -/
def GlobOk (lk : GlobalIdx → Option Instr) (G : List CGlobalType) : Prop :=
  ∀ (x : GlobalIdx) (t : IntType) (b : BitVec t.width), lk x = some (.intConst t b) →
    ∃ mu, G[x.toNat]? = some ⟨mu, .num (.int t)⟩

/-- `Y` may replace `X` in every well-formed context whose globals satisfy `Q`. -/
def TyReplG (Q : List CGlobalType → Prop) (X Y : List Instr) : Prop :=
  ∀ (C : Context) (it : InstrType), C.Wf → Q C.globals → InstrsOk C X it → InstrsOk C Y it

theorem initLocals_globals (C : Context) (xs : List Nat) :
    (C.initLocals xs).globals = C.globals := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

/-- Replacing one occurrence of an instruction in contexts satisfying `Q`. -/
theorem replace_oneG {Q : List CGlobalType → Prop} {i : Instr} {Y : List Instr}
    (h : ∀ C it, C.Wf → Q C.globals → InstrOk C i it → InstrsOk C Y it) :
    ∀ {C : Context} {L : List Instr} {it : InstrType}, InstrsOk C L it → C.Wf → Q C.globals →
      ∀ P R, L = P ++ i :: R → InstrsOk C (P ++ Y ++ R) it := by
  intro C L it hL
  induction hL using InstrsOk.ind with
  | nil => intro _ _ P R hPQ; cases P <;> simp at hPQ
  | @instr C i' it' hi =>
      intro hC hQ P R hPQ
      match P, R, hPQ with
      | [], [], hPQ =>
          simp only [List.nil_append, List.cons.injEq, and_true] at hPQ
          subst hPQ
          simpa using h C it' hC hQ hi
      | [], _ :: _, hPQ => simp at hPQ
      | _ :: P', _, hPQ => simp at hPQ
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      intro hC hQ P R hPQ
      have hQ' : Q (C.initLocals xs₁).globals := by rw [initLocals_globals]; exact hQ
      rcases List.append_eq_append_iff.mp hPQ with ⟨a, rfl, ha⟩ | ⟨c, hc, hR⟩
      · have := InstrsOk.seq h₁ hx (ih₂ (hC.initLocals _) hQ' a R ha)
        simpa [List.append_assoc] using this
      · cases c with
        | nil =>
          simp only [List.append_nil, List.nil_append] at hc hR
          subst hc
          have := InstrsOk.seq h₁ hx (ih₂ (hC.initLocals _) hQ' [] R hR.symm)
          simpa [List.append_assoc] using this
        | cons j c' =>
          simp only [List.cons_append, List.cons.injEq] at hR
          obtain ⟨rfl, rfl⟩ := hR
          have := InstrsOk.seq (ih₁ hC hQ P c' hc) hx h₂
          simpa [List.append_assoc] using this
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
      intro hC hQ P R hPQ
      have hQ' : Q (C.initLocals xs₁).globals := by rw [initLocals_globals]; exact hQ
      cases P with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        simpa using InstrsOk.seq (h C _ hC hQ hi) hx hs
      | cons a P' =>
        simp only [List.cons_append, List.cons.injEq] at hPQ
        obtain ⟨rfl, hPQ⟩ := hPQ
        simpa using InstrsOk.cons hi hx (ih (hC.initLocals _) hQ' P' R hPQ)
  | sub h hs hok ih => intro hC hQ P R hPQ; exact .sub (ih hC hQ P R hPQ) hs hok
  | frame h hok ih => intro hC hQ P R hPQ; exact .frame (ih hC hQ P R hPQ) hok

namespace TyReplG

variable {Q : List CGlobalType → Prop}

theorem refl (X : List Instr) : TyReplG Q X X := fun _ _ _ _ h => h

theorem of_instr {i : Instr} {Y : List Instr}
    (h : ∀ C it, C.Wf → Q C.globals → InstrOk C i it → InstrsOk C Y it) : TyReplG Q [i] Y :=
  fun _ _ hC hQ hX => by simpa using replace_oneG h hX hC hQ [] [] rfl

theorem append {X Y X' Y' : List Instr} (h : TyReplG Q X Y) (h' : TyReplG Q X' Y') :
    TyReplG Q (X ++ X') (Y ++ Y') := by
  intro C it hC hQ hX
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂, hL⟩ := InstrsOk.split hC hX rfl
  have r₁ := InstrsOk.regular hC h₁
  have hQ' : Q (C.initLocals xs₁).globals := by rw [initLocals_globals]; exact hQ
  have hY := InstrsOk.seq (h C _ hC hQ h₁) r₁.2.2 (h' _ _ (hC.initLocals _) hQ' h₂)
  have hreg := InstrsOk.regular hC hX
  refine .sub hY ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hreg
  intro x hx hn
  obtain ⟨lt, hlt⟩ := hreg.2.2 x hx
  have h2 := hL.set (Context.initLocals_set_of_mem hx hlt)
  rcases Context.initLocals_set h2 with hm | hm
  · exact absurd hm hn
  · exact ⟨_, hm⟩

theorem block {B B' : List Instr} (h : TyReplG Q B B') (bt : BlockType) :
    TyReplG Q [.block bt B] [.block bt B'] :=
  of_instr fun C it hC hQ hi => by
    cases hi with
    | block hbt hb =>
      exact .instr (.block hbt (h _ _ (wf_withLabel hC (hbt.regular hC).2) hQ hb))
    | _ => rename_i h; cases h

theorem loop {B B' : List Instr} (h : TyReplG Q B B') (bt : BlockType) :
    TyReplG Q [.loop bt B] [.loop bt B'] :=
  of_instr fun C it hC hQ hi => by
    cases hi with
    | loop hbt hb =>
      exact .instr (.loop hbt (h _ _ (wf_withLabel hC (hbt.regular hC).1) hQ hb))
    | _ => rename_i h; cases h

theorem if_ {B₁ B₁' B₂ B₂' : List Instr} (h₁ : TyReplG Q B₁ B₁') (h₂ : TyReplG Q B₂ B₂')
    (bt : BlockType) : TyReplG Q [.if_ bt B₁ B₂] [.if_ bt B₁' B₂'] :=
  of_instr fun C it hC hQ hi => by
    cases hi with
    | if_ hbt hb₁ hb₂ =>
      have hW := wf_withLabel hC (hbt.regular hC).2
      exact .instr (.if_ hbt (h₁ _ _ hW hQ hb₁) (h₂ _ _ hW hQ hb₂))
    | _ => rename_i h; cases h

theorem tryTable {B B' : List Instr} (h : TyReplG Q B B') (bt : BlockType) (cs : List Catch) :
    TyReplG Q [.tryTable bt cs B] [.tryTable bt cs B'] :=
  of_instr fun C it hC hQ hi => by
    cases hi with
    | tryTable hbt hb hc =>
      exact .instr (.tryTable hbt (h _ _ (wf_withLabel hC (hbt.regular hC).2) hQ hb) hc)
    | _ => rename_i h; cases h

end TyReplG

/-- **The site may replace the read** where the global has the literal's type. -/
theorem tyRepl_site {lk : GlobalIdx → Option Instr} {x : GlobalIdx} {t : IntType}
    {b : BitVec t.width} (hx : lk x = some (.intConst t b)) :
    TyReplG (GlobOk lk) [.globalGet x] [.intConst t b] :=
  TyReplG.of_instr fun C it _ hQ hi => by
    obtain ⟨mu, hg⟩ := hQ x t b hx
    cases hi with
    | «variable» h =>
      cases h with
      | globalGet h' =>
        rw [hg] at h'
        cases h'
        exact .instr (.numeric (.intConst t b))
    | _ => rename_i h; cases h

mutual
theorem GI.tyRepl {lk : GlobalIdx → Option Instr} {mi cur : ModuleInst} :
    ∀ {i i' : Instr}, GI lk mi cur i i' → TyReplG (GlobOk lk) [i] [i']
  | _, _, .flat _ => TyReplG.refl _
  | _, _, .site _ hx => tyRepl_site hx
  | _, _, .block h => TyReplG.block (GIL.tyRepl h) _
  | _, _, .loop h => TyReplG.loop (GIL.tyRepl h) _
  | _, _, .if_ h₁ h₂ => TyReplG.if_ (GIL.tyRepl h₁) (GIL.tyRepl h₂) _
  | _, _, .tryTable h => TyReplG.tryTable (GIL.tyRepl h) _ _
theorem GIL.tyRepl {lk : GlobalIdx → Option Instr} {mi cur : ModuleInst} :
    ∀ {is is' : List Instr}, GIL lk mi cur is is' → TyReplG (GlobOk lk) is is'
  | _, _, .nil => TyReplG.refl _
  | _, _, .cons h t => by
    simpa using TyReplG.append (GI.tyRepl h) (GIL.tyRepl t)
end

/-! ## Counting global imports -/

/-- Global extern addresses. -/
def xaG : ExternAddr → Bool
  | .global _ => true
  | _ => false

/-- Global extern types. -/
def xtG : CExternType → Bool
  | .global _ => true
  | _ => false

/-- Global imports. -/
def imG (i : Import) : Bool :=
  match i.type with
  | .global _ => true
  | _ => false

theorem externAddrOk_xaG {H : Type} {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : xaG xa = xtG xt := by
  induction h with
  | sub _ _ hs ih => rw [ih]; cases hs <;> rfl
  | _ => rfl

theorem importOk_imG {C : Context} {i : Import} {xt : CExternType} (h : ImportOk C i xt) :
    imG i = xtG xt := by
  obtain ⟨h, -⟩ := h
  unfold imG
  cases hty : i.type with
  | tag x =>
    rw [hty] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | global g =>
    rw [hty] at h
    cases h
    rfl
  | memory mt =>
    rw [hty] at h
    cases h
    rfl
  | table tt =>
    rw [hty] at h
    cases h
    rfl
  | func x =>
    rw [hty] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl

theorem filter_length_forall₂ {α β : Type _} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hR : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → (l.filter p).length = (l'.filter q).length
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.filter_cons, List.filter_cons, hR _ _ h]
    split <;> simp [filter_length_forall₂ hR t]

theorem externAddr_globals_length : ∀ xas : List ExternAddr,
    (ExternAddr.globals xas).length = (xas.filter xaG).length
  | [] => rfl
  | xa :: xas => by
    cases xa <;> simp [ExternAddr.globals, xaG, List.filter_cons, externAddr_globals_length xas]

theorem cextern_globals_length : ∀ xts : List CExternType,
    (CExternType.globals xts).length = (xts.filter xtG).length
  | [] => rfl
  | xt :: xts => by
    cases xt <;> simp [CExternType.globals, xtG, List.filter_cons, cextern_globals_length xts]

/-- The imported globals of a valid module number `numImportedGlobals`. -/
theorem imports_globals_length {C : Context} {m : BModule} {xtI : List CExternType}
    (h : List.Forall₂ (ImportOk C) m.base.imports xtI) :
    (CExternType.globals xtI).length = m.numImportedGlobals := by
  rw [cextern_globals_length, BModule.numImportedGlobals,
    ← filter_length_forall₂ (fun _ _ h => importOk_imG h) h]
  rfl

/-! ## The module context types the resolved globals -/

theorem globalsOk_get {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) :
    ∀ {i : Nat} {g : Global}, gs[i]? = some g →
      gts[i]? = some ⟨g.type.mutability, (liftVal g.type.value).substAll (C.types.map .dt)⟩ := by
  induction h with
  | nil => intro i g hg; simp at hg
  | @cons C g gs gt gts hg hs ih =>
    intro i g' hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢
      subst hi
      rw [hg.1]
      rfl
    | succ i => simpa using ih hi

theorem globOk_moduleCtx {m : BModule} {C' : Context} {xtI : List CExternType}
    {gts : List CGlobalType} (himports : List.Forall₂ (ImportOk { types := C'.types }) m.base.imports xtI)
    (hglobals : GlobalsOk C' m.base.globals gts) :
    GlobOk (lookup m) (CExternType.globals xtI ++ gts) := by
  intro x t b hx
  obtain ⟨hle, g, hg, hc, -, t', b', heq, hv⟩ := lookup_intConst hx
  cases heq
  have hlen := imports_globals_length himports
  refine ⟨g.type.mutability, ?_⟩
  rw [List.getElem?_append_right (by omega), hlen, globalsOk_get hglobals hg, hv]
  rfl

/-- Replacing the functions of a valid module, with the module context's globals known. -/
theorem moduleOk_replaceFuncsG {m : BModule} {mt : CModuleType} {fs : List Func}
    (h : ModuleOk m.lower mt)
    (hf : ∀ C fdts, C.Wf → GlobOk (lookup m) C.globals → List.Forall₂ (FuncOk C) m.lower.funcs fdts →
      List.Forall₂ (FuncOk C) fs fdts) :
    ModuleOk { m.lower with funcs := fs } mt := by
  obtain ⟨htypes, himports, rfl, rfl, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE
  have hW := moduleCtx_wf (rts := rts) (jts := jts) htypes himports htags hglobals htables
    (ModuleWf.funcs_mem hfuncs) (by
      intro rt hrt
      obtain ⟨_, _, he⟩ := forall₂_mem_right helems rt hrt
      exact he.2.1)
  exact ModuleOk.mk htypes himports rfl rfl htags hglobals hmems htables
    (hf _ _ hW (globOk_moduleCtx himports hglobals) hfuncs) hdata helems hstart hexports hnd

/-- A function stays valid when its body is replaced along `TyReplG`. -/
theorem funcOk_replaceBodyG {Q : List CGlobalType → Prop} {C : Context} (hC : C.Wf)
    (hQ : Q C.globals) {f : Func} {d : DefType} {body' : Expr}
    (h : FuncOk C f d) (hb : TyReplG Q f.body body') : FuncOk C { f with body := body' } d := by
  cases h with
  | @mk ps rs lts hd he hl hbody =>
    obtain ⟨hps, hrs⟩ := Expand.func_ok (hC.type hd) he
    exact .mk hd he hl (hb _ _ (hC.funcBody hps hrs (locals_tyOk hl)) hQ hbody)

/-! ## Instantiation establishes the invariant -/

theorem evalGlobals_lit {H : Type} {P : Numerics.Profile} {host : HostSemantics H} :
    ∀ {s : Store H} {f : Frame} {gts : List CGlobalType} {es : List Expr} {s' : Store H}
      {f' : Frame} {vs : List Val}, EvalGlobals P host s f gts es s' f' vs →
      vs.length = es.length ∧ ∀ (i : Nat) (t : IntType) (b : BitVec t.width),
        es[i]? = some [.intConst t b] → vs[i]? = some (.num ⟨.int t, b⟩) := by
  intro s f gts es s' f' vs h
  induction h with
  | nil => exact ⟨rfl, fun i t b h => by simp at h⟩
  | @cons s s₁ s'' f f₁ f'' g gs e es v vs he hs ih =>
    refine ⟨by simp [ih.1], fun i t b hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢
      subst hi
      have hT : Config.Terminal (⟨s, f, expression [.intConst t b]⟩ : Config H) :=
        ⟨.values [.num ⟨.int t, b⟩], by simp [expression, Result.toAdmin, vals, Val.toAdmin]⟩
      rcases Relation.ReflTransGen.cases_head he with heq | ⟨c₁, h₁, -⟩
      · simp only [Config.mk.injEq] at heq
        have h2 : v.toAdmin = (Val.num ⟨.int t, b⟩).toAdmin := by
          simpa [expression, vals, Val.toAdmin] using heq.2.2.symm
        have := congrArg Admin.val? h2
        simpa only [Admin.val?_toAdmin, Option.some.injEq] using this
      · exact (InlR.terminal_no_step hT c₁ h₁).elim
    | succ i => simpa using ih.2 i t b (by simpa using hi)

/-- **Every instantiation establishes the invariant** for the lookup of a module with the
same imports and globals. -/
theorem inst_ginv {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {m : BModule}
    {M : Module} (him : M.imports = m.base.imports) (hgl : M.globals = m.base.globals)
    {s : Store H} {xas : List ExternAddr} {c : Config H} (h : Instantiate P host s M xas c) :
    GInv (lookup m) c.frame.module c.store := by
  obtain ⟨xtE, xtI, hmt, hxas⟩ := h.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT, hE, hA, rfl⟩ := h.run
  obtain ⟨tagTypes, funcTypes, xi, -, -, -, hmi, hs4⟩ := allocModule?_inv hA
  have hnImp : (ExternAddr.globals xas).length = m.numImportedGlobals := by
    cases hmt with
    | mk _ himports =>
      rw [him] at himports
      rw [← imports_globals_length himports, externAddr_globals_length, cextern_globals_length]
      exact filter_length_forall₂ (fun _ _ h => externAddrOk_xaG h) hxas
  obtain ⟨hlenG, hlit⟩ := evalGlobals_lit hG
  simp only [List.length_map] at hlenG
  intro x t b hx
  obtain ⟨hle, g, hg, hc, hi, t', b', heq, -⟩ := lookup_intConst hx
  cases heq
  set i := x.toNat - m.numImportedGlobals with hi_def
  rw [← hgl] at hg
  have hilt : i < M.globals.length := (List.getElem?_eq_some_iff.mp hg).1
  have hv : valsG[i]? = some (.num ⟨.int t, b⟩) := hlit i t b (by simp [hg, hi])
  refine ⟨s₃.globals.length + i, ⟨⟨g.type.mutability,
    (liftVal g.type.value).substAll ((allocTypes M.types).map .dt)⟩, .num ⟨.int t, b⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · simp only [hmi]
    rw [List.getElem?_append_right (by omega), hnImp, List.getElem?_range' (by omega)]
    simp [hi_def]
  · rw [hs4]
    simp only
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp [List.zip_eq_zipWith, List.getElem?_zipWith, hg, hv]
  · exact hc
  · rfl

/-! ## Corresponding instantiations -/

section det

variable {H : Type} {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

theorem sr_of_alloc {lk : GlobalIdx → Option Instr} {M : Module} {xas : List ExternAddr}
    {g n₀ : Nat} {cL cR : Func} {c c' : Config H} (hg : M.funcs[g]? = some cL)
    (hA : InlR.FuncAlloc M xas c n₀)
    (hst : c'.store = InlS.withFuncs c.store (InlR.setCode c.store.funcs (n₀ + g) cR)) :
    ∃ dg, GlobRead.SR ⟨lk, c.frame.module, dg, n₀ + g, cL, cR⟩ c.store c'.store := by
  obtain ⟨dg, -, hcg⟩ := hA.code g cL hg
  refine ⟨dg, ⟨hcg, ?_⟩⟩
  rw [hst]
  congr 1
  unfold InlR.setCode
  rw [InlR.modify_eq_set_of _ hcg]
  rfl

/-- **The instantiations of a module and of the module with one function's code replaced
correspond**, when the codes are related and every instantiation of the left module
establishes the invariant. -/
theorem instCorr_of_set {lk : GlobalIdx → Option Instr} {M : Module} {g : Nat}
    {cL cR : Func} (hg : M.funcs[g]? = some cL) (hty : cR.type = cL.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cR } mt)
    (hgood : ∀ mi dg ag, GlobRead.PrmOk ⟨lk, mi, dg, ag, cL, cR⟩)
    (hinv : ∀ (s : Store H) xas c, Instantiate PD closedHost s M xas c →
      GInv lk c.frame.module c.store) :
    GlobRead.InstCorr (H := H) (o := o) M { M with funcs := M.funcs.set g cR } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      InlR.instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨dg, hSR⟩ := sr_of_alloc (lk := lk) hg hA hst
    exact ⟨c', _, hgood _ _ _, hi', hfr, hcode, hSR, hinv s xas c hi⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cR)[g]? = some cR := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cR } : Module) with
        funcs := (M.funcs.set g cR).set g cL } : Module) = M := by
      have : (M.funcs.set g cR).set g cL = M.funcs := by
        rw [List.set_set]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        by_cases hj : g = j
        · subst hj; simp [hlt, (List.getElem?_eq_some_iff.mp hg).2]
        · simp [hj]
      cases M
      simp only at this ⊢
      rw [this]
    obtain ⟨n₀, c, hi, hfr, hcode, hst, hA'⟩ :=
      InlR.instantiate_set (M := { M with funcs := M.funcs.set g cR }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := InlR.funcAlloc_back hg hty hA' hfr hst
    obtain ⟨dg, hSR⟩ := sr_of_alloc (lk := lk) hg hA hst'
    exact ⟨c, _, hgood _ _ _, hi, hfr.symm, hcode.symm, hSR, hinv s xas c hi⟩

end det

/-! ## One function -/

theorem forall₂_set {α β : Type _} {R : α → β → Prop} {x : α} :
    ∀ {l : List α} {l' : List β} {g : Nat} {a : α}, List.Forall₂ R l l' → l[g]? = some a →
      (∀ d, R a d → R x d) → List.Forall₂ R (l.set g x) l'
  | _, _, _, _, .nil, h, _ => by simp at h
  | _, _, 0, _, .cons hr t, h, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact .cons (hx _ hr) t
  | _, _, g + 1, _, .cons hr t, h, hx => .cons hr (forall₂_set t (by simpa using h) hx)

/-- Rewriting one function body of a module whose imports and globals are those of `m₀`
keeps validity, at the same module type. -/
theorem step_valid_mt {m₀ m : BModule} (hb : m.base = m₀.base) {g : Nat} {fg : BFunc}
    (hfg : m.funcs[g]? = some fg) {mt : CModuleType} (hmt : ModuleOk m.lower mt) :
    ModuleOk { m.lower with funcs := (m.lower.funcs.set g
      (({ fg with body := exprs m₀ fg.body } : BFunc).mapBody BExpr.lowerList)) } mt := by
  refine moduleOk_replaceFuncsG hmt fun C fdts hC hQ hf => ?_
  have hL : m.lower.funcs[g]? = some (fg.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hfg]
  refine forall₂_set hf hL fun d hd => ?_
  have hrel := GIL.tyRepl (exprs_rel m₀ ({} : ModuleInst) fg.body)
  rw [← lookup_congr hb] at hrel
  simpa [Declaration.Func.mapBody] using funcOk_replaceBodyG hC hQ hd hrel

theorem withBody_lower {m : BModule} {g : Nat} {fg : BFunc} (hfg : m.funcs[g]? = some fg)
    (B : List BExpr) :
    (m.withBody g B).lower = { m.lower with funcs := (m.lower.funcs.set g
      (({ fg with body := B } : BFunc).mapBody BExpr.lowerList)) } := by
  simp only [BModule.lower, withBody_eq_set hfg, List.map_set]
  rfl

/-- Export equivalence of two layer-D modules under the closed host. -/
abbrev EEq (H : Type) (o : Numerics.GrowKind → Nat → Nat → Nat → Bool) (a b : BModule) : Prop :=
  ExportEquiv (· = ·) (Numerics.Profile.deterministic o) (closedHost (H := H)) a.lower b.lower

/-- **Rewriting one function body** of a valid module whose imports and globals are those
of `m₀` keeps validity and export equivalence under the closed host. -/
theorem step_sound {m₀ m : BModule} (hb : m.base = m₀.base) {g : Nat} {fg : BFunc}
    (hfg : m.funcs[g]? = some fg) (hok : m.Ok) (o : Numerics.GrowKind → Nat → Nat → Nat → Bool)
    (H : Type) : (m.withBody g (exprs m₀ fg.body)).Ok ∧ EEq H o (m.withBody g (exprs m₀ fg.body)) m := by
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hL : m.lower.funcs[g]? = some (fg.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hfg]
  unfold EEq BModule.Ok
  rw [withBody_lower hfg]
  refine ⟨⟨mt₀, step_valid_mt hb hfg hmt₀⟩, GlobRead.exportEquiv_of_instCorr
    (instCorr_of_set (lk := lookup m₀) hL rfl (fun mt => ?_) (fun mi dg ag => ⟨rfl, ?_⟩)
      (fun s xas c hi => ?_))⟩
  · constructor
    · exact step_valid_mt hb hfg
    · intro h'
      have h₀ := step_valid_mt hb hfg hmt₀
      rw [ModuleOk.unique h' h₀]
      exact hmt₀
  · exact exprs_rel m₀ mi fg.body
  · exact inst_ginv (m := m₀) (by simp [BModule.lower, hb]) (by simp [BModule.lower, hb]) hi

/-- One step of the fold: rewrite function `g` with the lookup of `m₀`. -/
def stepAt (m₀ m : BModule) (g : Nat) : BModule :=
  match m.funcs[g]? with
  | some fg => m.withBody g (exprs m₀ fg.body)
  | none => m

theorem EEq.trans {H : Type} {o : Numerics.GrowKind → Nat → Nat → Nat → Bool} {a b c : BModule}
    (h₁ : EEq H o a b) (h₂ : EEq H o b c) : EEq H o a c :=
  ⟨h₁.1.trans (fun _ _ _ x y => x.trans y) h₂.1, h₂.2.trans (fun _ _ _ x y => y.trans x) h₁.2⟩

/-- **SimplifyGlobals is sound**: on a valid module, its output is valid and export
equivalent under the closed host. -/
theorem simplifyGlobals_sound (m : BModule) (hm : m.Ok)
    (o : Numerics.GrowKind → Nat → Nat → Nat → Bool) (H : Type) :
    (simplifyGlobals m).Ok ∧ EEq H o (simplifyGlobals m) m := by
  let F : BFunc → BFunc := fun f => { f with body := exprs m f.body }
  have key : ∀ k, ((List.range k).foldl (stepAt m) m).base = m.base ∧
      (∀ j, ((List.range k).foldl (stepAt m) m).funcs[j]? =
        if j < k then (m.funcs[j]?).map F else m.funcs[j]?) ∧
      ((List.range k).foldl (stepAt m) m).Ok ∧ EEq H o ((List.range k).foldl (stepAt m) m) m := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, fun j => by simp, hm, ?_⟩
      exact ⟨ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
        ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl (stepAt m) m = mk at ih ⊢
      obtain ⟨hb, hf, hok, he⟩ := ih
      have hk : mk.funcs[k]? = m.funcs[k]? := by rw [hf]; simp
      unfold stepAt
      cases hmk : mk.funcs[k]? with
      | none =>
        refine ⟨hb, fun j => ?_, hok, he⟩
        rw [hf j]
        by_cases hj : j < k
        · simp [hj, show j < k + 1 by omega]
        · by_cases hjk : j = k
          · subst hjk
            rw [← hk, hmk]
            simp
          · simp [hj, show ¬ j < k + 1 by omega]
      | some fk =>
        have hfk : m.funcs[k]? = some fk := by rw [← hk, hmk]
        obtain ⟨hok', he'⟩ := step_sound hb hmk hok o H
        refine ⟨hb, fun j => ?_, hok', he'.trans he⟩
        rw [withBody_eq_set hmk, List.getElem?_set]
        by_cases hjk : k = j
        · subst hjk
          simp [(List.getElem?_eq_some_iff.mp hmk).1, hfk, F]
        · simp only [hjk, ↓reduceIte]
          rw [hf j]
          by_cases hj : j < k
          · simp [hj, show j < k + 1 by omega]
          · simp [hj, show ¬ j < k + 1 by omega]
  obtain ⟨hb, hf, hok, he⟩ := key m.funcs.length
  generalize (List.range m.funcs.length).foldl (stepAt m) m = mk at hb hf hok he
  have heq : mk = simplifyGlobals m := by
    have hfs : mk.funcs = m.funcs.map F := by
      apply List.ext_getElem?
      intro j
      rw [hf j, List.getElem?_map]
      split
      · rfl
      · next hj => rw [List.getElem?_eq_none (by omega)]; rfl
    cases mk
    simp only at hb hfs
    subst hb hfs
    rfl
  subst heq
  exact ⟨hok, he⟩

end Silmaril.Wasm.Binaryen.SimplifyGlobals
