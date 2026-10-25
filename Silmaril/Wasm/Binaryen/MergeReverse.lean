module

public import Silmaril.Wasm.Binaryen.MergeLink

@[expose] public section

/-! # Separate instantiation from linked instantiation

The converse of `merged_exists`: if the linked module instantiates, so do the
provider and then the consumer against the provider's exports. The linked
initializer run contains a relocated copy of each part's initializers; a
relocated constant instruction that runs on the linked side also runs on the
source side when its indices are in the source frame's scope
(`instruction_back`), which validation provides (`xe_of_typing`). The forward
transport (`VisibleInitializers.instruction_transport`) then identifies the two
results, so the source run follows the linked one step by step.
-/

namespace Silmaril.Wasm.Binaryen.MergeChain

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.Preparation
open Silmaril.Wasm.Binaryen.MergeUntyped

variable {H : Type}

/-! ## One constant instruction -/

theorem source_runs {source target result' : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {i i' : Instr}
    (h : VisibleInitializers.Related r source target left right)
    (bounded : VisibleInitializers.Bounded source left)
    (rewrite : instruction? r i = some i') (scope : XE left.module i)
    (run : constInstr? target right vs i' = some (result', out)) :
    (constInstr? source left vs i).isSome := by
  cases i
  case intConst t x => simp [constInstr?]
  case floatConst t x => simp [constInstr?]
  case vecConst b => simp [constInstr?]
  case refNull ht => simp [constInstr?]
  case refFunc x =>
    have hx : x.toNat < left.module.funcs.length := by simpa only [XE] using scope
    simp [constInstr?, List.getElem?_eq_getElem hx]
  case globalGet x =>
    have hx : x.toNat < left.module.globals.length := by simpa only [XE] using scope
    have ha := List.getElem?_eq_getElem hx
    have hb := bounded _ (List.mem_of_getElem? ha)
    simp [constInstr?, Store.global?, ha, List.getElem?_eq_getElem hb]
  case refI31 =>
    simp only [instruction?, Option.some.injEq] at rewrite
    subst rewrite
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨pre, v⟩, hp, b, hb, -⟩ := run
    simp [constInstr?, hp, hb]
  case intBinOp t op =>
    simp only [instruction?, Option.some.injEq] at rewrite
    subst rewrite
    simp only [constInstr?] at run ⊢
    split at run
    · rename_i hop
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
      obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, run⟩ := run
      split at run
      · rename_i z hz
        simp [hop, hp, hx, hy, hz]
      · cases run
    · cases run
  case anyConvertExtern =>
    simp only [instruction?, Option.some.injEq] at rewrite
    subst rewrite
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨pre, v⟩, hp, run⟩ := run
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
    split at run <;> simp_all
  case externConvertAny =>
    simp only [instruction?, Option.some.injEq] at rewrite
    subst rewrite
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨pre, v⟩, hp, run⟩ := run
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
    cases v with
    | ref r => by_cases hr : r = Ref.null <;> simp [hr]
    | _ => simp at run
  case structNew x =>
    simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    have hx : x.toNat < left.module.types.length := by simpa only [XE] using scope
    have hd₀ := List.getElem?_eq_getElem hx
    have hdT := h.types hy hd₀
    simp only [constInstr?, structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Prod.exists] at run
    obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
    simp only [Frame.type?] at hd
    rw [hdT] at hd
    cases hd
    split at run
    · rename_i hall
      simp [constInstr?, structNew?, Frame.type?, hd₀, hf, hp, hall]
    · cases run
  case structNewDefault x =>
    simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    have hx : x.toNat < left.module.types.length := by simpa only [XE] using scope
    have hd₀ := List.getElem?_eq_getElem hx
    have hdT := h.types hy hd₀
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
    simp only [Frame.type?] at hd
    rw [hdT] at hd
    cases hd
    simp only [structNew?, Frame.type?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Prod.exists] at run
    obtain ⟨d', hd', fs', hf', pre, args, hp, run⟩ := run
    rw [hdT] at hd'
    cases hd'
    rw [hf] at hf'
    cases hf'
    split at run
    · rename_i hall
      simp [constInstr?, structNew?, Frame.type?, hd₀, hf, hv, hp, hall]
    · cases run
  case arrayNew x =>
    simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    have hx : x.toNat < left.module.types.length := by simpa only [XE] using scope
    have hd₀ := List.getElem?_eq_getElem hx
    have hdT := h.types hy hd₀
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨pre, v, nv⟩, hp, n, hn, run⟩ := run
    simp only [arrayNewFixed?, Frame.type?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Prod.exists] at run
    obtain ⟨d, hd, ft, hf, pre', args, hp', run⟩ := run
    rw [hdT] at hd
    cases hd
    split at run
    · rename_i hall
      simp [constInstr?, arrayNewFixed?, Frame.type?, hp, hn, hd₀, hf, hp']
      exact List.all_eq_true.mp hall
    · cases run
  case arrayNewDefault x =>
    simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    have hx : x.toNat < left.module.types.length := by simpa only [XE] using scope
    have hd₀ := List.getElem?_eq_getElem hx
    have hdT := h.types hy hd₀
    simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨pre, nv⟩, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
    simp only [Frame.type?] at hd
    rw [hdT] at hd
    cases hd
    simp only [arrayNewFixed?, Frame.type?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Prod.exists] at run
    obtain ⟨d', hd', ft', hf', pre', args, hp', run⟩ := run
    rw [hdT] at hd'
    cases hd'
    rw [hf] at hf'
    cases hf'
    split at run
    · rename_i hall
      simp [constInstr?, arrayNewFixed?, Frame.type?, hp, hn, hd₀, hf, hv, hp']
      exact List.all_eq_true.mp hall
    · cases run
  case arrayNewFixed x n =>
    simp only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at rewrite
    obtain ⟨y, hy, rfl⟩ := rewrite
    have hx : x.toNat < left.module.types.length := by simpa only [XE] using scope
    have hd₀ := List.getElem?_eq_getElem hx
    have hdT := h.types hy hd₀
    simp only [constInstr?, arrayNewFixed?, Frame.type?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Prod.exists] at run
    obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
    rw [hdT] at hd
    cases hd
    split at run
    · rename_i hall
      simp [constInstr?, arrayNewFixed?, Frame.type?, hd₀, hf, hp]
      exact List.all_eq_true.mp hall
    · cases run
  case select ts =>
    exfalso
    cases ts with
    | none =>
      simp only [instruction?, Option.some.injEq] at rewrite
      subst rewrite
      simp [constInstr?] at run
    | some ts =>
      simp only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨_, _, rfl⟩ := rewrite
      simp [constInstr?] at run
  all_goals exfalso
  all_goals (try simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    reduceCtorEq] at rewrite)
  all_goals first
    | (subst rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, rfl⟩ := rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, _, _, rfl⟩ := rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := rewrite; simp [constInstr?] at run)

/-- **A relocated constant instruction that runs on the linked side runs on the
source side**, with the same output and related stores. -/
theorem instruction_back {source target result' : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {i i' : Instr}
    (h : VisibleInitializers.Related r source target left right)
    (bounded : VisibleInitializers.Bounded source left)
    (rewrite : instruction? r i = some i') (scope : XE left.module i)
    (run : constInstr? target right vs i' = some (result', out)) :
    ∃ result, constInstr? source left vs i = some (result, out) ∧
      VisibleInitializers.Related r result result' left right := by
  obtain ⟨⟨result, out'⟩, hs⟩ := Option.isSome_iff_exists.mp (source_runs h bounded rewrite scope run)
  obtain ⟨result'', ht, hrel⟩ := VisibleInitializers.instruction_transport h rewrite hs
  rw [run] at ht
  cases ht
  exact ⟨result, hs, hrel⟩

/-! ## Expressions and global initializers -/

theorem fold_back {source target rT : Store H} {left right : Frame} {r : Relocation}
    {vs out : List Val} {e e' : Expr}
    (h : VisibleInitializers.Related r source target left right)
    (bounded : VisibleInitializers.Bounded source left)
    (rewrite : List.Forall₂ (fun i i' => instruction? r i = some i') e e')
    (scope : ∀ i ∈ e, XE left.module i)
    (run : e'.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 right st.2 i)
      (target, vs) = some (rT, out)) :
    ∃ rS, e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 left st.2 i)
        (source, vs) = some (rS, out) ∧
      VisibleInitializers.Related r rS rT left right ∧ VisibleInitializers.Bounded rS left := by
  induction rewrite generalizing source target vs with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨source, rfl, h, bounded⟩
  | @cons i i' es es' hi _ ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨t₁, vs₁⟩, h₁, h₂⟩ := run
    obtain ⟨s₁, hs₁, hrel₁⟩ := instruction_back h bounded hi (scope i (by simp)) h₁
    have bounded₁ : VisibleInitializers.Bounded s₁ left := fun a ha => by
      rw [(constInstr?_shape hs₁).1]
      exact bounded a ha
    obtain ⟨rS, hrS, hrel, hb⟩ := ih hrel₁ bounded₁ (fun j hj => scope j (by simp [hj])) h₂
    exact ⟨rS, by simp only [List.foldlM_cons, Option.bind_eq_bind, hs₁, Option.bind_some]
                  exact hrS, hrel, hb⟩

theorem constant_back {source target rT : Store H} {left right : Frame} {r : Relocation}
    {v : Val} {e e' : Expr}
    (h : VisibleInitializers.Related r source target left right)
    (bounded : VisibleInitializers.Bounded source left)
    (rewrite : instructions? r e = some e') (scope : ∀ i ∈ e, XE left.module i)
    (run : evalConst? target right e' = some (rT, v)) :
    ∃ rS, evalConst? source left e = some (rS, v) ∧
      VisibleInitializers.Related r rS rT left right ∧ VisibleInitializers.Bounded rS left := by
  unfold evalConst? at run
  split at run
  · rename_i t₀ v₀ hc
    cases run
    have hr := List.mapM_some_forall₂ (R := fun i i' => instruction? r i = some i')
      (fun h => h) rewrite
    unfold constExpr? at hc
    obtain ⟨rS, hrS, hrel, hb⟩ := fold_back h bounded hr scope hc
    exact ⟨rS, by simp only [evalConst?, constExpr?, hrS], hrel, hb⟩
  · cases run

/-- The scope of each initializer, by its position: a module instance with the
module's function and type counts and the globals evaluated so far. -/
def InitScope (es : List Expr) (nf nt ng : Nat) : Prop :=
  ∀ (k : Nat) (e : Expr), es[k]? = some e → ∀ i ∈ e, ∀ m : ModuleInst,
    m.funcs.length = nf → m.types.length = nt → m.globals.length = ng + k → XE m i

theorem InitScope.tail {e : Expr} {es : List Expr} {nf nt ng : Nat}
    (h : InitScope (e :: es) nf nt ng) : InitScope es nf nt (ng + 1) := by
  intro k e' hk i hi m hf ht hg
  exact h (k + 1) e' (by simpa using hk) i hi m hf ht (by omega)

/-- **A relocated initializer run on the linked side gives one on the source side**,
with the same values. -/
theorem globals_back {source target rT : Store H} {left right fT : Frame}
    {r : Relocation} {values : List Val} {types : List CGlobalType} {es es' : List Expr}
    (h : VisibleInitializers.Related r source target left right)
    (bounded : VisibleInitializers.Bounded source left)
    (length : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : List.Forall₂ (fun e e' => instructions? r e = some e') es es')
    (scope : InitScope es left.module.funcs.length left.module.types.length
      left.module.globals.length)
    (run : evalGlobals? evalConst? target right types es' = some (rT, fT, values)) :
    ∃ rS fS, evalGlobals? evalConst? source left types es = some (rS, fS, values) ∧
      VisibleInitializers.Related r rS rT fS fT := by
  induction rewrite generalizing types source target left right values rT fT with
  | nil =>
    cases types with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨source, left, rfl, h⟩
    | cons => simp only [evalGlobals?, reduceCtorEq] at run
  | @cons e e' es es' he _ ih =>
    cases types with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons type types =>
      simp only [evalGlobals?] at run
      split at run
      · cases run
      · rename_i t₁ value hv
        split at run
        · cases run
        · rename_i t₂ f₂ values₂ hg
          simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          obtain ⟨s₁, hs₁, hrel₁, hb₁⟩ := constant_back h bounded he
            (fun i hi => scope 0 e rfl i hi left.module rfl rfl (by simp)) hv
          have hrel₂ := hrel₁.allocGlobal hb₁ length type value
          have hb₂ := hb₁.allocGlobal type value
          have length₁ : (right.module.globals ++ [(allocGlobal t₁ type value).2]).length =
              r.globals + (left.module.globals ++ [(allocGlobal s₁ type value).2]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          obtain ⟨rS, fS, hrS, hrel⟩ := ih hrel₂ hb₂ length₁
            (by simpa using scope.tail) hg
          exact ⟨rS, fS, by simp only [evalGlobals?, hs₁, hrS], hrel⟩

theorem globals_split {s : Store H} {f : Frame} :
    ∀ {t₁ t₂ : List CGlobalType} {e₁ e₂ : List Expr} {s₂ : Store H} {f₂ : Frame}
      {values : List Val}, t₁.length = e₁.length →
      evalGlobals? evalConst? s f (t₁ ++ t₂) (e₁ ++ e₂) = some (s₂, f₂, values) →
      ∃ s₁ f₁ v₁ v₂, evalGlobals? evalConst? s f t₁ e₁ = some (s₁, f₁, v₁) ∧
        evalGlobals? evalConst? s₁ f₁ t₂ e₂ = some (s₂, f₂, v₂) ∧ values = v₁ ++ v₂ := by
  intro t₁
  induction t₁ generalizing s f with
  | nil =>
    intro t₂ e₁ e₂ s₂ f₂ values hlen run
    cases e₁ with
    | nil => exact ⟨s, f, [], values, rfl, run, rfl⟩
    | cons => simp at hlen
  | cons t ts ih =>
    intro t₂ e₁ e₂ s₂ f₂ values hlen run
    cases e₁ with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.cons_append, evalGlobals?] at run
      split at run
      · cases run
      · rename_i s' v he
        split at run
        · cases run
        · rename_i s'' f'' vs hr
          simp only [Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          obtain ⟨s₁, f₁, v₁, v₂, h₁, h₂, rfl⟩ := ih (by simpa using hlen) hr
          exact ⟨s₁, f₁, v :: v₁, v₂, by simp only [evalGlobals?, he, h₁], h₂, rfl⟩

/-- Validation scopes every global initializer: function, type and global indices
are in range of the module's counts, globals only before their own. -/
theorem globals_scope {C : Context} :
    ∀ {gs : List Global} {gts : List CGlobalType}, GlobalsOk C gs gts →
      InitScope (gs.map Global.init) C.funcs.length C.types.length C.globals.length := by
  intro gs gts h
  induction h with
  | nil => intro k e hk; simp at hk
  | @cons C g gs gt gts hg _ ih =>
    intro k e hk i hi m hf ht hgl
    cases k with
    | zero =>
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨-, -, hc⟩ := hg
      exact xe_of_typing hc.typed i hi m ⟨ht, hf, by simpa using hgl⟩
    | succ k =>
      simp only [List.map_cons, List.getElem?_cons_succ] at hk
      exact ih k e hk i hi m hf ht (by simp at hgl ⊢; omega)


theorem init_scope_of_valid {m : Module} {xtI xtE : List CExternType}
    (hm : Link.GC.inProfile m = true) (hok : ModuleOk m ⟨xtI, xtE⟩) :
    InitScope (m.globals.map Global.init) (xtI.length + m.funcs.length)
      (allocTypes m.types).length 0 := by
  cases hok with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
  rename_i dts jts gts tts fdts rts C' C
  subst hC'
  have h := globals_scope hglobals
  obtain ⟨hglob, -, -, -, hfunI⟩ := externs_of_funcs (import_types_funcs hm himports)
  have hfl := hfuncs.length_eq
  rw [allocTypes_eq htypes]
  intro k e hk i hi mi hf ht hg
  refine h k e hk i hi mi ?_ ht ?_
  · simp only [List.length_append, hfunI]
    omega
  · simpa only [hglob, List.length_nil] using hg

theorem initial_counts (s : Store H) (m : Module) (as : List Nat) :
    (ModuleInst.initial s m (imports as)).funcs.length = as.length + m.funcs.length ∧
      (ModuleInst.initial s m (imports as)).types.length = (allocTypes m.types).length ∧
      (ModuleInst.initial s m (imports as)).globals.length = 0 := by
  simp [ModuleInst.initial, imports_funcs, imports_globals]

/-- **The parts instantiate whenever the linked module does.** -/
theorem separate_exists {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result)
    (hl : link? ns provider consumer = some result) {s : Store H} {cl : Config H}
    {startL : Option FuncIdx}
    (hm : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    ∃ cp startP, prepare? evalConst? s provider (imports []) = some (cp, startP) ∧
      ∃ cc startC, prepare? evalConst? cp.store consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (cc, startC) := by
  obtain ⟨sL₁, fL₁, valuesL, globalsL, -, -, -, -⟩ := prepare_allocation (result_profile w) hm
  have initializers : result.globals.map Global.init =
      provider.globals.map Global.init ++ w.globals.map Global.init := by
    have globals : result.globals = w.providerGlobals ++ w.globals :=
      congrArg Module.globals w.output
    rw [globals, Identity.provider_globals w, List.map_append]
  rw [Initializers.link_closed_global_types w hl, initializers] at globalsL
  obtain ⟨t₁, f₁, v₁, v₂, run₁, run₂, -⟩ :=
    globals_split (by simp [Module.closedGlobalTypes]) globalsL
  -- the provider
  obtain ⟨⟨xtIP, xtEP⟩, hokP⟩ : ∃ mt, ModuleOk provider mt :=
    ⟨_, validate?_sound w.providerValidation⟩
  have hxtIP : xtIP.length = 0 := by
    cases hokP with
    | mk _ himports _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [w.providerImports] at himports
      cases himports
      rfl
  have viewsP := OrdinaryInitializers.provider_initial_views w hl s
  have relatedP : VisibleInitializers.Related Recipe.identity s s
      ⟨[], ModuleInst.initial s provider (imports [])⟩
      ⟨[], ModuleInst.initial s result (imports [])⟩ :=
    VisibleInitializers.Related.of_empty_globals viewsP rfl rfl rfl
  have rewriteP := Initializers.initializer_rewrite w.providerGlobalsRewrite
  rw [Identity.provider_globals w] at rewriteP
  have scopeP : InitScope (provider.globals.map Global.init)
      (ModuleInst.initial s provider (imports [])).funcs.length
      (ModuleInst.initial s provider (imports [])).types.length
      (ModuleInst.initial s provider (imports [])).globals.length := by
    obtain ⟨c1, c2, c3⟩ := initial_counts s provider []
    rw [c1, c2, c3]
    have := init_scope_of_valid w.providerProfile hokP
    simpa [hxtIP] using this
  obtain ⟨sP₁, fP₁, runP, hrelP⟩ := globals_back relatedP (VisibleInitializers.Bounded.empty rfl)
    (by simp only [ModuleInst.initial, imports_globals, Recipe.identity,
      List.length_nil, Nat.zero_add]) rewriteP scopeP run₁
  have hv₁ : v₁.length = provider.globals.length := by
    simpa [Module.closedGlobalTypes] using evalGlobals_values_length runP
  obtain ⟨sp, mip, hallocP⟩ := allocModule_exists (s := sP₁) (as := []) w.providerProfile hokP
    (by simp [w.providerImports]) hv₁
  have hp := prepare_of w.providerProfile runP hallocP
  refine ⟨_, _, hp, ?_⟩
  -- the consumer
  obtain ⟨⟨xtIC, xtEC⟩, hokC⟩ : ∃ mt, ModuleOk consumer mt :=
    ⟨_, validate?_sound w.consumerValidation⟩
  have hxtIC : xtIC.length = consumer.imports.length := by
    cases hokC with
    | mk _ himports _ _ _ _ _ _ _ _ _ _ _ _ => exact himports.length_eq.symm
  have shapeP := (evalGlobals?_shape run₁).2.2
  have countP : sp.funcs.length = s.funcs.length + provider.funcs.length :=
    (prepared_counts w.providerProfile hp).1
  have viewsC := OrdinaryInitializers.consumer_initial_views w hl s sp countP
  have viewsC' : Views.Successful (Recipe.relocation provider w.imports)
      (ModuleInst.initial sp consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))) f₁.module := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y a rewrite lookup
      rw [shapeP]
      exact viewsC.functions rewrite lookup
    · intro x y a rewrite lookup
      simp only [ModuleInst.initial, imports_globals, List.getElem?_nil, reduceCtorEq] at lookup
    · intro x y d rewrite lookup
      rw [shapeP]
      exact viewsC.types rewrite lookup
  have heapsP := OrdinaryInitializers.allocation_heaps hallocP
  have relatedC : VisibleInitializers.Related (Recipe.relocation provider w.imports) sp t₁
      ⟨[], ModuleInst.initial sp consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))⟩ f₁ :=
    VisibleInitializers.Related.of_empty_globals viewsC' (imports_globals _)
      (heapsP.1.trans hrelP.structs) (heapsP.2.trans hrelP.arrays)
  have lengthC : f₁.module.globals.length =
      (Recipe.relocation provider w.imports).globals +
        (ModuleInst.initial sp consumer
          (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).globals.length := by
    rw [shapeP]
    simp only [ModuleInst.initial, imports_globals, Recipe.relocation, List.nil_append,
      List.length_map, List.length_range, Module.closedGlobalTypes, List.length_nil,
      Nat.add_zero]
  have scopeC : InitScope (consumer.globals.map Global.init)
      (ModuleInst.initial sp consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).funcs.length
      (ModuleInst.initial sp consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).types.length
      (ModuleInst.initial sp consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).globals.length := by
    obtain ⟨c1, c2, c3⟩ := initial_counts sp consumer
      (w.imports.map (fun f => s.funcs.length+f.toNat))
    rw [c1, c2, c3, List.length_map, w.imports_length, ← hxtIC]
    exact init_scope_of_valid w.consumerProfile hokC
  obtain ⟨sC₁, fC₁, runC, -⟩ := globals_back relatedC
    (VisibleInitializers.Bounded.empty (imports_globals _)) lengthC
    (Initializers.initializer_rewrite w.globalsRewrite) scopeC run₂
  have hv₂ : v₂.length = consumer.globals.length := by
    simpa [Module.closedGlobalTypes] using evalGlobals_values_length runC
  obtain ⟨sc, mic, hallocC⟩ := allocModule_exists (s := sC₁)
    (as := w.imports.map (fun f => s.funcs.length+f.toNat)) w.consumerProfile hokC
    (by rw [List.length_map, w.imports_length]) hv₂
  exact ⟨_, _, prepare_of w.consumerProfile runC hallocC⟩

end Silmaril.Wasm.Binaryen.MergeChain
