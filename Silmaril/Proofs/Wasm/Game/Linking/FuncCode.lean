module

public import Silmaril.Wasm.Link.StoreRelation
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Static linking: FuncCode

Original module documentation:

# Instantiation does not read stored function code (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. Constant
evaluation (`constInstr?`, `evalConst?`, `evalGlobals?`) never reads the function instances
of the store, and the residue allocation of single instantiation only reads their number.
Hence replacing the function list of a store by another list of the same length commutes
with `instantiateOnce?` in the linker's profile (`instantiateOnce?_withFuncs`). This is the
fact behind `Linking.Setup.scs_eq_stubOut`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC

variable {H : Type}

/-- Replace the function list of a store. -/
def withFuncs (g : List (FuncInst H)) (s : Store H) : Store H := { s with funcs := g }

set_option linter.unusedTactic false in
theorem structNew?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : TypeIdx} (run : structNew? s f vs x = some (r, out)) :
    structNew? (withFuncs g s) f vs x = some (withFuncs g r, out) := by
  simp only [structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    simp only [structNew?, Option.bind_eq_bind, hd, Option.bind_some, hf, hp, ite_eq_left hall]
    all_goals rfl
  · cases run

set_option linter.unusedTactic false in
theorem arrayNewFixed?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : TypeIdx} {n : Fin (2 ^ 32)}
    (run : arrayNewFixed? s f vs x n = some (r, out)) :
    arrayNewFixed? (withFuncs g s) f vs x n = some (withFuncs g r, out) := by
  simp only [arrayNewFixed?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    simp only [arrayNewFixed?, Option.bind_eq_bind, hd, Option.bind_some, hf, hp, ite_eq_left hall]
    all_goals rfl
  · cases run

theorem global?_withFuncs (g : List (FuncInst H)) (s : Store H) (f : Frame) (x : GlobalIdx) :
    (withFuncs g s).global? f x = s.global? f x := rfl

private theorem constInstr?_structNewDefault_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : TypeIdx}
    (run : constInstr? s f vs (.structNewDefault x) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.structNewDefault x) = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
  simp only [constInstr?, Option.bind_eq_bind, hd, Option.bind_some, hf, hv]
  exact structNew?_withFuncs g run
private theorem constInstr?_arrayNew_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : TypeIdx}
    (run : constInstr? s f vs (.arrayNew x) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.arrayNew x) = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, nv, hp, n, hn, run⟩ := run
  simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn]
  exact arrayNewFixed?_withFuncs g run
private theorem constInstr?_arrayNewDefault_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : TypeIdx}
    (run : constInstr? s f vs (.arrayNewDefault x) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.arrayNewDefault x) = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
  simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn, hd, hf, hv]
  exact arrayNewFixed?_withFuncs g run
private theorem constInstr?_refFunc_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : FuncIdx}
    (run : constInstr? s f vs (.refFunc x) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.refFunc x) = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨a, ha, run⟩ := run
  cases run
  simp only [constInstr?, Option.bind_eq_bind, ha, Option.bind_some]
private theorem constInstr?_refI31_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val}
    (run : constInstr? s f vs .refI31 = some (r, out)) :
    constInstr? (withFuncs g s) f vs .refI31 = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, b, hb, run⟩ := run
  cases run
  simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hb]
private theorem constInstr?_globalGet_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {x : GlobalIdx}
    (run : constInstr? s f vs (.globalGet x) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.globalGet x) = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨a, gi, hgl, run⟩ := run
  cases run
  simp only [constInstr?, Option.bind_eq_bind, global?_withFuncs, hgl, Option.bind_some]
private theorem constInstr?_intBinOp_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {t : IntType} {op : IntBinOp}
    (run : constInstr? s f vs (.intBinOp t op) = some (r, out)) :
    constInstr? (withFuncs g s) f vs (.intBinOp t op) = some (withFuncs g r, out) := by
  simp only [constInstr?] at run
  split at run
  · rename_i hop
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
    obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, run⟩ := run
    split at run
    · rename_i z hz
      cases run
      simp only [constInstr?, Option.bind_eq_bind, ite_eq_left hop, hp, Option.bind_some, hx, hy, hz]
    · cases run
  · cases run
private theorem constInstr?_anyConvertExtern_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val}
    (run : constInstr? s f vs .anyConvertExtern = some (r, out)) :
    constInstr? (withFuncs g s) f vs .anyConvertExtern = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, run⟩ := run
  split at run
  · cases run
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
  · cases run
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
  · cases run
private theorem constInstr?_externConvertAny_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val}
    (run : constInstr? s f vs .externConvertAny = some (r, out)) :
    constInstr? (withFuncs g s) f vs .externConvertAny = some (withFuncs g r, out) := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, run⟩ := run
  split at run
  · split at run
    all_goals
      cases run
      simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
      split <;> simp_all
  · cases run
/-- One constant instruction does not read the stored functions. -/
theorem constInstr?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {vs out : List Val} {i : Instr} (run : constInstr? s f vs i = some (r, out)) :
    constInstr? (withFuncs g s) f vs i = some (withFuncs g r, out) := by
  cases i
  case structNew x => exact structNew?_withFuncs g run
  case arrayNewFixed x n => exact arrayNewFixed?_withFuncs g run
  case structNewDefault x => exact constInstr?_structNewDefault_withFuncs g run
  case arrayNew x => exact constInstr?_arrayNew_withFuncs g run
  case arrayNewDefault x => exact constInstr?_arrayNewDefault_withFuncs g run
  case refFunc x => exact constInstr?_refFunc_withFuncs g run
  case refI31 => exact constInstr?_refI31_withFuncs g run
  case globalGet x => exact constInstr?_globalGet_withFuncs g run
  case intBinOp t op => exact constInstr?_intBinOp_withFuncs g run
  case anyConvertExtern => exact constInstr?_anyConvertExtern_withFuncs g run
  case externConvertAny => exact constInstr?_externConvertAny_withFuncs g run
  case intConst | floatConst | vecConst | refNull =>
    obtain ⟨rfl, rfl⟩ : s = r ∧ _ := by simpa only [constInstr?, Option.some.injEq,
      Prod.mk.injEq] using run
    rfl
  all_goals simp only [constInstr?, reduceCtorEq] at run

theorem constExpr?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {e : Expr} {out : List Val} (run : constExpr? s f e = some (r, out)) :
    constExpr? (withFuncs g s) f e = some (withFuncs g r, out) := by
  unfold constExpr? at run ⊢
  suffices ∀ (es : Expr) (st : Store H × List Val) (res : Store H × List Val),
      es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) st = some res →
        es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i)
          (withFuncs g st.1, st.2) = some (withFuncs g res.1, res.2) from
    this e (s, []) (r, out) run
  intro es
  induction es with
  | nil =>
    intro st res h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons i es ih =>
    intro st res h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    have h₁' := constInstr?_withFuncs g (s := st.1) (r := st₁.1) (out := st₁.2) h₁
    simp only [List.foldlM_cons, Option.bind_eq_bind, h₁', Option.bind_some]
    exact ih st₁ res h₂

theorem evalConst?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f : Frame}
    {e : Expr} {v : Val} (run : evalConst? s f e = some (r, v)) :
    evalConst? (withFuncs g s) f e = some (withFuncs g r, v) := by
  unfold evalConst? at run
  split at run
  · rename_i s' w hw
    cases run
    simp only [evalConst?, constExpr?_withFuncs g hw]
  · cases run

/-- One step of `evalGlobals?`: evaluate the first initializer, allocate its global, and
evaluate the rest in the extended frame. -/
private theorem evalGlobals?_cons_inv {s r : Store H} {f f' : Frame} {type : CGlobalType}
    {types : List CGlobalType} {e : Expr} {es : List Expr} {vs : List Val}
    (run : evalGlobals? evalConst? s f (type :: types) (e :: es) = some (r, f', vs)) :
    ∃ source value values, evalConst? s f e = some (source, value) ∧
      evalGlobals? evalConst? (allocGlobal source type value).1
        { f with module := { f.module with globals := f.module.globals ++
          [(allocGlobal source type value).2] } } types es = some (r, f', values) ∧
      vs = value :: values := by
  simp only [evalGlobals?] at run
  split at run
  · cases run
  · rename_i source value he
    split at run
    · cases run
    · rename_i result final values hg
      cases run
      exact ⟨source, value, values, he, hg, rfl⟩

theorem evalGlobals?_withFuncs (g : List (FuncInst H)) {s r : Store H} {f f' : Frame}
    {types : List CGlobalType} {es : List Expr} {vs : List Val}
    (run : evalGlobals? evalConst? s f types es = some (r, f', vs)) :
    evalGlobals? evalConst? (withFuncs g s) f types es = some (withFuncs g r, f', vs) := by
  induction types generalizing s f es vs with
  | nil =>
    cases es with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ : s = r ∧ f = f' ∧ [] = vs := by
        simpa only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] using run
      rfl
    | cons => simp only [evalGlobals?, reduceCtorEq] at run
  | cons type types ih =>
    show evalGlobals? evalConst? (withFuncs g s) f (type :: types) es =
      some (withFuncs g r, f', vs)
    cases es with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons e es =>
      obtain ⟨source, value, values, he, hg, hvs⟩ := evalGlobals?_cons_inv run
      have hg' : evalGlobals? evalConst? (allocGlobal (withFuncs g source) type value).1
          { f with module := { f.module with globals := f.module.globals ++
            [(allocGlobal (withFuncs g source) type value).2] } } types es =
            some (withFuncs g r, f', values) := ih hg
      rw [hvs]
      simp only [evalGlobals?, evalConst?_withFuncs g he, hg']

/-- Two frames with empty locals and the same module instance are equal. -/
private theorem frame_eq_of_module {f f' : Frame} (hl : f.locals = []) (hl' : f'.locals = [])
    (hmod : f'.module = f.module) : f' = f := by
  obtain ⟨l, mo⟩ := f
  obtain ⟨l', mo'⟩ := f'
  simp only [Frame.mk.injEq] at hl hl' hmod ⊢
  exact ⟨hl'.trans hl.symm, hmod⟩

/-- The module instance allocated by `allocModule?` (no globals, tables or elements) does not
depend on the stored functions, only on their number. -/
private theorem allocModule?_withFuncs_module (g : List (FuncInst H)) {s₁ s' t' : Store H}
    {m : Module} {xas : List ExternAddr} {mi mi' : ModuleInst} (hgl : g.length = s₁.funcs.length)
    (ha : allocModule? s₁ m xas [] [] [] = some (s', mi))
    (ha' : allocModule? (withFuncs g s₁) m xas [] [] [] = some (t', mi')) : mi' = mi := by
  obtain ⟨tt, ft, xi, htt, hft, hxi, hmi, -⟩ := allocModule?_inv ha
  obtain ⟨tt', ft', xi', htt', hft', hxi', hmi', -⟩ := allocModule?_inv ha'
  have htt_eq : tt' = tt := Option.some.inj (htt'.symm.trans htt)
  subst htt_eq
  simp only [withFuncs, hgl] at hxi' hmi'
  have hxi_eq : xi' = xi := Option.some.inj (hxi'.symm.trans hxi)
  rw [hmi', hmi, hxi_eq]

/-- **Instantiation commutes with replacing the stored functions** (same number of
functions, linker profile). -/
theorem instantiateOnce?_withFuncs (g : List (FuncInst H)) {s s' t' : Store H} {m : Module}
    {as : List Nat} {f f' : Frame} {st st' : Option FuncIdx}
    (hg : g.length = s.funcs.length) (hm : inProfile m = true)
    (h : instantiateOnce? s m (Preparation.imports as) = some (s', f, st))
    (h' : instantiateOnce? (withFuncs g s) m (Preparation.imports as) = some (t', f', st')) :
    f' = f ∧ t' = withFuncs (g ++ s'.funcs.drop s.funcs.length) s' := by
  obtain ⟨s₁, f₁, vs, hge, ha, hl, -⟩ := PreparationOnce.once_allocation hm h
  obtain ⟨t₁, g₁, ws, hge', ha', hl', -⟩ := PreparationOnce.once_allocation hm h'
  have hinit : ModuleInst.initial (withFuncs g s) m (Preparation.imports as) =
      ModuleInst.initial s m (Preparation.imports as) := by
    simp only [ModuleInst.initial, withFuncs, hg]
  have hrun : evalGlobals? evalConst? (withFuncs g s)
      ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (withFuncs g s₁, f₁, vs) := evalGlobals?_withFuncs g hge
  have hrun' : evalGlobals? evalConst? (withFuncs g s)
      ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (t₁, g₁, ws) := by
    rw [← hinit]
    exact hge'
  have ht₁ : t₁ = withFuncs g s₁ := by
    have heq : (t₁, g₁, ws) = (withFuncs g s₁, f₁, vs) := Option.some.inj (hrun'.symm.trans hrun)
    exact congrArg Prod.fst heq
  have ha'' : allocModule? (withFuncs g s₁) m.globalResidue
      (PreparationOnce.residueImports s m as) [] [] [] = some (t', f'.module) := ht₁ ▸ ha'
  have hshape : s₁.funcs = s.funcs := (evalGlobals?_shape hge).2.1
  have hgl : g.length = s₁.funcs.length := hshape ▸ hg
  have hframe : f' = f := frame_eq_of_module hl hl' (allocModule?_withFuncs_module g hgl ha ha'')
  refine ⟨hframe, ?_⟩
  obtain ⟨ty, hty, hs'⟩ := PreparationOnce.residue_store hm ha
  obtain ⟨ty', hty', ht'⟩ := PreparationOnce.residue_store hm ha''
  have hty_eq : ty' = ty := Option.some.inj (hty'.symm.trans hty)
  rw [ht', hs', hty_eq, hframe]
  simp only [withFuncs, hshape, List.drop_left]

end Silmaril.Proofs.Wasm.Game.Linking
