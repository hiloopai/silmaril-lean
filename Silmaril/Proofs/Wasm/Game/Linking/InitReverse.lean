module

public import Silmaril.Wasm.Link.StoreRelation
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Static linking: InitReverse

Original module documentation:

# Reverse initializer transport under static linking (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. #1936's
`Initializers.globals_transport` carries a successful separate initializer run to the linked
one. Here the converse: when the linked (relocated) initializers succeed, so do the separate
ones, provided every relocated index lookup that succeeds on the linked side has a source
counterpart (`Reflects`, plus the global-count equation). The source run then agrees with the
linked one by the forward transport and determinism.

`consumer_globals_exist` applies this to the consumer's initializers after the provider:
from a successful instantiation of the linked module, the consumer's `$evalglobals` in the
provider's store succeeds.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC
  Silmaril.Wasm.Link.GC.Initializers

variable {H : Type}

/-- Successful relocated function and type lookups on the target side have source
counterparts. -/
structure Reflects (r : Relocation) (source target : ModuleInst) : Prop where
  functions : ∀ {x y : FuncIdx} {a : Nat}, function? r x = some y →
    target.funcs[y.toNat]? = some a → ∃ a', source.funcs[x.toNat]? = some a'
  types : ∀ {x y : TypeIdx} {d : DefType}, shiftIdx? r.types x = some y →
    target.types[y.toNat]? = some d → ∃ d', source.types[x.toNat]? = some d'

theorem Reflects.type_lookup {r : Relocation} {left right : Frame}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) {x y : TypeIdx} {d : DefType}
    (hy : shiftIdx? r.types x = some y) (hd : right.type? y = some d) : left.type? x = some d := by
  obtain ⟨d', hd'⟩ := refl.types hy hd
  have := views.types hy hd'
  have he : d' = d := Option.some.inj (this.symm.trans hd)
  subst he
  exact hd'

theorem Reflects.function_lookup {r : Relocation} {left right : Frame}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) {x y : FuncIdx} {a : Nat}
    (hy : function? r x = some y) (ha : right.module.funcs[y.toNat]? = some a) :
    left.module.funcs[x.toNat]? = some a := by
  obtain ⟨a', ha'⟩ := refl.functions hy ha
  have := views.functions hy ha'
  have he : a' = a := Option.some.inj (this.symm.trans ha)
  subst he
  exact ha'

theorem global_lookup_reflect {source target : Store H} {r : Relocation} {left right : Frame}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (hy : shiftIdx? r.globals x = some y)
    (hg : target.global? right y = some (a, g)) : source.global? left x = some (a, g) := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨a', ha, g', hg, rfl, rfl⟩ := hg
  have hyn := LinkExecution.shiftIdx?_toNat hy
  have hb := (List.getElem?_eq_some_iff.mp ha).1
  have hx : x.toNat < left.module.globals.length := by omega
  obtain ⟨b, hb'⟩ : ∃ b, left.module.globals[x.toNat]? = some b :=
    ⟨_, List.getElem?_eq_getElem hx⟩
  have hr := views.globals hy hb'
  have he : b = a' := Option.some.inj (hr.symm.trans ha)
  subst he
  simp only [Store.global?, Option.bind_eq_bind, hb', Option.bind_some, h.globals, hg,
    Option.pure_def]

theorem structNew_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {vs : List Val} {x y : TypeIdx} {p : Store H × List Val}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : shiftIdx? r.types x = some y)
    (run : structNew? target right vs y = some p) :
    ∃ q, structNew? source left vs x = some q := by
  simp only [structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    exact Option.isSome_iff_exists.mp (by
      simp only [structNew?, Option.bind_eq_bind, refl.type_lookup views hy hd,
        Option.bind_some, hf, hp, ite_eq_left hall, Option.isSome_some])
  · cases run

theorem arrayNewFixed_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {vs : List Val} {x y : TypeIdx} {n : Fin (2 ^ 32)} {p : Store H × List Val}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : shiftIdx? r.types x = some y)
    (run : arrayNewFixed? target right vs y n = some p) :
    ∃ q, arrayNewFixed? source left vs x n = some q := by
  simp only [arrayNewFixed?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    exact Option.isSome_iff_exists.mp (by
      simp only [arrayNewFixed?, Option.bind_eq_bind, refl.type_lookup views hy hd,
        Option.bind_some, hf, hp, ite_eq_left hall, Option.isSome_some])
  · cases run

private theorem refFunc_reflect {source target : Store H} {left right : Frame} {r : Relocation} {vs : List Val}
    {p : Store H × List Val} {x y : FuncIdx}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : function? r x = some y)
    (run : constInstr? target right vs (.refFunc y) = some p) :
    ∃ q, constInstr? source left vs (.refFunc x) = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨a, ha, -⟩ := run
  exact Option.isSome_iff_exists.mp (by simp only [constInstr?, Option.bind_eq_bind,
    refl.function_lookup views hy ha, Option.bind_some, Option.isSome_some])

private theorem refI31_reflect {source target : Store H} {left right : Frame} {vs : List Val} {p : Store H × List Val}
    (run : constInstr? target right vs .refI31 = some p) :
    ∃ q, constInstr? source left vs .refI31 = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, b, hb, -⟩ := run
  exact Option.isSome_iff_exists.mp (by
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hb, Option.isSome_some])

private theorem globalGet_reflect {source target : Store H} {left right : Frame} {r : Relocation} {vs : List Val}
    {p : Store H × List Val} {x y : GlobalIdx}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (hy : shiftIdx? r.globals x = some y)
    (run : constInstr? target right vs (.globalGet y) = some p) :
    ∃ q, constInstr? source left vs (.globalGet x) = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨a, g, hg, -⟩ := run
  exact Option.isSome_iff_exists.mp (by simp only [constInstr?, Option.bind_eq_bind,
    global_lookup_reflect h views glen hy hg, Option.bind_some, Option.isSome_some])

private theorem intBinOp_reflect {source target : Store H} {left right : Frame} {vs : List Val} {p : Store H × List Val} {t : IntType} {op : IntBinOp}
    (run : constInstr? target right vs (.intBinOp t op) = some p) :
    ∃ q, constInstr? source left vs (.intBinOp t op) = some q := by
  simp only [constInstr?] at run
  split at run
  · rename_i hop
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
    obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, run⟩ := run
    split at run
    · rename_i z hz
      exact Option.isSome_iff_exists.mp (by
        simp only [constInstr?, Option.bind_eq_bind, ite_eq_left hop, hp,
          Option.bind_some, hx, hy, hz, Option.isSome_some])
    · cases run
  · cases run

private theorem anyConvertExtern_reflect {source target : Store H} {left right : Frame} {vs : List Val} {p : Store H × List Val}
    (run : constInstr? target right vs .anyConvertExtern = some p) :
    ∃ q, constInstr? source left vs .anyConvertExtern = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, run⟩ := run
  split at run
  · exact Option.isSome_iff_exists.mp (by
      simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, Option.isSome_some])
  · exact Option.isSome_iff_exists.mp (by
      simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, Option.isSome_some])
  · cases run

private theorem externConvertAny_reflect {source target : Store H} {left right : Frame} {vs : List Val} {p : Store H × List Val}
    (run : constInstr? target right vs .externConvertAny = some p) :
    ∃ q, constInstr? source left vs .externConvertAny = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, hp, run⟩ := run
  split at run
  · simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · cases run

private theorem structNewDefault_reflect {source target : Store H} {left right : Frame} {r : Relocation} {vs : List Val}
    {p : Store H × List Val} {x y : TypeIdx}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : shiftIdx? r.types x = some y)
    (run : constInstr? target right vs (.structNewDefault y) = some p) :
    ∃ q, constInstr? source left vs (.structNewDefault x) = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
  obtain ⟨q, hq⟩ := structNew_reflect (source := source) views refl hy run
  exact ⟨q, by simp only [constInstr?, Option.bind_eq_bind, refl.type_lookup views hy hd,
    Option.bind_some, hf, hv]; exact hq⟩

private theorem arrayNew_reflect {source target : Store H} {left right : Frame} {r : Relocation} {vs : List Val}
    {p : Store H × List Val} {x y : TypeIdx}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : shiftIdx? r.types x = some y)
    (run : constInstr? target right vs (.arrayNew y) = some p) :
    ∃ q, constInstr? source left vs (.arrayNew x) = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, v, nv, hp, n, hn, run⟩ := run
  obtain ⟨q, hq⟩ := arrayNewFixed_reflect (source := source) views refl hy run
  exact ⟨q, by
    simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn]; exact hq⟩

private theorem arrayNewDefault_reflect {source target : Store H} {left right : Frame} {r : Relocation} {vs : List Val}
    {p : Store H × List Val} {x y : TypeIdx}
    (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module) (hy : shiftIdx? r.types x = some y)
    (run : constInstr? target right vs (.arrayNewDefault y) = some p) :
    ∃ q, constInstr? source left vs (.arrayNewDefault x) = some q := by
  simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
  obtain ⟨q, hq⟩ := arrayNewFixed_reflect (source := source) views refl hy run
  exact ⟨q, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn,
    refl.type_lookup views hy hd, hf, hv]; exact hq⟩

/-- A relocated `select` is never a constant instruction. -/
private theorem select_not_const {target : Store H} {right : Frame} {r : Relocation}
    {vs : List Val} {p : Store H × List Val} {o : Option (List ValType)} {i' : Instr}
    (rewrite : instruction? r (.select o) = some i')
    (run : constInstr? target right vs i' = some p) : False := by
  cases o <;> simp only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at rewrite
  · subst rewrite; simp [constInstr?] at run
  · obtain ⟨_, _, rfl⟩ := rewrite; simp [constInstr?] at run

/-- **Reverse instruction transport**: a successful relocated constant instruction has a
successful source counterpart. -/
theorem instruction_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {vs : List Val} {i i' : Instr} {p : Store H × List Val}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : instruction? r i = some i') (run : constInstr? target right vs i' = some p) :
    ∃ q, constInstr? source left vs i = some q := by
  cases i
  case intConst t x => exact ⟨_, rfl⟩
  case floatConst t x => exact ⟨_, rfl⟩
  case refNull ht => exact ⟨_, rfl⟩
  case refFunc x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, function? r x = some y ∧ Instr.refFunc y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact refFunc_reflect views refl hy (hi ▸ run)
  case refI31 =>
    have hi : Instr.refI31 = i' := by simpa only [instruction?, Option.some.injEq] using rewrite
    exact refI31_reflect (hi ▸ run)
  case globalGet x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.globals x = some y ∧ Instr.globalGet y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact globalGet_reflect h views glen hy (hi ▸ run)
  case intBinOp t op =>
    have hi : Instr.intBinOp t op = i' := by
      simpa only [instruction?, Option.some.injEq] using rewrite
    exact intBinOp_reflect (hi ▸ run)
  case anyConvertExtern =>
    have hi : Instr.anyConvertExtern = i' := by
      simpa only [instruction?, Option.some.injEq] using rewrite
    exact anyConvertExtern_reflect (hi ▸ run)
  case externConvertAny =>
    have hi : Instr.externConvertAny = i' := by
      simpa only [instruction?, Option.some.injEq] using rewrite
    exact externConvertAny_reflect (hi ▸ run)
  case structNew x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.types x = some y ∧ Instr.structNew y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact structNew_reflect views refl hy (hi ▸ run)
  case structNewDefault x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.types x = some y ∧ Instr.structNewDefault y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact structNewDefault_reflect views refl hy (hi ▸ run)
  case arrayNew x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.types x = some y ∧ Instr.arrayNew y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact arrayNew_reflect views refl hy (hi ▸ run)
  case arrayNewDefault x =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.types x = some y ∧ Instr.arrayNewDefault y = i' := by
      simpa only [instruction?, Option.map_eq_map, Option.map_eq_some_iff] using rewrite
    exact arrayNewDefault_reflect views refl hy (hi ▸ run)
  case arrayNewFixed x n =>
    obtain ⟨y, hy, hi⟩ : ∃ y, shiftIdx? r.types x = some y ∧ Instr.arrayNewFixed y n = i' := by
      simpa only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] using rewrite
    exact arrayNewFixed_reflect views refl hy (hi ▸ run)
  case select o => exact (select_not_const rewrite run).elim
  -- Every other instruction is relocated to an instruction of the same kind, which is not
  -- constant.
  all_goals simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    reduceCtorEq] at rewrite
  all_goals first
    | (subst rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, rfl⟩ := rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, _, _, rfl⟩ := rewrite; simp [constInstr?] at run)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := rewrite; simp [constInstr?] at run)

/-- `fold_reflect` along the instruction-wise relocation relation. -/
private theorem fold_reflect_forall₂ {source target : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {e e' : Expr} {res' : Store H}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (hr : List.Forall₂ (fun i i' => instruction? r i = some i') e e')
    (run : e'.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 right st.2 i)
      (target, vs) = some (res', out)) :
    ∃ res, e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 left st.2 i)
      (source, vs) = some (res, out) := by
  induction hr generalizing source target vs with
  | nil =>
    have hvs : target = res' ∧ vs = out := by
      simpa only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] using run
    exact ⟨source, by rw [hvs.2]; rfl⟩
  | cons hi _ ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨t₁, vs₁⟩, h₁, h₂⟩ := run
    obtain ⟨⟨s₁, o₁⟩, hs₁⟩ := instruction_reflect h views refl glen hi h₁
    obtain ⟨t₁', ht₁', data₁⟩ := instruction_transport h views hi hs₁
    obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ o₁ = vs₁ := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using ht₁'.symm.trans h₁
    obtain ⟨res, hres⟩ := ih data₁ h₂
    exact ⟨res, by simpa only [List.foldlM_cons, Option.bind_eq_bind, hs₁, Option.bind_some]⟩

theorem fold_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {vs out : List Val} {e e' : Expr} {res' : Store H}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : instructions? r e = some e')
    (run : e'.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 right st.2 i)
      (target, vs) = some (res', out)) :
    ∃ res, e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 left st.2 i)
      (source, vs) = some (res, out) := by
  have hr : List.Forall₂ (fun i i' => instruction? r i = some i') e e' :=
    List.mapM_some_forall₂ (R := fun i i' => instruction? r i = some i') (fun h => h) rewrite
  exact fold_reflect_forall₂ h views refl glen hr run

theorem constant_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {e e' : Expr} {res' : Store H} {v : Val}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : instructions? r e = some e')
    (run : evalConst? target right e' = some (res', v)) :
    ∃ res, evalConst? source left e = some (res, v) := by
  unfold evalConst? at run
  split at run
  · rename_i t w hw
    cases run
    obtain ⟨res, hres⟩ := fold_reflect h views refl glen rewrite hw
    exact ⟨res, by simp only [evalConst?]; unfold constExpr?; rw [hres]⟩
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

/-- **Reverse transport of sequential global initialization.** -/
theorem globals_reflect {source target : Store H} {left right : Frame} {r : Relocation}
    {types : List CGlobalType} {es es' : List Expr} {res' : Store H} {fin' : Frame}
    {values : List Val}
    (h : Initializers.Data source target) (views : Views.Successful r left.module right.module)
    (refl : Reflects r left.module right.module)
    (glen : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : List.Forall₂ (fun e e' => instructions? r e = some e') es es')
    (run : evalGlobals? evalConst? target right types es' = some (res', fin', values)) :
    ∃ res fin, evalGlobals? evalConst? source left types es = some (res, fin, values) := by
  induction rewrite generalizing types source target left right values with
  | nil =>
    cases types with
    | nil =>
      have hvs : target = res' ∧ right = fin' ∧ [] = values := by
        simpa only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] using run
      exact ⟨source, left, by rw [← hvs.2.2]; rfl⟩
    | cons => simp only [evalGlobals?, reduceCtorEq] at run
  | @cons e e' es es' he _ ih =>
    show ∃ res fin, evalGlobals? evalConst? source left types (e :: es) =
      some (res, fin, values)
    cases types with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons type types =>
      show ∃ res fin, evalGlobals? evalConst? source left (type :: types) (e :: es) =
        some (res, fin, values)
      obtain ⟨target₁, value, values₁, hv, hg, hvs⟩ := evalGlobals?_cons_inv run
      obtain ⟨source₁, hs₁⟩ := constant_reflect h views refl glen he hv
      obtain ⟨target₁', ht₁', data₁⟩ := constant_transport h views he hs₁
      have ht : target₁' = target₁ :=
        congrArg Prod.fst (Option.some.inj (ht₁'.symm.trans hv))
      have data₁' : Initializers.Data source₁ target₁ := ht ▸ data₁
      have ha : (allocGlobal source₁ type value).2 = (allocGlobal target₁ type value).2 :=
        congrArg List.length data₁'.globals
      have views₁ : Views.Successful r
          { left.module with
            globals := left.module.globals ++ [(allocGlobal source₁ type value).2] }
          { right.module with
            globals := right.module.globals ++ [(allocGlobal target₁ type value).2] } := by
        simpa only [ha] using append_global views glen (allocGlobal source₁ type value).2
      have glen₁ : (right.module.globals ++ [(allocGlobal target₁ type value).2]).length =
          r.globals + (left.module.globals ++ [(allocGlobal source₁ type value).2]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      obtain ⟨res, fin, hres⟩ :=
        ih (left := { left with module := { left.module with
          globals := left.module.globals ++ [(allocGlobal source₁ type value).2] } })
          (right := { right with module := { right.module with
          globals := right.module.globals ++ [(allocGlobal target₁ type value).2] } })
          (data₁'.allocGlobal type value) views₁ ⟨refl.functions, refl.types⟩ glen₁ hg
      exact ⟨res, fin, by rw [hvs]; simp only [evalGlobals?, hs₁, hres]⟩

end Silmaril.Proofs.Wasm.Game.Linking
