module

public import Silmaril.Wasm.Lime1.Execution.Instantiation
public import Silmaril.Raw.Wasm.Versions.Lime1.Execution.FromV1
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.V1.Execution.Instantiation
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Thms

/-!
# Preservation of module preparation and instantiation

Successful WebAssembly 1.0 initializers remain successful in Lime1. The converse
is deliberately absent: extended constant expressions accept new arithmetic.
The embeddings retain runtime values, addresses, limit matching and segment
contents while translating stored function code.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

private theorem mapM_preserves {A B C D : Type} (f : A → Option B) (g : C → Option D)
    (input : A → C) (output : B → D)
    (step : ∀ a b, f a = some b → g (input a) = some (output b))
    {xs : List A} {ys : List B} (h : xs.mapM f = some ys) :
    (xs.map input).mapM g = some (ys.map output) := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    simp only [List.map_cons, List.mapM_cons, step x y hy, ih hys,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]

@[simp] theorem constInstr?_toLime {H : Type} (s : Store H) (module : ModuleInst) (i : Instr) :
    Lime1.Execution.constInstr? (s.mapCode Func.toLime) module i.toLime =
      constInstr? s module i := by
  cases i <;> rfl

theorem constStep?_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {i : Instr} {v : Value} (h : constInstr? s module i = some v) (stack : List Value) :
    Lime1.Execution.constStep? (s.mapCode Func.toLime) module i.toLime stack = some (v :: stack) := by
  cases i <;> simp only [constInstr?] at h
  all_goals try contradiction
  case intConst t bits => cases h; rfl
  case floatConst t bits => cases h; rfl
  case globalGet i =>
    change constInstr? s module (.globalGet i) = some v at h
    change (constInstr? s module (.globalGet i)).map _ = _
    rw [h]
    rfl

private theorem constFold_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {es : Expr} {vs : List Value} (h : es.mapM (constInstr? s module) = some vs)
    (stack : List Value) :
    (Expr.toLime es).foldlM
      (fun stack i => Lime1.Execution.constStep? (s.mapCode Func.toLime) module i stack) stack =
      some (vs.reverse ++ stack) := by
  induction es generalizing vs stack with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    cases h
    rfl
  | cons i es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    simp only [Expr.toLime, List.foldlM_cons, constStep?_toLime s module hv,
      Option.bind_eq_bind, Option.bind_some, ih hvs, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append]

theorem constExpr?_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {es : Expr} {v : Value} (h : constExpr? s module es = some v) :
    Lime1.Execution.constExpr? (s.mapCode Func.toLime) module (Expr.toLime es) = some v := by
  simp only [constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  unfold Lime1.Execution.constExpr?
  rw [constFold_toLime s module hvs []]
  split at hv <;> simp_all

theorem offset?_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {es : Expr} {n : Nat} (h : offset? s module es = some n) :
    Lime1.Execution.offset? (s.mapCode Func.toLime) module (Expr.toLime es) = some n := by
  simp only [offset?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, hn⟩ := h
  unfold Lime1.Execution.offset?
  rw [constExpr?_toLime s module hv]
  exact hn

theorem ExternMatches.toLime {H : Type} {s : Store H} {v : ExternVal} {t : ExternType}
    (h : ExternMatches s v t) : Lime1.Execution.ExternMatches (s.mapCode Func.toLime) v t := by
  cases h with
  | func a fn ft found typed =>
    apply Lime1.Execution.ExternMatches.func a (fn.mapCode Func.toLime) ft
    · simp [found]
    · simpa using typed
  | table a table tt found limits => exact .table a table tt found limits
  | memory a memory mt found limits => exact .memory a memory mt found limits
  | global a global gt found type mutability => exact .global a global gt found type mutability

theorem ImportsMatch.toLime {H : Type} {s : Store H} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) :
    Lime1.Execution.ImportsMatch (s.mapCode Func.toLime) m.toLime imports := by
  apply List.Forall₂.imp _ h
  rintro i e ⟨t, ht, he⟩
  exact ⟨t, ht, he.toLime⟩


def Prepared.toLime {H : Type} (p : Prepared H) : Lime1.Execution.Prepared H :=
  ⟨p.store.mapCode Func.toLime, p.module, codeToLime p.start⟩

@[simp] theorem importedInstance_toLime (imports : List ExternVal) :
    Lime1.Execution.importedInstance imports = importedInstance imports := rfl

@[simp] theorem addresses_toLime (kind : AddrKind) (start count : Nat) :
    Lime1.Execution.addresses kind start count = addresses kind start count := rfl

@[simp] theorem exportValue?_toLime (module : ModuleInst) (i : ExternIdx) :
    Lime1.Execution.exportValue? module i = exportValue? module i := rfl

private theorem allocateFuncs_toLime {H : Type} (types : List FuncType) (module : ModuleInst)
    {fs : List Func} {out : List (FuncInst Func H)}
    (h : fs.mapM (fun f => types[f.type.toNat]?.bind fun ft => some (.wasm ft module f)) = some out) :
    (fs.map Func.toLime).mapM
      (fun f => types[f.type.toNat]?.bind fun ft => some (.wasm ft module f)) =
      some (out.map (FuncInst.mapCode Func.toLime)) := by
  apply mapM_preserves _
    (fun f : Lime1.Func => types[f.type.toNat]?.bind fun ft => some (.wasm ft module f))
    Func.toLime (FuncInst.mapCode Func.toLime) _ h
  intro f out found
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at found
  obtain ⟨ft, hft, rfl⟩ := found
  simp only [Func.toLime, hft, Option.bind_some, FuncInst.mapCode]

theorem allocate?_toLime {H : Type} (s : Store H) (m : Module) (imports : List ExternVal)
    {s' : Store H} {module : ModuleInst} (h : allocate? s m imports = some (s', module)) :
    Lime1.Execution.allocate? (s.mapCode Func.toLime) m.toLime imports =
      some (s'.mapCode Func.toLime, module) := by
  simp only [allocate?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨initializers, hi, exports, he, funcs, hf, h⟩ := h
  cases h
  have hi' := mapM_preserves _
    (fun g : Lime1.Global => Lime1.Execution.constExpr? (s.mapCode Func.toLime)
      { globals := (importedInstance imports).globals } g.init) Global.toLime id
    (fun g v hv => constExpr?_toLime s _ hv) hi
  simp only [List.map_id] at hi'
  unfold Lime1.Execution.allocate?
  simp only [Module.toLime, importedInstance_toLime, addresses_toLime,
    Store.mapCode, List.length_map, exportValue?_toLime] at hi' ⊢
  rw [hi']
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [he]
  simp only [Option.bind_some]
  rw [allocateFuncs_toLime m.types _ hf]
  simp [List.map_append, List.zipWith_map_left, Global.toLime]


def ElemWrite.toLime (w : ElemWrite) : Lime1.Execution.ElemWrite := ⟨w.address, w.offset, w.values⟩
def DataWrite.toLime (w : DataWrite) : Lime1.Execution.DataWrite := ⟨w.address, w.offset, w.bytes⟩

theorem resolveElem?_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {e : Elem} {w : ElemWrite} (h : resolveElem? s module e = some w) :
    Lime1.Execution.resolveElem? (s.mapCode Func.toLime) module e.toLime = some w.toLime := by
  simp only [resolveElem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨offset, ho, a, ha, table, ht, refs, hr, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst w
    simp only [Lime1.Execution.resolveElem?, Elem.toLime]
    rw [offset?_toLime s module ho]
    simp [Store.mapCode, ha, ht, hr, ElemWrite.toLime, ‹offset + refs.length ≤ table.refs.length›]
  · contradiction

theorem resolveData?_toLime {H : Type} (s : Store H) (module : ModuleInst)
    {d : Data} {w : DataWrite} (h : resolveData? s module d = some w) :
    Lime1.Execution.resolveData? (s.mapCode Func.toLime) module d.toLime = some w.toLime := by
  simp only [resolveData?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨offset, ho, a, ha, memory, hm, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst w
    simp only [Lime1.Execution.resolveData?, Data.toLime]
    rw [offset?_toLime s module ho]
    simp [Store.mapCode, ha, hm, DataWrite.toLime,
      ‹offset + d.bytes.size ≤ memory.data.size›]
  · contradiction

@[simp] theorem applyElem_toLime {H : Type} (s : Store H) (w : ElemWrite) :
    Lime1.Execution.applyElem (s.mapCode Func.toLime) w.toLime =
      (applyElem s w).mapCode Func.toLime := rfl

@[simp] theorem applyData_toLime {H : Type} (s : Store H) (w : DataWrite) :
    Lime1.Execution.applyData (s.mapCode Func.toLime) w.toLime =
      (applyData s w).mapCode Func.toLime := rfl

@[simp] theorem applyElems_toLime {H : Type} (s : Store H) (ws : List ElemWrite) :
    (ws.map ElemWrite.toLime).foldl Lime1.Execution.applyElem (s.mapCode Func.toLime) =
      (ws.foldl applyElem s).mapCode Func.toLime := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.foldl_cons, applyElem_toLime, ih]

@[simp] theorem applyDatas_toLime {H : Type} (s : Store H) (ws : List DataWrite) :
    (ws.map DataWrite.toLime).foldl Lime1.Execution.applyData (s.mapCode Func.toLime) =
      (ws.foldl applyData s).mapCode Func.toLime := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.foldl_cons, applyData_toLime, ih]

theorem prepare?_toLime {H : Type} (s : Store H) (m : Module) (imports : List ExternVal)
    {p : Prepared H} (h : prepare? s m imports = some p) :
    Lime1.Execution.prepare? (s.mapCode Func.toLime) m.toLime imports = some p.toLime := by
  simp only [prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨⟨allocated, module⟩, ha, elems, he, data, hd, h⟩ := h
  have he' := mapM_preserves _ (Lime1.Execution.resolveElem? (allocated.mapCode Func.toLime) module)
    Elem.toLime ElemWrite.toLime (fun _ _ h => resolveElem?_toLime allocated module h) he
  have hd' := mapM_preserves _ (Lime1.Execution.resolveData? (allocated.mapCode Func.toLime) module)
    Data.toLime DataWrite.toLime (fun _ _ h => resolveData?_toLime allocated module h) hd
  unfold Lime1.Execution.prepare?
  rw [allocate?_toLime s m imports ha]
  simp only [Option.bind_eq_bind, Option.bind_some, Module.toLime, he', hd',
    applyElems_toLime, applyDatas_toLime]
  cases hstart : m.start with
  | none =>
    simp only [hstart, Option.bind_some, Option.some.injEq] at h
    subst p
    rfl
  | some i =>
    simp only [hstart, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨start, ⟨a, found, rfl⟩, h⟩ := h
    subst p
    simp only [found, Option.map_some, Option.bind_some, Option.pure_def]
    rfl

/-- Preparation, initialized contents and the complete finite start result are preserved. -/
theorem Instantiation.toLime {H : Type} {source : HostSemantics H}
    {target : Lime1.Execution.HostSemantics H}
    (hosts : Runtime.HostSemantics.Compatible Func.toLime source target)
    {before after : Store H} {m : Module} {imports : List ExternVal}
    {module : ModuleInst} {outcome : Result}
    (h : Instantiation source before m imports after module outcome) :
    Lime1.Execution.Instantiation target (before.mapCode Func.toLime) m.toLime imports
      (after.mapCode Func.toLime) module outcome := by
  refine ⟨h.valid.toLime, h.importsMatch.toLime, ?_⟩
  obtain ⟨p, hp, hm, run⟩ := h.prepared
  refine ⟨p.toLime, prepare?_toLime before m imports hp, hm, ?_⟩
  simpa only [Config.toLime, Prepared.toLime, map_result] using run.toLime hosts

/-- A divergent start stays divergent; no termination or host determinism is assumed. -/
theorem instantiationDiverges_toLime {H : Type} {source : HostSemantics H}
    {target : Lime1.Execution.HostSemantics H}
    (hosts : Runtime.HostSemantics.Compatible Func.toLime source target)
    {before : Store H} {m : Module} {imports : List ExternVal}
    (h : InstantiationDiverges source before m imports) :
    Lime1.Execution.InstantiationDiverges target (before.mapCode Func.toLime) m.toLime imports := by
  obtain ⟨valid, matched, p, hp, diverges⟩ := h
  exact ⟨valid.toLime, matched.toLime, p.toLime, prepare?_toLime before m imports hp,
    diverges.toLime hosts⟩

end Silmaril.Wasm.V1.Execution
