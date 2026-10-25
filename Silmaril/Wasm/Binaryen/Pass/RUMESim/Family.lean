module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Basic

@[expose] public section

/-! # Simulation under address maps: the reduction families on foreign code

A family step of foreign code (a frame of a foreign module, foreign references)
reads only the foreign parts of the store, so it is the same step when the
module's functions and globals are replaced (`Store.withFG`), and it keeps the
store and the result foreign.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

/-! ## Flat foreign code -/

/-- A flat administrative instruction whose references are foreign. -/
def flatF (n0 : Nat) : Admin → Prop
  | .plain _ => True
  | .ref r => refF n0 r
  | .trap => True
  | _ => False

@[simp] theorem flatF_plain (n0 : Nat) (i : Instr) : flatF n0 (.plain i) = True := rfl
@[simp] theorem flatF_ref (n0 : Nat) (r : Ref) : flatF n0 (.ref r) = refF n0 r := rfl
@[simp] theorem flatF_trap (n0 : Nat) : flatF n0 .trap = True := rfl

@[simp] theorem flatF_constI32 (n0 : Nat) (b : BitVec 32) : flatF n0 (constI32 b) = True := rfl
@[simp] theorem flatF_store8 (n0 : Nat) (x : MemIdx) : flatF n0 (store8 x) = True := rfl
@[simp] theorem flatF_load8u (n0 : Nat) (x : MemIdx) : flatF n0 (load8u x) = True := rfl

@[simp] theorem flatF_toAdmin (n0 : Nat) (v : Val) : flatF n0 v.toAdmin = valF n0 v := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> rfl

theorem flatF_vals {n0 : Nat} {vs : List Val} :
    (∀ a ∈ vals vs, flatF n0 a) ↔ ∀ v ∈ vs, valF n0 v := by
  simp [vals]

theorem CodeR.of_flat {X : SimCtx} : ∀ {l : List Admin}, (∀ a ∈ l, flatF X.n0 a) →
    CodeR X .same l l
  | [], _ => .nil
  | x :: l, h => by
    have hx := h x (by simp)
    have ht := CodeR.of_flat (X := X) (l := l) (fun a ha => h a (by simp [ha]))
    cases x with
    | plain i => exact .cons .plainS ht
    | ref r => exact .cons (.ref hx) ht
    | trap => exact .cons .trap ht
    | callRefType d => exact absurd hx (by simp [flatF])
    | returnCallRefType d => exact absurd hx (by simp [flatF])
    | label n c b => exact absurd hx (by simp [flatF])
    | handler n c b => exact absurd hx (by simp [flatF])
    | frame n fr b => exact absurd hx (by simp [flatF])

/-! ## Foreign stores -/

theorem StoreF.congr {n0 g0 : Nat} {S S' : Store H} (hS : StoreF n0 g0 S)
    (h1 : S'.tables = S.tables) (h2 : S'.elems = S.elems) (h3 : S'.structs = S.structs)
    (h4 : S'.arrays = S.arrays) (h5 : S'.exns = S.exns) (h6 : S'.globals = S.globals)
    (h7 : S'.funcs = S.funcs) : StoreF n0 g0 S' :=
  ⟨h1 ▸ hS.tables, h2 ▸ hS.elems, h3 ▸ hS.structs, h4 ▸ hS.arrays, h5 ▸ hS.exns,
    h6 ▸ hS.globals, h7 ▸ hS.funcs⟩

theorem mem_set_or {α : Type} {l : List α} {n : Nat} {b x : α} (h : x ∈ l.set n b) :
    x ∈ l ∨ x = b := List.mem_or_eq_of_mem_set h

theorem mem_modify_or {α : Type} {l : List α} {n : Nat} {g : α → α} {x : α}
    (h : x ∈ l.modify n g) : x ∈ l ∨ ∃ u ∈ l, x = g u := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  rw [List.getElem_modify]
  have hi' : i < l.length := by simpa using hi
  split
  · exact .inr ⟨l[i], List.getElem_mem hi', rfl⟩
  · exact .inl (List.getElem_mem hi')

theorem StoreF.setTable {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a : Nat)
    (ti : TableInst) (h : ∀ r ∈ ti.refs, refF n0 r) : StoreF n0 g0 (S.setTable a ti) := by
  refine ⟨?_, hS.elems, hS.structs, hS.arrays, hS.exns, hS.globals, hS.funcs⟩
  intro t ht r hr
  rcases mem_set_or ht with ht | rfl
  · exact hS.tables t ht r hr
  · exact h r hr

theorem StoreF.setElem {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a : Nat) :
    StoreF n0 g0 (S.setElem a []) := by
  refine ⟨hS.tables, ?_, hS.structs, hS.arrays, hS.exns, hS.globals, hS.funcs⟩
  intro e he r hr
  rcases mem_modify_or he with he | ⟨u, -, rfl⟩
  · exact hS.elems e he r hr
  · simp at hr

theorem StoreF.setMem {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a : Nat) (mi : MemInst) :
    StoreF n0 g0 (S.setMem a mi) :=
  ⟨hS.tables, hS.elems, hS.structs, hS.arrays, hS.exns, hS.globals, hS.funcs⟩

theorem StoreF.setData {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a : Nat)
    (b : ByteArray) : StoreF n0 g0 (S.setData a b) :=
  ⟨hS.tables, hS.elems, hS.structs, hS.arrays, hS.exns, hS.globals, hS.funcs⟩

theorem StoreF.setGlobal {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a : Nat) (v : Val)
    (hv : valF n0 v) : StoreF n0 g0 (S.setGlobal a v) := by
  refine ⟨hS.tables, hS.elems, hS.structs, hS.arrays, hS.exns, ?_, hS.funcs⟩
  intro g hg
  rcases mem_modify_or hg with hg | ⟨u, -, rfl⟩
  · exact hS.globals g hg
  · exact hv

theorem StoreF.addExn {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (e : ExnInst)
    (he : ∀ v ∈ e.fields, valF n0 v) : StoreF n0 g0 (S.addExn e) := by
  refine ⟨hS.tables, hS.elems, hS.structs, hS.arrays, ?_, hS.globals, hS.funcs⟩
  intro e' he' v hv
  rcases List.mem_append.1 he' with he' | he'
  · exact hS.exns e' he' v hv
  · simp at he'; subst he'; exact he v hv

theorem StoreF.addStruct {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (si : StructInst)
    (h : ∀ fv ∈ si.fields, fvF n0 fv) : StoreF n0 g0 (S.addStruct si) := by
  refine ⟨hS.tables, hS.elems, ?_, hS.arrays, hS.exns, hS.globals, hS.funcs⟩
  intro s hs fv hfv
  rcases List.mem_append.1 hs with hs | hs
  · exact hS.structs s hs fv hfv
  · simp at hs; subst hs; exact h fv hfv

theorem StoreF.addArray {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (ai : ArrayInst)
    (h : ∀ fv ∈ ai.fields, fvF n0 fv) : StoreF n0 g0 (S.addArray ai) := by
  refine ⟨hS.tables, hS.elems, hS.structs, ?_, hS.exns, hS.globals, hS.funcs⟩
  intro s hs fv hfv
  rcases List.mem_append.1 hs with hs | hs
  · exact hS.arrays s hs fv hfv
  · simp at hs; subst hs; exact h fv hfv

theorem StoreF.setStructField {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a i : Nat)
    (fv : FieldVal) (h : fvF n0 fv) : StoreF n0 g0 (S.setStructField a i fv) := by
  refine ⟨hS.tables, hS.elems, ?_, hS.arrays, hS.exns, hS.globals, hS.funcs⟩
  intro s hs fv' hfv
  rcases mem_modify_or hs with hs | ⟨u, hu, rfl⟩
  · exact hS.structs s hs fv' hfv
  · rcases mem_set_or hfv with hfv | rfl
    · exact hS.structs u hu fv' hfv
    · exact h

theorem StoreF.setArrayField {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) (a i : Nat)
    (fv : FieldVal) (h : fvF n0 fv) : StoreF n0 g0 (S.setArrayField a i fv) := by
  refine ⟨hS.tables, hS.elems, hS.structs, ?_, hS.exns, hS.globals, hS.funcs⟩
  intro s hs fv' hfv
  rcases mem_modify_or hs with hs | ⟨u, hu, rfl⟩
  · exact hS.arrays s hs fv' hfv
  · rcases mem_set_or hfv with hfv | rfl
    · exact hS.arrays u hu fv' hfv
    · exact h

/-! ## Lookups -/

theorem table?_some {S : Store H} {f : Frame} {x : TableIdx} {a : Nat} {ti : TableInst}
    (h : S.table? f x = some (a, ti)) : f.module.tables[x.toNat]? = some a ∧ S.tables[a]? = some ti := by
  unfold Store.table? at h
  cases h1 : f.module.tables[x.toNat]? with
  | none => simp [h1] at h
  | some a' =>
    cases h2 : S.tables[a']? with
    | none => simp [h1, h2] at h
    | some ti' =>
      simp [h1, h2] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h2⟩

theorem elem?_some {S : Store H} {f : Frame} {x : ElemIdx} {a : Nat} {ei : ElemInst}
    (h : S.elem? f x = some (a, ei)) : f.module.elems[x.toNat]? = some a ∧ S.elems[a]? = some ei := by
  unfold Store.elem? at h
  cases h1 : f.module.elems[x.toNat]? with
  | none => simp [h1] at h
  | some a' =>
    cases h2 : S.elems[a']? with
    | none => simp [h1, h2] at h
    | some ei' =>
      simp [h1, h2] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h2⟩

theorem global?_some {S : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : S.global? f x = some (a, g)) :
    f.module.globals[x.toNat]? = some a ∧ S.globals[a]? = some g := by
  unfold Store.global? at h
  cases h1 : f.module.globals[x.toNat]? with
  | none => simp [h1] at h
  | some a' =>
    cases h2 : S.globals[a']? with
    | none => simp [h1, h2] at h
    | some g' =>
      simp [h1, h2] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h2⟩

theorem global?_of {S : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h1 : f.module.globals[x.toNat]? = some a) (h2 : S.globals[a]? = some g) :
    S.global? f x = some (a, g) := by
  unfold Store.global?
  simp [h1, h2]

theorem tableRefs_fgn {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) {f : Frame} {x : TableIdx}
    {a : Nat} {ti : TableInst} (h : S.table? f x = some (a, ti)) : ∀ r ∈ ti.refs, refF n0 r :=
  hS.tables ti (List.mem_of_getElem? (table?_some h).2)

theorem elemRefs_fgn {n0 g0 : Nat} {S : Store H} (hS : StoreF n0 g0 S) {f : Frame} {x : ElemIdx}
    {a : Nat} {ei : ElemInst} (h : S.elem? f x = some (a, ei)) : ∀ r ∈ ei.refs, refF n0 r :=
  hS.elems ei (List.mem_of_getElem? (elem?_some h).2)

/-! ## Values built by the families -/

theorem valF_packField_unpack {n0 : Nat} (sx : Option Signedness) {fv : FieldVal}
    (h : fvF n0 fv) : valF n0 (unpackField sx fv) := by
  rcases fv with v | ⟨p, b⟩
  · exact h
  · rcases sx with _ | ⟨_ | _⟩ <;> trivial

theorem fvF_packField {n0 : Nat} (z : CStorageType) {v : Val} (h : valF n0 v) :
    fvF n0 (packField z v) := by
  unfold packField
  split
  · trivial
  · exact h

theorem valF_readField {n0 : Nat} {z : CStorageType} {bytes : ByteArray} {off : Nat} {v : Val}
    (h : readField? z bytes off = some v) : valF n0 v := by
  unfold readField? at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h; trivial
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h; trivial
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h; trivial
  · cases h

theorem valF_defaultVal {n0 : Nat} {t : CValType} {v : Val} (h : defaultVal? t = some v) :
    valF n0 v := by
  unfold defaultVal? at h
  split at h <;> (try cases h) <;> trivial

theorem valF_mapM_default {n0 : Nat} {α : Type} {g : α → CValType} :
    ∀ {l : List α} {vs : List Val}, l.mapM (fun x => defaultVal? (g x)) = some vs →
      ∀ v ∈ vs, valF n0 v
  | [], vs, h => by simp at h; subst h; simp
  | x :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact valF_defaultVal hv
    · exact valF_mapM_default hvs' w hw

theorem valF_mapM_readField {n0 : Nat} {z : CStorageType} {bytes : ByteArray} {g : Nat → Nat} :
    ∀ {l : List Nat} {vs : List Val}, l.mapM (fun k => readField? z bytes (g k)) = some vs →
      ∀ v ∈ vs, valF n0 v
  | [], vs, h => by simp at h; subst h; simp
  | x :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact valF_readField hv
    · exact valF_mapM_readField hvs' w hw

/-! ## Transport across a change of the module's functions and globals -/

theorem tableStep_withFG {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : TableStep P ⟨S, f, l⟩ c') (fs : List (FuncInst H)) (gs : List GlobalInst) :
    TableStep P ⟨S.withFG fs gs, f, l⟩ ⟨c'.store.withFG fs gs, c'.frame, c'.code⟩ := by
  cases h <;> constructor <;> assumption

theorem memoryStep_withFG {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : MemoryStep P ⟨S, f, l⟩ c') (fs : List (FuncInst H)) (gs : List GlobalInst) :
    MemoryStep P ⟨S.withFG fs gs, f, l⟩ ⟨c'.store.withFG fs gs, c'.frame, c'.code⟩ := by
  cases h <;> constructor <;> assumption

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem aggregateStep_withFG {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : AggregateStep ⟨S, f, l⟩ c') (fs : List (FuncInst H)) (gs : List GlobalInst) :
    AggregateStep ⟨S.withFG fs gs, f, l⟩ ⟨c'.store.withFG fs gs, c'.frame, c'.code⟩ := by
  cases h <;> first
    | (apply AggregateStep.structNew <;> assumption)
    | (apply AggregateStep.structNewDefault <;> assumption)
    | (apply AggregateStep.structGetNull <;> assumption)
    | (apply AggregateStep.structGetStruct <;> assumption)
    | (apply AggregateStep.structSetNull <;> assumption)
    | (apply AggregateStep.structSetStruct <;> assumption)
    | (apply AggregateStep.arrayNew <;> assumption)
    | (apply AggregateStep.arrayNewDefault <;> assumption)
    | (apply AggregateStep.arrayNewFixed <;> assumption)
    | (apply AggregateStep.arrayNewElemOob <;> assumption)
    | (apply AggregateStep.arrayNewElemAlloc <;> assumption)
    | (apply AggregateStep.arrayNewDataOob <;> assumption)
    | (apply AggregateStep.arrayNewDataNum <;> assumption)
    | (apply AggregateStep.arrayGetNull <;> assumption)
    | (apply AggregateStep.arrayGetOob <;> assumption)
    | (apply AggregateStep.arrayGetArray <;> assumption)
    | (apply AggregateStep.arraySetNull <;> assumption)
    | (apply AggregateStep.arraySetOob <;> assumption)
    | (apply AggregateStep.arraySetArray <;> assumption)
    | (apply AggregateStep.arrayLenNull <;> assumption)
    | (apply AggregateStep.arrayLenArray <;> assumption)
    | (apply AggregateStep.arrayFillNull <;> assumption)
    | (apply AggregateStep.arrayFillOob <;> assumption)
    | (apply AggregateStep.arrayFillZero <;> assumption)
    | (apply AggregateStep.arrayFillSucc <;> assumption)
    | (apply AggregateStep.arrayCopyNull₁ <;> assumption)
    | (apply AggregateStep.arrayCopyNull₂ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₁ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
    | (apply AggregateStep.arrayCopyZero <;> assumption)
    | (apply AggregateStep.arrayCopyLe <;> assumption)
    | (apply AggregateStep.arrayCopyGt <;> assumption)
    | (apply AggregateStep.arrayInitElemNull <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitElemZero <;> assumption)
    | (apply AggregateStep.arrayInitElemSucc <;> assumption)
    | (apply AggregateStep.arrayInitDataNull <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitDataZero <;> assumption)
    | (apply AggregateStep.arrayInitDataNum <;> assumption)

theorem refStep_withFG {n0 : Nat} {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : RefStep ⟨S, f, l⟩ c') (fs : List (FuncInst H)) (gs : List GlobalInst)
    (hl : ∀ a ∈ l, flatF n0 a)
    (hok : ∀ r t, refF n0 r → (RefOk S r t ↔ RefOk (S.withFG fs gs) r t)) :
    RefStep ⟨S.withFG fs gs, f, l⟩ ⟨c'.store.withFG fs gs, c'.frame, c'.code⟩ := by
  cases h with
  | testTrue h => exact .testTrue ((hok _ _ (hl (.ref _) (by simp))).1 h)
  | testFalse h => exact .testFalse (fun h' => h ((hok _ _ (hl (.ref _) (by simp))).2 h'))
  | castSucceed h => exact .castSucceed ((hok _ _ (hl (.ref _) (by simp))).1 h)
  | castFail h => exact .castFail (fun h' => h ((hok _ _ (hl (.ref _) (by simp))).2 h'))
  | eqNull => exact .eqNull
  | eqTrue h => exact .eqTrue h
  | _ => constructor <;> assumption

theorem tableStep_fg {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : TableStep P ⟨S, f, l⟩ c') : c'.store.funcs = S.funcs ∧ c'.store.globals = S.globals ∧ c'.frame = f := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem memoryStep_fg {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : MemoryStep P ⟨S, f, l⟩ c') : c'.store.funcs = S.funcs ∧ c'.store.globals = S.globals ∧ c'.frame = f := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem aggregateStep_fg {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : AggregateStep ⟨S, f, l⟩ c') : c'.store.funcs = S.funcs ∧ c'.store.globals = S.globals ∧ c'.frame = f := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem refStep_fg {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : RefStep ⟨S, f, l⟩ c') : c'.store = S ∧ c'.frame = f := by
  cases h <;> exact ⟨rfl, rfl⟩

/-! ## Reference typing of foreign references -/

theorem refOk_transfer {n0 : Nat} {S T : Store H} (hf : ∀ a < n0, S.funcs[a]? = T.funcs[a]?)
    (hs : S.structs = T.structs) (ha : S.arrays = T.arrays) (he : S.exns = T.exns)
    {r : Ref} {t : CRefType} (h : RefOk S r t) (hr : refF n0 r) : RefOk T r t := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct (hs ▸ h)
  | array h => exact .array (ha ▸ h)
  | func h => exact .func ((hf _ hr) ▸ h)
  | exn h => exact .exn (he ▸ h)
  | host a => exact .host a
  | extern _ hn ih => exact .extern (ih hr) hn
  | sub _ hok hs ih => exact .sub (ih hr) hok hs

theorem refOk_withFG_iff {n0 : Nat} {S : Store H} {fs : List (FuncInst H)} {gs : List GlobalInst}
    (hf : ∀ a < n0, S.funcs[a]? = fs[a]?) {r : Ref} {t : CRefType} (hr : refF n0 r) :
    RefOk S r t ↔ RefOk (S.withFG fs gs) r t :=
  ⟨fun h => refOk_transfer (T := S.withFG fs gs) hf rfl rfl rfl h hr,
   fun h => refOk_transfer (S := S.withFG fs gs) (T := S) (fun a ha => (hf a ha).symm) rfl rfl rfl
     h hr⟩

theorem catchMatches_withFG {S : Store H} {fs : List (FuncInst H)} {gs : List GlobalInst}
    {f : Frame} {a : Nat} {c : Catch} :
    CatchMatches (S.withFG fs gs) f a c ↔ CatchMatches S f a c := by
  cases c <;> exact Iff.rfl

/-! ## Foreign results -/

theorem grow?_refs {ti ti' : TableInst} {n : Nat} {r : Ref} (h : ti.grow? n r = some ti') :
    ti'.refs = ti.refs ++ List.replicate n r := by
  unfold TableInst.grow? at h
  dsimp only at h
  by_cases hc : ti.refs.length + n ≤ 2 ^ ti.type.address.width - 1 ∧
      (∀ j, ti.type.limits.max = some j → ti.refs.length + n ≤ j.val)
  · rw [ite_eq_left hc] at h
    cases h; rfl
  · rw [ite_eq_right hc] at h
    cases h

theorem tableStep_fgn {n0 g0 : Nat} {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : TableStep P ⟨S, f, l⟩ c') (hS : StoreF n0 g0 S) (hl : ∀ a ∈ l, flatF n0 a) :
    StoreF n0 g0 c'.store ∧ ∀ a ∈ c'.code, flatF n0 a := by
  cases h with
  | getVal ht h =>
    refine ⟨hS, ?_⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact tableRefs_fgn hS ht _ (List.mem_of_getElem? h)
  | setVal ht h =>
    refine ⟨hS.setTable _ _ ?_, by simp⟩
    intro r hr
    rcases mem_set_or hr with hr | rfl
    · exact tableRefs_fgn hS ht r hr
    · exact hl (.ref _) (by simp)
  | growSucceed ht hg hp =>
    refine ⟨hS.setTable _ _ ?_, by simp⟩
    intro r' hr'
    rw [grow?_refs hg] at hr'
    rcases List.mem_append.1 hr' with hr' | hr'
    · exact tableRefs_fgn hS ht r' hr'
    · rw [List.eq_of_mem_replicate hr']
      exact hl (.ref _) (by simp)
  | initSucc _ he _ _ hr =>
    have hr' : refF n0 _ := elemRefs_fgn hS he _ (List.mem_of_getElem? hr)
    exact ⟨hS, by simp_all⟩
  | elemDrop he => exact ⟨hS.setElem _, by simp⟩
  | _ => exact ⟨hS, by simp_all⟩

theorem memoryStep_fgn {n0 g0 : Nat} {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : MemoryStep P ⟨S, f, l⟩ c') (hS : StoreF n0 g0 S) (hl : ∀ a ∈ l, flatF n0 a) :
    StoreF n0 g0 c'.store ∧ ∀ a ∈ c'.code, flatF n0 a := by
  cases h <;> refine ⟨by first | exact hS | exact hS.setMem _ _ | exact hS.setData _ _, ?_⟩ <;>
    simp_all

theorem refStep_fgn {n0 g0 : Nat} {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : RefStep ⟨S, f, l⟩ c') (hS : StoreF n0 g0 S) (hm : modF n0 g0 f.module)
    (hl : ∀ a ∈ l, flatF n0 a) : StoreF n0 g0 c'.store ∧ ∀ a ∈ c'.code, flatF n0 a := by
  cases h with
  | refFunc h =>
    refine ⟨hS, ?_⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact hm.1 _ (List.mem_of_getElem? h)
  | _ => exact ⟨hS, by simp_all⟩

theorem aggregateStep_fgn {n0 g0 : Nat} {S : Store H} {f : Frame} {l : List Admin} {c' : Config H}
    (h : AggregateStep ⟨S, f, l⟩ c') (hS : StoreF n0 g0 S) (hl : ∀ a ∈ l, flatF n0 a) :
    StoreF n0 g0 c'.store ∧ ∀ a ∈ c'.code, flatF n0 a := by
  cases h with
  | @structNew _ _ _ _ _ vs hd he hn hp =>
    have hvs : ∀ v ∈ vs, valF n0 v := fun v hv => by
      simpa using hl v.toAdmin (List.mem_append_left _ (List.mem_map_of_mem hv))
    refine ⟨hS.addStruct _ ?_, by simp⟩
    intro fv hfv
    simp only [List.mem_map, Prod.exists] at hfv
    obtain ⟨ft, v, hm, rfl⟩ := hfv
    exact fvF_packField _ (hvs v (List.of_mem_zip hm).2)
  | structNewDefault hd he hdef =>
    refine ⟨hS, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [vals, List.mem_map] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      simpa using valF_mapM_default hdef v hv
    · simp at ha; subst ha; trivial
  | structGetStruct hs hf hd he hi hu =>
    refine ⟨hS, ?_⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    simpa using valF_packField_unpack _
      (hS.structs _ (List.mem_of_getElem? hs) _ (List.mem_of_getElem? hf))
  | structSetStruct hd he hi hs hf hp =>
    refine ⟨hS.setStructField _ _ _ (fvF_packField _ ?_), by simp⟩
    simpa using hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | arrayNew v n =>
    have hv : valF n0 v := by simpa using hl v.toAdmin List.mem_cons_self
    refine ⟨hS, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [vals, List.mem_map] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      rw [List.eq_of_mem_replicate hw]
      simpa using hv
    · simp at ha; subst ha; trivial
  | arrayNewDefault hd he hv =>
    refine ⟨hS, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [vals, List.mem_map] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      rw [List.eq_of_mem_replicate hw]
      simpa using valF_defaultVal hv
    · simp at ha; subst ha; trivial
  | @arrayNewFixed _ _ _ _ _ _ vs hd he hn hp =>
    have hvs : ∀ v ∈ vs, valF n0 v := fun v hv => by
      simpa using hl v.toAdmin (List.mem_append_left _ (List.mem_map_of_mem hv))
    refine ⟨hS.addArray _ ?_, by simp⟩
    intro fv hfv
    simp only [List.mem_map] at hfv
    obtain ⟨v, hv, rfl⟩ := hfv
    exact fvF_packField _ (hvs v hv)
  | arrayNewElemAlloc he h =>
    refine ⟨hS, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_map] at ha
      obtain ⟨r, hr, rfl⟩ := ha
      exact elemRefs_fgn hS he r (List.mem_of_mem_drop (List.mem_of_mem_take hr))
    · simp at ha; subst ha; trivial
  | arrayNewDataNum hd he hdat hz hb hvs =>
    refine ⟨hS, ?_⟩
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [vals, List.mem_map] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      simpa using valF_mapM_readField hvs w hw
    · simp at ha; subst ha; trivial
  | arrayGetArray ha h hd he hu =>
    refine ⟨hS, ?_⟩
    intro a' ha'
    simp only [List.mem_singleton] at ha'
    subst ha'
    simpa using valF_packField_unpack _
      (hS.arrays _ (List.mem_of_getElem? ha) _ (List.mem_of_getElem? h))
  | arraySetArray ha h hd he hp =>
    refine ⟨hS.setArrayField _ _ _ (fvF_packField _ ?_), by simp⟩
    simpa using hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | arrayInitElemSucc _ he _ _ hr =>
    have hr' : refF n0 _ := elemRefs_fgn hS he _ (List.mem_of_getElem? hr)
    exact ⟨hS, by simp_all⟩
  | arrayInitDataNum _ _ _ _ _ _ hv =>
    have hv' : valF n0 _ := valF_readField hv
    exact ⟨hS, by simp_all⟩
  | _ => exact ⟨hS, by simp_all⟩

end Silmaril.Wasm.Binaryen.RUMESim
