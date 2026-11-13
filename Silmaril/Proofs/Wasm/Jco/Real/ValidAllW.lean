module

public import Silmaril.Wasm.Jco.Real.Typed.Defs
public import Silmaril.Proofs.Wasm.Jco.Real.ValidAll

/-!
# Validation of `adaptorLimeW md` (multi-value style, typed locals) for every world: proofs

`adaptorLimeW_limeValid`: the adaptor of the multi-value style with typed locals is a valid
Lime1 module under the hypotheses of `adaptorLime_limeValid`. A wide result (a record of at
least two scalars) is returned by the callee as its flat fields, popped into locals of the
fields' flat types (`setsRev`), stored into a block from the allocator (`storeFields`: packed
integer stores for narrow fields, `i64.store` for 64-bit integers, float stores for floats),
and the block pointer is returned. This is the general form of the litmus check
`adaptorLimeW_exWide_valid`, and settles the `i64` wide-result encoding issue: with typed locals
every `local.set` and every store is well typed.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real.ValidAll

open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (ValTy)

/-- The flat type of a scalar field. -/
abbrev hd (t : ValTy) : Lime1.ValType := t.flat.headD I32

section Steps

variable {C : Context} {is : List Lime1.Instr} {a st c : Lime1.ResultType}

theorem t_instr {i : Lime1.Instr} {x : Lime1.ResultType} (hi : InstrType C i x [])
    (ha : a = st ++ x) (k : ExprType C is st c) : ExprType C (i :: is) a c := by
  have h := InstrType.frame st hi
  rw [List.append_nil] at h
  exact ha ▸ .cons h k

/-- **The store of a scalar field** has type `[i32, t] → []`. -/
theorem t_store (fi : String → Nat) (hm : C.memories ≠ []) {t : ValTy} {sz : Nat}
    (hsz : scalarSize t = some sz) (off : Nat) (ha : a = st ++ [I32, hd t])
    (k : ExprType C is st c) :
    ExprType C (XInstr.toLime fi (.store (hd t) sz off) :: is) a c := by
  cases t <;> simp only [scalarSize, Option.some.injEq, reduceCtorEq] at hsz <;> subst hsz
  all_goals simp (config := { decide := true }) only [hd, ValTy.flat, List.headD,
    XInstr.toLime, intStoreL, packOf, alignExp, FloatType.width, ↓reduceIte] at ha ⊢
  all_goals first
    | refine t_instr (InstrType.intStore _ _ _ hm ?_) ha k
    | refine t_instr (InstrType.floatStore _ _ hm ?_) ha k
  all_goals simp [IntAccess, Aligned, memArg, V1.PackSize.width, IntType.width, FloatType.width]

/-- `local.set (base + k - 1) … local.set base` pops the top `k` values of `G` into locals of
their types. -/
theorem t_setsRev (fi : String → Nat) (base : Nat) (G : List Lime1.ValType) (k : Nat)
    (hk : k ≤ G.length)
    (hL : ∀ j (hj : j < k), C.locals[(mkIdx (base + j) : LocalIdx).toNat]? = some G[j])
    (st : Lime1.ResultType) (kont : ExprType C is st c) :
    ExprType C ((setsRev base k).map (XInstr.toLime fi) ++ is) (st ++ G.take k) c := by
  induction k generalizing is with
  | zero => simpa [setsRev] using kont
  | succ k ih =>
    have hlt : k < G.length := by omega
    have hrest : ExprType C ((setsRev base k).map (XInstr.toLime fi) ++ is) (st ++ G.take k) c :=
      ih (by omega) (fun j hj => hL j (by omega)) kont
    have hstack : st ++ G.take (k + 1) = (st ++ G.take k) ++ [G[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.append_assoc]
    simp only [setsRev, List.map_cons, List.cons_append]
    exact t_set (hL k (by omega)) hstack hrest

/-- **The stores of the fields** `j, j + 1, …` (each `[] → []`). -/
theorem t_storeFields (fi : String → Nat) (hm : C.memories ≠ []) (pl base : Nat)
    (hp : C.locals[(mkIdx pl : LocalIdx).toNat]? = some I32) :
    ∀ (ts : List ValTy) (ns : List Nat) (j : Nat) (os : List Nat),
      List.Forall₂ (fun t n => scalarSize t = some n) ts ns →
      (∀ m (hm : m < ts.length),
        C.locals[(mkIdx (base + (j + m)) : LocalIdx).toNat]? = some (hd ts[m])) →
      ExprType C is st c →
      ExprType C ((storeFields pl base j ts os ns).map (XInstr.toLime fi) ++ is) st c
  | [], _, _, _, _, _, kont => by simpa [storeFields] using kont
  | _ :: _, [], _, _, h, _, _ => by cases h
  | _ :: _, _ :: _, _, [], _, _, kont => by simpa [storeFields] using kont
  | t :: ts, n :: ns, j, o :: os, h, hL, kont => by
    obtain ⟨hsz, hrest⟩ := List.forall₂_cons.1 h
    have htail := t_storeFields fi hm pl base hp ts ns (j + 1) os hrest
      (fun m hm' => by
        have h1 := hL (m + 1) (by simp; omega)
        rwa [show j + (m + 1) = j + 1 + m by omega] at h1)
      kont
    have h0 : C.locals[(mkIdx (base + j) : LocalIdx).toNat]? = some (hd t) := by
      have h1 := hL 0 (by simp)
      rwa [Nat.add_zero] at h1
    have hst : ExprType C (XInstr.toLime fi (.store (hd t) n o) ::
        ((storeFields pl base (j + 1) ts os ns).map (XInstr.toLime fi) ++ is)) (st ++ [I32, hd t]) c :=
      t_store fi hm hsz o rfl htail
    simp only [storeFields, storeField, List.map_append, List.map_cons,
      List.append_assoc, List.cons_append, List.nil_append]
    refine t_get hp (t_get h0 ?_)
    cases hb : isBoolTy t
    · simpa using hst
    · cases t <;> simp [isBoolTy] at hb
      exact t_eqz (st := st ++ [I32]) (by simp [hd, ValTy.flat]) <|
        t_eqz (st := st ++ [I32]) rfl <| by simpa [hd, ValTy.flat] using hst

end Steps

/-! ## The multi-value shim -/

/-- The flattening of a record of scalars: one flat type per field. -/
theorem flatList_scalars {ts : List ValTy} {ns : List Nat}
    (h : List.Forall₂ (fun t n => scalarSize t = some n) ts ns) : ValTy.flatList ts = ts.map hd := by
  induction h with
  | nil => rfl
  | @cons t n ts ns ht _ ih =>
    have hf : t.flat = [hd t] := by cases t <;> simp [scalarSize] at ht <;> rfl
    rw [ValTy.flatList, hf, ih]
    rfl

theorem gets_toLimeX (fi : String → Nat) (n : Nat) :
    (gets n).map (XInstr.toLime fi ∘ XInstr.base) =
      (List.range n).map fun j => Lime1.Instr.localGet (mkIdx j) :=
  gets_toLime fi n

/-- The locals of the multi-value shim: parameters, the block pointer, the fields. -/
theorem mv_local {fp G : List Lime1.ValType} {j : Nat} (hj : j < G.length)
    (hb : fp.length + 1 + j < 2 ^ 32) :
    (fp ++ I32 :: G)[(mkIdx (fp.length + 1 + j) : LocalIdx).toNat]? = some G[j] := by
  rw [mkIdx_toNat, Nat.mod_eq_of_lt hb, List.getElem?_append_right (by omega),
    show fp.length + 1 + j - fp.length = j + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_eq_getElem hj]

theorem mv_ptr (fp G : List Lime1.ValType) (hb : fp.length < 2 ^ 32) :
    (fp ++ I32 :: G)[(mkIdx fp.length : LocalIdx).toNat]? = some I32 := by
  rw [mkIdx_toNat, Nat.mod_eq_of_lt hb]
  simp

/-- **The multi-value shim with typed locals is well typed.** -/
theorem mvShimT_valid (C : Context) (md : Meta) (s : Sig) (ts : List ValTy) (ns : List Nat)
    (ty : Nat) (hsc : List.Forall₂ (fun t n => scalarSize t = some n) ts ns)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some ⟨flatParams s.params, [I32]⟩)
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType)
    (hS : C.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? =
      some ⟨flatParams s.params, ValTy.flatList ts⟩)
    (hm : C.memories ≠ []) (hb : (flatParams s.params).length + ts.length + 2 < 2 ^ 32) :
    FuncValid C ((mvShimT md s ts ns).toLime (funcIdxOf md) ty) := by
  have hG : ValTy.flatList ts = (ts.map hd).take ts.length := by
    rw [flatList_scalars hsc, List.take_of_length_le (by simp)]
  rw [hG] at hS
  refine ⟨_, hT, trivial, ?_⟩
  let C' := functionContext C ⟨flatParams s.params, [I32]⟩ (I32 :: ts.map hd)
  have hL : ∀ j (hj : j < (ts.map hd).length),
      C'.locals[(mkIdx ((flatParams s.params).length + 1 + j) : LocalIdx).toNat]? =
        some (ts.map hd)[j] :=
    fun j hj => mv_local (fp := flatParams s.params) hj (by simp at hj; omega)
  have hP : C'.locals[(mkIdx (flatParams s.params).length : LocalIdx).toNat]? = some I32 :=
    mv_ptr (flatParams s.params) (ts.map hd) (by omega)
  have hA' : C'.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType := hA
  have hS' : C'.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? =
      some ⟨flatParams s.params, (ts.map hd).take ts.length⟩ := hS
  have hm' : C'.memories ≠ [] := hm
  have hlen : (flatParams s.params).length ≤ C'.locals.length := by simp [C', functionContext]
  have htake : [] ++ C'.locals.take (flatParams s.params).length = [] ++ flatParams s.params := by
    simp [C', functionContext]
  simp only [XFnT.toLime, mvShimT, mvShim, toLimeL_eq, List.map_append, List.map_map,
    List.append_assoc, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    flatList_scalars hsc, gets_toLimeX]
  exact t_gets (C := C') _ hlen (by omega) [] <| t_call (st := []) hS' htake <|
    t_setsRev _ _ (ts.map hd) ts.length (by simp) (fun j hj => hL j (by simpa using hj)) [] <|
    t_const .i32 _ <| t_const .i32 _ <| t_call (st := []) hA' rfl <| t_set (st := []) hP rfl <|
    t_storeFields _ hm' _ ((flatParams s.params).length + 1) hP ts ns 0 _ hsc
      (fun m hm' => by
        have h1 := hL m (by simpa using hm')
        rw [List.getElem_map] at h1
        simpa using h1) <|
    t_get hP <| t_end rfl

/-- The fields of a wide result are scalars. -/
theorem wideOf_scalars {r : Option Silmaril.Wasm.Jco.PTy} {ts : List ValTy} {ns : List Nat}
    (h : wideOf r = some (ts, ns)) : List.Forall₂ (fun t n => scalarSize t = some n) ts ns := by
  unfold wideOf at h
  split at h
  · split at h
    · obtain ⟨ns', hns, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact List.mapM_eq_some_iff_forall₂.1 hns
    · cases h
  · cases h

/-- `cabi_realloc` of the multi-value style (the plain allocator call). -/
theorem reallocW_valid (C : Context) (md : Meta) (ty : Nat)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some reallocType)
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType) :
    FuncValid C ((XFnT.ofX (reallocShim md.alloc).toX).toLime (funcIdxOf md) ty) := by
  refine ⟨reallocType, hT, trivial, ?_⟩
  simp only [XFnT.toLime, XFnT.ofX, AFn.toX, reallocShim, toLimeL_eq,
    List.map_cons, List.map_nil, XInstr.toLime, AInstr.toLime]
  exact t_get (t := I32) rfl <| t_get (t := I32) rfl <| t_call (st := []) hA rfl <| t_end rfl

/-- **Every export shim of the multi-value style, with typed locals, is well typed.** -/
theorem shimW_valid (C : Context) (md : Meta) (s : Sig) (ty : Nat)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some (shimTypeW s))
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType)
    (hS : C.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? = some (calleeTypeW s))
    (hm : C.memories ≠ []) (hb : (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32) :
    FuncValid C ((exportShimWT md s).toLime (funcIdxOf md) ty) := by
  rcases hw : wideOf s.result with _ | ⟨ts, ns⟩
  · have hsT : shimTypeW s = shimType s := by simp [shimTypeW, hw]
    have hcT : calleeTypeW s = calleeType s := by simp [calleeTypeW, hw]
    have he : exportShimWT md s = XFnT.ofX (exportShim md s).toX := by simp [exportShimWT, hw]
    rw [hsT] at hT
    rw [hcT] at hS
    rw [he]
    exact shim_valid C md s ty hT hA hS hb
  · have hsT : shimTypeW s = ⟨flatParams s.params, [I32]⟩ := by simp [shimTypeW, hw]
    have hcT : calleeTypeW s = ⟨flatParams s.params, ValTy.flatList ts⟩ := by
      simp [calleeTypeW, hw]
    have he : exportShimWT md s = mvShimT md s ts ns := by simp [exportShimWT, hw]
    rw [hsT] at hT
    rw [hcT] at hS
    rw [he]
    exact mvShimT_valid C md s ts ns ty (wideOf_scalars hw) hT hA hS hm (hq ts ns hw)

/-- `adaptorLimeW md` has the adaptor shape. -/
theorem shape_adaptorLimeW (md : Meta) :
    Shape (adaptorLimeW md) calleeTypeW shimTypeW md
      ((XFnT.ofX (reallocShim md.alloc).toX).toLime (funcIdxOf md) (md.world.length + 1))
      (fun (s, i) => (exportShimWT md s).toLime (funcIdxOf md) (md.world.length + 2 + i)) where
  types := rfl
  imports := rfl
  exports := rfl
  funcs := rfl
  ty0 := rfl
  tyF := fun ⟨_, _⟩ => rfl
  tables := rfl
  memories := rfl
  globals := rfl
  elems := rfl
  data := rfl
  start := rfl

theorem funcsW_valid (md : Meta) (hn : (importNames md).Nodup)
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    ∀ f ∈ (adaptorLimeW md).funcs, FuncValid (moduleContext (adaptorLimeW md)) f := by
  have h := shape_adaptorLimeW md
  intro f hf
  rw [h.funcs, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (Tg calleeTypeW shimTypeW md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? =
        some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact reallocW_valid _ md _ hT (ctx_alloc h hw)
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (Tg calleeTypeW shimTypeW md)[(mkIdx (md.world.length + 2 + i) :
        TypeIdx).toNat]? = some (shimTypeW md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    have hs := List.getElem_mem hi
    exact shimW_valid _ md _ _ hT (ctx_alloc h hw) (ctx_callee h hw hn hi) (ctx_memories h)
      (hp _ hs) (hq _ hs)

/-- **The adaptor of the multi-value style, with typed locals, is a valid Lime1 module.** -/
theorem adaptorLimeW_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    ModuleValid (adaptorLimeW md) :=
  shape_valid (shape_adaptorLimeW md) hw hn hr (funcsW_valid md hn hp hq hw)

end Silmaril.Proofs.Wasm.Jco.Real.ValidAll
