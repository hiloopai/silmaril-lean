module

public import Silmaril.Wasm.Lime1.ToCore.Modules

/-!
# The Lime1 decoder is a retraction up to element-segment types

`Lime1.Module.ofCore?` accepts exactly the canonical image of `Lime1.Module.toCore`, except
for one field: an element segment may have the type `funcref` (the image) or the non-null
`(ref func)` (`Lime1.Elem.ofCore?`). So a Core module that decodes is the image of its
decoding once its element types are set to `funcref`:

* `Module.toCore_of_ofCore?`: `ofCore? M = some l → l.toCore = funcrefElems M`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm

/-- The Core module with every element segment typed `funcref`. -/
def funcrefElems (M : Module) : Module :=
  { M with elems := M.elems.map fun e => { e with type := V1.funcref } }

theorem mapM_map_eq {α β γ : Type _} {f : α → Option β} {g : β → γ} {k : α → γ}
    (hf : ∀ x y, f x = some y → g y = k x) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.map g = xs.map k
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    simp only [List.map_cons, hf x y hy, mapM_map_eq hf hys]

theorem mapM_retract {α β : Type _} {f : α → Option β} {g : β → α}
    (hf : ∀ x y, f x = some y → g y = x) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.map g = xs := by
  simpa only [List.map_id] using mapM_map_eq (k := id) hf h

theorem valType_retract {t : ValType} {u : V1.ValType} (h : V1.ValType.ofCore? t = some u) :
    u.toCore = t := by
  cases t <;> simp only [V1.ValType.ofCore?, Option.some.injEq, reduceCtorEq] at h
  subst h; rfl

theorem narrow32_retract {n : Fin (2 ^ 64)} {k : Fin (2 ^ 32)} (h : V1.narrow32? n = some k) :
    V1.widen32 k = n := by
  unfold V1.narrow32? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem limits_retract {l : Limits} {k : V1.Limits} (h : V1.Limits.ofCore? l = some k) :
    k.toCore = l := by
  rcases l with ⟨mn, mx⟩
  cases mx with
  | none =>
    simp only [V1.Limits.ofCore?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.bind_some] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [V1.Limits.toCore, narrow32_retract ha]
  | some n =>
    simp only [V1.Limits.ofCore?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, _, ⟨c, hc, rfl⟩, rfl⟩ := h
    simp [V1.Limits.toCore, narrow32_retract ha, narrow32_retract hc]

theorem funcType_retract {t : FuncType} {u : V1.FuncType} (h : V1.FuncType.ofCore? t = some u) :
    u.toCore = t := by
  rcases t with ⟨ps, rs⟩
  simp only [V1.FuncType.ofCore?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  simp only [V1.FuncType.toCore, mapM_retract (fun _ _ => valType_retract) ha,
    mapM_retract (fun _ _ => valType_retract) hb]

theorem funcTypeRec_retract {t : RecType} {u : V1.FuncType} (h : V1.FuncType.ofCoreRec? t = some u) :
    u.toCoreRec = t := by
  unfold V1.FuncType.ofCoreRec? at h
  split at h
  · rw [V1.FuncType.toCoreRec, funcType_retract h]
  · cases h

theorem tableType_retract {t : TableType} {u : V1.TableType} (h : V1.TableType.ofCore? t = some u) :
    u.toCore = t := by
  rcases t with ⟨a, l, e⟩
  simp only [V1.TableType.ofCore?, Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨k, hk, rfl⟩ := h
    simp only [V1.TableType.toCore, limits_retract hk]
  · cases h

theorem memoryType_retract {t : MemoryType} {u : V1.MemoryType}
    (h : V1.MemoryType.ofCore? t = some u) : u.toCore = t := by
  rcases t with ⟨a, l⟩
  simp only [V1.MemoryType.ofCore?, Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · rename_i hc
    subst hc
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨k, hk, rfl⟩ := h
    simp only [V1.MemoryType.toCore, limits_retract hk]
  · cases h

theorem globalType_retract {t : GlobalType} {u : V1.GlobalType}
    (h : V1.GlobalType.ofCore? t = some u) : u.toCore = t := by
  rcases t with ⟨mu, v⟩
  simp only [V1.GlobalType.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [V1.GlobalType.toCore, valType_retract hk]

theorem importDesc_retract {t : ExternType} {u : V1.ImportDesc}
    (h : V1.ImportDesc.ofCore? t = some u) : u.toCore = t := by
  cases t <;> simp only [V1.ImportDesc.ofCore?, Option.some.injEq, Option.map_eq_some_iff,
    reduceCtorEq] at h
  case func => subst h; rfl
  case table => obtain ⟨k, hk, rfl⟩ := h; simp only [V1.ImportDesc.toCore, tableType_retract hk]
  case memory => obtain ⟨k, hk, rfl⟩ := h; simp only [V1.ImportDesc.toCore, memoryType_retract hk]
  case global => obtain ⟨k, hk, rfl⟩ := h; simp only [V1.ImportDesc.toCore, globalType_retract hk]

theorem import_retract {t : Import} {u : V1.Import} (h : V1.Import.ofCore? t = some u) :
    u.toCore = t := by
  rcases t with ⟨a, b, d⟩
  simp only [V1.Import.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [V1.Import.toCore, importDesc_retract hk]

theorem externIdx_retract {t : ExternIdx} {u : V1.ExternIdx} (h : V1.ExternIdx.ofCore? t = some u) :
    u.toCore = t := by
  cases t <;> simp only [V1.ExternIdx.ofCore?, Option.some.injEq, reduceCtorEq] at h <;>
    (subst h; rfl)

theorem export_retract {t : Export} {u : V1.Export} (h : V1.Export.ofCore? t = some u) :
    u.toCore = t := by
  rcases t with ⟨a, d⟩
  simp only [V1.Export.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [V1.Export.toCore, externIdx_retract hk]

theorem packSize_retract {t : PackSize} {u : V1.PackSize} (h : V1.PackSize.ofCore? t = some u) :
    u.toCore = t := by
  cases t <;> simp only [V1.PackSize.ofCore?, Option.some.injEq, reduceCtorEq] at h <;>
    (subst h; rfl)

theorem memArg_retract {t : MemArg} {u : V1.MemArg} (h : V1.MemArg.ofCore? t = some u) :
    u.toCore = t := by
  rcases t with ⟨a, o⟩
  simp only [V1.MemArg.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [V1.MemArg.toCore, narrow32_retract hk]

theorem blockType_retract {t : BlockType} {u : Lime1.BlockType}
    (h : Lime1.BlockType.ofCore? t = some u) : u.toCore = t := by
  unfold Lime1.BlockType.ofCore? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> (subst h; rfl)

theorem intUnOp_retract {t : IntUnOp} {u : Lime1.IntUnOp} (h : Lime1.IntUnOp.ofCore? t = some u) :
    u.toCore = t := by
  cases t <;> simp only [Lime1.IntUnOp.ofCore?, Option.some.injEq, Option.map_eq_some_iff] at h
  case extend => obtain ⟨k, hk, rfl⟩ := h; simp only [Lime1.IntUnOp.toCore, packSize_retract hk]
  all_goals (subst h; rfl)

theorem loadPack_retract {t : Option (PackSize × Signedness)} {u : Option (V1.PackSize × Signedness)}
    (h : Lime1.loadPackOfCore? t = some u) : Lime1.loadPackToCore u = t := by
  rcases t with _ | ⟨n, sg⟩ <;> simp only [Lime1.loadPackOfCore?, Option.some.injEq,
    Option.map_eq_some_iff] at h
  · subst h; rfl
  · obtain ⟨k, hk, rfl⟩ := h; simp only [Lime1.loadPackToCore, Option.map_some, packSize_retract hk]

theorem storePack_retract {t : Option PackSize} {u : Option V1.PackSize}
    (h : Lime1.storePackOfCore? t = some u) : u.map V1.PackSize.toCore = t := by
  rcases t with _ | n <;> simp only [Lime1.storePackOfCore?, Option.some.injEq,
    Option.map_eq_some_iff] at h
  · subst h; rfl
  · obtain ⟨k, hk, rfl⟩ := h; simp only [Option.map_some, packSize_retract hk]

theorem retract_block {t : BlockType} {body : Expr} {j : Lime1.Instr}
    (ih : ∀ {fs}, Lime1.Expr.ofCore? body = some fs → Lime1.Expr.toCore fs = body)
    (h : Lime1.Instr.ofCore? (.block t body) = some j) : j.toCore = .block t body := by
  simp only [Lime1.Instr.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, blockType_retract ha, ih hb]

theorem retract_loop {t : BlockType} {body : Expr} {j : Lime1.Instr}
    (ih : ∀ {fs}, Lime1.Expr.ofCore? body = some fs → Lime1.Expr.toCore fs = body)
    (h : Lime1.Instr.ofCore? (.loop t body) = some j) : j.toCore = .loop t body := by
  simp only [Lime1.Instr.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, blockType_retract ha, ih hb]

theorem retract_if {t : BlockType} {l r : Expr} {j : Lime1.Instr}
    (ihl : ∀ {fs}, Lime1.Expr.ofCore? l = some fs → Lime1.Expr.toCore fs = l)
    (ihr : ∀ {fs}, Lime1.Expr.ofCore? r = some fs → Lime1.Expr.toCore fs = r)
    (h : Lime1.Instr.ofCore? (.if_ t l r) = some j) : j.toCore = .if_ t l r := by
  simp only [Lime1.Instr.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
  simp only [Lime1.Instr.toCore, blockType_retract ha, ihl hb, ihr hc]

theorem retract_select {ts : Option (List ValType)} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? (.select ts) = some j) : j.toCore = .select ts := by
  rcases ts with _ | ts <;> simp only [Lime1.Instr.ofCore?, Option.some.injEq, reduceCtorEq] at h
  subst h; rfl

theorem retract_callIndirect {tb : TableIdx} {ty : TypeIdx} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? (.callIndirect tb ty) = some j) : j.toCore = .callIndirect tb ty := by
  simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

theorem retract_intLoad {t : IntType} {p : Option (PackSize × Signedness)} {mem : MemIdx}
    {a : MemArg} {j : Lime1.Instr} (h : Lime1.Instr.ofCore? (.intLoad t p mem a) = some j) :
    j.toCore = .intLoad t p mem a := by
  simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨rfl, k, hk, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, loadPack_retract hk, memArg_retract hb]

theorem retract_floatLoad {t : FloatType} {mem : MemIdx} {a : MemArg} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? (.floatLoad t mem a) = some j) : j.toCore = .floatLoad t mem a := by
  simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨rfl, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, memArg_retract hb]

theorem retract_intStore {t : IntType} {p : Option PackSize} {mem : MemIdx} {a : MemArg}
    {j : Lime1.Instr} (h : Lime1.Instr.ofCore? (.intStore t p mem a) = some j) :
    j.toCore = .intStore t p mem a := by
  simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨rfl, k, hk, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, storePack_retract hk, memArg_retract hb]

theorem retract_floatStore {t : FloatType} {mem : MemIdx} {a : MemArg} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? (.floatStore t mem a) = some j) : j.toCore = .floatStore t mem a := by
  simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨rfl, b, hb, rfl⟩ := h
  simp only [Lime1.Instr.toCore, memArg_retract hb]

theorem retract_mem {i : Instr} {j : Lime1.Instr}
    (hi : (∃ mem, i = .memorySize mem) ∨ (∃ mem, i = .memoryGrow mem) ∨
      (∃ mem, i = .memoryFill mem) ∨ (∃ d sr, i = .memoryCopy d sr))
    (h : Lime1.Instr.ofCore? i = some j) : j.toCore = i := by
  rcases hi with ⟨mem, rfl⟩ | ⟨mem, rfl⟩ | ⟨mem, rfl⟩ | ⟨d, sr, rfl⟩ <;>
    simp only [Lime1.Instr.ofCore?, Option.ite_none_right_eq_some, Option.some.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl

theorem retract_intUnOp {t : IntType} {op : IntUnOp} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? (.intUnOp t op) = some j) : j.toCore = .intUnOp t op := by
  simp only [Lime1.Instr.ofCore?, Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  simp only [Lime1.Instr.toCore, intUnOp_retract hk]

mutual
theorem instr_retract {i : Instr} {j : Lime1.Instr} (h : Lime1.Instr.ofCore? i = some j) :
    j.toCore = i := by
  cases i
  case block t body => exact retract_block (fun h => expr_retract h) h
  case loop t body => exact retract_loop (fun h => expr_retract h) h
  case if_ t l r => exact retract_if (fun h => expr_retract h) (fun h => expr_retract h) h
  all_goals first
    | (simp only [Lime1.Instr.ofCore?, reduceCtorEq] at h; done)
    | (simp only [Lime1.Instr.ofCore?, Option.some.injEq] at h; subst h; rfl)
    | exact retract_select h | exact retract_callIndirect h | exact retract_intLoad h
    | exact retract_floatLoad h | exact retract_intStore h | exact retract_floatStore h
    | exact retract_intUnOp h | exact retract_mem (.inl ⟨_, rfl⟩) h
    | exact retract_mem (.inr (.inl ⟨_, rfl⟩)) h | exact retract_mem (.inr (.inr (.inl ⟨_, rfl⟩))) h
    | exact retract_mem (.inr (.inr (.inr ⟨_, _, rfl⟩))) h
termination_by sizeOf i

theorem expr_retract {es : Expr} {fs : Lime1.Expr} (h : Lime1.Expr.ofCore? es = some fs) :
    Lime1.Expr.toCore fs = es := by
  cases es with
  | nil =>
    simp only [Lime1.Expr.ofCore?, Option.some.injEq] at h
    subst h; rfl
  | cons i es =>
    simp only [Lime1.Expr.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Lime1.Expr.toCore, instr_retract ha, expr_retract hb]
termination_by sizeOf es
end

theorem func_retract {f : Func} {g : Lime1.Func} (h : Lime1.Func.ofCore? f = some g) :
    g.toCore = f := by
  rcases f with ⟨t, ls, b⟩
  simp only [Lime1.Func.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, c, hc, rfl⟩ := h
  simp only [Lime1.Func.toCore, mapM_retract (fun _ _ => valType_retract) ha, expr_retract hc]

theorem global_retract {f : Global} {g : Lime1.Global} (h : Lime1.Global.ofCore? f = some g) :
    g.toCore = f := by
  rcases f with ⟨t, e⟩
  simp only [Lime1.Global.ofCore?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a, ha, c, hc, rfl⟩ := h
  simp only [Lime1.Global.toCore, globalType_retract ha, expr_retract hc]

theorem table_retract {t : Table} {u : V1.TableType} (h : Lime1.tableOfCore? t = some u) :
    Lime1.tableToCore u = t := by
  rcases t with ⟨ty, init⟩
  unfold Lime1.tableOfCore? at h
  split at h
  · rename_i hi
    simp only at hi
    simp only [Lime1.tableToCore, tableType_retract h, hi]
  · cases h

theorem funcRef_retract {e : Expr} {f : FuncIdx} (h : Lime1.funcRef? e = some f) :
    Lime1.funcRef f = e := by
  unfold Lime1.funcRef? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

/-- An element segment with its type set to `funcref`. -/
def funcrefElem (e : Elem) : Elem := { e with type := V1.funcref }

theorem elem_retract {e : Elem} {f : Lime1.Elem} (h : Lime1.Elem.ofCore? e = some f) :
    f.toCore = funcrefElem e := by
  rcases e with ⟨ty, init, mode⟩
  simp only [Lime1.Elem.ofCore?, Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · cases h
  · cases mode <;> simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [Lime1.Elem.toCore, funcrefElem, expr_retract ha,
      mapM_retract (fun _ _ => funcRef_retract) hb]

theorem data_retract {d : Data} {f : Lime1.Data} (h : Lime1.Data.ofCore? d = some f) :
    f.toCore = d := by
  rcases d with ⟨bs, mode⟩
  cases mode <;> simp only [Lime1.Data.ofCore?, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at h
  obtain ⟨a, ha, rfl⟩ := h
  simp only [Lime1.Data.toCore, expr_retract ha]

/-- **The Lime1 decoder is a retraction up to element types**: a Core module that decodes to
`l` is the image of `l` once its element segments are typed `funcref`. -/
theorem module_retract {M : Module} {l : Lime1.Module} (h : Lime1.Module.ofCore? M = some l) :
    l.toCore = funcrefElems M := by
  rcases M with ⟨ty, im, tg, gl, me, ta, fu, da, el, st, ex⟩
  simp only [Lime1.Module.ofCore?, Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · cases h
  · rename_i htg
    have htg' : tg = [] := List.isEmpty_iff.mp (by simpa using htg)
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, a8, h8, a9, h9, rfl⟩ := h
    simp only [Lime1.Module.toCore, funcrefElems, htg',
      mapM_retract (fun _ _ => funcTypeRec_retract) h1, mapM_retract (fun _ _ => import_retract) h2,
      mapM_retract (fun _ _ => func_retract) h3, mapM_retract (fun _ _ => global_retract) h4,
      mapM_retract (fun _ _ => table_retract) h5, mapM_retract (fun _ _ => memoryType_retract) h6,
      mapM_map_eq (fun _ _ => elem_retract) h7, mapM_retract (fun _ _ => data_retract) h8,
      mapM_retract (fun _ _ => export_retract) h9]
    rfl

end Silmaril.Proofs.Wasm.Component.Lime1Inst
