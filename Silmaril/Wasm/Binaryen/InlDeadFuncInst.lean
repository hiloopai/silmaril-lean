module

public import Silmaril.Wasm.Binaryen.InlDeadFuncConst

@[expose] public section

/-! # Appending a dead function: instantiation

The instantiations of a module `M` and of `M` with one more defined function `F` correspond
(`inst_fwd`, `inst_back`): the initialisers run alike in the provisional instances
(`InlDeadFuncConst.lean`), and the allocation gives the instance with one more trailing
function address and the store with one more function instance (`alloc_fwd`, `alloc_back`).
A valid module never names the extra index, so the export instances are the same.
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS

variable {H : Type}

/-- The module with one more defined function. -/
abbrev appendFunc (M : Module) (F : Func) : Module := { M with funcs := M.funcs ++ [F] }

/-! ## Lists -/

theorem mapM_snoc_some {α β : Type} {f : α → Option β} {l : List α} {a : α} {r : List β} {b : β}
    (hl : l.mapM f = some r) (ha : f a = some b) : (l ++ [a]).mapM f = some (r ++ [b]) := by
  simp [List.mapM_append, hl, ha]

theorem mapM_snoc_inv {α β : Type} {f : α → Option β} {l : List α} {a : α} {r' : List β}
    (h : (l ++ [a]).mapM f = some r') :
    ∃ r b, l.mapM f = some r ∧ f a = some b ∧ r' = r ++ [b] := by
  rw [List.mapM_append] at h
  cases hl : l.mapM f with
  | none => simp [hl] at h
  | some r =>
    cases ha : f a with
    | none => simp [hl, ha] at h
    | some b =>
      simp [hl, ha] at h
      exact ⟨r, b, rfl, rfl, h.symm⟩

theorem mapM_some_mem {α β : Type} {f : α → Option β} {l : List α} {r : List β}
    (h : l.mapM f = some r) : ∀ a ∈ l, ∃ b, f a = some b :=
  forall₂_exists_left (forall₂_of_mapM h)

theorem mapM_some_mem_right {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b := by
  intro l r h b hb
  exact forall₂_mem_right (forall₂_of_mapM h) b hb

/-! ## Export instances -/

theorem allocExport?_bound {ei : ModuleInst} {e : Export} {v : ExportInst}
    (h : allocExport? ei e = some v) :
    ∀ x : FuncIdx, e.index = .func x → x.toNat < ei.funcs.length := by
  intro x hx
  simp only [allocExport?, hx] at h
  cases ha : ei.funcs[x.toNat]? with
  | none => simp [ha] at h
  | some a => exact (List.getElem?_eq_some_iff.mp ha).1

theorem allocExport?_mext {ei : ModuleInst} {e : Export} (l : List Nat)
    (hb : ∀ x : FuncIdx, e.index = .func x → x.toNat < ei.funcs.length) :
    allocExport? (mext ei l) e = allocExport? ei e := by
  cases hx : e.index with
  | func x =>
    simp only [allocExport?, hx, mext_funcs, List.getElem?_append_left (hb x hx)]
  | _ => simp only [allocExport?, hx, mext]

theorem mapM_allocExport?_mext {ei : ModuleInst} (l : List Nat) :
    ∀ {es : List Export}, (∀ e ∈ es, ∀ x : FuncIdx, e.index = .func x → x.toNat < ei.funcs.length) →
      es.mapM (allocExport? (mext ei l)) = es.mapM (allocExport? ei)
  | [], _ => rfl
  | e :: es, hb => by
    simp only [List.mapM_cons, allocExport?_mext l (hb e (List.mem_cons_self ..)),
      mapM_allocExport?_mext l (fun e' he' => hb e' (List.mem_cons_of_mem _ he'))]

/-! ## Allocation -/

theorem allocModule?_isSome {s : Store H} {m : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {tagTypes funcTypes : List DefType}
    {xi : List ExportInst}
    (ht : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes)
    (hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes)
    (hx : m.exports.mapM (allocExport?
        { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
          globals := ExternAddr.globals xas ++ List.range' s.globals.length
            (min m.globals.length valsG.length),
          mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
          tables := ExternAddr.tables xas ++ List.range' s.tables.length
            (min m.tables.length refsT.length),
          funcs := ExternAddr.funcs xas ++
            (List.range m.funcs.length).map (s.funcs.length + ·) }) = some xi) :
    ∃ S MI, allocModule? s m xas valsG refsT refsE = some (S, MI) := by
  unfold allocModule?
  simp only [Option.bind_eq_bind]
  simp only [ht, hf, Option.bind_some, allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq,
    allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq, List.length_zip, List.length_map]
  simp [hx]

/-- The function list of the extended store: the original one, with the module's functions
in the extended instance, and the new function. -/
theorem fl_append {P : List (FuncInst H)} {ps : List (DefType × Func)} {mi mi' : ModuleInst}
    (hm : MExt mi mi') (E : List (FuncInst H)) :
    FL (P ++ ps.map (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)))
      (P ++ ps.map (fun p => (⟨p.1, mi', .wasm p.2⟩ : FuncInst H)) ++ E) := by
  refine ⟨by simp, fun i fi hi => ?_⟩
  rcases Nat.lt_or_ge i P.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    refine ⟨fi, ?_, FIRel.refl fi⟩
    rw [List.append_assoc, List.getElem?_append_left hlt]
    exact hi
  · rw [List.getElem?_append_right hge, List.getElem?_map] at hi
    cases hp : ps[i - P.length]? with
    | none => simp [hp] at hi
    | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hi
      subst hi
      refine ⟨⟨p.1, mi', .wasm p.2⟩, ?_, ⟨rfl, rfl, hm⟩⟩
      have hlt : i - P.length < ps.length := (List.getElem?_eq_some_iff.mp hp).1
      rw [List.append_assoc, List.getElem?_append_right hge,
        List.getElem?_append_left (by simpa using hlt), List.getElem?_map, hp]
      rfl

/-- The export instance `$allocmodule` resolves exports against. -/
def eiOf (s : Store H) (m : Module) (xas : List ExternAddr) (tagTypes : List DefType)
    (valsG : List Val) (refsT : List Ref) : ModuleInst :=
  { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
    globals := ExternAddr.globals xas ++ List.range' s.globals.length
      (min m.globals.length valsG.length),
    mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
    tables := ExternAddr.tables xas ++ List.range' s.tables.length
      (min m.tables.length refsT.length),
    funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) }

theorem eiOf_append (s : Store H) (M : Module) (F : Func) (xas : List ExternAddr)
    (tagTypes : List DefType) (valsG : List Val) (refsT : List Ref) :
    eiOf s (appendFunc M F) xas tagTypes valsG refsT =
      mext (eiOf s M xas tagTypes valsG refsT) [s.funcs.length + M.funcs.length] := by
  simp [eiOf, mext, List.range_succ, List.append_assoc]

theorem eiOf_funcs_length (s : Store H) (M : Module) (xas : List ExternAddr)
    (tagTypes : List DefType) (valsG : List Val) (refsT : List Ref) :
    (eiOf s M xas tagTypes valsG refsT).funcs.length =
      (ExternAddr.funcs xas).length + M.funcs.length := by
  simp [eiOf]

/-- **Allocation of the extended module.** -/
theorem alloc_fwd {s s₄ : Store H} {M : Module} {F : Func} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    {dF : DefType} (hA : allocModule? s M xas valsG refsT refsE = some (s₄, mi))
    (hF : (allocTypes M.types)[F.type.toNat]? = some dF) :
    ∃ X, allocModule? s (appendFunc M F) xas valsG refsT refsE =
        some (withFuncs s₄ X, mext mi [s.funcs.length + M.funcs.length]) ∧
      FL s₄.funcs X := by
  obtain ⟨tagTypes, funcTypes, xi, ht, hf, hx, hmi, hs₄⟩ := allocModule?_inv hA
  have hx' : M.exports.mapM (allocExport? (eiOf s M xas tagTypes valsG refsT)) = some xi := hx
  have hlen : funcTypes.length = M.funcs.length := ((forall₂_of_mapM hf).length_eq).symm
  have hf₁ : (appendFunc M F).funcs.mapM
      (fun fn => (allocTypes (appendFunc M F).types)[fn.type.toNat]?) =
      some (funcTypes ++ [dF]) := mapM_snoc_some hf hF
  have hb : ∀ e ∈ M.exports, ∀ y : FuncIdx, e.index = .func y →
      y.toNat < (eiOf s M xas tagTypes valsG refsT).funcs.length := by
    intro e he y hy
    obtain ⟨v, hv⟩ := mapM_some_mem hx' e he
    exact allocExport?_bound hv y hy
  have hx₁ : (appendFunc M F).exports.mapM
      (allocExport? (eiOf s (appendFunc M F) xas tagTypes valsG refsT)) = some xi := by
    rw [eiOf_append]
    show M.exports.mapM _ = some xi
    rw [mapM_allocExport?_mext _ hb]
    exact hx'
  obtain ⟨S₁, MI₁, hA₁⟩ := allocModule?_isSome (s := s) (xas := xas) (valsG := valsG)
    (refsT := refsT) (refsE := refsE) (m := appendFunc M F) ht hf₁ hx₁
  obtain ⟨tagTypes', funcTypes', xi', ht', hf', hx'', hmi', hs₁⟩ := allocModule?_inv hA₁
  have e1 : tagTypes' = tagTypes := Option.some.inj (ht'.symm.trans ht)
  have e2 : funcTypes' = funcTypes ++ [dF] := Option.some.inj (hf'.symm.trans hf₁)
  subst e1 e2
  have e3 : xi' = xi := Option.some.inj (hx''.symm.trans hx₁)
  subst e3
  have hMI : MI₁ = mext mi [s.funcs.length + M.funcs.length] := by
    rw [hmi', hmi]
    simp [mext, List.range_succ, List.append_assoc]
  refine ⟨S₁.funcs, ?_, ?_⟩
  · rw [hA₁, hMI]
    congr 2
    rw [hs₁, hs₄]
    rfl
  · rw [hs₁, hs₄]
    simp only
    rw [List.zip_append hlen, List.map_append, hMI, ← List.append_assoc]
    exact fl_append ⟨_, rfl⟩ _

/-- **Allocation of the original module**, from that of the extended one. -/
theorem alloc_back {s S₁ : Store H} {M : Module} {F : Func} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)} {MI₁ : ModuleInst}
    (hA₁ : allocModule? s (appendFunc M F) xas valsG refsT refsE = some (S₁, MI₁))
    (hb : ∀ e ∈ M.exports, ∀ x : FuncIdx, e.index = .func x →
      x.toNat < (ExternAddr.funcs xas).length + M.funcs.length) :
    ∃ s₄ mi X dF, allocModule? s M xas valsG refsT refsE = some (s₄, mi) ∧
      (allocTypes M.types)[F.type.toNat]? = some dF ∧
      S₁ = withFuncs s₄ X ∧ MI₁ = mext mi [s.funcs.length + M.funcs.length] ∧ FL s₄.funcs X := by
  obtain ⟨tagTypes, funcTypes₁, xi, ht, hf₁, hx₁, -, -⟩ := allocModule?_inv hA₁
  obtain ⟨funcTypes, dF, hf, hF, -⟩ := mapM_snoc_inv hf₁
  have hx₁' : (appendFunc M F).exports.mapM
      (allocExport? (eiOf s (appendFunc M F) xas tagTypes valsG refsT)) = some xi := hx₁
  have hb' : ∀ e ∈ M.exports, ∀ x : FuncIdx, e.index = .func x →
      x.toNat < (eiOf s M xas tagTypes valsG refsT).funcs.length := by
    intro e he x hx
    rw [eiOf_funcs_length]
    exact hb e he x hx
  have hx : M.exports.mapM (allocExport? (eiOf s M xas tagTypes valsG refsT)) = some xi := by
    rw [← mapM_allocExport?_mext [s.funcs.length + M.funcs.length] hb',
      ← eiOf_append s M F xas tagTypes valsG refsT]
    exact hx₁'
  obtain ⟨s₄, mi, hA⟩ := allocModule?_isSome (s := s) (xas := xas) (valsG := valsG)
    (refsT := refsT) (refsE := refsE) (m := M) ht hf hx
  obtain ⟨X, hA₁', hX⟩ := alloc_fwd hA hF
  rw [hA₁] at hA₁'
  simp only [Option.some.injEq, Prod.mk.injEq] at hA₁'
  exact ⟨s₄, mi, X, dF, hA, hF, hA₁'.1, hA₁'.2, hX⟩

/-! ## Validity -/

theorem moduleOk_xtI_eq {M : Module} {F : Func} {xtI xtE xtI₁ xtE₁ : List CExternType}
    (h : ModuleOk M ⟨xtI, xtE⟩) (h₁ : ModuleOk (appendFunc M F) ⟨xtI₁, xtE₁⟩) : xtI₁ = xtI := by
  cases h with
  | mk ht hi _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases h₁ with
    | mk ht₁ hi₁ _ _ _ _ _ _ _ _ _ _ _ _ =>
      obtain rfl := TypesOk.det ht ht₁
      exact List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hi₁ hi

/-- The type of the extra function is allocated. -/
theorem funcType_of_moduleOk {M : Module} {F : Func} {mt : CModuleType}
    (h : ModuleOk (appendFunc M F) mt) : ∃ dF, (allocTypes M.types)[F.type.toNat]? = some dF := by
  cases h with
  | mk htypes _ hC' hC _ _ _ _ hfuncs _ _ _ _ _ =>
    obtain ⟨d, hFd⟩ :=
      forall₂_exists_left hfuncs F (List.mem_append_right _ (List.mem_singleton_self F))
    cases hFd with
    | mk hd _ _ _ =>
      refine ⟨d, ?_⟩
      have e : allocTypes M.types = _ := allocTypes_eq htypes
      rw [e]
      subst hC
      subst hC'
      exact hd

/-! ## Instantiation -/

theorem initial_append (s : Store H) (M : Module) (F : Func) (xas : List ExternAddr) :
    ModuleInst.initial s (appendFunc M F) xas =
      mext (ModuleInst.initial s M xas) [s.funcs.length + M.funcs.length] := by
  simp [ModuleInst.initial, mext, List.range_succ, List.append_assoc]

theorem initial_funcs_length (s : Store H) (M : Module) (xas : List ExternAddr) :
    (ModuleInst.initial s M xas).funcs.length = (ExternAddr.funcs xas).length + M.funcs.length := by
  simp [ModuleInst.initial]

section inst

variable {P : Numerics.Profile} {host : HostSemantics H}

/-- **An instantiation of the original module gives one of the extended module.** -/
theorem inst_fwd {s : Store H} {M : Module} {F : Func} {xas : List ExternAddr} {c : Config H}
    {xtI₁ xtE₁ : List CExternType} (hM₁ : ModuleOk (appendFunc M F) ⟨xtI₁, xtE₁⟩)
    (hi : Instantiate P host s M xas c) :
    ∃ c', Instantiate P host s (appendFunc M F) xas c' ∧ Rel c c' := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT,
    hE, hA, rfl⟩ := hi
  have e := moduleOk_xtI_eq hmt hM₁
  subst e
  obtain ⟨hcG, hcT, hcE⟩ := hmt.initConst
  obtain ⟨dF, hF⟩ := funcType_of_moduleOk hM₁
  obtain ⟨X, hA₁, hX⟩ := alloc_fwd (F := F) hA hF
  have hG₁ := evalGlobals_fwd hG (fun e he => hcG e he) [s.funcs.length + M.funcs.length]
  have hT₁ := evalExprs_fwd hT (fun e he => hcT e he) [s.funcs.length + M.funcs.length]
  have hE₁ := evalExprss_fwd hE (fun es hes => hcE es hes) [s.funcs.length + M.funcs.length]
  refine ⟨_, ⟨⟨_, _, hM₁, hxas⟩, hbd, s₁, s₂, s₃, withFuncs s₄ X, _, _, _, valsG, refsT,
    refsE, mext mi [s₃.funcs.length + M.funcs.length], ?_, hT₁, hE₁, hA₁, rfl⟩,
    ⟨X, rfl, hX⟩, ⟨[s₃.funcs.length + M.funcs.length], rfl⟩, CRel.refl _⟩
  rw [initial_append]
  exact hG₁

/-- **An instantiation of the extended module gives one of the original module.** -/
theorem inst_back {s : Store H} {M : Module} {F : Func} {xas : List ExternAddr} {c' : Config H}
    {xtI xtE : List CExternType} (hM : ModuleOk M ⟨xtI, xtE⟩)
    (hi : Instantiate P host s (appendFunc M F) xas c') :
    ∃ c, Instantiate P host s M xas c ∧ Rel c c' := by
  obtain ⟨⟨xtE₁, xtI₁, hmt₁, hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁', f₂', f₃', valsG, refsT, refsE, mi',
    hG, hT, hE, hA, rfl⟩ := hi
  have e := moduleOk_xtI_eq hM hmt₁
  subst e
  obtain ⟨hcG, hcT, hcE⟩ := hM.initConst
  have hB := moduleOk_funcBounds hM hxas
  rw [initial_append] at hG
  obtain ⟨f₁, hf₁, hG₀⟩ := evalGlobals_back hG (f := ⟨[], ModuleInst.initial s M xas⟩)
    (l := [s.funcs.length + M.funcs.length]) rfl (fun e he => hcG e he)
    (fun e he x hx => by
      show x.toNat < (ModuleInst.initial s M xas).funcs.length
      rw [initial_funcs_length]
      exact hB.globals e he x hx)
  subst hf₁
  have hfun₁ : f₁.module.funcs = (ModuleInst.initial s M xas).funcs :=
    (EvalGlobals.shape hG₀ (fun e he => hcG e he)).2.2
  obtain ⟨hf₂, hT₀⟩ := evalExprs_back hT (f := f₁) rfl (fun e he => hcT e he)
    (fun e he x hx => by
      rw [hfun₁, initial_funcs_length]
      exact hB.tables e he x hx)
  subst hf₂
  obtain ⟨hf₃, hE₀⟩ := evalExprss_back hE (f := f₁) rfl (fun es hes => hcE es hes)
    (fun es hes e he x hx => by
      rw [hfun₁, initial_funcs_length]
      exact hB.elems es hes e he x hx)
  subst hf₃
  obtain ⟨s₄, mi, X, dF, hA₀, -, hs₄, hmi, hX⟩ := alloc_back hA hB.exports
  subst hs₄ hmi
  exact ⟨_, ⟨⟨_, _, hM, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₁, f₁, valsG, refsT, refsE, mi, hG₀,
    hT₀, hE₀, hA₀, rfl⟩, ⟨X, rfl, hX⟩, ⟨[s₃.funcs.length + M.funcs.length], rfl⟩, CRel.refl _⟩

theorem externAddrOk_func_lt {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : ∀ a, xa = .func a → a < s.funcs.length := by
  induction h with
  | func h => intro a ha; cases ha; exact (List.getElem?_eq_some_iff.mp h).1
  | sub _ _ _ ih => exact ih
  | _ => intro a ha; cases ha

theorem exportFunc?_mem {mi : ModuleInst} {x : String} {a : Nat} (h : exportFunc? mi x = some a) :
    ∃ ex ∈ mi.exports, ex.addr = .func a := by
  unfold exportFunc? at h
  cases hf : mi.exports.find? (fun e => e.name == x) with
  | none => rw [hf] at h; cases h
  | some ex =>
    rw [hf] at h
    rcases ex with ⟨nm, addr⟩
    cases addr <;> simp at h
    subst h
    exact ⟨_, List.mem_of_find?_eq_some hf, rfl⟩

theorem allocExport?_func {ei : ModuleInst} {e : Export} {ex : ExportInst} {a : Nat}
    (h : allocExport? ei e = some ex) (ha : ex.addr = .func a) : a ∈ ei.funcs := by
  cases hi : e.index <;> simp [allocExport?, hi] at h <;> obtain ⟨b, hb, rfl⟩ := h <;>
    simp at ha
  subst ha
  exact List.mem_of_getElem? hb

/-- **The original instance exports functions with numeric parameters.** -/
theorem inst_left_facts {s : Store H} {M : Module} {xas : List ExternAddr} {c : Config H}
    (hs : StoreOk s) (hp : ∀ d ∈ allocTypes M.types, NumParams d)
    (hi : Instantiate P host s M xas c) : SessInv c.store c.frame.module := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, -, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT,
    hE, hA, rfl⟩ := hi
  obtain ⟨hcG, hcT, hcE⟩ := hmt.initConst
  have hfs₃ : s₃.funcs = s.funcs := by
    rw [(EvalExprss.shape hE (fun es hes => hcE es hes)).1.funcs,
      (EvalExprs.shape hT (fun e he => hcT e he)).1.funcs,
      (EvalGlobals.shape hG (fun e he => hcG e he)).1.funcs]
  obtain ⟨tagTypes, funcTypes, xi, -, hf, hx, hmi, hs₄⟩ := allocModule?_inv hA
  have hlen : funcTypes.length = M.funcs.length := ((forall₂_of_mapM hf).length_eq).symm
  have hfuncs : s₄.funcs = s₃.funcs ++
      (funcTypes.zip M.funcs).map (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)) := by
    rw [hs₄]
  · intro x a hxa
    obtain ⟨ex, hex, haddr⟩ := exportFunc?_mem hxa
    have hex' : ex ∈ xi := by rw [hmi] at hex; exact hex
    obtain ⟨e, -, he⟩ := mapM_some_mem_right hx ex hex'
    have hmem := allocExport?_func he haddr
    change a ∈ ExternAddr.funcs xas ++ (List.range M.funcs.length).map (s₃.funcs.length + ·)
      at hmem
    simp only [List.mem_append, List.mem_map, List.mem_range] at hmem
    rcases hmem with hmem | ⟨j, hj, rfl⟩
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      obtain ⟨d, hd, hext⟩ := InlR.forall₂_getElem? (ExternAddrOk.forall₂_funcs hxas) hi
      have hlt : a < s.funcs.length := externAddrOk_func_lt hext a rfl
      have hd' : d ∈ allocTypes M.types := by
        cases hmt with
        | mk htypes himports _ _ _ _ _ _ _ _ _ _ _ _ =>
          rw [allocTypes_eq htypes]
          exact imports_funcs_mem himports d (List.mem_of_getElem? hd)
      have hnp := numParams_externAddr hs hext (hp d hd')
      have hget : s₄.funcs[a]? = s.funcs[a]? := by
        rw [hfuncs, List.getElem?_append_left (by rw [hfs₃]; exact hlt), hfs₃]
      refine ⟨?_, fun fi hfi => hnp fi (by rw [← hget]; exact hfi)⟩
      rw [hfuncs, List.length_append, hfs₃]
      omega
    · have hlen₄ : s₄.funcs.length = s₃.funcs.length + M.funcs.length := by
        rw [hfuncs]; simp [hlen]
      refine ⟨by rw [hlen₄]; omega, fun fi hfi => ?_⟩
      have hmem₄ : fi ∈ (funcTypes.zip M.funcs).map
          (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)) := by
        rw [hfuncs, List.getElem?_append_right (by omega)] at hfi
        exact List.mem_of_getElem? hfi
      obtain ⟨⟨d, F'⟩, hp', rfl⟩ := List.mem_map.mp hmem₄
      obtain ⟨fn, -, hfn⟩ := mapM_some_mem_right hf d (List.of_mem_zip hp').1
      exact hp d (List.mem_of_getElem? hfn)

end inst

end Silmaril.Wasm.Binaryen.InlDF
