module

public import Silmaril.Wasm.Models.V2Sound.Thms

/-!
# 2.0 instantiation progress in the empty store

A 2.0-valid module without imports instantiates in the empty store, at every profile and under
every host, and the configuration it starts is host-free:

* the global and element initialisers are constant expressions, which denote values without
  reading the host (`exprOkConst_evalExpr`, `constExpr?`);
* `allocModule?` succeeds: function types, export indices and the lengths of the initialiser
  lists are all in range by `Module_ok`;
* every function the allocation adds is a Wasm function, so the store is host-free.

`instantiate_empty` packages the three. The proofs are new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstDom

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm (FuncIdx GlobalIdx)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree)

variable {H : Type}

/-! ## List helpers -/

/-- `Forall₂` from a witness at every element. -/
theorem forall₂_of_exists {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := forall₂_of_exists (l := l) fun x hx => h x (by simp [hx])
    exact ⟨b :: l', .cons hb hl'⟩

/-- A witness at every element of a `Forall₂`. -/
theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b, R a b
  | _, _, .nil => fun _ h => by simp at h
  | _, _, .cons hab hrest => fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hab⟩
    · exact exists_of_forall₂ hrest x hx

/-- `List.mapM` in `Option` succeeds when it succeeds at every element. -/
theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
    obtain ⟨l', hl'⟩ := mapM_some (l := l) fun x hx => h x (by simp [hx])
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-! ## Host-freeness of the allocated store -/

/-- Allocating Wasm functions keeps a store host-free. -/
theorem hostFree_allocFuncs (mi : ModuleInst) :
    ∀ (s : Store H) (fs : List (FuncType × Func)), HostFree s → HostFree (allocFuncs s mi fs).1
  | _, [], h => h
  | s, p :: fs, h => by
    refine hostFree_allocFuncs mi (allocFunc s p.1 mi (.wasm p.2)).1 fs ?_
    intro fi hfi x hx
    simp only [allocFunc, List.mem_append, List.mem_singleton] at hfi
    rcases hfi with hfi | rfl
    · exact h fi hfi x hx
    · cases hx

/-- `allocModule?` keeps a store host-free. -/
theorem hostFree_allocModule {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) (hs : HostFree s) : HostFree s' := by
  obtain ⟨fts, s₁, s₂, s₃, s₄, s₅, -, h₁, h₂, h₃, h₄, h₅, h', -⟩ := allocModule?_spec h
  have e : s'.funcs = s₁.funcs := by
    subst h₂ h₃ h₄ h₅ h'
    simp only [allocDatas, allocElems, allocMems, allocTables, allocGlobals]
    rw [allocMany_fst (fun s : Store H => s.funcs) (fun _ _ => rfl),
      allocMany_fst (fun s : Store H => s.funcs) (fun _ _ => rfl),
      allocMany_fst (fun s : Store H => s.funcs) (fun _ _ => rfl),
      allocMany_fst (fun s : Store H => s.funcs) (fun _ _ => rfl),
      allocMany_fst (fun s : Store H => s.funcs) (fun _ _ => rfl)]
  intro fi hfi
  rw [e, h₁] at hfi
  exact hostFree_allocFuncs mi s _ hs fi hfi

/-- A lookup below the length of a list succeeds, under `Option.map`. -/
theorem isSome_map_getElem? {α β : Type} (f : α → β) {l : List α} {i : Nat} (h : i < l.length) :
    (Option.map f l[i]?).isSome = true := by
  simp [h]

/-- The index a lookup succeeded at is below the length. -/
theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- An export that `Export_ok` accepts resolves in address lists at least as long as the
context's index spaces. -/
theorem instExport?_isSome {C : Context} {e : Export} {t : ExternType} (h : ExportOk C e t)
    {fas : List FuncAddr} {gas : List GlobalAddr} {tas : List TableAddr} {mas : List MemAddr}
    (hf : C.funcs.length ≤ fas.length) (hg : C.globals.length ≤ gas.length)
    (ht : C.tables.length ≤ tas.length) (hm : C.mems.length ≤ mas.length) :
    (instExport? fas gas tas mas e).isSome := by
  obtain ⟨nm, idx⟩ := e
  unfold ExportOk at h
  simp only [instExport?, Option.isSome_map]
  cases h with
  | func hx => exact isSome_map_getElem? _ (Nat.lt_of_lt_of_le (lt_of_getElem? hx) hf)
  | global hx => exact isSome_map_getElem? _ (Nat.lt_of_lt_of_le (lt_of_getElem? hx) hg)
  | table hx => exact isSome_map_getElem? _ (Nat.lt_of_lt_of_le (lt_of_getElem? hx) ht)
  | memory hx => exact isSome_map_getElem? _ (Nat.lt_of_lt_of_le (lt_of_getElem? hx) hm)

/-! ## Constant initialisers in the empty store -/

/-- The bounds `$instantiate` assumes of the segments (`Instantiate.bounded`). -/
def SegBounded (m : Module) : Prop :=
  m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
    (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32)

/-- The initial frame of an instantiation in the empty store. -/
abbrev f₀ (m : Module) : Frame := Frame.initial ({} : Store H) m []

/-- A host used only to instantiate the implicit host of `exprOkConst_evalExpr`. -/
def noHost : HostSemantics H := fun _ _ _ _ => False

/-- A constant expression of a context with no more functions than `m` and no globals denotes a
value in the empty store, at `m`'s initial frame. -/
theorem const_denotes {C : Context} {m : Module} {e : Expr} {t : ValType} (h : ExprOkConst C e t)
    (hf : C.funcs.length ≤ m.funcs.length) (hg : C.globals = []) :
    ∃ v, constExpr? ({} : Store H) (f₀ (H := H) m).module e = some v := by
  have hF : ∀ x : FuncIdx, x.toNat < C.funcs.length →
      ((f₀ (H := H) m).module.funcAddr? x).isSome := fun x hx => by
    simp [f₀, Frame.initial, ModuleInst.initial, ModuleInst.funcAddr?, ExternAddr.funcs]
    omega
  have hG : ∀ x : GlobalIdx, x.toNat < C.globals.length → ∃ a,
      (f₀ (H := H) m).module.globalAddr? x = some a ∧ (({} : Store H).globalInst? a).isSome :=
    fun x hx => absurd hx (by simp [hg])
  obtain ⟨v, hv, -⟩ := exprOkConst_evalExpr (P := Profile.spec false default) (host := noHost)
    (s := ({} : Store H)) (f := f₀ m) h hF hG
  exact ⟨v, hv⟩

/-- At a reference type, the value is a reference. -/
theorem const_ref_denotes {C : Context} {m : Module} {e : Expr} {rt : RefType}
    (h : ExprOkConst C e (.ref rt)) (hf : C.funcs.length ≤ m.funcs.length) (hg : C.globals = []) :
    ∃ r, constExpr? ({} : Store H) (f₀ (H := H) m).module e = some (Val.ref r) := by
  obtain ⟨v, hv⟩ := const_denotes (H := H) h hf hg
  have hty : v.type = .ref rt :=
    constExpr?_type (f := f₀ m) h hv fun x _ _ _ hx => absurd hx (by simp [hg])
  cases v with
  | ref r => exact ⟨r, hv⟩
  | num n => exact absurd hty (by simp [Val.type])
  | vec w => exact absurd hty (by simp [Val.type])

/-- The context `Module_ok` checks initialisers in: no imported globals, and the module's own
functions. -/
theorem ctx_of_moduleOk {m : Module} {xt : List ExternType} (hm : ModuleOk m [] xt) :
    ∃ C' : Context,
      (∀ g ∈ m.globals, ExprOkConst C' g.init g.type.value) ∧
      (∀ e ∈ m.elems, ∀ ex ∈ e.init, ExprOkConst C' ex (.ref e.type)) ∧
      C'.funcs.length ≤ m.funcs.length ∧ C'.globals = [] := by
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    refine ⟨C', fun g hg => ?_, fun e he ex hex => ?_, ?_, ?_⟩
    · obtain ⟨t, ht, -, hok⟩ := exists_of_forall₂ hglobals g hg
      exact ht ▸ hok
    · obtain ⟨rt, hrt, hok, -⟩ := exists_of_forall₂ helems e he
      exact hrt ▸ hok ex hex
    · simp [hC', ExternType.funcs, hfuncs.length_eq]
    · simp [hC', ExternType.globals]

/-! ## Allocation -/

/-- `allocModule?` succeeds in the empty store for a valid import-free module, given initialiser
lists of the right lengths. -/
theorem allocModule_some {m : Module} {xt : List ExternType} (hm : ModuleOk m [] xt)
    {vs : List Val} {rss : List (List Ref)} (hvs : m.globals.length = vs.length)
    (hrss : m.elems.length = rss.length) :
    ∃ r, allocModule? ({} : Store H) m [] vs rss = some r := by
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    obtain ⟨fts, hfts⟩ : ∃ fts, (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts :=
      mapM_some fun fn hfn => by
        obtain ⟨t, ⟨hx, -⟩⟩ := exists_of_forall₂ hfuncs fn hfn
        have hx' : ft'[fn.type.toNat]? = some t := by subst hC; exact hx
        have hlt : fn.type.toNat < m.types.length := htypes.length_eq ▸ lt_of_getElem? hx'
        simp [hlt]
    have hlen : ft.length = m.funcs.length ∧ gt.length = m.globals.length ∧
        tt.length = m.tables.length ∧ mt.length = m.memories.length :=
      ⟨hfuncs.length_eq.symm, hglobals.length_eq.symm, htables.length_eq.symm,
        hmems.length_eq.symm⟩
    obtain ⟨xi, hxi⟩ : ∃ xi, m.exports.mapM (instExport?
        (ExternAddr.funcs [] ++ (List.range m.funcs.length).map (({} : Store H).funcs.length + ·))
        (ExternAddr.globals [] ++ (List.range m.globals.length).map (({} : Store H).globals.length + ·))
        (ExternAddr.tables [] ++ (List.range m.tables.length).map (({} : Store H).tables.length + ·))
        (ExternAddr.mems [] ++ (List.range m.memories.length).map (({} : Store H).mems.length + ·))) =
          some xi :=
      mapM_some fun e he => by
        obtain ⟨t, ht⟩ := exists_of_forall₂ hexports e he
        subst hC
        refine instExport?_isSome ht ?_ ?_ ?_ ?_ <;>
          simp [ExternType.funcs, ExternType.globals, ExternType.tables, ExternType.mems,
            ExternAddr.funcs, ExternAddr.globals, ExternAddr.tables, ExternAddr.mems, hlen]
    simp only [allocModule?, hfts, ← hvs, ← hrss, hxi]
    exact ⟨_, rfl⟩

/-! ## Instantiation progress -/

/-- **A valid import-free 2.0 module instantiates in the empty store**, under every host, and
the configuration's store is host-free. -/
theorem instantiate_empty (P : Profile) {m : Module} {xt : List ExternType}
    (hm : ModuleOk m [] xt) (hb : SegBounded m) :
    ∃ c : Config H, (∀ host : HostSemantics H, Instantiate P host ({} : Store H) m [] c) ∧
      HostFree c.store := by
  obtain ⟨C', hglobals, helems, hf, hg⟩ : ∃ C' : Context,
      (∀ g ∈ m.globals, ExprOkConst C' g.init g.type.value) ∧
      (∀ e ∈ m.elems, ∀ ex ∈ e.init, ExprOkConst C' ex (.ref e.type)) ∧
      C'.funcs.length ≤ m.funcs.length ∧ C'.globals = [] := ctx_of_moduleOk hm
  obtain ⟨vs, hvs⟩ : ∃ vs, List.Forall₂ (fun (g : Global) (v : Val) =>
      constExpr? ({} : Store H) (f₀ (H := H) m).module g.init = some v) m.globals vs :=
    forall₂_of_exists fun g hg' => const_denotes (hglobals g hg') hf hg
  obtain ⟨rss, hrss⟩ : ∃ rss, List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        constExpr? ({} : Store H) (f₀ (H := H) m).module ex = some (Val.ref r)) e.init rs)
      m.elems rss :=
    forall₂_of_exists fun e he =>
      forall₂_of_exists fun ex hex => const_ref_denotes (helems e he ex hex) hf hg
  obtain ⟨⟨s', mi⟩, hal⟩ := allocModule_some (H := H) hm hvs.length_eq hrss.length_eq
  refine ⟨⟨s', { module := mi }, expression (runElems m ++ runDatas m ++
    (match m.start with | some x => [Instr.call x] | none => []))⟩, fun host => ?_,
    hostFree_allocModule hal fun _ h => by simp at h⟩
  refine ⟨⟨[], xt, hm, .nil⟩, hb, vs, rss, s', mi, ?_, ?_, hal, rfl⟩
  · exact hvs.imp fun _ _ h => evalExpr_of_constExpr? h
  · exact hrss.imp fun _ _ h => h.imp fun _ _ h => evalExpr_of_constExpr? h

end Silmaril.Proofs.Wasm.Models.V2CoreInstDom
