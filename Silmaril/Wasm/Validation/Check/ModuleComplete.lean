module

public import Silmaril.Wasm.Validation.Check.Module

@[expose] public section

/-! # Completeness of the module-validator assembly

`checkModule?_complete`: if every part checker is complete (returns exactly the
output of any derivation of its relation), then `checkModule?` returns the module
type of any `ModuleOk` derivation. All part relations are functional in their
outputs, so the exact-output formulation is used throughout.
-/

namespace Silmaril.Wasm.Validation

/-- Completeness of each part checker (converse of `ModuleCheckers.Sound`). -/
structure ModuleCheckers.Complete (K : ModuleCheckers) : Prop where
  types : ∀ {C rts dts}, TypesOk C rts dts → K.types? C rts = some dts
  import_ : ∀ {C im xt}, ImportOk C im xt → K.import? C im = some xt
  tag : ∀ {C x d}, TagOk C x d → K.tag? C x = some d
  globals : ∀ {C gs gts}, GlobalsOk C gs gts → K.globals? C gs = some gts
  mem : ∀ {mt}, MemOk mt → K.mem mt = true
  table : ∀ {C t tt}, TableOk C t tt → K.table? C t = some tt
  func : ∀ {C f d}, FuncOk C f d → K.func C f d = true
  data : ∀ {C d}, DataOk C d → K.data C d = true
  elem : ∀ {C e rt}, ElemOk C e rt → K.elem? C e = some rt
  start : ∀ {C x}, StartOk C x → K.start C x = true
  export_ : ∀ {C e xt}, ExportOk C e xt → K.export? C e = some xt

theorem allPairs_complete {α β : Type _} {p : α → β → Bool} {R : α → β → Prop}
    (hp : ∀ a b, R a b → p a b = true) {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : allPairs p as bs = true := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [allPairs, Bool.and_eq_true]; exact ⟨hp _ _ h, ih⟩

theorem List.mapM_some_of_forall₂ {α β : Type _} {f : α → Option β} {R : α → β → Prop}
    (hf : ∀ a b, R a b → f a = some b) {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : as.mapM f = some bs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [List.mapM_cons, hf _ _ h, ih]

theorem List.Forall₂.eq_map {α β : Type _} {R : α → β → Prop} {g : α → β}
    (hR : ∀ a b, R a b → b = g a) {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : bs = as.map g := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, ← hR _ _ h, ← ih]

theorem checkModule?_complete {K : ModuleCheckers} {m : Module} {mt : CModuleType}
    (hK : K.Complete) (h : ModuleOk m mt) : checkModule? K m = some mt := by
  obtain ⟨htypes, himports, rfl, rfl, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE
  have hfd : m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type) = some fdts :=
    List.mapM_some_of_forall₂ (fun _ _ hf => by
      cases hf with | mk hd _ _ _ => exact hd) hfuncs
  have hrts : rts = m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type :=
    List.Forall₂.eq_map (g := fun e => (moduleCtx' m dts xtI fdts).closeRef e.type)
      (fun _ _ he => he.1) helems
  subst hrts
  have htags' : List.Forall₂ (TagOk (moduleCtx' m dts xtI fdts)) m.tags jts := htags
  have hglobals' : GlobalsOk (moduleCtx' m dts xtI fdts) m.globals gts := hglobals
  have htables' : List.Forall₂ (TableOk (moduleCtx' m dts xtI fdts)) m.tables tts := htables
  generalize hCdef : moduleCtx m (moduleCtx' m dts xtI fdts) xtI jts gts tts
    (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) = C
  have hfuncs' : List.Forall₂ (FuncOk C) m.funcs fdts := hCdef ▸ hfuncs
  have hdata' : ∀ d ∈ m.data, DataOk C d := hCdef ▸ hdata
  have helems' : List.Forall₂ (ElemOk C) m.elems
      (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) := hCdef ▸ helems
  have hstart' : ∀ x, m.start = some x → StartOk C x := hCdef ▸ hstart
  have hexports' : List.Forall₂ (ExportOk C) m.exports xtE := hCdef ▸ hexports
  have hc : (m.memories.all K.mem && allPairs (K.func C) m.funcs fdts &&
      m.data.all (K.data C) &&
      allPairs (fun e rt => K.elem? C e == some rt) m.elems
        (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type) &&
      m.start.all (K.start C)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨fun x hx => hK.mem (hmems x hx), allPairs_complete (fun _ _ h => hK.func h) hfuncs'⟩,
      fun d hd => hK.data (hdata' d hd)⟩,
      allPairs_complete (fun _ _ he => by simp [hK.elem he]) helems'⟩, ?_⟩
    cases hs : m.start with
    | none => rfl
    | some x => simpa using hK.start (hstart' x hs)
  simp only [checkModule?, Option.bind_eq_bind, hK.types htypes,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.import_ h) himports, Option.bind_some, hfd,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.tag h) htags', hK.globals hglobals',
    List.mapM_some_of_forall₂ (fun _ _ h => hK.table h) htables', hCdef, hc, ite_true,
    List.mapM_some_of_forall₂ (fun _ _ h => hK.export_ h) hexports', hnd]

theorem checkModule?_isSome_iff {K : ModuleCheckers} {m : Module}
    (hS : K.Sound) (hC : K.Complete) : (checkModule? K m).isSome ↔ ModuleValid m :=
  ⟨checkModuleValid_sound hS, fun ⟨_, h⟩ => by rw [checkModule?_complete hC h]; rfl⟩

/-- Decidability of module validity from a sound and complete set of part checkers. -/
def decidableModuleValid {K : ModuleCheckers} (hS : K.Sound) (hC : K.Complete) (m : Module) :
    Decidable (ModuleValid m) :=
  decidable_of_iff _ (checkModule?_isSome_iff (m := m) hS hC)

end Silmaril.Wasm.Validation
