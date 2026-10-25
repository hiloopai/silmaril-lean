module

public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Module-level validator assembly

`checkModule? K m` assembles a `Module_ok` checker from per-part checkers `K`
(written elsewhere), following `ModuleOk.mk` step by step. Soundness is relative
to the soundness of the part checkers (`ModuleCheckers.Sound`).

Element segments: `ElemOk C e rt` is checked in the full context `C`, whose
`ELEMS` is `rts` itself. Since `rt = C.closeRef e.type` depends only on `TYPES`,
the checker first computes `rts` by closing the element types, builds `C`, and then
requires `K.elem? C e = some rt` for each segment.
-/

namespace Silmaril.Wasm.Validation

/-- The per-part checkers a module validator is assembled from. -/
structure ModuleCheckers where
  types? : Context → List RecType → Option (List DefType)
  import? : Context → Import → Option CExternType
  tag? : Context → TagType → Option DefType
  globals? : Context → List Global → Option (List CGlobalType)
  mem : MemoryType → Bool
  table? : Context → Table → Option CTableType
  func : Context → Func → DefType → Bool
  data : Context → Data → Bool
  elem? : Context → Elem → Option CRefType
  start : Context → FuncIdx → Bool
  export? : Context → Export → Option CExternType

/-- Soundness of each part checker. -/
structure ModuleCheckers.Sound (K : ModuleCheckers) : Prop where
  types : ∀ {C rts dts}, K.types? C rts = some dts → TypesOk C rts dts
  import_ : ∀ {C im xt}, K.import? C im = some xt → ImportOk C im xt
  tag : ∀ {C x d}, K.tag? C x = some d → TagOk C x d
  globals : ∀ {C gs gts}, K.globals? C gs = some gts → GlobalsOk C gs gts
  mem : ∀ {mt}, K.mem mt = true → MemOk mt
  table : ∀ {C t tt}, K.table? C t = some tt → TableOk C t tt
  func : ∀ {C f d}, K.func C f d = true → FuncOk C f d
  data : ∀ {C d}, K.data C d = true → DataOk C d
  elem : ∀ {C e rt}, K.elem? C e = some rt → ElemOk C e rt
  start : ∀ {C x}, K.start C x = true → StartOk C x
  export_ : ∀ {C e xt}, K.export? C e = some xt → ExportOk C e xt

/-! ## List helpers -/

/-- Pointwise Boolean check on two lists of equal length. -/
def allPairs {α β : Type _} (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && allPairs p as bs
  | _, _ => false

theorem allPairs_sound {α β : Type _} {p : α → β → Bool} {R : α → β → Prop}
    (hp : ∀ {a b}, p a b = true → R a b) :
    ∀ {as : List α} {bs : List β}, allPairs p as bs = true → List.Forall₂ R as bs
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [allPairs, Bool.and_eq_true] at h
    exact .cons (hp h.1) (allPairs_sound hp h.2)
  | [], _ :: _, h => by simp [allPairs] at h
  | _ :: _, [], h => by simp [allPairs] at h

theorem List.mapM_some_forall₂ {α β : Type _} {f : α → Option β} {R : α → β → Prop}
    (hf : ∀ {a b}, f a = some b → R a b) :
    ∀ {as : List α} {bs : List β}, as.mapM f = some bs → List.Forall₂ R as bs
  | [], bs, h => by
    simp at h; subst h; exact .nil
  | a :: as, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    exact .cons (hf hb) (List.mapM_some_forall₂ hf hbs)

/-! ## The checker -/

/-- The context `C'` of `Module_ok` (`hC'`). -/
def moduleCtx' (m : Module) (dts : List DefType) (xtI : List CExternType)
    (fdts : List DefType) : Context :=
  { types := dts, globals := CExternType.globals xtI,
    funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m }

/-- The context `C` of `Module_ok` (`hC`). -/
def moduleCtx (m : Module) (C' : Context) (xtI : List CExternType) (jts : List DefType)
    (gts : List CGlobalType) (tts : List CTableType) (rts : List CRefType) : Context :=
  { C' with
    tags := CExternType.tags xtI ++ jts, globals := C'.globals ++ gts,
    mems := CExternType.mems xtI ++ m.memories,
    tables := CExternType.tables xtI ++ tts,
    datas := m.data.map fun _ => (), elems := rts }

/-- `Module_ok` checker assembled from part checkers. -/
def checkModule? (K : ModuleCheckers) (m : Module) : Option CModuleType := do
  let dts ← K.types? {} m.types
  let xtI ← m.imports.mapM (K.import? { types := dts })
  let fdts ← m.funcs.mapM (fun f => ({ types := dts } : Context).type? f.type)
  let C' := moduleCtx' m dts xtI fdts
  let jts ← m.tags.mapM (K.tag? C')
  let gts ← K.globals? C' m.globals
  let tts ← m.tables.mapM (K.table? C')
  let rts := m.elems.map fun e => C'.closeRef e.type
  let C := moduleCtx m C' xtI jts gts tts rts
  if m.memories.all K.mem && allPairs (K.func C) m.funcs fdts && m.data.all (K.data C) &&
      allPairs (fun e rt => K.elem? C e == some rt) m.elems rts && m.start.all (K.start C) then
    let xtE ← m.exports.mapM (K.export? C)
    if (m.exports.map Export.name).Nodup then some ⟨xtI, xtE⟩ else none
  else none

theorem checkModule?_sound {K : ModuleCheckers} {m : Module} {mt : CModuleType}
    (hK : K.Sound) (h : checkModule? K m = some mt) : ModuleOk m mt := by
  simp only [checkModule?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨dts, hdts, xtI, hxtI, fdts, hfdts, jts, hjts, gts, hgts, tts, htts, h⟩ := h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨hmem, hfun⟩, hdat⟩, hel⟩, hst⟩ := hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨xtE, hxtE, h⟩ := h
    split at h
    · rename_i hnd
      cases h
      exact ModuleOk.mk (C' := moduleCtx' m dts xtI fdts)
        (C := moduleCtx m (moduleCtx' m dts xtI fdts) xtI jts gts tts
          (m.elems.map fun e => (moduleCtx' m dts xtI fdts).closeRef e.type)) (hK.types hdts)
        (List.mapM_some_forall₂ hK.import_ hxtI) rfl rfl
        (List.mapM_some_forall₂ hK.tag hjts) (hK.globals hgts)
        (fun mt hm => hK.mem (hmem mt hm))
        (List.mapM_some_forall₂ hK.table htts)
        (allPairs_sound hK.func hfun)
        (fun d hd => hK.data (hdat d hd))
        (allPairs_sound (fun h => hK.elem (eq_of_beq h)) hel)
        (fun x hx => by
          rw [hx] at hst
          exact hK.start (by simpa using hst))
        (List.mapM_some_forall₂ hK.export_ hxtE) hnd
    · cases h
  · cases h

theorem checkModuleValid_sound {K : ModuleCheckers} {m : Module} (hK : K.Sound)
    (h : (checkModule? K m).isSome) : ModuleValid m := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.1 h
  exact ⟨mt, checkModule?_sound hK hmt⟩

end Silmaril.Wasm.Validation
