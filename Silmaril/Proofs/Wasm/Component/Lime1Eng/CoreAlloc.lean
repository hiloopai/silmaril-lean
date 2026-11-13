module

public import Silmaril.Proofs.Wasm.Component.Lime1Eng.Segs
public import Silmaril.Proofs.Wasm.Component.Lime1Inst.BridgeG

/-!
# The Core 3.0 allocation of the residue is the image of the Lime1 allocation

Core 3.0's executable `prepare?` of a global-free module evaluates the table initializers
(`ref.null`), the element initializers (`ref.func`, which read only the frame) and allocates the
module. When Lime1 allocates the same module (`allocate?`), the copied `allocModule_core` computes
the Core allocation from the Lime1 one, so the Core store and frame that `prepare?` returns are
related to the Lime1 allocation by `Rel` (`rel_of_prepare`). No segment is resolved: this is the
half of the copied `prepare_parts` before the segment run, from allocation alone.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm Silmaril.Wasm.Lime1
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst)
open Silmaril.Wasm.Execution.Core (evalConst? evalExprs? evalExprss? allocModule?)
open Silmaril.Proofs.Wasm.Component.Lime1Inst (withElems frame0 funcrefElem)

variable {H : Type}

/-- `ref.func` initializers keep the store and the frame. -/
theorem evalExprs_refFunc {S : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ {es : List Silmaril.Wasm.Expr} {S' : Silmaril.Wasm.Execution.Core.Store H}
      {F' : Silmaril.Wasm.Execution.Core.Frame} {rs : List Silmaril.Wasm.Execution.Core.Ref},
      (∀ e ∈ es, ∃ x, e = Lime1.funcRef x) → evalExprs? evalConst? S F es = some (S', F', rs) →
      S' = S ∧ F' = F
  | [], _, _, _, _, h => by
    simp only [evalExprs?, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  | e :: es, S', F', _, hx, h => by
    obtain ⟨x, rfl⟩ := hx e (by simp)
    have hrest : ∀ e ∈ es, ∃ x, e = Lime1.funcRef x := fun e he => hx e (by simp [he])
    rcases ha : F.module.funcs[x.toNat]? with _ | a
    · simp [evalExprs?, evalConst?, Silmaril.Wasm.Execution.Core.constExpr?,
        Silmaril.Wasm.Execution.Core.constInstr?, Lime1.funcRef, ha] at h
    · have h' : ∃ S'' F'' rs', evalExprs? evalConst? S F es = some (S'', F'', rs') ∧
          (S'', F'') = (S', F') := by
        simp only [evalExprs?, evalConst?, Silmaril.Wasm.Execution.Core.constExpr?,
          Silmaril.Wasm.Execution.Core.constInstr?, Lime1.funcRef, ha, List.foldlM_cons,
          List.foldlM_nil, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          List.nil_append] at h
        split at h
        · cases h
        · rename_i S'' F'' rs' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨S'', F'', rs', hr, by rw [h.1, h.2.1]⟩
      obtain ⟨S'', F'', rs', hr, heq⟩ := h'
      obtain ⟨rfl, rfl⟩ := evalExprs_refFunc hrest hr
      exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

theorem evalExprs_length {S : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ {ess : List (List Silmaril.Wasm.Expr)} {S' : Silmaril.Wasm.Execution.Core.Store H}
      {F' : Silmaril.Wasm.Execution.Core.Frame} {rss : List (List Silmaril.Wasm.Execution.Core.Ref)},
      (∀ es ∈ ess, ∀ e ∈ es, ∃ x, e = Lime1.funcRef x) →
      evalExprss? evalConst? S F ess = some (S', F', rss) → S' = S ∧ F' = F ∧ rss.length = ess.length
  | [], _, _, _, _, h => by
    simp only [evalExprss?, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, by rw [← h.2.2]; rfl⟩
  | es :: ess, _, _, _, hx, h => by
    have h' : ∃ S₁ F₁ rs S₂ F₂ rss, evalExprs? evalConst? S F es = some (S₁, F₁, rs) ∧
        evalExprss? evalConst? S₁ F₁ ess = some (S₂, F₂, rss) := by
      simp only [evalExprss?] at h
      split at h
      · cases h
      · rename_i S₁ F₁ rs h₁
        split at h
        · cases h
        · rename_i S₂ F₂ rss h₂
          exact ⟨S₁, F₁, rs, S₂, F₂, rss, h₁, h₂⟩
    obtain ⟨S₁, F₁, rs, S₂, F₂, rss, h₁, h₂⟩ := h'
    obtain ⟨rfl, rfl⟩ := evalExprs_refFunc (hx es (by simp)) h₁
    obtain ⟨rfl, rfl, hl⟩ := evalExprs_length (fun es' h' => hx es' (by simp [h'])) h₂
    simp only [evalExprss?, h₁, h₂, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, by simp [hl]⟩

/-- The parts of a successful executable preparation of a global-free module. -/
theorem prepare?_parts {s : Silmaril.Wasm.Execution.Core.Store H} {m : Silmaril.Wasm.Module}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr} {c : Silmaril.Wasm.Execution.Core.Config H}
    {st : Option FuncIdx} (hg : m.globals = [])
    (h : Silmaril.Wasm.Execution.Core.prepare? evalConst? s m xas = some (c, st)) :
    ∃ S₂ F₂ refsT S₃ F₃ refsE mi,
      evalExprs? evalConst? s (frame0 s m xas) (m.tables.map Silmaril.Wasm.Table.init) =
        some (S₂, F₂, refsT) ∧
      evalExprss? evalConst? S₂ F₂ (m.elems.map Silmaril.Wasm.Elem.init) = some (S₃, F₃, refsE) ∧
      allocModule? S₃ m xas [] refsT refsE = some (c.store, mi) ∧ c.frame = { module := mi } := by
  unfold Silmaril.Wasm.Execution.Core.prepare? at h
  rw [hg] at h
  simp only [List.map_nil, Silmaril.Wasm.Execution.Core.evalGlobals?] at h
  split at h
  · split at h
    · cases h
    · rename_i S₂ F₂ refsT h₂
      split at h
      · cases h
      · rename_i S₃ F₃ refsE h₃
        split at h
        · cases h
        · rename_i S₄ mi h₄
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨S₂, F₂, refsT, S₃, F₃, refsE, mi, h₂, h₃, h₄, rfl⟩
  · cases h

/-- The element initializers of a module whose `funcref`-typed segments are Lime1 images. -/
theorem elems_funcRef {L : Lime1.Module} {es : List Silmaril.Wasm.Elem}
    (hes : es.map funcrefElem = L.toCore.elems) :
    ∀ es' ∈ (withElems L es).elems.map Silmaril.Wasm.Elem.init, ∀ e ∈ es', ∃ x, e = Lime1.funcRef x := by
  intro es' hes' e he
  have hinit : es.map Silmaril.Wasm.Elem.init = L.elems.map fun e => e.init.map Lime1.funcRef := by
    have h := congrArg (List.map Silmaril.Wasm.Elem.init) hes
    simpa [List.map_map, funcrefElem, Function.comp_def, Lime1.Module.toCore,
      Lime1.Elem.toCore] using h
  have hes'' : es' ∈ L.elems.map fun e => e.init.map Lime1.funcRef := hinit ▸ hes'
  obtain ⟨e', -, rfl⟩ := List.mem_map.mp hes''
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  exact ⟨x, rfl⟩

/-- The allocation step of the Core 3.0 preparation of a global-free Lime1 image. -/
theorem prepare_alloc {before : Silmaril.Wasm.Lime1.Execution.Store Nat} {L : Lime1.Module}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal} (hg : L.globals = [])
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = L.toCore.elems)
    {c : Silmaril.Wasm.Execution.Core.Config Nat} {st : Option FuncIdx}
    (hp : Silmaril.Wasm.Execution.Core.prepare? evalConst? before.toCore (withElems L es)
      (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) = some (c, st)) :
    ∃ refsE mi, allocModule? before.toCore (withElems L es)
        (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) []
        (L.tables.map fun _ => .null) refsE = some (c.store, mi) ∧
      c.frame = { module := mi } ∧ refsE.length = es.length := by
  have hgW : (withElems L es).globals = [] := by simp [Lime1.Module.toCore, hg]
  obtain ⟨S₂, F₂, refsT, S₃, F₃, refsE, mi, h₂, h₃, h₄, hF⟩ := prepare?_parts hgW hp
  have hT := Silmaril.Wasm.Execution.Core.evalExprs?_complete
    Silmaril.Proofs.Wasm.Instantiation.evalConst?_evalComplete
    (Silmaril.Wasm.Lime1.Execution.evalExprs_tables (P := Silmaril.Wasm.Numerics.Profile.spec)
      (tgt := Silmaril.Wasm.SingleThreaded.Det.noHost) before.toCore
      (frame0 before.toCore (withElems L es)
        (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore)) L.tables)
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.constExpr_tables L es)
  have h₂' := Option.some.inj (hT.symm.trans h₂)
  simp only [Prod.mk.injEq] at h₂'
  obtain ⟨rfl, rfl, rfl⟩ := h₂'
  obtain ⟨rfl, rfl, hlenE⟩ := evalExprs_length (elems_funcRef hes) h₃
  exact ⟨refsE, mi, h₄, hF, by simpa using hlenE⟩

/-- The Lime1 allocation computes a Core 3.0 allocation of the image, related to it. -/
theorem alloc_lime1 {before : Silmaril.Wasm.Lime1.Execution.Store Nat} {L : Lime1.Module}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal}
    {A : Silmaril.Wasm.Lime1.Execution.Store Nat} {mod : ModuleInst} (hg : L.globals = [])
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = L.toCore.elems)
    (hal : Silmaril.Wasm.Lime1.Execution.allocate? before L imports = some (A, mod))
    {refsE : List (List Silmaril.Wasm.Execution.Core.Ref)} (hlenE : refsE.length = es.length) :
    ∃ Sa mi, allocModule? before.toCore (withElems L es)
        (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) []
        (L.tables.map fun _ => .null) refsE = some (Sa, mi) ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase Sa = A.toCore ∧
      Sa.globals = A.globals.map GlobalInst.toCore ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInst.erase mi = mod.toCore := by
  have hlen : es.length = L.toCore.elems.length := by rw [← hes, List.length_map]
  obtain ⟨exports, funcs, hex, hfn, hmod, halloc⟩ :=
    Silmaril.Wasm.Lime1.Execution.allocate?_inv hg hal
  obtain ⟨Sa0, mi0, hAM0, hmi, -, -, -, -, hSaG0, hSaS0⟩ :=
    Silmaril.Wasm.Lime1.Execution.allocModule_core (refsE := refsE) hg hex hfn
      (by rw [hlenE, hlen]; simp [Lime1.Module.toCore])
  obtain ⟨Sa, hAM, hre⟩ := Silmaril.Proofs.Wasm.Component.Lime1Inst.allocModule?_elems hlen hAM0
  have hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase Sa = A.toCore := by
    rw [Silmaril.Proofs.Wasm.Component.Lime1Inst.erase_retype hre, hSaS0, halloc]
  have hG : Sa.globals = A.globals.map GlobalInst.toCore := by
    rw [hre.1, hSaG0, halloc]; rfl
  exact ⟨Sa, mi0, hAM, hS, hG, by rw [hmod]; exact hmi⟩

/-- **The Core 3.0 allocation is related to the Lime1 allocation.** -/
theorem rel_of_prepare {before : Silmaril.Wasm.Lime1.Execution.Store Nat} {L : Lime1.Module}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal}
    {A : Silmaril.Wasm.Lime1.Execution.Store Nat} {mod : ModuleInst} (hg : L.globals = [])
    {es : List Silmaril.Wasm.Elem} (hes : es.map funcrefElem = L.toCore.elems)
    (hal : Silmaril.Wasm.Lime1.Execution.allocate? before L imports = some (A, mod))
    {c : Silmaril.Wasm.Execution.Core.Config Nat} {st : Option FuncIdx}
    (hp : Silmaril.Wasm.Execution.Core.prepare? evalConst? before.toCore (withElems L es)
      (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) = some (c, st)) :
    Rel c.store c.frame A mod := by
  obtain ⟨refsE, mi, h₄, hF, hlenE⟩ := prepare_alloc hg hes hp
  obtain ⟨Sa, mi', hAM, hS, hG, hmi⟩ := alloc_lime1 hg hes hal hlenE
  have hc : (Sa, mi') = (c.store, mi) := Option.some.inj (hAM.symm.trans h₄)
  have hSa : Sa = c.store := congrArg Prod.fst hc
  have hmi0 : mi' = mi := congrArg Prod.snd hc
  have hS' : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase c.store = A.toCore := hSa ▸ hS
  have hG' : c.store.globals = A.globals.map GlobalInst.toCore := hSa ▸ hG
  have hmi' : Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInst.erase c.frame.module =
      mod.toCore := by rw [hF, ← hmi0]; exact hmi
  exact ⟨hG', congrArg Silmaril.Wasm.Execution.Core.Store.tables hS',
    congrArg Silmaril.Wasm.Execution.Core.Store.mems hS',
    congrArg Silmaril.Wasm.Execution.Core.ModuleInst.globals hmi',
    congrArg Silmaril.Wasm.Execution.Core.ModuleInst.tables hmi',
    congrArg Silmaril.Wasm.Execution.Core.ModuleInst.mems hmi'⟩

end Silmaril.Proofs.Wasm.Component.Lime1Eng
