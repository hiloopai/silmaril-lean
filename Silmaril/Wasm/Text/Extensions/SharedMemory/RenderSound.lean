module

public import Silmaril.Wasm.Text.Extensions.SharedMemory.Render
public import Silmaril.Wasm.Text.Extensions.SharedMemory.RenderTypesSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

private theorem mapM_sound {α β : Type} {f : α → Option β} {R : β → α → Prop}
    (hf : ∀ a b, f a = some b → R b a) :
    ∀ {as bs}, as.mapM f = some bs → List.Forall₂ R bs as := by
  intro as
  induction as with
  | nil => intro bs h; cases h; exact .nil
  | cons a as ih =>
    intro bs h
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs', hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons (hf a b hb) (ih hbs)

private theorem liftCoreFields_sound {I : Core.IdCtx} {xs : List SExp} {os : List Core.FieldOut}
    (h : List.Forall₂ (fun x (o : Core.FieldOut) => Core.DeclT I x o.1 o.2.1 o.2.2) xs os) :
    List.Forall₂ (DeclT I) xs (liftCoreFields os) := by
  induction h with
  | nil => exact .nil
  | cons ho _ ih => exact .cons (DeclT.core ho) ih

theorem memorySyntax?_sound {m : MemoryType} {x : SExp}
    (h : memorySyntax? m = some x) (I : Core.IdCtx) :
    DeclT I x (([.mem m.core], { mems := [none] }, []), [], [m.shared]) := by
  unfold memorySyntax? at h
  obtain ⟨xs, hx, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact .memory (memoryTypeSyntax?_sound hx)

theorem importSyntax?_sound {I : Core.IdCtx} {im : Wasm.Extensions.SharedMemory.Import} {x : SExp}
    (h : importSyntax? I im = some x) :
    DeclT I x (([.import_ im.coreShape], Wat.importContext im.coreShape, []), [im.type.isShared], []) := by
  cases im with
  | mk mn n t =>
    cases t
    case memory m =>
      unfold importSyntax? at h
      obtain ⟨src, hs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨field, hn, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xs, hm, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .importMemory (Wat.nameSyntax?_sound hs) (Wat.nameSyntax?_sound hn)
        (memoryTypeSyntax?_sound hm)
    all_goals
      simp only [importSyntax?] at h
      have hc := Wat.importSyntax?_sound h
      simpa [Wasm.Extensions.SharedMemory.Import.coreShape,
        Wasm.Extensions.SharedMemory.ExternType.coreShape,
        Wasm.Extensions.SharedMemory.ExternType.isShared, coreImportFlags, coreMemoryFlags]
        using (DeclT.core hc)

theorem moduleFields_core (m : Wasm.Extensions.SharedMemory.Module) :
    (moduleFields m).map (·.1) = Wat.moduleFieldsAll m.coreShape := by
  simp [moduleFields, liftCoreFields, importFields, memoryFields, Wat.moduleFieldsAll,
    Wat.typeFields, Wat.importFields, Wat.tagFields, Wat.memoryFields, Wat.globalFields,
    Wat.tableFields, Wat.functionFields, Wat.dataFields, Wat.elemFields, Wat.startFields,
    Wat.exportFields, Wasm.Extensions.SharedMemory.Module.coreShape, List.map_map,
    Function.comp_def]

private theorem flatMap_empty {α : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List Bool)) = [] := by
  exact List.flatMap_eq_nil_iff.mpr (by simp)

theorem moduleFields_importFlags (m : Wasm.Extensions.SharedMemory.Module) :
    (moduleFields m).flatMap (·.2.1) = m.imports.map (fun i => i.type.isShared) := by
  simp [moduleFields, liftCoreFields, importFields, memoryFields, coreImportFlags,
    Wat.typeFields, Wat.tagFields, Wat.globalFields, Wat.tableFields, Wat.functionFields,
    Wat.dataFields, Wat.elemFields, Wat.startFields, Wat.exportFields,
    List.flatMap_map, flatMap_empty, ← List.map_eq_flatMap]

theorem moduleFields_memoryFlags (m : Wasm.Extensions.SharedMemory.Module) :
    (moduleFields m).flatMap (·.2.2) = m.memories.map (·.shared) := by
  simp [moduleFields, liftCoreFields, importFields, memoryFields, coreMemoryFlags,
    Wat.typeFields, Wat.tagFields, Wat.globalFields, Wat.tableFields, Wat.functionFields,
    Wat.dataFields, Wat.elemFields, Wat.startFields, Wat.exportFields,
    List.flatMap_map, flatMap_empty, ← List.map_eq_flatMap]

/-- Every emitted declaration is read by the independent extended text grammar;
its per-index shared flags agree with the complete retained module. -/
theorem moduleSyntax?_sound {m : Wasm.Extensions.SharedMemory.Module} {x : SExp}
    (h : moduleSyntax? m = some x) : ModuleT x m := by
  unfold moduleSyntax? at h
  dsimp only at h
  split at h
  · cases h
  · next hok =>
    have hok : (Wat.moduleContextAll m.coreShape).Ok := by simpa using hok
    obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ims, hims, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tags, htags, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ms, hms, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨gs, hgs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tables, htables, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ds, hds, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨elems, helems, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ss, hss, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨es, hes, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    let I := Wat.moduleContextAll m.coreShape
    have hts := mapM_sound (fun a x hx => Wat.typeSyntax?_sound hx I) hts
    have hims := mapM_sound (fun a x hx => importSyntax?_sound (I := I) (im := a) (x := x) hx) hims
    have htags := mapM_sound (fun a x hx => Wat.tagSyntax?_sound (I := I) (t := a) (x := x) hx) htags
    have hms := mapM_sound (fun a x hx => memorySyntax?_sound hx I) hms
    have hgs := mapM_sound (fun a x hx => Wat.globalSyntax?_sound hx I) hgs
    have htables := mapM_sound (fun a x hx => Wat.tableSyntax?_sound hx I) htables
    have hfs := mapM_sound (fun a x hx => Wat.functionSyntax?_sound (I := I) (f := a) (x := x) hx) hfs
    have hds := mapM_sound (fun a x hx => Wat.dataSyntax?_sound hx I) hds
    have helems := mapM_sound (fun a x hx => Wat.elemSyntax?_sound hx I) helems
    have hss := mapM_sound (fun a x hx => Wat.startSyntax?_sound hx I) hss
    have hes := mapM_sound (fun a x hx => Wat.exportSyntax?_sound hx I) hes
    have hts' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ts (Wat.typeFields m.types) := by
      simpa [Wat.typeFields, List.forall₂_map_right_iff] using hts
    have hims' : List.Forall₂ (DeclT I) ims (importFields m.imports) := by
      simpa [importFields, List.forall₂_map_right_iff] using hims
    have htags' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) tags (Wat.tagFields m.tags) := by
      simpa [Wat.tagFields, List.forall₂_map_right_iff] using htags
    have hms' : List.Forall₂ (DeclT I) ms (memoryFields m.memories) := by
      simpa [memoryFields, List.forall₂_map_right_iff] using hms
    have hgs' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) gs (Wat.globalFields m.globals) := by
      simpa [Wat.globalFields, List.forall₂_map_right_iff] using hgs
    have htables' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) tables (Wat.tableFields m.tables) := by
      simpa [Wat.tableFields, List.forall₂_map_right_iff] using htables
    have hfs' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) fs (Wat.functionFields m.funcs) := by
      simpa [Wat.functionFields, List.forall₂_map_right_iff] using hfs
    have hds' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ds (Wat.dataFields m.data) := by
      simpa [Wat.dataFields, List.forall₂_map_right_iff] using hds
    have helems' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) elems (Wat.elemFields m.elems) := by
      simpa [Wat.elemFields, List.forall₂_map_right_iff] using helems
    have hss' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) ss (Wat.startFields m.start) := by
      simpa [Wat.startFields, List.forall₂_map_right_iff] using hss
    have hes' : List.Forall₂ (fun x (o : Text.Core.FieldOut) =>
        Text.Core.DeclT I x o.1 o.2.1 o.2.2) es (Wat.exportFields m.exports) := by
      simpa [Wat.exportFields, List.forall₂_map_right_iff] using hes
    have hfields := List.rel_append (List.rel_append (List.rel_append (List.rel_append
      (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append
      (List.rel_append (liftCoreFields_sound hts') hims') (liftCoreFields_sound htags')) hms')
      (liftCoreFields_sound hgs')) (liftCoreFields_sound htables')) (liftCoreFields_sound hfs'))
      (liftCoreFields_sound hds')) (liftCoreFields_sound helems')) (liftCoreFields_sound hss'))
      (liftCoreFields_sound hes')
    refine ⟨ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es,
      moduleFields m, I, rfl, hfields, ?_⟩
    dsimp only
    rw [moduleFields_core]
    exact ⟨Wat.moduleFieldsAll_layout m.coreShape hok,
      (moduleFields_importFlags m).symm, (moduleFields_memoryFlags m).symm⟩

end Silmaril.Wasm.Text.Extensions.SharedMemory
