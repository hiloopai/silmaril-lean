module

public import Silmaril.Wasm.Text.Extensions.Structured.Render
public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructionsSound
public import Silmaril.Wasm.Text.Extensions.SharedMemory.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

set_option maxHeartbeats 1000000 in
theorem moduleSyntax?_sound {Body : Type}
    (function : Core.IdCtx → Declaration.Func ValType Body → Option SExp)
    (F : Core.IdCtx → SExp → Declaration.Func ValType Body → Prop)
    (hfunction : ∀ I f x, function I f = some x → F I x f)
    (shape : Body → Wasm.Expr) {m : Wasm.Extensions.Structured.FunctionModule Body} {x : SExp}
    (h : moduleSyntax? function shape m = some x) : ModuleT F shape x m := by
  unfold moduleSyntax? at h
  dsimp only at h
  split at h
  · cases h
  · next hok =>
    have hok : (Wat.moduleContextAll (m.contextShape shape).coreShape).Ok := by simpa using hok
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
    let I := Wat.moduleContextAll (m.contextShape shape).coreShape
    refine ⟨hok, ts, ims, tags, ms, gs, tables, fs, ds, elems, ss, es, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mapM_sound (fun a x hx => Wat.typeSyntax?_sound hx I) hts
    · exact mapM_sound (fun a x hx => SharedMemory.importSyntax?_sound (I := I) (im := a) (x := x) hx) hims
    · exact mapM_sound (fun a x hx => Wat.tagSyntax?_sound (I := I) (t := a) (x := x) hx) htags
    · exact mapM_sound (fun a x hx => SharedMemory.memorySyntax?_sound hx I) hms
    · exact mapM_sound (fun a x hx => Wat.globalSyntax?_sound hx I) hgs
    · exact mapM_sound (fun a x hx => Wat.tableSyntax?_sound hx I) htables
    · exact mapM_sound (fun a x hx => hfunction I a x hx) hfs
    · exact mapM_sound (fun a x hx => Wat.dataSyntax?_sound hx I) hds
    · exact mapM_sound (fun a x hx => Wat.elemSyntax?_sound hx I) helems
    · exact mapM_sound (fun a x hx => Wat.startSyntax?_sound hx I) hss
    · exact mapM_sound (fun a x hx => Wat.exportSyntax?_sound hx I) hes

end Silmaril.Wasm.Text.Extensions.Structured
