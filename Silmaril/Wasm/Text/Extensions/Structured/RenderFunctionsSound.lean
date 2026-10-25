module

public import Silmaril.Wasm.Text.Extensions.Structured.RenderFunctions
public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructionsSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

theorem functionSyntax?_sound {Leaf : Type} {G : Core.IdCtx → List SExp → Leaf → Prop}
    (leaf : Core.IdCtx → Leaf → Option (List SExp))
    (hleaf : ∀ I i xs, leaf I i = some xs → G I xs i)
    {I : Core.IdCtx} {f : Declaration.Func ValType (Wasm.Extensions.Structured.Expr Leaf)} {x : SExp}
    (h : functionSyntax? leaf I f = some x) : FuncT G I x f := by
  unfold functionSyntax? at h
  obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  · next hlen =>
    have hlen : f.locals.length < 2 ^ 32 := Nat.lt_of_not_ge hlen
    dsimp only at h
    split at h
    · cases h
    · next hok =>
      have hok : (I ++ ({ locals := List.replicate ft.params.length none ++
          (List.map (fun (_ : ValType) => (none : Option String)) f.locals) } : Core.IdCtx)).Ok := by simpa using hok
      obtain ⟨tx, htx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ls, hls, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨body, hbody, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hl := mapM_sound (fun t x ht => Wat.valueSyntax?_sound ht I) hls
      have ht := Core.TypeUseT.ofType (Wat.indexSyntax?_sound htx _) (Wat.functionType?_sound hft)
      have hloc : Core.Concat (Core.LocalT I) [L (K "local" :: ls)]
          (f.locals.map (·, none)) :=
        ⟨[f.locals.map (·, none)], .cons (.inr ⟨ls, f.locals, rfl, hl, rfl⟩) .nil,
          by simp, by simpa using hlen⟩
      have hb : InstrsT G _ body.flatten f.body := .of_forall₂
        (mapM_sound (fun i xs hi => instructionTree?_sound leaf hleaf (i := i) (xs := xs) hi) hbody)
      simpa [List.map_map, Function.comp_def] using FuncT.func ht hloc
        (by simpa only [List.map_map, Function.comp_def] using hok)
        (by simpa only [List.map_map, Function.comp_def] using hb)

end Silmaril.Wasm.Text.Extensions.Structured
