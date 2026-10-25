module

public import Silmaril.Wasm.Binaryen.InlReverseIH

@[expose] public section

/-! # Runtime context closure for normalized reverse progress

Positive source matches use the existing context-stable initialization chain.
Target-only administrative reductions retain the original and strictly decrease
the actual target code rank, also after adding runtime contexts.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

namespace ReverseProgress

theorem context {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (vs : List Val)
    {oldRest newRest : List Admin} (rest : LN p oldRest newRest) :
    ReverseProgress p P .gen
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨target.store, target.frame, vals vs ++ target.code ++ newRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨frames, code⟩, stores, rank⟩
  · exact .inl (matched.context vs rest)
  · refine .inr ⟨⟨normalized.store, normalized.frame,
      vals vs ++ normalized.code ++ newRest⟩, init.context vs newRest,
      ⟨frames, LN.append (LN.append (LN.of_vals vs) code) rest⟩, stores, ?_⟩
    simp only [aszs_append]
    omega

theorem label {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (n : Nat) (cont : List Instr) :
    ReverseProgress p P .gen
      ⟨original.store, original.frame, [.label n cont original.code]⟩
      ⟨target.store, target.frame, [.label n cont target.code]⟩
      ⟨next.store, next.frame, [.label n cont next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨frames, code⟩, stores, rank⟩
  · exact .inl (matched.label n cont)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.label n cont normalized.code]⟩,
      init.label n cont, ⟨frames, .cons (.label code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz_label]
    omega

theorem handler {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (n : Nat) (catches : List Catch) :
    ReverseProgress p P .gen
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨target.store, target.frame, [.handler n catches target.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨frames, code⟩, stores, rank⟩
  · exact .inl (matched.handler n catches)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
      init.handler n catches, ⟨frames, .cons (.handler code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz]
    omega

theorem frame_gen {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (n : Nat) (outer : Frame) :
    ReverseProgress p P .gen
      ⟨original.store, outer, [.frame n original.frame original.code]⟩
      ⟨target.store, outer, [.frame n target.frame target.code]⟩
      ⟨next.store, outer, [.frame n next.frame next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨frames, code⟩, stores, rank⟩
  · exact .inl (matched.frame_gen n outer)
  · refine .inr ⟨⟨normalized.store, outer, [.frame n normalized.frame normalized.code]⟩,
      init.frame n outer, ⟨rfl, ?_⟩, stores, ?_⟩
    · rw [frames]
      exact .cons (.frame (.gen code)) .nil
    · simp only [aszs_cons, aszs_nil, asz]
      omega

theorem frame_caller {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (n : Nat) (outer : Frame) :
    ReverseProgress p P .gen
      ⟨original.store, outer, [.frame n original.frame original.code]⟩
      ⟨target.store, outer, [.frame n target.frame target.code]⟩
      ⟨next.store, outer, [.frame n next.frame next.code]⟩ := by
  rcases progress with matched |
      ⟨normalized, init, ⟨moduleEq, locals, E, extra, frames, code⟩, stores, rank⟩
  · exact .inl (matched.frame_caller n outer)
  · refine .inr ⟨⟨normalized.store, outer, [.frame n normalized.frame normalized.code]⟩,
      init.frame n outer, ⟨rfl, ?_⟩, stores, ?_⟩
    · rw [frames]
      exact .cons (.frame (.g moduleEq locals extra code)) .nil
    · simp only [aszs_cons, aszs_nil, asz]
      omega

end ReverseProgress

end Silmaril.Wasm.Binaryen.InlR
