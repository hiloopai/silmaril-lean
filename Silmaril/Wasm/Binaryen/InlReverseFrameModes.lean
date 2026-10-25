module

public import Silmaril.Wasm.Binaryen.InlReverseFrame
public import Silmaril.Wasm.Binaryen.InlReverseProgress

@[expose] public section

/-! # Nested activation exits and contexts in every reverse mode

Activation exits do not inspect the enclosing frame. Their exact source run
therefore applies when the enclosing caller or relocated callee has different
locals. Recursive bodies may themselves use generic or changed-caller mode.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

theorem reverse_caller_frame {n : Nat} {s t : Store H} {fo oldFrame newFrame : Frame}
    {E : List (Option Val)} {oldBody newBody : List Admin} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (related : FR p oldFrame newFrame oldBody newBody)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.frame n newFrame newBody) next) :
    (∃ bodyNext : Config H, args = [] ∧ FR p oldFrame newFrame oldBody newBody ∧
      Step P Det.noHost ⟨t, newFrame, newBody⟩ bodyNext ∧
      next = ⟨bodyNext.store, ⟨fo.locals ++ E, p.mi⟩,
        [.frame n bodyNext.frame bodyNext.code]⟩) ∨
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.frame n oldFrame oldBody]⟩ next := by
  rcases reverse_frame_core (oldOuter := fo) stores related selected with
    contextual | ⟨code, steps, rfl, flat⟩
  · exact .inl contextual
  · exact .inr (ReverseMatch.of_steps steps
      ⟨moduleEq, locals, E, extra, rfl, LG.of_flatRes flat⟩ stores)

theorem reverse_callee_frame {d n : Nat} {s t : Store H} {fo oldFrame newFrame : Frame}
    {L : List (Option Val)} {oldBody newBody : List Admin} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (prefixLength : L.length = p.base)
    (locals : fo.locals.length = p.ext) (stores : SR p s t)
    (related : FR p oldFrame newFrame oldBody newBody)
    (selected : Det.Head P t ⟨L ++ fo.locals, p.mi⟩ args (.frame n newFrame newBody) next) :
    (∃ bodyNext : Config H, args = [] ∧ FR p oldFrame newFrame oldBody newBody ∧
      Step P Det.noHost ⟨t, newFrame, newBody⟩ bodyNext ∧
      next = ⟨bodyNext.store, ⟨L ++ fo.locals, p.mi⟩,
        [.frame n bodyNext.frame bodyNext.code]⟩) ∨
    ReverseMatch p P (.i d L) ⟨s, fo, vals args ++ [.frame n oldFrame oldBody]⟩ next := by
  rcases reverse_frame_core (oldOuter := fo) stores related selected with
    contextual | ⟨code, steps, rfl, flat⟩
  · exact .inl contextual
  · exact .inr (ReverseMatch.of_steps steps
      ⟨moduleEq, prefixLength, locals, rfl, LI.of_flatRes flat⟩ stores)

namespace ReverseProgress

/-- A frame context changes reverse mode only through its runtime relation.
The actual source steps, target initialization and decreasing stutters lift
uniformly, even when the enclosing frames differ. -/
theorem frame_mode {innerMode outerMode : Mode} {original target next : Config H}
    (progress : ReverseProgress p P innerMode original target next)
    (n : Nat) (oldOuter newOuter : Frame)
    (relation : ∀ {s t : Store H} {oldFrame newFrame : Frame} {oldCode newCode : List Admin},
      MR p innerMode ⟨s, oldFrame, oldCode⟩ ⟨t, newFrame, newCode⟩ →
      MR p outerMode ⟨s, oldOuter, [.frame n oldFrame oldCode]⟩
        ⟨t, newOuter, [.frame n newFrame newCode]⟩) :
    ReverseProgress p P outerMode
      ⟨original.store, oldOuter, [.frame n original.frame original.code]⟩
      ⟨target.store, newOuter, [.frame n target.frame target.code]⟩
      ⟨next.store, newOuter, [.frame n next.frame next.code]⟩ := by
  rcases progress with ⟨oldNext, normalized, steps, init, runtime, stores⟩ |
      ⟨normalized, init, runtime, stores, rank⟩
  · exact .inl ⟨⟨oldNext.store, oldOuter, [.frame n oldNext.frame oldNext.code]⟩,
      ⟨normalized.store, newOuter, [.frame n normalized.frame normalized.code]⟩,
      tg_frame steps n oldOuter, init.frame n newOuter, relation runtime, stores⟩
  · refine .inr ⟨⟨normalized.store, newOuter, [.frame n normalized.frame normalized.code]⟩,
      init.frame n newOuter, relation runtime, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz]
    omega

theorem caller_frame_gen {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (n : Nat)
    (fo : Frame) {E : List (Option Val)} (moduleEq : fo.module = p.mi)
    (locals : fo.locals.length = p.base) (extra : E.length = p.ext) :
    ReverseProgress p P .g
      ⟨original.store, fo, [.frame n original.frame original.code]⟩
      ⟨target.store, ⟨fo.locals ++ E, p.mi⟩, [.frame n target.frame target.code]⟩
      ⟨next.store, ⟨fo.locals ++ E, p.mi⟩, [.frame n next.frame next.code]⟩ := by
  apply progress.frame_mode n fo ⟨fo.locals ++ E, p.mi⟩
  intro s t oldFrame newFrame oldCode newCode runtime
  obtain ⟨rfl, code⟩ := runtime
  exact ⟨moduleEq, locals, E, extra, rfl, .head (.frame (.gen code)) .nil⟩

theorem caller_frame_caller {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (n : Nat)
    (fo : Frame) {E : List (Option Val)} (moduleEq : fo.module = p.mi)
    (locals : fo.locals.length = p.base) (extra : E.length = p.ext) :
    ReverseProgress p P .g
      ⟨original.store, fo, [.frame n original.frame original.code]⟩
      ⟨target.store, ⟨fo.locals ++ E, p.mi⟩, [.frame n target.frame target.code]⟩
      ⟨next.store, ⟨fo.locals ++ E, p.mi⟩, [.frame n next.frame next.code]⟩ := by
  apply progress.frame_mode n fo ⟨fo.locals ++ E, p.mi⟩
  intro s t oldFrame newFrame oldCode newCode runtime
  obtain ⟨innerModule, innerLocals, innerExtra, extraLength, rfl, code⟩ := runtime
  exact ⟨moduleEq, locals, E, extra, rfl,
    .head (.frame (.g innerModule innerLocals extraLength code)) .nil⟩

theorem callee_frame_gen {original target next : Config H}
    (progress : ReverseProgress p P .gen original target next) (n : Nat)
    (fo : Frame) {d : Nat} {L : List (Option Val)} (moduleEq : fo.module = p.mi)
    (prefixLength : L.length = p.base) (locals : fo.locals.length = p.ext) :
    ReverseProgress p P (.i d L)
      ⟨original.store, fo, [.frame n original.frame original.code]⟩
      ⟨target.store, ⟨L ++ fo.locals, p.mi⟩, [.frame n target.frame target.code]⟩
      ⟨next.store, ⟨L ++ fo.locals, p.mi⟩, [.frame n next.frame next.code]⟩ := by
  apply progress.frame_mode n fo ⟨L ++ fo.locals, p.mi⟩
  intro s t oldFrame newFrame oldCode newCode runtime
  obtain ⟨rfl, code⟩ := runtime
  exact ⟨moduleEq, prefixLength, locals, rfl, .cons (.frame (.gen code)) .nil⟩

theorem callee_frame_caller {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (n : Nat)
    (fo : Frame) {d : Nat} {L : List (Option Val)} (moduleEq : fo.module = p.mi)
    (prefixLength : L.length = p.base) (locals : fo.locals.length = p.ext) :
    ReverseProgress p P (.i d L)
      ⟨original.store, fo, [.frame n original.frame original.code]⟩
      ⟨target.store, ⟨L ++ fo.locals, p.mi⟩, [.frame n target.frame target.code]⟩
      ⟨next.store, ⟨L ++ fo.locals, p.mi⟩, [.frame n next.frame next.code]⟩ := by
  apply progress.frame_mode n fo ⟨L ++ fo.locals, p.mi⟩
  intro s t oldFrame newFrame oldCode newCode runtime
  obtain ⟨innerModule, innerLocals, innerExtra, extraLength, rfl, code⟩ := runtime
  exact ⟨moduleEq, prefixLength, locals, rfl,
    .cons (.frame (.g innerModule innerLocals extraLength code)) .nil⟩

end ReverseProgress

end Silmaril.Wasm.Binaryen.InlR
