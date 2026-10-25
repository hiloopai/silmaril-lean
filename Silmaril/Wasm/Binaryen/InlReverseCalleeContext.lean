module

public import Silmaril.Wasm.Binaryen.InlReverseProgress

@[expose] public section

/-! # Normalized reverse progress through relocated callee contexts

Labels increase relocation depth; handlers retain it. At the inline site the
source has both a callee label and an activation, while the target has only the
inline label. These lifts preserve that actual difference in runtime syntax.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile} {d : Nat} {L : List (Option Val)}

namespace ReverseMatch

theorem callee_context {original next : Config H}
    (matched : ReverseMatch p P (.i d L) original next) (vs : List Val)
    {oldRest newRest : List Admin} (rest : LI p d oldRest newRest) :
    ReverseMatch p P (.i d L)
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  obtain ⟨oldNext, normalized, steps, init, ⟨hm, hl, he, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, vals vs ++ oldNext.code ++ oldRest⟩,
    ⟨normalized.store, normalized.frame, vals vs ++ normalized.code ++ newRest⟩,
    tg_instrs steps vs oldRest, init.context vs newRest,
    ⟨hm, hl, he, frames, LI.append (LI.append (LI.of_vals d vs) code) rest⟩, stores⟩

theorem callee_label {original next : Config H}
    (matched : ReverseMatch p P (.i (d + 1) L) original next)
    (n : Nat) {cont : List Instr} (good : InlineTy.retGoodL d cont) :
    ReverseMatch p P (.i d L)
      ⟨original.store, original.frame, [.label n cont original.code]⟩
      ⟨next.store, next.frame, [.label n (InlineTy.xformL p.base d cont) next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, init, ⟨hm, hl, he, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.label n cont oldNext.code]⟩,
    ⟨normalized.store, normalized.frame,
      [.label n (InlineTy.xformL p.base d cont) normalized.code]⟩,
    tg_label steps n cont, init.label n (InlineTy.xformL p.base d cont),
    ⟨hm, hl, he, frames, .cons (.label good code) .nil⟩, stores⟩

theorem callee_handler {original next : Config H}
    (matched : ReverseMatch p P (.i d L) original next) (n : Nat) (catches : List Catch) :
    ReverseMatch p P (.i d L)
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, init, ⟨hm, hl, he, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.handler n catches oldNext.code]⟩,
    ⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
    tg_handler steps n catches, init.handler n catches,
    ⟨hm, hl, he, frames, .cons (.handler code) .nil⟩, stores⟩

theorem inline_site {caller : Frame} {original next : Config H}
    (matched : ReverseMatch p P (.i 0 caller.locals) original next)
    (moduleEq : caller.module = p.mi) (n : Nat) :
    ReverseMatch p P .g
      ⟨original.store, caller, [.frame n original.frame [.label n [] original.code]]⟩
      ⟨next.store, next.frame, [.label n [] next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, init, ⟨hm, hl, he, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, caller, [.frame n oldNext.frame [.label n [] oldNext.code]]⟩,
    ⟨normalized.store, normalized.frame, [.label n [] normalized.code]⟩,
    tg_frame (tg_label steps n []) n caller, init.label n [],
    ⟨moduleEq, hl, oldNext.frame.locals, he, frames,
      .head (.site hm rfl (.a code)) .nil⟩, stores⟩

end ReverseMatch

namespace ReverseProgress

theorem callee_context {original target next : Config H}
    (progress : ReverseProgress p P (.i d L) original target next) (vs : List Val)
    {oldRest newRest : List Admin} (rest : LI p d oldRest newRest) :
    ReverseProgress p P (.i d L)
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨target.store, target.frame, vals vs ++ target.code ++ newRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨hm, hl, he, frames, code⟩, stores, rank⟩
  · exact .inl (matched.callee_context vs rest)
  · refine .inr ⟨⟨normalized.store, normalized.frame,
      vals vs ++ normalized.code ++ newRest⟩, init.context vs newRest,
      ⟨hm, hl, he, frames, LI.append (LI.append (LI.of_vals d vs) code) rest⟩, stores, ?_⟩
    simp only [aszs_append]
    omega

theorem callee_label {original target next : Config H}
    (progress : ReverseProgress p P (.i (d + 1) L) original target next)
    (n : Nat) {cont : List Instr} (good : InlineTy.retGoodL d cont) :
    ReverseProgress p P (.i d L)
      ⟨original.store, original.frame, [.label n cont original.code]⟩
      ⟨target.store, target.frame, [.label n (InlineTy.xformL p.base d cont) target.code]⟩
      ⟨next.store, next.frame, [.label n (InlineTy.xformL p.base d cont) next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨hm, hl, he, frames, code⟩, stores, rank⟩
  · exact .inl (matched.callee_label n good)
  · refine .inr ⟨⟨normalized.store, normalized.frame,
      [.label n (InlineTy.xformL p.base d cont) normalized.code]⟩,
      init.label n (InlineTy.xformL p.base d cont),
      ⟨hm, hl, he, frames, .cons (.label good code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz_label]
    omega

theorem callee_handler {original target next : Config H}
    (progress : ReverseProgress p P (.i d L) original target next)
    (n : Nat) (catches : List Catch) :
    ReverseProgress p P (.i d L)
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨target.store, target.frame, [.handler n catches target.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨hm, hl, he, frames, code⟩, stores, rank⟩
  · exact .inl (matched.callee_handler n catches)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
      init.handler n catches, ⟨hm, hl, he, frames, .cons (.handler code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz]
    omega

theorem inline_site {caller : Frame} {original target next : Config H}
    (progress : ReverseProgress p P (.i 0 caller.locals) original target next)
    (moduleEq : caller.module = p.mi) (n : Nat) :
    ReverseProgress p P .g
      ⟨original.store, caller, [.frame n original.frame [.label n [] original.code]]⟩
      ⟨target.store, target.frame, [.label n [] target.code]⟩
      ⟨next.store, next.frame, [.label n [] next.code]⟩ := by
  rcases progress with matched | ⟨normalized, init, ⟨hm, hl, he, frames, code⟩, stores, rank⟩
  · exact .inl (matched.inline_site moduleEq n)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.label n [] normalized.code]⟩,
      init.label n [], ⟨moduleEq, hl, original.frame.locals, he, frames,
        .head (.site hm rfl (.a code)) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz_label]
    omega

end ReverseProgress

end Silmaril.Wasm.Binaryen.InlR
