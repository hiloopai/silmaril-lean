module

public import Silmaril.Wasm.Binaryen.InlReverseMatch
public import Silmaril.Wasm.Binaryen.InlReverseInit
public import Silmaril.Wasm.Binaryen.InlReverseCaller

@[expose] public section

/-! # Chosen reverse caller structured entries

Ordinary block, loop, conditional and exception-handler entries replay the
actual selected target control step. At the distinguished inline site, the
source fetches and enters its original callee, while the target's parameter and
local writes normalize by the context-stable Initialization relation. All
matches retain actual mutable stores and require no numerical determinism.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

section ordinary

variable {s t : Store H} {fo : Frame} {E : List (Option Val)}
  {args : List Val} {next : Config H}

theorem reverse_caller_block {bt : BlockType} {oldBody body : List Instr}
    (bodyRelated : IRL p oldBody body)
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.block bt body)) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain (.block bt oldBody)]⟩ next := by
  obtain ⟨params, results, type, arity, rfl⟩ := head_block selected
  exact ReverseMatch.of_steps (.single (Det.Head.block
    (by rw [moduleEq]; exact type) arity).toStep)
    ⟨moduleEq, locals, E, extra, rfl, LG.label_body .nil bodyRelated⟩ stores

theorem reverse_caller_loop {bt : BlockType} {oldBody body : List Instr}
    (bodyRelated : IRL p oldBody body)
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.loop bt body)) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain (.loop bt oldBody)]⟩ next := by
  cases selected with
  | loop type arity =>
    exact ReverseMatch.of_steps (.single (Det.Head.loop
      (by rw [moduleEq]; exact type) arity).toStep)
      ⟨moduleEq, locals, E, extra, rfl,
        LG.label_body (.cons (.loop bodyRelated) .nil) bodyRelated⟩ stores
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem reverse_caller_if {bt : BlockType} {oldYes yes oldNo no : List Instr}
    (yesRelated : IRL p oldYes yes) (noRelated : IRL p oldNo no)
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.if_ bt yes no)) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain (.if_ bt oldYes oldNo)]⟩ next := by
  cases selected with
  | ifTrue condition =>
    exact ReverseMatch.of_steps (.single (Det.Head.ifTrue condition).toStep)
      ⟨moduleEq, locals, E, extra, rfl,
        .plain (.cons (.block yesRelated) .nil)⟩ stores
  | ifFalse condition =>
    exact ReverseMatch.of_steps (.single (Det.Head.ifFalse condition).toStep)
      ⟨moduleEq, locals, E, extra, rfl,
        .plain (.cons (.block noRelated) .nil)⟩ stores
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem reverse_caller_tryTable {bt : BlockType} {catches : List Catch}
    {oldBody body : List Instr} (bodyRelated : IRL p oldBody body)
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.tryTable bt catches body)) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain (.tryTable bt catches oldBody)]⟩ next := by
  cases selected with
  | tryTable type arity =>
    exact ReverseMatch.of_steps (.single (Det.Head.tryTable
      (by rw [moduleEq]; exact type) arity).toStep)
      ⟨moduleEq, locals, E, extra, rfl,
        .head (.handler (LG.label_body .nil bodyRelated)) .nil⟩ stores
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

end ordinary

/-- Match the pending fetched source call against the actual selected inline
block entry, retaining Initialization until its surrounding contexts are added. -/
theorem reverse_caller_site_pending (parameters : PrmOk p) (initialization : PrmC p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) {args : List Val} {next : Config H} (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ReverseMatch p P .g
      ⟨s, fo, vals (args ++ [.ref (.func p.af)]) ++ [.callRefType p.df]⟩ next := by
  obtain ⟨oldNext, normalized, enters, initializes, runtime, related⟩ :=
    reverse_site_block_head_initializes parameters initialization moduleEq locals extra stores selected
  exact ⟨oldNext, normalized, .single enters.toStep, initializes, runtime, related⟩

/-- Match the actual direct source call by its fetch and activation steps. -/
theorem reverse_caller_site_call (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) {args : List Val} {next : Config H} (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args
      (.plain (.block (.typeIdx p.ty) p.SBL)) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain (.call p.fx)]⟩ next :=
  reverse_site_call_block_head_initializes parameters initialization functionIndex
    moduleEq locals extra stores selected

/-- Dispatch every structured IR-related caller instruction, including the
actual call-to-inline-block site alternative. -/
theorem reverse_caller_structured_head (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af)
    {s t : Store H} {fo : Frame} {E : List (Option Val)} {old instruction : Instr}
    (instructions : IR p old instruction)
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) {args : List Val} {next : Config H} (stores : SR p s t)
    (structured : StructE (.plain instruction))
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain instruction) next) :
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.plain old]⟩ next := by
  rcases structured with ⟨bt, body, shape⟩ | ⟨bt, body, shape⟩ |
      ⟨bt, yes, no, shape⟩ | ⟨bt, catches, body, shape⟩
  · cases shape
    rcases instructions.block_inv_right with ⟨rfl, rfl, rfl⟩ | ⟨oldBody, rfl, related⟩
    · exact reverse_caller_site_call parameters initialization functionIndex
        moduleEq locals extra stores selected
    · exact reverse_caller_block related moduleEq locals extra stores selected
  · cases shape
    obtain ⟨oldBody, rfl, related⟩ := instructions.loop_inv_right
    exact reverse_caller_loop related moduleEq locals extra stores selected
  · cases shape
    obtain ⟨oldYes, oldNo, rfl, yesRelated, noRelated⟩ := instructions.if_inv_right
    exact reverse_caller_if yesRelated noRelated moduleEq locals extra stores selected
  · cases shape
    obtain ⟨oldBody, rfl, related⟩ := instructions.tryTable_inv_right
    exact reverse_caller_tryTable related moduleEq locals extra stores selected

namespace ReverseMatch

/-- Lift the selected caller match through actual outer values and an
IR-related plain suffix, after preserving its complete initialization chain. -/
theorem caller_context {original next : Config H}
    (matched : ReverseMatch p P .g original next) (vs : List Val)
    {oldRest newRest : List Admin} (rest : LGq p oldRest newRest) :
    ReverseMatch p P .g
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes,
    ⟨moduleEq, locals, E, extra, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, vals vs ++ oldNext.code ++ oldRest⟩,
    ⟨normalized.store, normalized.frame, vals vs ++ normalized.code ++ newRest⟩,
    tg_instrs steps vs oldRest, initializes.context vs newRest,
    ⟨moduleEq, locals, E, extra, frames, LG.append_LGq rest (LG.vals_append vs code)⟩, stores⟩

/-- Caller labels retain their independently related branch continuations. -/
theorem caller_label {original next : Config H}
    (matched : ReverseMatch p P .g original next) (n : Nat)
    {oldCont newCont : List Instr} (cont : IRL p oldCont newCont) :
    ReverseMatch p P .g
      ⟨original.store, original.frame, [.label n oldCont original.code]⟩
      ⟨next.store, next.frame, [.label n newCont next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes,
    ⟨moduleEq, locals, E, extra, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.label n oldCont oldNext.code]⟩,
    ⟨normalized.store, normalized.frame, [.label n newCont normalized.code]⟩,
    tg_label steps n oldCont, initializes.label n newCont,
    ⟨moduleEq, locals, E, extra, frames, .head (.label cont code) .nil⟩, stores⟩

theorem caller_handler {original next : Config H}
    (matched : ReverseMatch p P .g original next) (n : Nat) (catches : List Catch) :
    ReverseMatch p P .g
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  obtain ⟨oldNext, normalized, steps, initializes,
    ⟨moduleEq, locals, E, extra, frames, code⟩, stores⟩ := matched
  exact ⟨⟨oldNext.store, oldNext.frame, [.handler n catches oldNext.code]⟩,
    ⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
    tg_handler steps n catches, initializes.handler n catches,
    ⟨moduleEq, locals, E, extra, frames, .head (.handler code) .nil⟩, stores⟩

end ReverseMatch

end Silmaril.Wasm.Binaryen.InlR
