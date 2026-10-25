module

public import Silmaril.Wasm.Binaryen.InlReverseFrame
public import Silmaril.Wasm.Binaryen.InlReverseCallerStructured
public import Silmaril.Wasm.Binaryen.InlReverseProgress

@[expose] public section

/-! # Chosen reverse caller label and handler exits

Ordinary caller controls retain IR-related continuations and LG-related bodies.
The contextual alternative exposes the actual selected target-body step. Every
terminal alternative constructs an actual source run and retains the selected
result. Traps and throws may have an unreachable original suffix, so their
source runs first bubble or strip that suffix rather than assuming one source
head step suffices.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Branches, returns and tail-call exits are unchanged in caller code, even
though their discarded original suffix may differ from the target suffix. -/
theorem LG.control_prefix_right {E : List (Option Val)} {body rest : List Admin}
    {values : List Val} {head : Admin}
    (control : (∃ index, head = .plain (.br index)) ∨ head = .plain .return_ ∨ head.IsReturnCallRef)
    (related : LG p E body (vals values ++ head :: rest)) :
    ∃ oldRest, body = vals values ++ head :: oldRest := by
  have nonvalue : head.val? = none := by
    rcases control with ⟨index, rfl⟩ | rfl | tail
    · rfl
    · rfl
    · exact Det.IsReturnCallRef.val_none tail
  rcases LG.vals_cons_inv_right nonvalue related with ordinary | pending | trapped | thrown
  · obtain ⟨oldHead, oldRest, shape, headRelated, _⟩ := ordinary
    have unchanged : oldHead = head := by
      rcases control with ⟨index, rfl⟩ | returns
      · obtain ⟨instruction, rfl, translated⟩ := AG.plain_inv_right headRelated
        rw [IR.eq_of_nonstruct_right translated (by simp [StructE])]
      · exact AG.eq_of_frameExit_right returns headRelated
    exact ⟨oldRest, by rw [unchanged] at shape; exact shape⟩
  · obtain ⟨rfl, _⟩ := pending
    rcases control with ⟨_, impossible⟩ | impossible | impossible
    · cases impossible
    · cases impossible
    · exact impossible.elim
  · obtain ⟨rfl, _⟩ := trapped
    rcases control with ⟨_, impossible⟩ | impossible | impossible
    · cases impossible
    · cases impossible
    · exact impossible.elim
  · obtain ⟨rfl, _⟩ := thrown
    rcases control with ⟨_, impossible⟩ | impossible | impossible
    · cases impossible
    · cases impossible
    · exact impossible.elim

/-- Terminal caller controls preserve both frames and all mutable store state. -/
theorem ReverseMatch.caller_control {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    {original oldResult newResult : List Admin}
    (steps : Relation.TransGen (Step P Det.noHost) ⟨s, fo, original⟩ ⟨s, fo, oldResult⟩)
    (code : LG p E oldResult newResult) :
    ReverseMatch p P .g ⟨s, fo, original⟩ ⟨t, ⟨fo.locals ++ E, p.mi⟩, newResult⟩ :=
  ReverseMatch.of_steps steps ⟨moduleEq, locals, E, extra, rfl, code⟩ stores

/-- A selected caller label either steps its actual body, or has an actual
source run matching its selected terminal result and related continuation. -/
theorem reverse_caller_label {n : Nat} {cont cont' : List Instr} {body body' : List Admin}
    {s t : Store H} {fo : Frame} {E : List (Option Val)} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (continuations : IRL p cont cont') (related : LG p E body body')
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.label n cont' body') next) :
    (∃ bodyNext : Config H, args = [] ∧
      Step P Det.noHost ⟨t, ⟨fo.locals ++ E, p.mi⟩, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.label n cont' bodyNext.code]⟩) ∨
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.label n cont body]⟩ next := by
  have frames : FR p fo ⟨fo.locals ++ E, p.mi⟩ body body' := .g moduleEq locals extra related
  cases selected with
  | ctxtLabel step => exact .inl ⟨_, rfl, step, rfl⟩
  | labelVals shape =>
    rw [shape] at related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.labelVals (LG.vals_inv_right related))) (LG.of_out (Out.vals _)))
  | brLabelZero shape zero count =>
    rename_i discarded returned index rest
    have combined : vals discarded ++ vals returned ++ [Admin.plain (.br index)] ++ rest =
        vals (discarded ++ returned) ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inl ⟨index, rfl⟩) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.brLabelZero (by simpa using oldShape) zero count))
      (LG.vals_append returned (.plain (LGq.of_IRL continuations))))
  | brLabelSucc shape positive =>
    rename_i values index rest
    have combined : vals values ++ [Admin.plain (.br index)] ++ rest =
        vals values ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inl ⟨index, rfl⟩) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.brLabelSucc (by simpa using oldShape) positive))
      (LG.vals_append values (.plain (.cons (.flat _) .nil))))
  | returnCallRefLabel shape tail =>
    rename_i values head rest
    rw [show vals values ++ [head] ++ rest = vals values ++ head :: rest by simp] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inr (.inr tail)) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.returnCallRefLabel (by simpa using oldShape) tail))
      (LG.vals_append values (.head (AG.of_ret tail) .nil)))
  | returnLabel shape =>
    rename_i values rest
    rw [show vals values ++ [Admin.plain .return_] ++ rest =
      vals values ++ .plain .return_ :: rest by simp] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inr (.inl rfl)) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.returnLabel (by simpa using oldShape)))
      (LG.vals_append values (.plain (.cons (.flat _) .nil))))
  | throwRefLabel =>
    obtain ⟨oldRest, oldShape⟩ := FR.throwing_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (by rw [oldShape]; exact bubble_label_throw)
      (LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))))
  | trapLabel =>
    obtain ⟨oldRest, oldShape⟩ := FR.trap_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (by rw [oldShape]; exact bubble_label_trap) (LG.of_out Out.trap))
  | callRefNull call => exact absurd call (by simp [Admin.IsCallRef])
  | callRefFunc _ call => exact absurd call (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-- Strip only an unreachable trap suffix before taking the actual handler exit. -/
theorem caller_handler_pre_trap {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {rest : List Admin} :
    Steps P Det.noHost ⟨s, f, [.handler n cs (.trap :: rest)]⟩
      ⟨s, f, [.handler n cs [.trap]]⟩ := by
  cases rest with
  | nil => exact .refl
  | cons head tail =>
    refine .single (.ctxtHandler ?_)
    simpa [vals] using Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := f)
      (vs := []) (rest := head :: tail) (.inr (by simp))

/-- Handler exits replay the selected catch clause and exception address.
Only an actual inner contextual step remains for recursive simulation. -/
theorem reverse_caller_handler {n : Nat} {catches : List Catch} {body body' : List Admin}
    {s t : Store H} {fo : Frame} {E : List (Option Val)} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t) (related : LG p E body body')
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.handler n catches body') next) :
    (∃ bodyNext : Config H, args = [] ∧
      Step P Det.noHost ⟨t, ⟨fo.locals ++ E, p.mi⟩, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.handler n catches bodyNext.code]⟩) ∨
    ReverseMatch p P .g ⟨s, fo, vals args ++ [.handler n catches body]⟩ next := by
  have frames : FR p fo ⟨fo.locals ++ E, p.mi⟩ body body' := .g moduleEq locals extra related
  cases selected with
  | ctxtHandler step => exact .inl ⟨_, rfl, step, rfl⟩
  | brHandler shape =>
    rename_i values index rest
    rw [show vals values ++ [Admin.plain (.br index)] ++ rest =
      vals values ++ .plain (.br index) :: rest by simp] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inl ⟨index, rfl⟩) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.brHandler (by simpa using oldShape)))
      (LG.vals_append values (.plain (.cons (.flat _) .nil))))
  | returnCallRefHandler shape tail =>
    rename_i values head rest
    rw [show vals values ++ [head] ++ rest = vals values ++ head :: rest by simp] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inr (.inr tail)) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.returnCallRefHandler (by simpa using oldShape) tail))
      (LG.vals_append values (.head (AG.of_ret tail) .nil)))
  | returnHandler shape =>
    rename_i values rest
    rw [show vals values ++ [Admin.plain .return_] ++ rest =
      vals values ++ .plain .return_ :: rest by simp] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := LG.control_prefix_right (.inr (.inl rfl)) related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.returnHandler (by simpa using oldShape)))
      (LG.vals_append values (.plain (.cons (.flat _) .nil))))
  | throwRefHandlerEmpty =>
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerEmpty))
      (LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))))
  | throwRefHandlerCatch exception tag =>
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    rw [stores.ht] at exception
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw
        (tg_head (.throwRefHandlerCatch (s := s) exception (by rw [moduleEq]; exact tag))))
      (LG.vals_append _ (.plain (.cons (.flat _) .nil))))
  | throwRefHandlerCatchRef exception tag =>
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    rw [stores.ht] at exception
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw
        (tg_head (.throwRefHandlerCatchRef (s := s) exception (by rw [moduleEq]; exact tag))))
      (LG.vals_append _ (.val rfl (.plain (.cons (.flat _) .nil)))))
  | throwRefHandlerCatchAll =>
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerCatchAll))
      (.plain (.cons (.flat _) .nil)))
  | throwRefHandlerCatchAllRef =>
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerCatchAllRef))
      (.val rfl (.plain (.cons (.flat _) .nil))))
  | throwRefHandlerNext noMatch =>
    rename_i clause remaining address
    obtain ⟨oldRest, rfl⟩ := FR.throwing_prefix_right frames
    have originalNoMatch : ¬ CatchMatches s fo address clause := by
      rw [stores.ht] at noMatch
      cases clause <;> simpa only [CatchMatches, moduleEq, withFuncs] using noMatch
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre handler_pre_throw (tg_head (.throwRefHandlerNext originalNoMatch)))
      (.head (.handler (LG.of_out (.ok (by
        simp [okI, structuredInstr, IsLocalI, IsTailI])))) .nil))
  | handlerVals shape =>
    rw [shape] at related
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_head (.handlerVals (LG.vals_inv_right related))) (LG.of_out (Out.vals _)))
  | trapHandler =>
    obtain ⟨oldRest, rfl⟩ := FR.trap_prefix_right frames
    exact .inr (ReverseMatch.caller_control moduleEq locals extra stores
      (tg_of_pre caller_handler_pre_trap (tg_head .trapHandler)) (LG.of_out Out.trap))
  | callRefNull call => exact absurd call (by simp [Admin.IsCallRef])
  | callRefFunc _ call => exact absurd call (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

namespace ReverseProgress

/-- Caller progress remains valid under actual outer values and an independently
IR-related suffix. A target-only step keeps its strict decrease in code rank. -/
theorem caller_context {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (vs : List Val)
    {oldRest newRest : List Admin} (rest : LGq p oldRest newRest) :
    ReverseProgress p P .g
      ⟨original.store, original.frame, vals vs ++ original.code ++ oldRest⟩
      ⟨target.store, target.frame, vals vs ++ target.code ++ newRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ newRest⟩ := by
  rcases progress with matched |
      ⟨normalized, init, ⟨moduleEq, locals, E, extra, frames, code⟩, stores, rank⟩
  · exact .inl (matched.caller_context vs rest)
  · refine .inr ⟨⟨normalized.store, normalized.frame,
      vals vs ++ normalized.code ++ newRest⟩, init.context vs newRest,
      ⟨moduleEq, locals, E, extra, frames, LG.append_LGq rest (LG.vals_append vs code)⟩, stores, ?_⟩
    simp only [aszs_append]
    omega

/-- Label continuations retain their IRL relation across positive source
progress and decreasing target-only administrative steps alike. -/
theorem caller_label {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (n : Nat)
    {oldCont newCont : List Instr} (cont : IRL p oldCont newCont) :
    ReverseProgress p P .g
      ⟨original.store, original.frame, [.label n oldCont original.code]⟩
      ⟨target.store, target.frame, [.label n newCont target.code]⟩
      ⟨next.store, next.frame, [.label n newCont next.code]⟩ := by
  rcases progress with matched |
      ⟨normalized, init, ⟨moduleEq, locals, E, extra, frames, code⟩, stores, rank⟩
  · exact .inl (matched.caller_label n cont)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.label n newCont normalized.code]⟩,
      init.label n newCont,
      ⟨moduleEq, locals, E, extra, frames, .head (.label cont code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz_label]
    omega

theorem caller_handler {original target next : Config H}
    (progress : ReverseProgress p P .g original target next) (n : Nat) (catches : List Catch) :
    ReverseProgress p P .g
      ⟨original.store, original.frame, [.handler n catches original.code]⟩
      ⟨target.store, target.frame, [.handler n catches target.code]⟩
      ⟨next.store, next.frame, [.handler n catches next.code]⟩ := by
  rcases progress with matched |
      ⟨normalized, init, ⟨moduleEq, locals, E, extra, frames, code⟩, stores, rank⟩
  · exact .inl (matched.caller_handler n catches)
  · refine .inr ⟨⟨normalized.store, normalized.frame, [.handler n catches normalized.code]⟩,
      init.handler n catches,
      ⟨moduleEq, locals, E, extra, frames, .head (.handler code) .nil⟩, stores, ?_⟩
    simp only [aszs_cons, aszs_nil, asz]
    omega

end ReverseProgress

end Silmaril.Wasm.Binaryen.InlR
