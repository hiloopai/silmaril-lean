module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: head rules of `LABEL_`, `HANDLER_` and `FRAME_`

`adminStep?` decides the head rules of the structured administrative
instructions that are not context rules (`ctxtLabel`, `ctxtHandler`,
`ctxtFrame`): exits with values, branches, returns, tail calls, exception
propagation and handling, and traps. It consumes no operands.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace Adm

/-- Label body at its first non-value `c` (under values `vs`, before `rest`). -/
def labelAt (s : Store H) (f : Frame) (n : Nat) (cont : List Instr) (vs : List Val) (c : Admin)
    (rest : List Admin) : Option (Config H) :=
  match c with
  | .plain (.br l) =>
    if l.toNat = 0 then
      if n ≤ vs.length then some ⟨s, f, vals (vs.drop (vs.length - n)) ++ expression cont⟩
      else none
    else some ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩
  | .plain .return_ => some ⟨s, f, vals vs ++ [.plain .return_]⟩
  | .plain (.returnCallRef y) => some ⟨s, f, vals vs ++ [.plain (.returnCallRef y)]⟩
  | .returnCallRefType d => some ⟨s, f, vals vs ++ [.returnCallRefType d]⟩
  | .plain .throwRef =>
    match vs, rest with
    | [.ref (.exn a)], [] => some ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
    | _, _ => none
  | .trap =>
    match vs, rest with
    | [], [] => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def labelStep (s : Store H) (f : Frame) (n : Nat) (cont : List Instr) (body : List Admin) :
    Option (Config H) :=
  match splitVals body with
  | (vs, []) => some ⟨s, f, vals vs⟩
  | (vs, c :: rest) => labelAt s f n cont vs c rest

/-- The code a handler clause jumps to on catching exception `a`, if it catches it. -/
def catchStep (s : Store H) (f : Frame) (a : Nat) : Catch → Option (List Admin)
  | .catch_ x l =>
    match s.exns[a]?, f.module.tags[x.toNat]? with
    | some e, some t => if e.tag = t then some (vals e.fields ++ [.plain (.br l)]) else none
    | _, _ => none
  | .catchRef x l =>
    match s.exns[a]?, f.module.tags[x.toNat]? with
    | some e, some t =>
      if e.tag = t then some (vals e.fields ++ [.ref (.exn a), .plain (.br l)]) else none
    | _, _ => none
  | .catchAll l => some [.plain (.br l)]
  | .catchAllRef l => some [.ref (.exn a), .plain (.br l)]

def throwHandler (s : Store H) (f : Frame) (n : Nat) (cs : List Catch) (a : Nat) :
    Option (Config H) :=
  match cs with
  | [] => some ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
  | c :: cs' =>
    match catchStep s f a c with
    | some code => some ⟨s, f, code⟩
    | none => some ⟨s, f, [.handler n cs' [.ref (.exn a), .plain .throwRef]]⟩

def handlerAt (s : Store H) (f : Frame) (n : Nat) (cs : List Catch) (vs : List Val) (c : Admin)
    (rest : List Admin) : Option (Config H) :=
  match c with
  | .plain (.br l) => some ⟨s, f, vals vs ++ [.plain (.br l)]⟩
  | .plain .return_ => some ⟨s, f, vals vs ++ [.plain .return_]⟩
  | .plain (.returnCallRef y) => some ⟨s, f, vals vs ++ [.plain (.returnCallRef y)]⟩
  | .returnCallRefType d => some ⟨s, f, vals vs ++ [.returnCallRefType d]⟩
  | .plain .throwRef =>
    match vs, rest with
    | [.ref (.exn a)], [] => throwHandler s f n cs a
    | _, _ => none
  | .trap =>
    match vs, rest with
    | [], [] => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def handlerStep (s : Store H) (f : Frame) (n : Nat) (cs : List Catch) (body : List Admin) :
    Option (Config H) :=
  match splitVals body with
  | (vs, []) => some ⟨s, f, vals vs⟩
  | (vs, c :: rest) => handlerAt s f n cs vs c rest

/-- `RETURN_CALL_REF` leaving a frame: `vs` are the values under the tail call `c`. -/
def frameRCR (s : Store H) (f fi : Frame) (vs : List Val) (c : Admin) : Option (Config H) :=
  match vs.getLast? with
  | some (.ref .null) => some ⟨s, f, [.trap]⟩
  | some (.ref (.func a)) =>
    match s.funcs[a]? with
    | some fn =>
      match fn.type.expand? with
      | some (.func ps _) =>
        if ps.length ≤ vs.dropLast.length then
          some ⟨s, f, vals (vs.dropLast.drop (vs.dropLast.length - ps.length)) ++
            [.ref (.func a), c.retToCallIn fi.module]⟩
        else none
      | _ => none
    | none => none
  | _ => none

def frameAt (s : Store H) (f : Frame) (n : Nat) (fi : Frame) (vs : List Val) (c : Admin)
    (rest : List Admin) : Option (Config H) :=
  match c with
  | .plain .return_ =>
    if n ≤ vs.length then some ⟨s, f, vals (vs.drop (vs.length - n))⟩ else none
  | .plain (.returnCallRef y) => frameRCR s f fi vs (.plain (.returnCallRef y))
  | .returnCallRefType d => frameRCR s f fi vs (.returnCallRefType d)
  | .plain .throwRef =>
    match vs, rest with
    | [.ref (.exn a)], [] => some ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
    | _, _ => none
  | .trap =>
    match vs, rest with
    | [], [] => some ⟨s, f, [.trap]⟩
    | _, _ => none
  | _ => none

def frameStep (s : Store H) (f : Frame) (n : Nat) (fi : Frame) (body : List Admin) :
    Option (Config H) :=
  match splitVals body with
  | (vs, []) => if vs.length = n then some ⟨s, f, vals vs⟩ else none
  | (vs, c :: rest) => frameAt s f n fi vs c rest

/-- `LABEL_`, `HANDLER_` or `FRAME_`. -/
def IsNest : Admin → Prop
  | .label .. | .handler .. | .frame .. => True
  | _ => False

end Adm

set_option linter.unusedVariables false in
/-- One non-context head step of a `LABEL_`, `HANDLER_` or `FRAME_`; consumes no operands. -/
def adminStep? (o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .label n cont is => (Adm.labelStep s f n cont is).map (0, ·)
  | .handler n cs is => (Adm.handlerStep s f n cs is).map (0, ·)
  | .frame n fi is => (Adm.frameStep s f n fi is).map (0, ·)
  | _ => none

namespace Adm

theorem body_vals {body : List Admin} {vs : List Val} (h : splitVals body = (vs, [])) :
    body = vals vs := by
  have := SingleThreaded.splitVals_spec body
  rw [h] at this; simpa using this

theorem vals_take_drop (vs : List Val) (k : Nat) (c : Admin) (rest : List Admin) :
    vals vs ++ c :: rest = vals (vs.take k) ++ vals (vs.drop k) ++ [c] ++ rest := by
  rw [← vals_append, List.take_append_drop]; simp

theorem throw_body {body : List Admin} {a : Nat}
    (hb : body = vals [.ref (.exn a)] ++ [Admin.plain .throwRef]) :
    body = [.ref (.exn a), .plain .throwRef] := by
  rw [hb]; rfl

theorem trap_body {body : List Admin} (hb : body = vals [] ++ [Admin.trap]) :
    body = [.trap] := by
  rw [hb]; rfl

variable {P : Profile} {s : Store H} {f : Frame}

theorem labelAt_sound {n : Nat} {cont : List Instr} {vs : List Val} {c : Admin}
    {rest body : List Admin} {cfg : Config H} (hb : body = vals vs ++ c :: rest)
    (h : labelAt s f n cont vs c rest = some cfg) : Head P s f [] (.label n cont body) cfg := by
  unfold labelAt at h
  split at h
  · rename_i l
    split_ifs at h with h0 hn
    · cases h
      refine .brLabelZero (vs' := vs.take (vs.length - n)) (vs := vs.drop (vs.length - n))
        (by rw [hb, vals_take_drop vs (vs.length - n)]) h0 (by simp; omega)
    · cases h
      exact .brLabelSucc (rest := rest) (by rw [hb]; simp) (by omega)
  · cases h; exact .returnLabel (rest := rest) (by rw [hb]; simp)
  · cases h; exact .returnCallRefLabel (rest := rest) (by rw [hb]; simp) trivial
  · cases h; exact .returnCallRefLabel (rest := rest) (by rw [hb]; simp) trivial
  · split at h
    · cases h; rw [throw_body hb]; exact .throwRefLabel
    · cases h
  · split at h
    · cases h; rw [trap_body hb]; exact .trapLabel
    · cases h
  · cases h

theorem labelStep_sound {n : Nat} {cont : List Instr} {body : List Admin} {cfg : Config H}
    (h : labelStep s f n cont body = some cfg) : Head P s f [] (.label n cont body) cfg := by
  unfold labelStep at h
  split at h
  · rename_i vs hsv
    cases h; exact .labelVals (body_vals hsv)
  · rename_i vs c rest hsv
    exact labelAt_sound (SingleThreaded.splitVals_eq hsv).1 h

theorem throwHandler_sound {n : Nat} {cs : List Catch} {a : Nat} {cfg : Config H}
    (h : throwHandler s f n cs a = some cfg) :
    Head P s f [] (.handler n cs [.ref (.exn a), .plain .throwRef]) cfg := by
  unfold throwHandler at h
  split at h
  · cases h; exact .throwRefHandlerEmpty
  · rename_i c cs'
    split at h
    · rename_i code hc
      cases h
      cases c with
      | catch_ x l =>
        simp only [catchStep] at hc
        split at hc
        · rename_i e t he ht
          split_ifs at hc with het
          cases hc; subst het; exact .throwRefHandlerCatch he ht
        · cases hc
      | catchRef x l =>
        simp only [catchStep] at hc
        split at hc
        · rename_i e t he ht
          split_ifs at hc with het
          cases hc; subst het; exact .throwRefHandlerCatchRef he ht
        · cases hc
      | catchAll l => cases hc; exact .throwRefHandlerCatchAll
      | catchAllRef l => cases hc; exact .throwRefHandlerCatchAllRef
    · rename_i hc
      cases h
      refine .throwRefHandlerNext ?_
      intro hm
      cases c with
      | catch_ x l =>
        obtain ⟨e, t, he, ht, rfl⟩ := hm
        simp [catchStep, he, ht] at hc
      | catchRef x l =>
        obtain ⟨e, t, he, ht, rfl⟩ := hm
        simp [catchStep, he, ht] at hc
      | catchAll l => cases hc
      | catchAllRef l => cases hc

theorem handlerAt_sound {n : Nat} {cs : List Catch} {vs : List Val} {c : Admin}
    {rest body : List Admin} {cfg : Config H} (hb : body = vals vs ++ c :: rest)
    (h : handlerAt s f n cs vs c rest = some cfg) : Head P s f [] (.handler n cs body) cfg := by
  unfold handlerAt at h
  split at h
  · cases h; exact .brHandler (rest := rest) (by rw [hb]; simp)
  · cases h; exact .returnHandler (rest := rest) (by rw [hb]; simp)
  · cases h; exact .returnCallRefHandler (rest := rest) (by rw [hb]; simp) trivial
  · cases h; exact .returnCallRefHandler (rest := rest) (by rw [hb]; simp) trivial
  · split at h
    · rw [throw_body hb]; exact throwHandler_sound h
    · cases h
  · split at h
    · cases h; rw [trap_body hb]; exact .trapHandler
    · cases h
  · cases h

theorem handlerStep_sound {n : Nat} {cs : List Catch} {body : List Admin} {cfg : Config H}
    (h : handlerStep s f n cs body = some cfg) : Head P s f [] (.handler n cs body) cfg := by
  unfold handlerStep at h
  split at h
  · rename_i vs hsv
    cases h; exact .handlerVals (body_vals hsv)
  · rename_i vs c rest hsv
    exact handlerAt_sound (SingleThreaded.splitVals_eq hsv).1 h

theorem frameRCR_sound {n : Nat} {fi : Frame} {vs : List Val} {c : Admin}
    {rest body : List Admin} {cfg : Config H} (hc : c.IsReturnCallRef)
    (hb : body = vals vs ++ c :: rest)
    (h : frameRCR s f fi vs c = some cfg) : Head P s f [] (.frame n fi body) cfg := by
  unfold frameRCR at h
  split at h
  · rename_i hl
    cases h
    obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    refine .returnCallRefFrameNull (vs := L) (rest := rest) ?_ hc
    rw [hb]; simp [Val.toAdmin]
  · rename_i a hl
    obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    split at h
    · rename_i fn hfn
      split at h
      · rename_i ps rs hex
        simp only [List.dropLast_concat] at h
        split_ifs at h with hle
        cases h
        refine .returnCallRefFrameAddr (vs' := L.take (L.length - ps.length))
          (vs := L.drop (L.length - ps.length)) (rest := rest) ?_ hc hfn
          (Expand.iff.2 hex) (by simp [Ty.length] at hle ⊢; omega)
        rw [hb]; simp [Val.toAdmin]
        rw [← List.append_assoc, ← vals_append, List.take_append_drop]
      · cases h
    · cases h
  · cases h

theorem frameAt_sound {n : Nat} {fi : Frame} {vs : List Val} {c : Admin}
    {rest body : List Admin} {cfg : Config H} (hb : body = vals vs ++ c :: rest)
    (h : frameAt s f n fi vs c rest = some cfg) : Head P s f [] (.frame n fi body) cfg := by
  unfold frameAt at h
  split at h
  · split_ifs at h with hn
    cases h
    exact .returnFrame (vs' := vs.take (vs.length - n)) (vs := vs.drop (vs.length - n))
      (rest := rest) (by rw [hb, vals_take_drop vs (vs.length - n)]) (by simp; omega)
  · exact frameRCR_sound (c := .plain (.returnCallRef _)) (hb := hb) (h := h) trivial
  · exact frameRCR_sound (c := .returnCallRefType _) (hb := hb) (h := h) trivial
  · split at h
    · cases h; rw [throw_body hb]; exact .throwRefFrame
    · cases h
  · split at h
    · cases h; rw [trap_body hb]; exact .trapFrame
    · cases h
  · cases h

theorem frameStep_sound {n : Nat} {fi : Frame} {body : List Admin} {cfg : Config H}
    (h : frameStep s f n fi body = some cfg) : Head P s f [] (.frame n fi body) cfg := by
  unfold frameStep at h
  split at h
  · rename_i vs hsv
    split_ifs at h with hn
    cases h; exact .frameVals (body_vals hsv) hn
  · rename_i vs c rest hsv
    exact frameAt_sound (SingleThreaded.splitVals_eq hsv).1 h

end Adm

theorem adminStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (h : adminStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  unfold adminStep? at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨c', hc', rfl, rfl⟩ := h
    simpa using Adm.labelStep_sound hc'
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨c', hc', rfl, rfl⟩ := h
    simpa using Adm.handlerStep_sound hc'
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨c', hc', rfl, rfl⟩ := h
    simpa using Adm.frameStep_sound hc'
  · cases h

/-! ## Completeness: a `none` on a structured instruction leaves only context rules -/

namespace Adm

/-- Rule out a family head or a call head on a structured instruction. -/
macro "fam_kill" : tactic => `(tactic| first
  | exact absurd (famOf_of_shape (ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd ‹Admin.IsCallRef _› (by simp [Admin.IsCallRef]))

variable {s : Store H} {f : Frame}

theorem labelStep_cons {n : Nat} {cont : List Instr} {W : List Val} {c : Admin} (rest : List Admin)
    (hc : c.val? = none) :
    labelStep s f n cont (vals W ++ c :: rest) = labelAt s f n cont W c rest := by
  unfold labelStep; rw [Det.splitVals_vals_cons hc]

theorem handlerStep_cons {n : Nat} {cs : List Catch} {W : List Val} {c : Admin}
    (rest : List Admin) (hc : c.val? = none) :
    handlerStep s f n cs (vals W ++ c :: rest) = handlerAt s f n cs W c rest := by
  unfold handlerStep; rw [Det.splitVals_vals_cons hc]

theorem frameStep_cons {n : Nat} {fi : Frame} {W : List Val} {c : Admin} (rest : List Admin)
    (hc : c.val? = none) :
    frameStep s f n fi (vals W ++ c :: rest) = frameAt s f n fi W c rest := by
  unfold frameStep; rw [Det.splitVals_vals_cons hc]

theorem throwHandler_ne_none {n : Nat} {cs : List Catch} {a : Nat} :
    throwHandler s f n cs a ≠ none := by
  unfold throwHandler
  split
  · simp
  · split <;> simp

theorem handlerAt_throw {n : Nat} {cs : List Catch} {a : Nat} :
    handlerAt s f n cs [.ref (.exn a)] (.plain .throwRef) [] = throwHandler s f n cs a := rfl

theorem frameAt_rcr {n : Nat} {fi : Frame} {W : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) : frameAt s f n fi W c rest = frameRCR s f fi W c := by
  rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> rfl

theorem throw_eq (a : Nat) :
    ([.ref (.exn a), .plain .throwRef] : List Admin) = vals [.ref (.exn a)] ++ .plain .throwRef :: [] :=
  rfl

theorem trap_eq : ([.trap] : List Admin) = vals [] ++ .trap :: [] := rfl

theorem br_eq (vs' vs : List Val) (c : Admin) (rest : List Admin) :
    vals vs' ++ vals vs ++ [c] ++ rest = vals (vs' ++ vs) ++ c :: rest := by simp

theorem br_eq' (vs : List Val) (c : Admin) (rest : List Admin) :
    vals vs ++ [c] ++ rest = vals vs ++ c :: rest := by simp

variable {P : Profile}

theorem labelStep_complete {n : Nat} {cont : List Instr} {body : List Admin} {args : List Val}
    {c : Config H} (h : Head P s f args (.label n cont body) c)
    (hnone : labelStep s f n cont body = none) :
    ∃ s' f' is', c = ⟨s', f', [.label n cont is']⟩ ∧ Step P noHost ⟨s, f, body⟩ ⟨s', f', is'⟩ := by
  cases h with
  | ctxtLabel h => exact ⟨_, _, _, rfl, h⟩
  | labelVals hb => subst hb; simp [labelStep, Det.splitVals_vals] at hnone
  | brLabelZero hb hl hn =>
    subst hb; rw [br_eq, labelStep_cons _ rfl] at hnone
    simp [labelAt, hl] at hnone; omega
  | brLabelSucc hb hl =>
    subst hb; rw [br_eq', labelStep_cons _ rfl] at hnone
    simp [labelAt, Nat.pos_iff_ne_zero.mp hl] at hnone
  | returnLabel hb =>
    subst hb; rw [br_eq', labelStep_cons _ rfl] at hnone; simp [labelAt] at hnone
  | returnCallRefLabel hb hc =>
    subst hb; rw [br_eq', labelStep_cons _ (IsReturnCallRef.val_none hc)] at hnone
    rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> simp [labelAt] at hnone
  | throwRefLabel => rw [throw_eq, labelStep_cons _ rfl] at hnone; simp [labelAt] at hnone
  | trapLabel => rw [trap_eq, labelStep_cons _ rfl] at hnone; simp [labelAt] at hnone
  | _ => fam_kill

theorem handlerStep_complete {n : Nat} {cs : List Catch} {body : List Admin} {args : List Val}
    {c : Config H} (h : Head P s f args (.handler n cs body) c)
    (hnone : handlerStep s f n cs body = none) :
    ∃ s' f' is', c = ⟨s', f', [.handler n cs is']⟩ ∧ Step P noHost ⟨s, f, body⟩ ⟨s', f', is'⟩ := by
  cases h with
  | ctxtHandler h => exact ⟨_, _, _, rfl, h⟩
  | handlerVals hb => subst hb; simp [handlerStep, Det.splitVals_vals] at hnone
  | brHandler hb =>
    subst hb; rw [br_eq', handlerStep_cons _ rfl] at hnone; simp [handlerAt] at hnone
  | returnHandler hb =>
    subst hb; rw [br_eq', handlerStep_cons _ rfl] at hnone; simp [handlerAt] at hnone
  | returnCallRefHandler hb hc =>
    subst hb; rw [br_eq', handlerStep_cons _ (IsReturnCallRef.val_none hc)] at hnone
    rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> simp [handlerAt] at hnone
  | throwRefHandlerEmpty =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | throwRefHandlerCatch =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | throwRefHandlerCatchRef =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | throwRefHandlerCatchAll =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | throwRefHandlerCatchAllRef =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | throwRefHandlerNext =>
    rw [throw_eq, handlerStep_cons _ rfl, handlerAt_throw] at hnone
    exact (throwHandler_ne_none hnone).elim
  | trapHandler => rw [trap_eq, handlerStep_cons _ rfl] at hnone; simp [handlerAt] at hnone
  | _ => fam_kill

theorem frameStep_complete {n : Nat} {fi : Frame} {body : List Admin} {args : List Val}
    {c : Config H} (h : Head P s f args (.frame n fi body) c)
    (hnone : frameStep s f n fi body = none) :
    ∃ s' fi' is', c = ⟨s', f, [.frame n fi' is']⟩ ∧ Step P noHost ⟨s, fi, body⟩ ⟨s', fi', is'⟩ := by
  cases h with
  | ctxtFrame h => exact ⟨_, _, _, rfl, h⟩
  | frameVals hb hn => subst hb; simp [frameStep, Det.splitVals_vals, hn] at hnone
  | returnFrame hb hn =>
    subst hb; rw [br_eq, frameStep_cons _ rfl] at hnone
    simp [frameAt] at hnone; omega
  | returnCallRefFrameNull hb hc =>
    subst hb
    rw [show ∀ (vs : List Val) (c : Admin) (rest : List Admin), vals vs ++ [.ref .null, c] ++ rest =
        vals (vs ++ [.ref .null]) ++ c :: rest by intros; simp [Val.toAdmin],
      frameStep_cons _ (IsReturnCallRef.val_none hc), frameAt_rcr hc] at hnone
    simp [frameRCR] at hnone
  | returnCallRefFrameAddr hb hc hf he hn =>
    subst hb
    rw [show ∀ (vs' vs : List Val) (a : Nat) (c : Admin) (rest : List Admin),
        vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest by intros; simp [Val.toAdmin],
      frameStep_cons _ (IsReturnCallRef.val_none hc), frameAt_rcr hc] at hnone
    simp [frameRCR, hf, Expand.iff.1 he] at hnone
    simp [Ty.length] at hn hnone; omega
  | throwRefFrame => rw [throw_eq, frameStep_cons _ rfl] at hnone; simp [frameAt] at hnone
  | trapFrame => rw [trap_eq, frameStep_cons _ rfl] at hnone; simp [frameAt] at hnone
  | _ => fam_kill

end Adm

theorem adminStep?_none {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {args : List Val} {c : Config H} (hnone : adminStep? o s f vs e = none)
    (h : Head (profile o) s f args e c) :
    (∃ n cont is s' f' is', e = .label n cont is ∧ c = ⟨s', f', [.label n cont is']⟩ ∧
        Step (profile o) noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) ∨
      (∃ n cs is s' f' is', e = .handler n cs is ∧ c = ⟨s', f', [.handler n cs is']⟩ ∧
        Step (profile o) noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) ∨
      (∃ n fi is s' fi' is', e = .frame n fi is ∧ c = ⟨s', f, [.frame n fi' is']⟩ ∧
        Step (profile o) noHost ⟨s, fi, is⟩ ⟨s', fi', is'⟩) ∨
      ¬ Adm.IsNest e := by
  cases e with
  | label n cont is =>
    simp only [adminStep?, Option.map_eq_none_iff] at hnone
    obtain ⟨s', f', is', rfl, hs⟩ := Adm.labelStep_complete h hnone
    exact .inl ⟨n, cont, is, s', f', is', rfl, rfl, hs⟩
  | handler n cs is =>
    simp only [adminStep?, Option.map_eq_none_iff] at hnone
    obtain ⟨s', f', is', rfl, hs⟩ := Adm.handlerStep_complete h hnone
    exact .inr (.inl ⟨n, cs, is, s', f', is', rfl, rfl, hs⟩)
  | frame n fi is =>
    simp only [adminStep?, Option.map_eq_none_iff] at hnone
    obtain ⟨s', fi', is', rfl, hs⟩ := Adm.frameStep_complete h hnone
    exact .inr (.inr (.inl ⟨n, fi, is, s', fi', is', rfl, rfl, hs⟩))
  | _ => exact .inr (.inr (.inr (by simp [Adm.IsNest])))

end Silmaril.Wasm.SingleThreaded.Exec
