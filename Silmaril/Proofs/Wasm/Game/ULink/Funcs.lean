module

public import Silmaril.Wasm.Game.ULink.Defs
public import Silmaril.Wasm.Binaryen.InlStore
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Host-free steps under a replaced function list

`step_withFuncs`: a host-free Core step in a store `s` is a step in the store with function
list `X` of the same types, **or** it is a call (under an evaluation context) of a Wasm
function of `s` that `X` does not have at that address. The stubbed and the real store of a
link differ exactly in the code of the provider functions, so consumer steps in the stubbed
store are linked steps, and linked steps are consumer steps or calls into the provider.

The family cases are silmaril-lean's `Silmaril.Wasm.Binaryen.InlS` lemmas (written for the
inliner); the control cases are new.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Binaryen.InlS

variable {H : Type}

/-- The step from `c` to `c'` is a call, under the context `E`, of a Wasm function of `c.store`
at an address where `X` has another function. -/
def CallAt (X : List (FuncInst H)) (c c' : Config H) : Prop :=
  ∃ (E : Ctx) (vs : List Val) (a : Nat) (cr : Admin) (fi : FuncInst H) (ps rs : Ty (.list .val))
    (code : Func), c.code = E.fill (vals vs ++ [.ref (.func a), cr]) ∧ cr.IsCallRef ∧
    c.store.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧ vs.length = ps.length ∧
    fi.code = .wasm code ∧ X[a]? ≠ some fi ∧
    c' = ⟨c.store, c.frame, E.fill [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩

/-- `CallAt` under a value prefix and a suffix. -/
theorem CallAt.wrap {X : List (FuncInst H)} {s : Store H} {f : Frame} {is : List Admin}
    {c' : Config H} (h : CallAt X ⟨s, f, is⟩ c') (vs : List Val) (rest : List Admin) :
    CallAt X ⟨s, f, vals vs ++ is ++ rest⟩ ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ := by
  obtain ⟨E, ws, a, cr, fi, ps, rs, code, hc, hcr, hf, he, hn, hcode, hX, rfl⟩ := h
  refine ⟨E.wrap vs rest, ws, a, cr, fi, ps, rs, code, ?_, hcr, hf, he, hn, hcode, hX, ?_⟩
  · show vals vs ++ is ++ rest = _
    rw [Ctx.fill_wrap, ← hc]
  · rw [Ctx.fill_wrap]

/-- A call keeps the store and the frame. -/
theorem CallAt.eq {X : List (FuncInst H)} {c c' : Config H} (h : CallAt X c c') :
    c'.store = c.store ∧ c'.frame = c.frame := by
  obtain ⟨E, ws, a, cr, fi, ps, rs, code, -, -, -, -, -, -, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- `CallAt` inside a structured instruction `k`, under any frame. -/
theorem CallAt.nest {X : List (FuncInst H)} {s s' : Store H} {g g' : Frame}
    {is is' : List Admin} (h : CallAt X ⟨s, g, is⟩ ⟨s', g', is'⟩) (K : Ctx → Ctx)
    (k : List Admin → Admin) (hK : ∀ E xs, (K E).fill xs = [k (E.fill xs)]) (f : Frame) :
    CallAt X ⟨s, f, [k is]⟩ ⟨s', f, [k is']⟩ := by
  obtain ⟨E, ws, a, cr, fi, ps, rs, code, hc, hcr, hf, he, hn, hcode, hX, heq⟩ := h
  have heq' : s' = s ∧ g' = g ∧ is' = E.fill [.frame rs.length
      (Frame.forCall fi.module ws code.locals) [.label rs.length [] (expression code.body)]] := by
    simpa only [Config.mk.injEq] using heq
  refine ⟨K E, ws, a, cr, fi, ps, rs, code, ?_, hcr, hf, he, hn, hcode, hX, ?_⟩
  · show [k is] = _
    rw [hK, ← hc]
  · rw [hK, heq'.1, heq'.2.2]

/-! ### Family steps under a replaced function list -/

section Families

variable {P : Profile} {c c' : Config H}

theorem variable_wf (h : VariableStep c c') (X : List (FuncInst H)) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩
      ⟨withFuncs c'.store X, c'.frame, c'.code⟩ := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  exact .variable (variableStep_withFuncs h X).2

theorem table_wf (h : TableStep P c c') (X : List (FuncInst H)) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩
      ⟨withFuncs c'.store X, c'.frame, c'.code⟩ := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  obtain ⟨-, hf, h'⟩ := tableStep_withFuncs h X
  cases hf
  exact .table (h' _)

theorem memory_wf (h : MemoryStep P c c') (X : List (FuncInst H)) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩
      ⟨withFuncs c'.store X, c'.frame, c'.code⟩ := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  obtain ⟨-, hf, h'⟩ := memoryStep_withFuncs h X
  cases hf
  exact .memory (h' _)

theorem reference_wf (h : RefStep c c') {X : List (FuncInst H)} (hX : SameTypes X c.store.funcs) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩
      ⟨withFuncs c'.store X, c'.frame, c'.code⟩ := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  obtain ⟨-, hf, h'⟩ := refStep_withFuncs h hX
  cases hf
  exact .reference (h' _)

theorem aggregate_wf (h : AggregateStep c c') (X : List (FuncInst H)) :
    Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩
      ⟨withFuncs c'.store X, c'.frame, c'.code⟩ := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  obtain ⟨-, hf, h'⟩ := aggregateStep_withFuncs h X
  cases hf
  exact .aggregate (h' _)

end Families

/-- **A host-free step under a function list of the same types**: a step there, or a call of a
Wasm function that the new list does not have. -/
theorem step_withFuncs {P : Profile} {c c' : Config H} (h : Execution.Core.Step P (fun _ _ _ _ => False) c c') :
    ∀ {X : List (FuncInst H)}, SameTypes X c.store.funcs →
      Execution.Core.Step P (fun _ _ _ _ => False) ⟨withFuncs c.store X, c.frame, c.code⟩ ⟨withFuncs c'.store X, c'.frame, c'.code⟩ ∨
        CallAt X c c' := by
  induction h with
  | parametric h => exact fun _ => .inl (.parametric h)
  | numeric h => exact fun _ => .inl (.numeric h)
  | vector h => exact fun _ => .inl (.vector h)
  | «variable» h => exact fun {X} _ => .inl (variable_wf h X)
  | table h => exact fun {X} _ => .inl (table_wf h X)
  | memory h => exact fun {X} _ => .inl (memory_wf h X)
  | reference h => exact fun hX => .inl (reference_wf h hX)
  | aggregate h => exact fun {X} _ => .inl (aggregate_wf h X)
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    intro X hX
    rcases ih hX with h' | h'
    · exact .inl (.ctxtInstrs h' hne)
    · exact .inr (h'.wrap vs rest)
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro X hX
    rcases ih hX with h' | h'
    · exact .inl (.ctxtLabel h')
    · have hf' : f' = f := h'.eq.2
      rw [hf']
      exact .inr (h'.nest (fun E => .label [] n cont E []) (.label n cont)
        (fun E xs => by simp [Ctx.fill, vals]) f)
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    intro X hX
    rcases ih hX with h' | h'
    · exact .inl (.ctxtHandler h')
    · have hf' : f' = f := h'.eq.2
      rw [hf']
      exact .inr (h'.nest (fun E => .handler [] n cs E []) (.handler n cs)
        (fun E xs => by simp [Ctx.fill, vals]) f)
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    intro X hX
    rcases ih hX with h' | h'
    · exact .inl (.ctxtFrame h')
    · have hfi : fi' = fi := h'.eq.2
      rw [hfi]
      exact .inr (h'.nest (fun E => .frame [] n fi E []) (fun b => .frame n fi b)
        (fun E xs => by simp [Ctx.fill, vals]) f)
  | block hbt hm => exact fun _ => .inl (.block hbt hm)
  | loop hbt hm => exact fun _ => .inl (.loop hbt hm)
  | ifTrue hc => exact fun _ => .inl (.ifTrue hc)
  | ifFalse => exact fun _ => .inl .ifFalse
  | labelVals => exact fun _ => .inl .labelVals
  | brLabelZero hl hn => exact fun _ => .inl (.brLabelZero hl hn)
  | brLabelSucc hl => exact fun _ => .inl (.brLabelSucc hl)
  | brHandler => exact fun _ => .inl .brHandler
  | brIfTrue hc => exact fun _ => .inl (.brIfTrue hc)
  | brIfFalse => exact fun _ => .inl .brIfFalse
  | brTableLt hi => exact fun _ => .inl (.brTableLt hi)
  | brTableGe hi => exact fun _ => .inl (.brTableGe hi)
  | brOnNullNull => exact fun _ => .inl .brOnNullNull
  | brOnNullAddr hv => exact fun _ => .inl (.brOnNullAddr hv)
  | brOnNonNullNull => exact fun _ => .inl .brOnNonNullNull
  | brOnNonNullAddr hv => exact fun _ => .inl (.brOnNonNullAddr hv)
  | brOnCastSucceed h => exact fun hX => .inl (.brOnCastSucceed ((refOk_withFuncs_iff hX).2 h))
  | brOnCastFail h =>
    exact fun hX => .inl (.brOnCastFail fun h' => h ((refOk_withFuncs_iff hX).1 h'))
  | brOnCastFailSucceed h =>
    exact fun hX => .inl (.brOnCastFailSucceed ((refOk_withFuncs_iff hX).2 h))
  | brOnCastFailFail h =>
    exact fun hX => .inl (.brOnCastFailFail fun h' => h ((refOk_withFuncs_iff hX).1 h'))
  | @call s f x a fi hx hf =>
    intro X hX
    obtain ⟨fi', hf', ht⟩ := hX.get hf
    exact .inl (ht ▸ Step.call (P := P) (host := fun _ _ _ _ => False) (s := withFuncs s X) (f := f) hx hf')
  | callRefNull hc => exact fun _ => .inl (.callRefNull hc)
  | @callRefFunc s f cr vs a fi ps rs code hc hf he hn hcode =>
    intro X _
    by_cases hX : X[a]? = some fi
    · exact .inl (.callRefFunc hc hX he hn hcode)
    · exact .inr ⟨.top [] [], vs, a, cr, fi, ps, rs, code, by simp [Ctx.fill], hc, hf, he, hn,
        hcode, hX, by simp [Ctx.fill]⟩
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | @returnCall s f x a fi hx hf =>
    intro X hX
    obtain ⟨fi', hf', ht⟩ := hX.get hf
    exact .inl (ht ▸ Step.returnCall (P := P) (host := fun _ _ _ _ => False) (s := withFuncs s X) (f := f)
      hx hf')
  | returnCallRefLabel hc => exact fun _ => .inl (.returnCallRefLabel hc)
  | returnCallRefHandler hc => exact fun _ => .inl (.returnCallRefHandler hc)
  | returnCallRefFrameNull hc => exact fun _ => .inl (.returnCallRefFrameNull hc)
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hc hf he hn =>
    intro X hX
    obtain ⟨fn', hf', ht⟩ := hX.get hf
    have he' : Expand fn'.type (.func ps rs) := ht ▸ he
    exact .inl (.returnCallRefFrameAddr hc hf' he' hn)
  | callIndirect => exact fun _ => .inl .callIndirect
  | returnCallIndirect => exact fun _ => .inl .returnCallIndirect
  | frameVals hn => exact fun _ => .inl (.frameVals hn)
  | returnFrame hn => exact fun _ => .inl (.returnFrame hn)
  | returnLabel => exact fun _ => .inl .returnLabel
  | returnHandler => exact fun _ => .inl .returnHandler
  | throw ht he hn => exact fun _ => .inl (.throw ht he hn)
  | throwRefNull => exact fun _ => .inl .throwRefNull
  | throwRefInstrs hne => exact fun _ => .inl (.throwRefInstrs hne)
  | throwRefLabel => exact fun _ => .inl .throwRefLabel
  | throwRefFrame => exact fun _ => .inl .throwRefFrame
  | throwRefHandlerEmpty => exact fun _ => .inl .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact fun _ => .inl (.throwRefHandlerCatch he ht)
  | throwRefHandlerCatchRef he ht => exact fun _ => .inl (.throwRefHandlerCatchRef he ht)
  | throwRefHandlerCatchAll => exact fun _ => .inl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact fun _ => .inl .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact fun _ => .inl (.throwRefHandlerNext h)
  | tryTable hbt hm => exact fun _ => .inl (.tryTable hbt hm)
  | handlerVals => exact fun _ => .inl .handlerVals
  | trapInstrs hne => exact fun _ => .inl (.trapInstrs hne)
  | trapLabel => exact fun _ => .inl .trapLabel
  | trapHandler => exact fun _ => .inl .trapHandler
  | trapFrame => exact fun _ => .inl .trapFrame

end Silmaril.Proofs.Wasm.Game.ULink
