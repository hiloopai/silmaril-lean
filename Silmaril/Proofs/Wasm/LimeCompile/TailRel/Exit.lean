module

public import Silmaril.Wasm.LimeCompile.TailRel.Defs
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# The non-local shapes of the tail-call rewrite: runs

Runs of the two shapes of `TailRel.Defs`, at every profile and host:

* `fill_step`, `fill_steps`: steps lift through a label-only context;
* `bubble`: a kernel that leaves a label with its values (`return_call_ref`, `return`) leaves a
  whole label-only context, accumulating the values in front of it;
* `cut`: a `trap` or a thrown exception leaves a label-only context and a frame;
* `src_exit`: the source's pending tail call leaves its labels and its frame and becomes a call
  outside the frame (`return_call_ref-label` repeatedly, then `return_call_ref-frame-addr`);
* `wrap_step`: a step of the callee lifts into the target's wrapper (`ctxt-instrs`,
  `ctxt-label`, `ctxt-frame`); the wrapper's frame records the callee's frame updates;
* `wrap_vals`, `wrap_trap`, `wrap_throw`: once the callee has returned `r` with as many values as
  the caller's arity, trapped or thrown, the wrapper reduces to the same outcome (`return-label`
  repeatedly, then `return-frame`; or the trap/throw bubbling rules).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.TailRel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (Step.append_right Step.vals_left)
open Silmaril.Wasm.LimeCompile.TailRel

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem fill_hole (X : List Admin) : LabCtx.hole.fill X = X := by rw [LabCtx.fill]

theorem fill_label (n : Nat) (cont : List Instr) (pre : List Val) (L : LabCtx)
    (rest X : List Admin) :
    (LabCtx.label n cont pre L rest).fill X = [.label n cont (vals pre ++ L.fill X ++ rest)] := by
  rw [LabCtx.fill]

/-- A step in a value prefix and a suffix. -/
theorem step_mid {s s' : Store H} {g g' : Frame} {Y Y' : List Admin}
    (h : Step P host ⟨s, g, Y⟩ ⟨s', g', Y'⟩) (pre : List Val) (rest : List Admin) :
    Step P host ⟨s, g, vals pre ++ Y ++ rest⟩ ⟨s', g', vals pre ++ Y' ++ rest⟩ :=
  Step.append_right (Step.vals_left h pre) rest

/-- **Steps lift through a label-only context.** -/
theorem fill_step {s s' : Store H} {g g' : Frame} {Y Y' : List Admin}
    (h : Step P host ⟨s, g, Y⟩ ⟨s', g', Y'⟩) :
    ∀ L : LabCtx, Step P host ⟨s, g, L.fill Y⟩ ⟨s', g', L.fill Y'⟩
  | .hole => by rw [fill_hole, fill_hole]; exact h
  | .label n cont pre L rest => by
    rw [fill_label, fill_label]
    exact .ctxtLabel (step_mid (fill_step h L) pre rest)

theorem fill_steps {s s' : Store H} {g g' : Frame} {Y Y' : List Admin}
    (h : Steps P host ⟨s, g, Y⟩ ⟨s', g', Y'⟩) (L : LabCtx) :
    Steps P host ⟨s, g, L.fill Y⟩ ⟨s', g', L.fill Y'⟩ :=
  Relation.ReflTransGen.lift (fun c : Config H => (⟨c.store, c.frame, L.fill c.code⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩; exact fill_step hs L) _ _ h

/-- **Bubbling a kernel out of a label-only context.** A kernel `κ` that leaves a label keeping
the values before it (`return_call_ref-label`, `return-label`) leaves every label-only context;
the values of the context accumulate in front of it. -/
theorem bubble {κ : Admin}
    (hlab : ∀ (s : Store H) (g : Frame) (n : Nat) (cont : List Instr) (vs : List Val)
      (rest : List Admin),
      Step P host ⟨s, g, [.label n cont (vals vs ++ [κ] ++ rest)]⟩ ⟨s, g, vals vs ++ [κ]⟩)
    (s : Store H) (g : Frame) :
    ∀ (L : LabCtx) (W : List Val) (restL : List Admin),
      ∃ (W₀ : List Val) (R : List Admin),
        Steps P host ⟨s, g, L.fill (vals W ++ κ :: restL)⟩ ⟨s, g, vals (W₀ ++ W) ++ κ :: R⟩
  | .hole, W, restL => ⟨[], restL, by rw [fill_hole, List.nil_append]⟩
  | .label n cont pre L rest, W, restL => by
    obtain ⟨W₀, R, h⟩ := bubble hlab s g L W restL
    have hin : Steps P host ⟨s, g, (LabCtx.label n cont pre L rest).fill (vals W ++ κ :: restL)⟩
        ⟨s, g, [.label n cont (vals (pre ++ W₀ ++ W) ++ [κ] ++ (R ++ rest))]⟩ := by
      rw [fill_label]
      have h' := Steps.label (n := n) (cont := cont)
        (Steps.ctxtInstrs (vs := pre) (rest := rest) h)
      simpa [vals_append, List.append_assoc] using h'
    have hout := hlab s g n cont (pre ++ W₀ ++ W) (R ++ rest)
    refine ⟨pre ++ W₀, [], ?_⟩
    have e : vals (pre ++ W₀ ++ W) ++ [κ] = vals (pre ++ W₀ ++ W) ++ κ :: [] := rfl
    exact hin.tail (e ▸ hout)

/-- **A trap or thrown exception leaves a label-only context.** -/
theorem cut {K : List Admin}
    (hdisc : ∀ (s : Store H) (g : Frame) (W : List Val) (R : List Admin),
      Steps P host ⟨s, g, vals W ++ K ++ R⟩ ⟨s, g, K⟩)
    (hlab : ∀ (s : Store H) (g : Frame) (n : Nat) (cont : List Instr),
      Step P host ⟨s, g, [.label n cont K]⟩ ⟨s, g, K⟩)
    (s : Store H) (g : Frame) :
    ∀ (L : LabCtx) (W : List Val) (restL : List Admin),
      Steps P host ⟨s, g, L.fill (vals W ++ K ++ restL)⟩ ⟨s, g, K⟩
  | .hole, W, restL => by rw [fill_hole]; exact hdisc s g W restL
  | .label n cont pre L rest, W, restL => by
    rw [fill_label]
    have h₁ : Steps P host ⟨s, g, [.label n cont (vals pre ++ L.fill (vals W ++ K ++ restL) ++ rest)]⟩
        ⟨s, g, [.label n cont (vals pre ++ K ++ rest)]⟩ :=
      Steps.label (Steps.ctxtInstrs (cut hdisc hlab s g L W restL))
    have h₂ : Steps P host ⟨s, g, [.label n cont (vals pre ++ K ++ rest)]⟩
        ⟨s, g, [.label n cont K]⟩ := Steps.label (hdisc s g pre rest)
    exact (h₁.trans h₂).tail (hlab s g n cont)

/-- Discarding around a trap. -/
theorem disc_trap (s : Store H) (g : Frame) (W : List Val) (R : List Admin) :
    Steps P host ⟨s, g, vals W ++ [.trap] ++ R⟩ ⟨s, g, [.trap]⟩ := by
  by_cases hne : W ≠ [] ∨ R ≠ []
  · exact .single (.trapInstrs hne)
  · have hW : W = [] := by simpa using (not_or.mp hne).1
    have hR : R = [] := by simpa using (not_or.mp hne).2
    rw [hW, hR]
    exact .refl

/-- Discarding around a thrown exception. -/
theorem disc_throw (a : Nat) (s : Store H) (g : Frame) (W : List Val) (R : List Admin) :
    Steps P host ⟨s, g, vals W ++ throwing a ++ R⟩ ⟨s, g, throwing a⟩ := by
  by_cases hne : W ≠ [] ∨ R ≠ []
  · exact .single (.throwRefInstrs hne)
  · have hW : W = [] := by simpa using (not_or.mp hne).1
    have hR : R = [] := by simpa using (not_or.mp hne).2
    rw [hW, hR]
    exact .refl

/-- **The source's pending tail call leaves its labels and its frame**: it becomes the call of
`a` on the arguments `vs`, outside the caller's frame. -/
theorem src_exit {s : Store H} {f fi : Frame} {k : Nat} {pre pre' vs : List Val} {L : LabCtx}
    {a : Nat} {c : Admin} {restL rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    Steps P host ⟨s, f, [srcPending k fi pre L pre' vs a c restL rest]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  have hlab : ∀ (s : Store H) (g : Frame) (n : Nat) (cont : List Instr) (vs : List Val)
      (rest : List Admin),
      Step P host ⟨s, g, [.label n cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, g, vals vs ++ [c]⟩ :=
    fun _ _ _ _ _ _ => .returnCallRefLabel hc
  obtain ⟨W₀, R, hb⟩ := bubble hlab s fi L (pre' ++ (vs ++ [.ref (.func a)])) restL
  have h₁ : Steps P host ⟨s, f, [srcPending k fi pre L pre' vs a c restL rest]⟩
      ⟨s, f, [.frame k fi (vals (pre ++ W₀ ++ pre') ++ vals vs ++ [.ref (.func a), c] ++
        (R ++ rest))]⟩ := by
    have h' := Steps.frame (f := f) (n := k)
      (Steps.ctxtInstrs (vs := pre) (rest := rest) hb)
    simpa [srcPending, vals, Val.toAdmin, List.append_assoc] using h'
  have h₂ := Step.returnCallRefFrameAddr (P := P) (host := host) (s := s) (f := f) (fi := fi)
    (k := k) (vs' := pre ++ W₀ ++ pre') (vs := vs) (rest := R ++ rest) hc hf he hn
  exact h₁.tail h₂

/-- **A step of the callee lifts into the target's wrapper.** -/
theorem wrap_step {s s' : Store H} {f fi fi' : Frame} {k : Nat} {pre pre' : List Val}
    {L : LabCtx} {X X' restL rest : List Admin} (h : Step P host ⟨s, fi, X⟩ ⟨s', fi', X'⟩) :
    Step P host ⟨s, f, [tgtWrap k fi pre L pre' X restL rest]⟩
      ⟨s', f, [tgtWrap k fi' pre L pre' X' restL rest]⟩ := by
  have hX := step_mid h pre' (.plain .return_ :: restL)
  have hL := fill_step hX L
  have h' := Step.ctxtFrame (f := f) (n := k) (step_mid hL pre rest)
  simpa [tgtWrap, List.append_assoc] using h'

/-- **The wrapper returns the callee's results** when there are as many as the caller's
arity. -/
theorem wrap_vals {s : Store H} {f fi : Frame} {k : Nat} {pre pre' r : List Val} {L : LabCtx}
    {restL rest : List Admin} (hk : r.length = k) :
    Steps P host ⟨s, f, [tgtWrap k fi pre L pre' (vals r) restL rest]⟩ ⟨s, f, vals r⟩ := by
  have hlab : ∀ (s : Store H) (g : Frame) (n : Nat) (cont : List Instr) (vs : List Val)
      (rest : List Admin),
      Step P host ⟨s, g, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, g, vals vs ++ [.plain .return_]⟩ :=
    fun _ _ _ _ _ _ => .returnLabel
  obtain ⟨W₀, R, hb⟩ := bubble hlab s fi L (pre' ++ r) restL
  have h₁ : Steps P host ⟨s, f, [tgtWrap k fi pre L pre' (vals r) restL rest]⟩
      ⟨s, f, [.frame k fi (vals (pre ++ W₀ ++ pre') ++ vals r ++ [.plain .return_] ++
        (R ++ rest))]⟩ := by
    have h' := Steps.frame (f := f) (n := k)
      (Steps.ctxtInstrs (vs := pre) (rest := rest) hb)
    simpa [tgtWrap, vals_append, List.append_assoc] using h'
  exact h₁.tail (.returnFrame hk)

/-- The wrapper around a trap traps. -/
theorem wrap_trap {s : Store H} {f fi : Frame} {k : Nat} {pre pre' : List Val} {L : LabCtx}
    {restL rest : List Admin} :
    Steps P host ⟨s, f, [tgtWrap k fi pre L pre' [.trap] restL rest]⟩ ⟨s, f, [.trap]⟩ := by
  have hc := cut (P := P) (host := host) (K := [.trap]) disc_trap (fun _ _ _ _ => .trapLabel) s fi L pre'
    (.plain .return_ :: restL)
  have h₁ : Steps P host ⟨s, f, [tgtWrap k fi pre L pre' [.trap] restL rest]⟩
      ⟨s, f, [.frame k fi [.trap]]⟩ := by
    have h' := Steps.frame (f := f) (n := k)
      ((Steps.ctxtInstrs (vs := pre) (rest := rest) hc).trans (disc_trap s fi pre rest))
    simpa [tgtWrap, List.append_assoc] using h'
  exact h₁.tail .trapFrame

/-- The wrapper around a thrown exception throws it. -/
theorem wrap_throw {s : Store H} {f fi : Frame} {k : Nat} {pre pre' : List Val} {L : LabCtx}
    {restL rest : List Admin} (a : Nat) :
    Steps P host ⟨s, f, [tgtWrap k fi pre L pre' (throwing a) restL rest]⟩ ⟨s, f, throwing a⟩ := by
  have hc := cut (P := P) (host := host) (K := throwing a) (disc_throw a) (fun _ _ _ _ => .throwRefLabel) s fi L pre'
    (.plain .return_ :: restL)
  have h₁ : Steps P host ⟨s, f, [tgtWrap k fi pre L pre' (throwing a) restL rest]⟩
      ⟨s, f, [.frame k fi (throwing a)]⟩ := by
    have h' := Steps.frame (f := f) (n := k)
      ((Steps.ctxtInstrs (vs := pre) (rest := rest) hc).trans (disc_throw a s fi pre rest))
    simpa [tgtWrap, List.append_assoc] using h'
  exact h₁.tail .throwRefFrame

end Silmaril.Proofs.Wasm.LimeCompile.TailRel
