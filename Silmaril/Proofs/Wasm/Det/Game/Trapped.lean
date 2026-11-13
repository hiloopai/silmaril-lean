module

public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# Trapped code stays trapped

A thread resumed with a trap holds `E.fill [TRAP]`, a `TRAP` under a callout context. Every
host-free step from such code, at every profile, leads to code of the same shape
(`step_trapped`): the step is a bubble of the `TRAP` or a step inside a label, handler or frame
around it. Hence a host-free run from trapped code never reaches an import call
(`Ctx.decompose?_fill_trap`) and finishes only with a trap (`fill_trap_toAdmin`).

New proofs; they follow the case split of
`Silmaril.Proofs.Wasm.Game.Choice.step_doomed`, by direct head inversion instead of `soft_join`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)

/-- The first non-value of trapped code: the `TRAP`, or a block around it. -/
def TrapHead : Admin → Prop
  | .trap => True
  | .label .. => True
  | .handler .. => True
  | .frame .. => True
  | _ => False

theorem fill_trap_split (E : Ctx) :
    ∃ pre x rest, E.fill [.trap] = vals pre ++ x :: rest ∧ x.val? = none ∧ TrapHead x := by
  cases E with
  | top pre rest => exact ⟨pre, .trap, rest, by simp [Ctx.fill], rfl, trivial⟩
  | label pre n cont E rest =>
    exact ⟨pre, .label n cont (E.fill [.trap]), rest, by simp [Ctx.fill], rfl, trivial⟩
  | handler pre n cs E rest =>
    exact ⟨pre, .handler n cs (E.fill [.trap]), rest, by simp [Ctx.fill], rfl, trivial⟩
  | frame pre n f E rest =>
    exact ⟨pre, .frame n f (E.fill [.trap]), rest, by simp [Ctx.fill], rfl, trivial⟩

/-- The head after the value prefix. -/
def TrapHeadL : List Admin → Prop
  | x :: _ => TrapHead x
  | [] => False

/-- The first non-value of trapped code is a `TrapHead`. -/
theorem fill_trap_fnv (E : Ctx) : TrapHeadL (fnv (E.fill [.trap])).2 := by
  obtain ⟨pre, x, rest, hf, hx, ht⟩ := fill_trap_split E
  rw [hf, fnv_vals_append, fnv_cons_of_none hx]
  exact ht

theorem retCallRef_ok {c : Admin} (hc : c.IsReturnCallRef) : c.val? = none ∧ ¬ TrapHead c := by
  rcases c with i | _ | _ | _ | _ | _ | _ | _
  · cases i <;> first | exact hc.elim | exact ⟨rfl, id⟩
  all_goals first | exact hc.elim | exact ⟨rfl, id⟩

/-- Trapped code starts with a `TrapHead`. -/
theorem no_fill {E : Ctx} {X : List Admin} (h : X = E.fill [.trap])
    (hX : ¬ TrapHeadL (fnv X).2) : False :=
  hX (h ▸ fill_trap_fnv E)

/-- Not the family of a block. -/
local macro "no_fam" : tactic => `(tactic| first
  | exact absurd (famOf_of_shape (ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (AggregateStep.shape ‹_›)).2 (by simp [famOf]))

variable {H : Type} {P : Profile}

theorem no_rcr {E : Ctx} {B : List Admin} {vs : List Val} {c : Admin} {rest : List Admin}
    (hB : B = E.fill [.trap]) (hb : B = vals vs ++ [c] ++ rest) (hc : c.IsReturnCallRef) :
    False := by
  have h := fill_trap_fnv E
  rw [← hB, hb] at h
  simp only [List.append_assoc, List.singleton_append, fnv_vals_append,
    fnv_cons_of_none (retCallRef_ok hc).1, TrapHeadL] at h
  exact (retCallRef_ok hc).2 h

/-- Host-free steps from `E.fill [TRAP]` lead to trapped code. -/
def StepsTrapped (P : Profile) (H : Type) (E : Ctx) : Prop :=
  ∀ (s : Store H) (f : Frame) (d : Config H), Step P noHost ⟨s, f, E.fill [.trap]⟩ d →
    ∃ E' : Ctx, d.code = E'.fill [.trap]

theorem ctxt_trapped {E : Ctx} {B is' : List Admin} {s s' : Store H} {f f' : Frame}
    (hB : B = E.fill [.trap]) (h : Step P noHost ⟨s, f, B⟩ ⟨s', f', is'⟩)
    (ih : StepsTrapped P H E) : ∃ E' : Ctx, is' = E'.fill [.trap] := by
  subst hB
  exact ih _ _ _ h

variable {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H} {E : Ctx}
  {B : List Admin} {n : Nat}

/-- A head step of a label around trapped code. -/
theorem head_label {cont : List Instr} (hB : B = E.fill [.trap])
    (hh : Head P s f args (.label n cont B) c₀) (ih : StepsTrapped P H E) :
    args = [] ∧ ∃ E' : Ctx, c₀.code = E'.fill [.trap] := by
  cases hh with
  | ctxtLabel h =>
    obtain ⟨E', hE'⟩ := ctxt_trapped hB h ih
    exact ⟨rfl, .label [] n cont E' [], by simp [Ctx.fill, hE']⟩
  | trapLabel => exact ⟨rfl, .top [] [], by simp [Ctx.fill]⟩
  | labelVals hb => exact (Ctx.fill_trap_not_vals E ⟨_, hB.symm.trans hb⟩).elim
  | returnCallRefLabel hb hc => exact (no_rcr hB hb hc).elim
  | brLabelZero hb | brLabelSucc hb | returnLabel hb =>
    exact (no_fill (hb.symm.trans hB) (by simp [TrapHeadL, TrapHead])).elim
  | throwRefLabel => exact (no_fill hB (by simp [TrapHeadL, TrapHead, fnv, Admin.val?])).elim
  | callRefNull hc | callRefFunc _ hc => exact hc.elim
  | parametric | numeric | vector | «variable» | table | memory | reference | aggregate =>
    no_fam

/-- A head step of a handler around trapped code. -/
theorem head_handler {cs : List Catch} (hB : B = E.fill [.trap])
    (hh : Head P s f args (.handler n cs B) c₀) (ih : StepsTrapped P H E) :
    args = [] ∧ ∃ E' : Ctx, c₀.code = E'.fill [.trap] := by
  cases hh with
  | ctxtHandler h =>
    obtain ⟨E', hE'⟩ := ctxt_trapped hB h ih
    exact ⟨rfl, .handler [] n cs E' [], by simp [Ctx.fill, hE']⟩
  | trapHandler => exact ⟨rfl, .top [] [], by simp [Ctx.fill]⟩
  | handlerVals hb => exact (Ctx.fill_trap_not_vals E ⟨_, hB.symm.trans hb⟩).elim
  | returnCallRefHandler hb hc => exact (no_rcr hB hb hc).elim
  | brHandler hb | returnHandler hb =>
    exact (no_fill (hb.symm.trans hB) (by simp [TrapHeadL, TrapHead])).elim
  | throwRefHandlerEmpty | throwRefHandlerCatch | throwRefHandlerCatchRef
  | throwRefHandlerCatchAll | throwRefHandlerCatchAllRef | throwRefHandlerNext =>
    exact (no_fill hB (by simp [TrapHeadL, TrapHead, fnv, Admin.val?])).elim
  | callRefNull hc | callRefFunc _ hc => exact hc.elim
  | parametric | numeric | vector | «variable» | table | memory | reference | aggregate =>
    no_fam

/-- A head step of a frame around trapped code. -/
theorem head_frame {fi : Frame} (hB : B = E.fill [.trap])
    (hh : Head P s f args (.frame n fi B) c₀) (ih : StepsTrapped P H E) :
    args = [] ∧ ∃ E' : Ctx, c₀.code = E'.fill [.trap] := by
  cases hh with
  | ctxtFrame h =>
    obtain ⟨E', hE'⟩ := ctxt_trapped hB h ih
    exact ⟨rfl, .frame [] n _ E' [], by simp only [Ctx.fill, hE']; rfl⟩
  | trapFrame => exact ⟨rfl, .top [] [], by simp [Ctx.fill]⟩
  | frameVals hb => exact (Ctx.fill_trap_not_vals E ⟨_, hB.symm.trans hb⟩).elim
  | @returnCallRefFrameNull _ _ _ _ vs c rest hb hc =>
    exact (no_rcr hB (vs := vs ++ [.ref .null]) (rest := rest) (by rw [hb]; simp [vals, Val.toAdmin])
      hc).elim
  | @returnCallRefFrameAddr _ _ _ _ vs' vs a c rest _ _ _ hb hc _ _ _ =>
    exact (no_rcr hB (vs := vs' ++ vs ++ [.ref (.func a)]) (rest := rest)
      (by rw [hb]; simp [vals, Val.toAdmin]) hc).elim
  | returnFrame hb => exact (no_fill (hb.symm.trans hB) (by simp [TrapHeadL, TrapHead])).elim
  | throwRefFrame => exact (no_fill hB (by simp [TrapHeadL, TrapHead, fnv, Admin.val?])).elim
  | callRefNull hc | callRefFunc _ hc => exact hc.elim
  | parametric | numeric | vector | «variable» | table | memory | reference | aggregate =>
    no_fam

/-- A step of a block around trapped code. -/
theorem block_case {s : Store H} {f : Frame} {d : Config H} {pre : List Val} {x : Admin}
    {rest : List Admin} (hx : x.val? = none) (hnt : x ≠ .trap) (hnr : x ≠ .plain .throwRef)
    (hstep : Step P noHost ⟨s, f, vals pre ++ x :: rest⟩ d)
    (hhead : ∀ args c₀, Head P s f args x c₀ → args = [] ∧ ∃ E' : Ctx, c₀.code = E'.fill [.trap]) :
    ∃ E' : Ctx, d.code = E'.fill [.trap] := by
  obtain ⟨vs, args, c₀, -, hh, rfl⟩ := hostFree_head_inv hx hnt hnr hstep
  obtain ⟨rfl, E', hE'⟩ := hhead _ _ hh
  exact ⟨E'.wrap vs rest, by simp [hE', Ctx.fill_wrap]⟩

/-- A step from a top-level `TRAP` bubbles it. -/
theorem step_top_trapped {pre : List Val} {rest : List Admin} {d : Config H}
    (h : Step P noHost ⟨s, f, (Ctx.top pre rest).fill [.trap]⟩ d) :
    ∃ E' : Ctx, d.code = E'.fill [.trap] := by
  have hf : fnv (Ctx.fill (.top pre rest) [.trap]) = (pre, .trap :: rest) := by
    simp [Ctx.fill]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest', c₀, hf', -, hh, -⟩ := fnv_headDec hd
    have he : (pre, Admin.trap :: rest) = (vs ++ args, e :: rest') := hf.symm.trans hf'
    have he' : Admin.trap = e := by simp only [Prod.mk.injEq, List.cons.injEq] at he; exact he.2.1
    exact (hh.good.ne_trap he'.symm).elim
  · obtain ⟨p, q, u, r, -, ⟨-, -, hc⟩ | ⟨a, hf', -, -⟩⟩ := fnv_bubble hb
    · exact ⟨.top p r, by rw [hc]; simp [Ctx.fill]⟩
    · have he : (pre, Admin.trap :: rest) = _ := hf.symm.trans hf'
      simp at he

/-- **A host-free step from trapped code leads to trapped code**, at every profile. -/
theorem step_trapped (E : Ctx) : StepsTrapped P H E := by
  induction E with
  | top pre rest => exact fun _ _ _ h => step_top_trapped h
  | label pre n cont E rest ih =>
    intro s f d h
    have h' : Step P noHost ⟨s, f, vals pre ++ .label n cont (E.fill [.trap]) :: rest⟩ d := by
      simpa [Ctx.fill] using h
    exact block_case rfl (by simp) (by simp) h' (fun _ _ hh => head_label rfl hh ih)
  | handler pre n cs E rest ih =>
    intro s f d h
    have h' : Step P noHost ⟨s, f, vals pre ++ .handler n cs (E.fill [.trap]) :: rest⟩ d := by
      simpa [Ctx.fill] using h
    exact block_case rfl (by simp) (by simp) h' (fun _ _ hh => head_handler rfl hh ih)
  | frame pre n fi E rest ih =>
    intro s f d h
    have h' : Step P noHost ⟨s, f, vals pre ++ .frame n fi (E.fill [.trap]) :: rest⟩ d := by
      simpa [Ctx.fill] using h
    exact block_case rfl (by simp) (by simp) h' (fun _ _ hh => head_frame rfl hh ih)

end Silmaril.Proofs.Wasm.Det.Game

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-- **Host-free runs from trapped code stay trapped.** -/
theorem reach_trapped {P : Profile} {s s' : Store Nat} {F : Frame} {E : Ctx} {t' : Thread}
    (h : Reach P (s, .active F (E.fill [.trap])) (s', t')) :
    ∃ E' : Ctx, (t'.config s').code = E'.fill [.trap] := by
  suffices ∀ y, Reach P (s, .active F (E.fill [.trap])) y →
      ∃ E' : Ctx, (y.2.config y.1).code = E'.fill [.trap] from this _ h
  intro y hy
  induction hy with
  | refl => exact ⟨E, rfl⟩
  | tail _ hyz ih =>
    obtain ⟨E', hE'⟩ := ih
    obtain ⟨f', c', hz, hst⟩ := hyz
    rename_i y z _
    have hc : y.2.config y.1 =
        ⟨(y.2.config y.1).store, (y.2.config y.1).frame, E'.fill [.trap]⟩ := by
      rw [← hE']
    rw [hc] at hst
    obtain ⟨E'', hE''⟩ := step_trapped E' _ _ _ hst
    refine ⟨E'', ?_⟩
    rw [hz]
    exact hE''

/-- Trapped code is the code of a result only if that result is a trap. -/
theorem fill_trap_toAdmin {E : Ctx} {r : Result} (h : E.fill [.trap] = r.toAdmin) :
    r = .trap := by
  cases r with
  | trap => rfl
  | values vs => exact (Ctx.fill_trap_not_vals E ⟨vs, h⟩).elim
  | throw a =>
    have h' := fill_trap_fnv E
    rw [h] at h'
    simp [Result.toAdmin, TrapHeadL, TrapHead, fnv, Admin.val?] at h'

end Silmaril.Proofs.Wasm.Det.Game
