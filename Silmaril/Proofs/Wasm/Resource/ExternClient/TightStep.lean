module

public import Silmaril.Proofs.Wasm.Resource.ExternClient.Tight

/-!
# Call targets: preservation by every Core step

**`Step.tight`**: a host-free Core 3.0 step (every profile) keeps `Tight R true p`, from the
reachability invariant `CfgIn G fs (CallPl R bad fs)`, bodies of the functions of `G` without
dynamic calls, and a step that is not a call of a function in `bad` (`BadStep`). The step
families never produce a call instruction (`tight_simple`); `call` and `return_call` name
functions of `R` (`CallPl`); `call_ref` of a Wasm function opens a body without dynamic calls;
`return_call_ref` leaving a block keeps the reference and its call together; the dynamic calls
are excluded.

`BadStep.ctxtInstrs`, `BadStep.ctxtLabel`, `BadStep.ctxtHandler`, `BadStep.ctxtFrame`: a bad
call under a context is a bad call.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn RefIn PlOK CallPl BadStep refFuncs instrRF instrCalls
  instrCallees)

variable {H : Type} {R G : Nat → Prop} {bad : Nat → Bool} {fs : List Nat} {B : Nat → Prop}

/-! ## Bad calls under contexts -/

theorem BadStep.ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hb : BadStep B fs ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    BadStep B fs ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨E, x, a, d, he, he', hx, ha⟩ := hb
  cases he'
  exact ⟨E.wrap vs rest, x, a, d, by simp only [Ctx.fill_wrap, ← he], by simp only [Ctx.fill_wrap],
    hx, ha⟩

theorem BadStep.ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (hb : BadStep B fs ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    BadStep B fs ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨E, x, a, d, he, he', hx, ha⟩ := hb
  cases he'
  exact ⟨.label [] n cont E [], x, a, d, by simp [Ctx.fill, vals, ← he], by simp [Ctx.fill, vals],
    hx, ha⟩

theorem BadStep.ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (hb : BadStep B fs ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    BadStep B fs ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨E, x, a, d, he, he', hx, ha⟩ := hb
  cases he'
  exact ⟨.handler [] n cs E [], x, a, d, by simp [Ctx.fill, vals, ← he], by simp [Ctx.fill, vals],
    hx, ha⟩

theorem BadStep.ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (hb : BadStep B fs ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    BadStep B fs ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨E, x, a, d, he, he', hx, ha⟩ := hb
  cases he'
  exact ⟨.frame [] n fi E [], x, a, d, by simp [Ctx.fill, vals, ← he], by simp [Ctx.fill, vals],
    hx, ha⟩

/-! ## The families -/

@[simp] theorem simpleT_constI32 (b : BitVec 32) : SimpleT (constI32 b) := simpleT_toAdmin _

/-- Close `Tight` of a right-hand side without call instructions. -/
macro "tight_simple_tac" : tactic => `(tactic| (
  apply tight_simple
  verify_mem_split
  all_goals first
    | (simp [noDynI, arrRef, store8, load8u]; done)
    | (intro _ _; simp [noDynI, arrRef, store8, load8u]; done)
    | (intro _; simp [noDynI, arrRef, store8, load8u]; done)
    | trivial))

section
variable {P : Profile} {p : Prop}

theorem ParametricStep.tight {is is' : List Admin} (h : ParametricStep is is') :
    Tight R true p is' := by
  cases h <;> tight_simple_tac

theorem NumericStep.tight {is is' : List Admin} (h : NumericStep P is is') :
    Tight R true p is' := by
  cases h <;> tight_simple_tac

theorem VectorStep.tight {is is' : List Admin} (h : VectorStep P is is') :
    Tight R true p is' := by
  cases h <;> tight_simple_tac

theorem VariableStep.tight {c c' : Config H} (h : VariableStep c c') : Tight R true p c'.code := by
  cases h <;> tight_simple_tac

theorem TableStep.tight {c c' : Config H} (h : TableStep P c c') : Tight R true p c'.code := by
  cases h <;> tight_simple_tac

theorem MemoryStep.tight {c c' : Config H} (h : MemoryStep P c c') : Tight R true p c'.code := by
  cases h <;> tight_simple_tac

theorem RefStep.tight {c c' : Config H} (h : RefStep c c') : Tight R true p c'.code := by
  cases h <;> tight_simple_tac

theorem AggregateStep.tight {c c' : Config H} (h : AggregateStep c c') :
    Tight R true p c'.code := by
  cases h <;> tight_simple_tac

end

/-! ## One element -/

theorem tight_label_single {n : Nat} {k : List Instr} {b : List Admin} {pr : Bool} {p : Prop} :
    Tight R pr p [.label n k b] ↔ noDynL k = true ∧ Tight R true False b := by
  simp [Tight]

theorem tight_handler_single {n : Nat} {cs : List Catch} {b : List Admin} {pr : Bool} {p : Prop} :
    Tight R pr p [.handler n cs b] ↔ Tight R true False b := by
  simp [Tight]

theorem tight_frame_single {n : Nat} {fr : Frame} {b : List Admin} {pr : Bool} {p : Prop} :
    Tight R pr p [.frame n fr b] ↔ Tight R true False b := by
  simp [Tight]

theorem tight_vals_plain {vs : List Val} {i : Instr} {l : List Admin} {pr : Bool} {p : Prop}
    (h : Tight R pr p (vals vs ++ .plain i :: l)) : noDynI i = true := by
  rw [tight_vals_append] at h
  simp only [Tight] at h
  exact h.1

theorem isReturnCallRef_cases {c : Admin} (h : c.IsReturnCallRef) :
    (∃ y, c = .plain (.returnCallRef y)) ∨ ∃ d, c = .returnCallRefType d := by
  unfold Admin.IsReturnCallRef at h
  split at h <;> simp_all

theorem afP_false_vals (vs : List Val) (p : Prop) : afP R False (vals vs) → afP R p (vals vs) :=
  afP_mono False.elim

/-! ## The rules -/

section Rules
variable {P : Profile} {p : Prop}

theorem tight_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hs : Step P (fun _ _ _ _ => False) ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : Tight R true (afP R p (vals vs)) is → Tight R true (afP R p (vals vs)) is')
    (ht : Tight R true p (vals vs ++ is ++ rest)) : Tight R true p (vals vs ++ is' ++ rest) := by
  have hall : (vals vs ++ is).all Admin.isVal = false := by
    simpa [List.all_append] using Step.not_all_isVal hs
  have h₁ : Tight R true p (vals vs ++ is) ∧ Tight R false (afP R p (vals vs ++ is)) rest := by
    simpa [afPr_of_not_all _ _ hall] using (tight_append _ rest true p).1 ht
  have h₂ : Tight R true (afP R p (vals vs)) is := (tight_vals_append vs is true p).1 h₁.1
  exact (tight_append _ rest true p).2
    ⟨(tight_vals_append vs is' true p).2 (ih h₂), Tight.of_post _ _ h₁.2⟩

theorem tight_body_of_plain {vs : List Val} {i : Instr} {b : List Instr}
    (ht : Tight R true p (vals vs ++ [.plain i])) (hi : noDynI i = true → noDynL b = true) :
    ∀ pr q, Tight R pr q (vals vs ++ expression b) :=
  tight_vals_expression (hi (tight_vals_plain ht))

theorem tight_if {c : Admin} {bt : BlockType} {b₁ b₂ : List Instr} (hc : c.val?.isSome = true)
    (hcd : ∃ i, c = .plain i ∧ noDynI i = true)
    (ht : Tight R true p [c, .plain (.if_ bt b₁ b₂)]) :
    noDynL b₁ = true ∧ noDynL b₂ = true := by
  obtain ⟨i, rfl, -⟩ := hcd
  have h₁ : noDynI (.if_ bt b₁ b₂) = true := (by simpa [Tight, hc] using ht : _ ∧ _).2
  simpa [noDynI] using h₁

theorem tight_if_post {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
    (ht : Tight R true p [constI32 c, .plain (.if_ bt b₁ b₂)]) :
    Tight R true p [.plain (.block bt b₁)] ∧ Tight R true p [.plain (.block bt b₂)] := by
  have hb : noDynL b₁ = true ∧ noDynL b₂ = true := tight_if rfl ⟨_, rfl, rfl⟩ ht
  exact ⟨tight_simple (by simpa [noDynI] using hb.1) _ _,
    tight_simple (by simpa [noDynI] using hb.2) _ _⟩

theorem tight_call_post {G : Nat → Prop} {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    {d : DefType} (hc : CfgIn G fs (CallPl R bad fs) ⟨s, f, [.plain (.call x)]⟩)
    (hx : f.module.funcs[x.toNat]? = some a)
    (hnb : ¬ BadStep (fun a => bad a = true) fs (⟨s, f, [.plain (.call x)]⟩ : Config H)
      ⟨s, f, [.ref (.func a), .callRefType d]⟩) :
    Tight R true p [.ref (.func a), .callRefType d] := by
  have hi : CallPl R bad fs (.call x) :=
    hc.2.2.plain_head.of_callee (x := x.toNat) (by simp [instrCallees])
  have hfx : fs[x.toNat]? = some a := hc.2.1.resolve hx
  have hR : R a := (hi.2 x.toNat (by simp [instrCalls]) a hfx).resolve_right fun hb =>
    hnb ⟨.top [] [], x, a, d, by simp [Ctx.fill, vals], by simp [Ctx.fill, vals], hfx, hb⟩
  simp [Tight, RefIn, refFuncs, hR]

theorem tight_returnCall_post {G : Nat → Prop} {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    {d : DefType} (hc : CfgIn G fs (CallPl R bad fs) ⟨s, f, [.plain (.returnCall x)]⟩)
    (hx : f.module.funcs[x.toNat]? = some a) :
    Tight R true p [.ref (.func a), .returnCallRefType d] := by
  have hi : CallPl R bad fs (.returnCall x) :=
    hc.2.2.plain_head.of_callee (x := x.toNat) (by simp [instrCallees])
  have hR : R a := hi.1 x.toNat (by simp [instrRF]) a (hc.2.1.resolve hx)
  simp [Tight, RefIn, refFuncs, hR]

/-- `return_call_ref` leaving a block: the values and the call stay together. -/
theorem tight_returnCall_out {vs : List Val} {c : Admin} {rest : List Admin}
    (hcr : c.IsReturnCallRef) (hb : Tight R true False (vals vs ++ [c] ++ rest)) :
    Tight R true p (vals vs ++ [c]) := by
  have hb' : Tight R true (afP R False (vals vs)) (c :: rest) := by
    simpa [List.append_assoc] using (tight_vals_append vs ([c] ++ rest) true False).1
      (by simpa [List.append_assoc] using hb)
  refine (tight_vals_append vs [c] true p).2 ?_
  rcases isReturnCallRef_cases hcr with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact absurd hb' (by simp [Tight, noDynI])
  · have hp : afP R False (vals vs) := (by simpa [Tight] using hb' : _ ∧ _).1
    simpa [Tight] using afP_false_vals vs p hp

/-- `return_call_ref` leaving a frame: the reference and its call stay together. -/
theorem tight_returnCallFrame_out {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin}
    (hcr : c.IsReturnCallRef) (m : ModuleInst)
    (hb : Tight R true False (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)) :
    Tight R true p (vals vs ++ [.ref (.func a), c.retToCallIn m]) := by
  have hb' : Tight R true (RefIn R (.func a)) (c :: rest) := by
    have h₁ := (tight_vals_append (vs' ++ vs) ([.ref (.func a), c] ++ rest) true False).1
      (by simpa [vals_append, List.append_assoc] using hb)
    simpa [Tight] using h₁
  refine (tight_vals_append vs _ true p).2 ?_
  rcases isReturnCallRef_cases hcr with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact absurd hb' (by simp [Tight, noDynI])
  · have hR : RefIn R (.func a) := by
      simpa [RefIn, refFuncs] using (by simpa [Tight] using hb' : _ ∧ _).1
    simpa [Tight, Admin.retToCallIn] using hR

end Rules

/-! ## Every step -/

/-- **Every host-free Core 3.0 step keeps the call targets in `R`** (every profile), outside the
calls of functions in `bad`. -/
theorem Step.tight {P : Profile} {c c' : Config H} (h : Step P (fun _ _ _ _ => False) c c') :
    CfgIn G fs (CallPl R bad fs) c →
    (∀ a fi code, G a → c.store.funcs[a]? = some fi → fi.code = .wasm code →
      noDynL code.body = true) →
    ¬ BadStep (fun a => bad a = true) fs c c' → ∀ p, Tight R true p c.code →
      Tight R true p c'.code := by
  induction h with
  | parametric h => exact fun _ _ _ _ _ => ParametricStep.tight h
  | numeric h => exact fun _ _ _ _ _ => NumericStep.tight h
  | vector h => exact fun _ _ _ _ _ => VectorStep.tight h
  | «variable» h => exact fun _ _ _ _ _ => VariableStep.tight h
  | table h => exact fun _ _ _ _ _ => TableStep.tight h
  | memory h => exact fun _ _ _ _ _ => MemoryStep.tight h
  | reference h => exact fun _ _ _ _ _ => RefStep.tight h
  | aggregate h => exact fun _ _ _ _ _ => AggregateStep.tight h
  | ctxtInstrs hs _ ih =>
    exact fun hc hnd hnb p => tight_ctxtInstrs hs (ih ⟨hc.1, hc.2.1,
      (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩ hnd (fun hb => hnb (BadStep.ctxtInstrs hb)) _)
  | ctxtLabel _ ih =>
    exact fun hc hnd hnb p ht => tight_label_single.2 ⟨(tight_label_single.1 ht).1,
      ih ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩ hnd (fun hb => hnb (BadStep.ctxtLabel hb)) _
        (tight_label_single.1 ht).2⟩
  | ctxtHandler _ ih =>
    exact fun hc hnd hnb p ht => tight_handler_single.2 (ih ⟨hc.1, hc.2.1,
      CodeIn.handler_iff.1 hc.2.2⟩ hnd (fun hb => hnb (BadStep.ctxtHandler hb)) _
        (tight_handler_single.1 ht))
  | ctxtFrame _ ih =>
    exact fun hc hnd hnb p ht => tight_frame_single.2 (ih ⟨hc.1, (CodeIn.frame_iff.1 hc.2.2).1,
      (CodeIn.frame_iff.1 hc.2.2).2⟩ hnd (fun hb => hnb (BadStep.ctxtFrame hb)) _
        (tight_frame_single.1 ht))
  | block =>
    exact fun _ _ _ p ht => tight_label_single.2
      ⟨rfl, tight_body_of_plain ht (fun h => by simpa [noDynI] using h) _ _⟩
  | loop =>
    exact fun _ _ _ p ht => tight_label_single.2
      ⟨by simpa [noDynL, noDynI] using tight_vals_plain ht,
        tight_body_of_plain ht (fun h => by simpa [noDynI] using h) _ _⟩
  | tryTable =>
    exact fun _ _ _ p ht => tight_handler_single.2 (tight_label_single.2
      ⟨rfl, tight_body_of_plain ht (fun h => by simpa [noDynI] using h) _ _⟩)
  | ifTrue => exact fun _ _ _ p ht => (tight_if_post ht).1
  | ifFalse => exact fun _ _ _ p ht => (tight_if_post ht).2
  | brLabelZero =>
    exact fun _ _ _ p ht => tight_vals_expression (tight_label_single.1 ht).1 _ _
  | call hx _ => exact fun hc _ hnb p _ => tight_call_post hc hx hnb
  | @callRefFunc s f c vs a fi ps rs code _ hf _ _ hcode =>
    exact fun hc hnd _ p _ => tight_frame_single.2 (tight_label_single.2 ⟨rfl, tight_expression
      (hnd a fi code (by simpa [refFuncs] using hc.2.2.ref_of_mem (r := .func a) (by simp)) hf
        hcode) _ _⟩)
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall hx _ => exact fun hc _ _ p _ => tight_returnCall_post hc hx
  | returnCallRefLabel hcr =>
    exact fun _ _ _ p ht => tight_returnCall_out hcr (tight_label_single.1 ht).2
  | returnCallRefHandler hcr =>
    exact fun _ _ _ p ht => tight_returnCall_out hcr (tight_handler_single.1 ht)
  | returnCallRefFrameAddr hcr =>
    exact fun _ _ _ p ht => tight_returnCallFrame_out hcr _ (tight_frame_single.1 ht)
  | callIndirect => exact fun _ _ _ p ht => absurd ht (by simp [Tight, noDynI])
  | returnCallIndirect => exact fun _ _ _ p ht => absurd ht (by simp [Tight, noDynI])
  | throwRefHandlerNext =>
    exact fun _ _ _ p _ => tight_handler_single.2 (by simp [Tight, noDynI])
  | _ => intro _ _ _ p _; tight_simple_tac

end Silmaril.Wasm.Resource.ExternClient
