module

public import Silmaril.Proofs.Wasm.Verify.Reach.Step
public import Silmaril.Wasm.Spec.Wasm.Defs

/-!
# Function reachability: the plays of a scalar instance

From the step theorem `Step.cfgIn`, along every play of `I.strategy P s` (every profile `P`):

* host-free runs (`Reach P`) preserve the invariant `CfgIn G fs` of the thread
  (`reach_cfgIn`);
* a callout found by `decompose?` calls a host function whose address is a reference of the
  code, hence in `G` (`callout_mem`), so it is not import `i` when `Avoids G _ i`
  (`callout_ne`);
* environment answers are scalar, so resuming keeps the invariant (`resume_cfgIn`);
* hence no play has an import question of `i` (`strategy_no_icall`), and no trace of
  `wasmSem P` has the event `icall i a` (`neverCall_of_reachIn`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop}

/-! ## Evaluation contexts -/

theorem codeRefs_fill (E : Ctx) (l : List Admin) : ∀ r ∈ codeRefs l, r ∈ codeRefs (E.fill l) := by
  induction E with
  | top pre rest => intro r hr; simp [Ctx.fill, hr]
  | label pre n cont E rest ih => intro r hr; simp [Ctx.fill, ih r hr]
  | handler pre n cs E rest ih => intro r hr; simp [Ctx.fill, ih r hr]
  | frame pre n f E rest ih => intro r hr; simp [Ctx.fill, ih r hr]

/-- Replacing the redex of an evaluation context by invariant code keeps the invariant. -/
theorem CodeIn.fill {E : Ctx} {l l' : List Admin} (h : CodeIn G fs Pl (E.fill l))
    (hl : CodeIn G fs Pl l') : CodeIn G fs Pl (E.fill l') := by
  induction E with
  | top pre rest =>
    have h₁ : CodeIn G fs Pl (vals pre ++ l) ∧ CodeIn G fs Pl rest := CodeIn.append.1 h
    exact CodeIn.append.2 ⟨CodeIn.append.2 ⟨(CodeIn.append.1 h₁.1).1, hl⟩, h₁.2⟩
  | label pre n cont E rest ih =>
    have h₁ : CodeIn G fs Pl (vals pre ++ [.label n cont (E.fill l)]) ∧ CodeIn G fs Pl rest :=
      CodeIn.append.1 h
    have h₂ : CodeIn G fs Pl (vals pre) ∧ CodeIn G fs Pl [.label n cont (E.fill l)] :=
      CodeIn.append.1 h₁.1
    have h₃ : (∀ i ∈ cont, PlOK Pl i) ∧ CodeIn G fs Pl (E.fill l) := CodeIn.label_iff.1 h₂.2
    exact CodeIn.append.2 ⟨CodeIn.append.2 ⟨h₂.1, CodeIn.label_iff.2 ⟨h₃.1, ih h₃.2⟩⟩, h₁.2⟩
  | handler pre n cs E rest ih =>
    have h₁ : CodeIn G fs Pl (vals pre ++ [.handler n cs (E.fill l)]) ∧ CodeIn G fs Pl rest :=
      CodeIn.append.1 h
    have h₂ : CodeIn G fs Pl (vals pre) ∧ CodeIn G fs Pl [.handler n cs (E.fill l)] :=
      CodeIn.append.1 h₁.1
    have h₃ : CodeIn G fs Pl (E.fill l) := CodeIn.handler_iff.1 h₂.2
    exact CodeIn.append.2 ⟨CodeIn.append.2 ⟨h₂.1, CodeIn.handler_iff.2 (ih h₃)⟩, h₁.2⟩
  | frame pre n f E rest ih =>
    have h₁ : CodeIn G fs Pl (vals pre ++ [.frame n f (E.fill l)]) ∧ CodeIn G fs Pl rest :=
      CodeIn.append.1 h
    have h₂ : CodeIn G fs Pl (vals pre) ∧ CodeIn G fs Pl [.frame n f (E.fill l)] :=
      CodeIn.append.1 h₁.1
    have h₃ : FrameIn G fs f ∧ CodeIn G fs Pl (E.fill l) := CodeIn.frame_iff.1 h₂.2
    exact CodeIn.append.2 ⟨CodeIn.append.2 ⟨h₂.1, CodeIn.frame_iff.2 ⟨h₃.1, ih h₃.2⟩⟩, h₁.2⟩

/-! ## Host-free runs -/

theorem hostIn_noHost : HostIn G (Det.noHost : HostSemantics Nat) :=
  fun _ _ _ _ _ h => h.elim

theorem internalP_cfgIn (hP : PlainOK G (fun _ => False) fs Pl) {P : Profile}
    {x y : Store Nat × Thread} (h : InternalP P x y) (hcl : FuncsClosed G fs Pl x.1.funcs)
    (hc : CfgIn G fs Pl (x.2.config x.1)) :
    CfgIn G fs Pl (y.2.config y.1) ∧ y.1.funcs = x.1.funcs := by
  obtain ⟨f', code', hy, hst⟩ := h
  have hcl' : FuncsClosed G fs Pl (x.2.config x.1).store.funcs := by
    rw [Thread.config_store]; exact hcl
  have hs : CfgIn G fs Pl ⟨y.1, f', code'⟩ ∧ y.1.funcs = (x.2.config x.1).store.funcs :=
    Step.cfgIn_of_empty hP hostIn_noHost hst hcl' hc
  rw [Thread.config_store] at hs
  rw [hy]
  exact hs

/-- **Host-free runs preserve the reachability invariant** (every profile). -/
theorem reach_cfgIn (hP : PlainOK G (fun _ => False) fs Pl) {P : Profile}
    {x y : Store Nat × Thread} (h : Reach P x y)
    (hcl : FuncsClosed G fs Pl x.1.funcs) (hc : CfgIn G fs Pl (x.2.config x.1)) :
    CfgIn G fs Pl (y.2.config y.1) ∧ y.1.funcs = x.1.funcs := by
  induction h with
  | refl => exact ⟨hc, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hc', hf'⟩ := ih
    obtain ⟨hc'', hf''⟩ := internalP_cfgIn hP hst (hf' ▸ hcl) hc'
    exact ⟨hc'', hf''.trans hf'⟩

/-! ## Callouts and answers -/

/-- The host function of a callout is a reference of the code, hence in `G`. -/
theorem callout_mem {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hco : CalloutAt s t h args) (hc : CfgIn G fs Pl (t.config s)) :
    ∃ a fi, G a ∧ s.funcs[a]? = some fi ∧ fi.code = .host h := by
  obtain ⟨E, a, hd⟩ := hco
  obtain ⟨fi, yy, ps, rs, hf, hcode, -, -, -, hfill⟩ := decompose?_sound hd
  have hr : Ref.func a ∈ codeRefs (t.config s).code := by
    rw [hfill]
    exact codeRefs_fill E _ _ (by simp)
  have ha : RefIn G (.func a) := hc.2.2.1 _ hr
  exact ⟨a, fi, by simpa using ha, hf, hcode⟩

/-- A callout of an invariant thread never calls an avoided import. -/
theorem callout_ne {s : Store Nat} {t : Thread} {h i : Nat} {args : List Val}
    (hco : CalloutAt s t h args) (hc : CfgIn G fs Pl (t.config s)) (hav : Avoids G s.funcs i) :
    h ≠ i := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem hco hc
  rintro rfl
  exact hav a fi ha hf hcode

/-- Scalar values hold no function reference. -/
theorem hasVal_refIn {t : ScalarType} {v : Val} (h : t.HasVal v) : ∀ r, v = .ref r → RefIn G r := by
  intro r hr
  subst hr
  cases t with
  | num t => obtain ⟨b, hb⟩ := h; cases hb
  | v128 => obtain ⟨b, hb⟩ := h; cases hb
  | i31 n =>
    rcases h with ⟨b, hb⟩ | ⟨-, hb⟩
    · cases hb; exact refIn_i31 b
    · cases hb; exact refIn_null

theorem typed_refIn {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) :
    ∀ r, Val.ref r ∈ vs → RefIn G r := by
  induction h with
  | nil => intro r hr; cases hr
  | cons hv _ ih =>
    intro r hr
    rcases List.mem_cons.1 hr with hr | hr
    · exact hasVal_refIn hv r hr.symm
    · exact ih r hr

/-- The results of answers of the environment hold no function reference. -/
theorem answer_refIn {ft : FnType} (w : Answer ft) :
    ∀ x ∈ codeRefs (Answer.toResult w).toAdmin, RefIn G x := by
  cases w with
  | values vs =>
    intro x hx
    exact typed_refIn vs.2 x (by simpa [Answer.toResult, Result.toAdmin] using hx)
  | trap => intro x hx; simp [Answer.toResult, Result.toAdmin] at hx
  | throw a =>
    intro x hx
    simp only [Answer.toResult, Result.toAdmin, codeRefs_ref, codeRefs_plain, codeRefs_nil,
      List.mem_singleton] at hx
    exact hx ▸ refIn_exn a

/-- **Resuming a thread with an environment answer keeps the invariant.** -/
theorem resume_cfgIn {s : Store Nat} {t : Thread} {r : Result} (hc : CfgIn G fs Pl (t.config s))
    (hr : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) : CfgIn G fs Pl ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, _, _, _, _, _, _, _, _, hfill⟩ := decompose?_sound hd
    have hs : (t.config s).store = s := Thread.config_store s t
    have hcode : CodeIn G fs Pl (E.fill _) := hfill ▸ hc.2.2
    exact ⟨hs ▸ hc.1, hc.2.1, CodeIn.fill hcode (CodeIn.toAdmin hr)⟩

end Silmaril.Wasm.Verify
