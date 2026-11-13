module

public import Silmaril.Proofs.Wasm.Jco.Real.Load
public import Silmaril.Wasm.Jco.Styles.Realloc.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# Adaptor code against the reference engine: sequences and functions

* `sim_step`: every instruction of the fragment `Frag`;
* `sim_exec`: instruction sequences of the fragment (`execX`);
* `run_frame`: an adaptor function (`XFn.run`) with `i32` locals, run in a Core 3.0 call frame
  of its Lime1 image (`XFn.toLime`), returns the same values in the same store;
* `invoke_xfn`: the same from `$invoke` of a function instance whose code is that image.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

theorem FrameEnv.of_module {cf cf' : Silmaril.Wasm.Execution.Core.Frame}
    (h : FrameEnv mi ma fi cf) (hm : cf'.module = cf.module) : FrameEnv mi ma fi cf' :=
  ⟨hm ▸ h.mem, hm ▸ h.call⟩

/-- **One instruction of the fragment.** -/
theorem sim_step {i : XInstr} (hi : Frag i) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) i f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi i)] := by
  cases hi with
  | localGet hi => exact sim_localGet P host mi ma fi hi h hl
  | localSet hi => exact sim_localSet P host mi ma fi hi h hl
  | i32Const c => exact sim_i32Const P host mi ma fi c h hl
  | call g n => exact sim_call P host mi ma fi g n h he hl
  | i32Eqz => exact sim_i32Eqz P host mi ma fi h hl
  | i32LtU => exact sim_i32LtU P host mi ma fi h hl
  | select => exact sim_select P host mi ma fi h hl
  | loadInt hn hoff => exact sim_loadInt P host mi ma fi hn hoff h he hl

/-- **A sequence of instructions of the fragment.** -/
theorem sim_exec : ∀ (is : List XInstr), (∀ i ∈ is, Frag i) →
    ∀ {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H},
    execX (realInst H P host mi ma) is f s (.ok f' s') →
    ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
    cf.locals = localsOf f.locals → Sim P host f f' s s' cf (codeOf fi is)
  | [], _, f, f', s, s', h, cf, _, hl => by
    have h' : (pure f : RM (Store H) Silmaril.Wasm.Jco.Frame) s (.ok f' s') := h
    obtain ⟨rfl, rfl⟩ := ok_pure h'
    exact ⟨cf, rfl, hl, by simpa [codeOf] using Relation.ReflTransGen.refl⟩
  | i :: is, hF, f, f', s, s', h, cf, he, hl => by
    rw [execX_cons] at h
    obtain ⟨f₁, s₁, h₁, h₂⟩ := ok_bind h
    obtain ⟨cf₁, hm₁, hl₁, hrun₁⟩ :=
      sim_step P host mi ma fi (hF i (List.mem_cons_self ..)) h₁ he hl
    obtain ⟨cf₂, hm₂, hl₂, hrun₂⟩ :=
      sim_exec is (fun j hj => hF j (List.mem_cons_of_mem _ hj)) h₂ (FrameEnv.of_module mi ma fi he hm₁) hl₁
    refine ⟨cf₂, hm₂.trans hm₁, hl₂, ?_⟩
    have hA := Silmaril.Wasm.Execution.Core.Sim.Steps.append_right hrun₁ (codeOf fi is)
    simp only [List.append_assoc] at hA
    exact hA.trans hrun₂

theorem codeOf_toLimeL : ∀ (is : List XInstr),
    expression (Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi is)) = codeOf fi is
  | [] => rfl
  | i :: is => by
    simp only [XInstr.toLimeL, Silmaril.Wasm.Lime1.Expr.toCore, expression, codeOf,
      List.map_cons, coreOf]
    have := codeOf_toLimeL is
    simp only [expression, codeOf] at this
    rw [this]
    rfl

theorem forCall_i32 (mod : Silmaril.Wasm.Execution.Core.ModuleInst) (args : List Flat) (fn : XFn)
    (ty : Nat) :
    (Frame.forCall mod (args.map toVal) (fn.toLime fi ty).toCore.locals).locals =
      localsOf (args ++ List.replicate fn.locals (i32n 0)) := by
  simp [Frame.forCall, localsOf, XFn.toLime, Silmaril.Wasm.Lime1.Func.toCore,
    Silmaril.Wasm.Validation.liftVal, defaultVal?, List.map_replicate, toVal,
    Silmaril.Wasm.V1.ValType.toCore, Silmaril.Wasm.Validation.Ty.substAll, Function.comp_def]
  exact Or.inr rfl

/-- **An adaptor function with `i32` locals, in a Core call frame of its image.** -/
theorem run_frame (fn : XFn) (ty : Nat) (hF : ∀ i ∈ fn.body, Frag i) {args rs : List Flat}
    {s s' : Store H} (h : fn.run (realInst H P host mi ma) args s (.ok rs s'))
    (mod : Silmaril.Wasm.Execution.Core.ModuleInst) (he : FrameEnv mi ma fi { module := mod })
    (g : Silmaril.Wasm.Execution.Core.Frame) :
    Steps P host ⟨s, g, [.frame rs.length (Frame.forCall mod (args.map toVal)
        (fn.toLime fi ty).toCore.locals)
        [.label rs.length [] (expression (fn.toLime fi ty).toCore.body)]]⟩
      ⟨s', g, vals (rs.map toVal)⟩ := by
  obtain ⟨u, s₁, hc, h₁⟩ := ok_bind h
  obtain ⟨-, rfl⟩ : args.length = fn.params ∧ s₁ = s := by
    unfold RM.check at hc
    split at hc
    · rename_i hb
      obtain ⟨-, rfl⟩ := ok_pure hc
      exact ⟨by simpa using hb, rfl⟩
    · cases hc
  obtain ⟨fr, s₂, hx, hp⟩ := ok_bind h₁
  obtain ⟨rfl, rfl⟩ := ok_pure hp
  set cf := Frame.forCall mod (args.map toVal) (fn.toLime fi ty).toCore.locals with hcf
  have hloc : cf.locals = localsOf (args ++ List.replicate fn.locals (i32n 0)) :=
    forCall_i32 fi mod args fn ty
  have he' : FrameEnv mi ma fi cf := FrameEnv.of_module mi ma fi he rfl
  obtain ⟨cf', -, -, hrun⟩ := sim_exec P host mi ma fi fn.body hF hx he' hloc
  have hbody : expression (fn.toLime fi ty).toCore.body = codeOf fi fn.body :=
    codeOf_toLimeL fi fn.body
  have hnil : stackCode ([] : List Flat) = [] := rfl
  rw [hnil, List.nil_append] at hrun
  rw [hbody]
  have hL := Steps.frame (f := g) (n := fr.stack.reverse.length)
    (Steps.label (n := fr.stack.reverse.length) (cont := []) hrun)
  exact (hL.tail (Step.ctxtFrame Step.labelVals)).tail (Step.frameVals (by simp))

/-- **An adaptor function with `i32` locals, invoked**: `$invoke` of a function instance whose
code is the Core image of the function's Lime1 encoding, in a module linked to `mi`, returns
what `XFn.run` returns, in the same final store. -/
theorem invoke_xfn (fn : XFn) (ty : Nat) (hF : ∀ i ∈ fn.body, Frag i) {args rs : List Flat}
    {s s' : Store H} (h : fn.run (realInst H P host mi ma) args s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts))
    (hps : args.length = ps.length) (hrts : rs.length = rts.length) :
    Steps P host (invoke s b (args.map toVal)) ⟨s', {}, vals (rs.map toVal)⟩ := by
  have hinv : invoke s b (args.map toVal) =
      ⟨s, {}, vals (args.map toVal) ++ [.ref (.func b), .callRefType fA.type]⟩ := by
    simp [invoke, hb]
  rw [hinv]
  have hstep := Step.callRefFunc (P := P) (host := host) (f := {})
    (c := .callRefType fA.type) (vs := args.map toVal) trivial hb hexp (by simpa using hps) hcode
  rw [← hrts] at hstep
  exact (Relation.ReflTransGen.single hstep).trans (run_frame P host mi ma fi fn ty hF h _ he _)

end Silmaril.Proofs.Wasm.Jco.Real
