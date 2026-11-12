module

public import Silmaril.Proofs.Wasm.Auto.EquivFn.Frame
public import Silmaril.Wasm.Auto.Front.Defs

/-!
# Function-level equivalence from the extended checker

* `pinned_of_xsexec`: a body that the executor of `Silmaril.Wasm.Auto.Equiv` runs from a typed
  context `c` (locals of types `lt`, empty stack, globals `gt`, memory `0` when `mem`) is pinned
  to `xOutcome c mem A`: a trap at the first failing guard, or the final stack;
* `Pinned.of_outEquivX`: `OutEquivX` transfers pinning (the pinning postcondition is blind to
  the frame);
* **`callEquivAt_of_outEquivX`**: two functions of one store whose bodies are `OutEquivX` (for
  instance by `outEquivX_of_checkOutX`) and the first of which runs symbolically are
  call-equivalent (`CallEquivAt`) on the arguments of a typed context;
* **`behaviours_eq_of_outEquivX`**: the same bodies in two stores (two modules) have equal
  behaviour sets of `$invoke`, when the two contexts agree on the inputs and the initial memory
  bytes; `exportRefines_of_outEquivX` gives the front end's `ExportRefines` for every reflexive
  relation.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivFn

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivFn
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem code_init (c : XCtx H) (lt gt : List IntType) (a : List Instr) :
    c.code lt [] gt [] a [] = expression a := by
  simp [XCtx.code, XCtx.stackOf, initX]

/-- **The executor pins the bodies it runs.** -/
theorem pinned_of_xsexec {lt gt : List IntType} {mem : Bool} {c : XCtx H}
    (hc : c.Ok lt [] gt mem) {a : List Instr} {A : XState}
    (ha : xsexec mem (initX lt [] gt) a = some A) :
    Pinned P host c.s c.f (expression a) (xOutcome c mem A).1 (xOutcome c mem A).2 := by
  have h := wp_init_iff (m := .total) (P := P) (host := host) hc ha [] []
    (Pin (xOutcome c mem A).1 (xOutcome c mem A).2)
  rw [code_init] at h
  refine h.mpr ?_
  unfold XOut
  cases hT : firstFail c.ρ c.mi.bytes A.guards with
  | some T =>
    simp only [xOutcome, hT]
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [xOutcome, hT, List.nil_append, List.append_nil]
    exact wp_vals_iff'.mpr ⟨rfl, rfl⟩

theorem fits_xOutcome {mem : Bool} {c : XCtx H} {A : XState} {n : Nat}
    (hlen : A.stack.length = n) : Fits n (xOutcome c mem A).2 := by
  cases hT : firstFail c.ρ c.mi.bytes A.guards with
  | some T =>
    simp only [xOutcome, hT]
    trivial
  | none =>
    simp only [xOutcome, hT]
    show (c.stackOf A).reverse.length = n
    simp [XCtx.stackOf, hlen]

theorem simple_xOutcome {mem : Bool} {c : XCtx H} {A : XState} :
    (xOutcome c mem A).2 = .trap ∨ ∃ res, (xOutcome c mem A).2 = .normal res := by
  cases hT : firstFail c.ρ c.mi.bytes A.guards with
  | some T => simp [xOutcome, hT]
  | none => simp [xOutcome, hT]

/-- The outcome of a symbolic run depends on the inputs and the initial memory bytes only. -/
theorem xOutcome_snd_congr {mem : Bool} {c c' : XCtx H} {A : XState} (hρ : c.ρ = c'.ρ)
    (hb : c.mi.bytes = c'.mi.bytes) : (xOutcome c mem A).2 = (xOutcome c' mem A).2 := by
  unfold xOutcome
  rw [hρ, hb]
  cases firstFail c'.ρ c'.mi.bytes A.guards with
  | some T => rfl
  | none => simp [XCtx.stackOf, hρ, hb]

/-- **`OutEquivX` transfers pinning.** -/
theorem Pinned.of_outEquivX {lt gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : OutEquivX lt [] gt mem a b) {c : XCtx H} (hc : c.Ok lt [] gt mem) {s' : Store H}
    {o' : Outcome} (hp : Pinned P host c.s c.f (expression a) s' o') :
    Pinned P host c.s c.f (expression b) s' o' := by
  have h₁ := h .total P host c [] (Pin s' o') hc (fun _ _ _ _ _ => Iff.rfl)
  rw [code_init, code_init] at h₁
  exact h₁.mp hp

/-- **Function-level equivalence from body equivalence**, in one store. -/
theorem callEquivAt_of_outEquivX {lt gt : List IntType} {mem : Bool} {s : Store H} {a₁ a₂ : Nat}
    {args : List Val} {fi₁ fi₂ : FuncInst H} {code₁ code₂ : Func} {ps rs : Ty (.list .val)}
    {A : XState} (heq : OutEquivX lt [] gt mem code₁.body code₂.body)
    (hf₁ : s.funcs[a₁]? = some fi₁) (hcode₁ : fi₁.code = .wasm code₁)
    (he₁ : Expand fi₁.type (.func ps rs))
    (hf₂ : s.funcs[a₂]? = some fi₂) (hcode₂ : fi₂.code = .wasm code₂)
    (he₂ : Expand fi₂.type (.func ps rs)) (hn : args.length = ps.length)
    (hF : Frame.forCall fi₂.module args code₂.locals = Frame.forCall fi₁.module args code₁.locals)
    (c : XCtx H) (hc : c.Ok lt [] gt mem) (hs : c.s = s)
    (hf : c.f = Frame.forCall fi₁.module args code₁.locals)
    (hA : xsexec mem (initX lt [] gt) code₁.body = some A) (hlen : A.stack.length = rs.length) :
    CallEquivAt P host s a₁ a₂ args := by
  have hp₁ : Pinned P host c.s c.f (expression code₁.body) (xOutcome c mem A).1
      (xOutcome c mem A).2 := pinned_of_xsexec hc hA
  have hp₂ := Pinned.of_outEquivX heq hc hp₁
  rw [hs, hf] at hp₁ hp₂
  rw [← hF] at hp₂
  exact callEquivAt_of_pinned hf₁ hcode₁ he₁ hn hf₂ hcode₂ he₂ hn rfl hp₁ hp₂ (fits_xOutcome hlen)

/-- **Equal behaviours from body equivalence**, in two stores. -/
theorem behaviours_eq_of_outEquivX {lt gt : List IntType} {mem : Bool} {s₁ s₂ : Store H}
    {a₁ a₂ : Nat} {args : List Val} {fi₁ fi₂ : FuncInst H} {code₁ code₂ : Func}
    {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)} {A : XState}
    (heq : OutEquivX lt [] gt mem code₁.body code₂.body)
    (hf₁ : s₁.funcs[a₁]? = some fi₁) (hcode₁ : fi₁.code = .wasm code₁)
    (he₁ : Expand fi₁.type (.func ps₁ rs₁)) (hn₁ : args.length = ps₁.length)
    (hf₂ : s₂.funcs[a₂]? = some fi₂) (hcode₂ : fi₂.code = .wasm code₂)
    (he₂ : Expand fi₂.type (.func ps₂ rs₂)) (hn₂ : args.length = ps₂.length)
    (c₁ c₂ : XCtx H) (hc₁ : c₁.Ok lt [] gt mem) (hc₂ : c₂.Ok lt [] gt mem)
    (hs₁ : c₁.s = s₁) (hF₁ : c₁.f = Frame.forCall fi₁.module args code₁.locals)
    (hs₂ : c₂.s = s₂) (hF₂ : c₂.f = Frame.forCall fi₂.module args code₂.locals)
    (hρ : c₁.ρ = c₂.ρ) (hb : c₁.mi.bytes = c₂.mi.bytes)
    (hA : xsexec mem (initX lt [] gt) code₁.body = some A) (hlen₁ : A.stack.length = rs₁.length)
    (hlen₂ : A.stack.length = rs₂.length) :
    behaviours P host s₁ a₁ args = behaviours P host s₂ a₂ args := by
  have hp₁ : Pinned P host c₁.s c₁.f (expression code₁.body) (xOutcome c₁ mem A).1
      (xOutcome c₁ mem A).2 := pinned_of_xsexec hc₁ hA
  have hp₂ := Pinned.of_outEquivX heq hc₂ (pinned_of_xsexec (P := P) (host := host) hc₂ hA)
  rw [hs₁, hF₁] at hp₁
  rw [hs₂, hF₂] at hp₂
  have ht₁ := tfspec_of_pinned hf₁ hcode₁ he₁ hn₁ hp₁ (fits_xOutcome hlen₁)
  have ht₂ := tfspec_of_pinned hf₂ hcode₂ he₂ hn₂ hp₂ (fits_xOutcome hlen₂)
  rw [behaviours_of_pinned ht₁ simple_xOutcome, behaviours_of_pinned ht₂ simple_xOutcome,
    xOutcome_snd_congr hρ hb]

open Silmaril.Wasm.Auto.Front (ExportRefines) in
/-- **Export refinement from body equivalence**, for every reflexive relation, when every
accepted argument list has typed contexts in both stores that agree on the inputs and memory. -/
theorem exportRefines_of_outEquivX {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {lt gt : List IntType} {mem : Bool} {s₁ s₂ : Store Nat} {a₁ a₂ : Nat}
    {fi₁ fi₂ : FuncInst Nat} {code₁ code₂ : Func} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
    {A : XState} (heq : OutEquivX lt [] gt mem code₁.body code₂.body)
    (hf₁ : s₁.funcs[a₁]? = some fi₁) (hcode₁ : fi₁.code = .wasm code₁)
    (he₁ : Expand fi₁.type (.func ps₁ rs₁))
    (hf₂ : s₂.funcs[a₂]? = some fi₂) (hcode₂ : fi₂.code = .wasm code₂)
    (he₂ : Expand fi₂.type (.func ps₂ rs₂)) (hps : ps₁.length = ps₂.length)
    (hA : xsexec mem (initX lt [] gt) code₁.body = some A) (hlen₁ : A.stack.length = rs₁.length)
    (hlen₂ : A.stack.length = rs₂.length)
    (hctx : ∀ args, InvokeOk s₁ a₁ args → args.length = ps₁.length ∧
      ∃ c₁ c₂ : XCtx Nat, c₁.Ok lt [] gt mem ∧ c₂.Ok lt [] gt mem ∧ c₁.s = s₁ ∧
        c₁.f = Frame.forCall fi₁.module args code₁.locals ∧ c₂.s = s₂ ∧
        c₂.f = Frame.forCall fi₂.module args code₂.locals ∧ c₁.ρ = c₂.ρ ∧
        c₁.mi.bytes = c₂.mi.bytes) :
    ∀ P, ExportRefines R P s₁ a₁ s₂ a₂ := by
  intro P args hok b hb
  obtain ⟨hn₁, c₁, c₂, hc₁, hc₂, hs₁, hF₁, hs₂, hF₂, hρ, hbytes⟩ := hctx args hok
  have he := behaviours_eq_of_outEquivX (P := P) (host := SingleThreaded.Det.noHost) heq hf₁ hcode₁
    he₁ hn₁ hf₂ hcode₂ he₂ (hps ▸ hn₁) c₁ c₂ hc₁ hc₂ hs₁ hF₁ hs₂ hF₂ hρ hbytes hA hlen₁ hlen₂
  exact ⟨b, he ▸ hb, hR b⟩

end Silmaril.Proofs.Wasm.Auto.EquivFn