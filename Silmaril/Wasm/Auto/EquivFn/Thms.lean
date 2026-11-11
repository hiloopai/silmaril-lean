module

public import Silmaril.Wasm.Auto.EquivFn.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Behaviour.Semantics.V3
public import Silmaril.Wasm.Auto.Front.Defs
import Silmaril.Proofs.Wasm.Auto.EquivFn.X

/-!
# Function-level equivalence: results

For the notions of `Silmaril.Wasm.Auto.EquivFn.Defs` (proofs in
`Silmaril/Proofs/Wasm/Auto/EquivFn/{Frame,X}`):

**The converse of the frame rule for pinned bodies.** The frame rule (`Safe.frame`,
`TSafe.frame`) has no converse in general: a body reaching `REF.NULL; RETURN_CALL_REF` is stuck
at the top level and traps inside a frame. For a **pinned** body (every run terminates, with one
outcome `o'` in one store `s'`; `Pinned`), it does:

* `wp_frame_pinned`: `Wp (vals us ++ [FRAME_n{F} b]) Q ↔ FrameOut n f us Q s' o'` (both readings);
* `pinned_label`: pinning survives the function's label;
* `wp_call_pinned`: a call of a Wasm function with a pinned body has the weakest precondition of
  its outcome (`call_step_inv`: the call's only step enters the frame);
* `callEquivAt_of_pinned`: functions whose bodies are pinned to the same outcome are
  call-equivalent (`CallEquivAt`: equal weakest preconditions in every caller context);
* `tfspec_of_pinned`, `behaviours_of_pinned`: a total specification, and the behaviour set
  `{outBeh o'}` of `$invoke`.

**From the extended checker** (`Silmaril.Wasm.Auto.Equiv`):

* `pinned_of_xsexec`: every body the symbolic executor runs is pinned, to `xOutcome`;
* `Pinned.of_outEquivX`: `OutEquivX` transfers pinning;
* **`callEquivAt_of_outEquivX`**: body equivalence (`outEquivX_of_checkOutX`) gives call-level
  equivalence in one store;
* **`behaviours_eq_of_outEquivX`**, **`exportRefines_of_outEquivX`**: equal behaviour sets of
  `$invoke` in two stores (two modules), hence the front end's `ExportRefines` for every
  reflexive relation, given typed contexts for the accepted argument lists.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivFn

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.EquivFn` -/

section
-- from Silmaril/Proofs/Wasm/Auto/EquivFn/Frame.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivFn
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv (wp_step_inv wp_exit_post)

theorem wp_steps_inv {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {Q : Post H}
    {c c' : Config H}
    (h : Wp m P host c.store c.frame c.code Q) (hs : Steps P host c c') :
    Wp m P host c'.store c'.frame c'.code Q :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.wp_steps_inv (H := H) (P := P) (host := host) (m := m) (Q := Q)
    (c := c) (c' := c') (h := h) (hs := hs)

theorem steps_frame {H : Type} {P : Profile} {host : HostSemantics H} {n : Nat} {f : Frame}
    {us : List Val} {c c' : Config H}
    (hs : Steps P host c c') :
    Steps P host ⟨c.store, f, vals us ++ [.frame n c.frame c.code]⟩
      ⟨c'.store, f, vals us ++ [.frame n c'.frame c'.code]⟩ :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.steps_frame (H := H) (P := P) (host := host) (n := n) (f := f)
    (us := us) (c := c) (c' := c') (hs := hs)

theorem tsafe_exists_exit {H : Type} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {c : Config H} (h : TSafe P host Q c) :
    ∃ c' o, Steps P host c c' ∧ Exits o c'.code ∧ Q c'.store c'.frame o :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.tsafe_exists_exit (H := H) (P := P) (host := host) (Q := Q)
    (c := c) (h := h)

/-- A configuration with exactly one successor has the weakest precondition of it. -/
theorem wp_iff_of_det {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {Q : Post H}
    {c c' : Config H} (hst : Step P host c c')
    (huniq : ∀ d, Step P host c d → d = c') :
    Wp m P host c.store c.frame c.code Q ↔ Wp m P host c'.store c'.frame c'.code Q :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.wp_iff_of_det (H := H) (P := P) (host := host) (m := m) (Q := Q)
    (c := c) (c' := c') (hst := hst) (huniq := huniq)

/-- **A frame around a pinned body.** -/
theorem wp_frame_pinned {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {n : Nat}
    {s s' : Store H} {F f : Frame} {b : List Admin}
    {o' : Outcome} {us : List Val} {Q : Post H} (hp : Pinned P host s F b s' o') (ho : Fits n o') :
    Wp m P host s f (vals us ++ [.frame n F b]) Q ↔ FrameOut n f us Q s' o' :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.wp_frame_pinned (H := H) (P := P) (host := host) (m := m) (n := n)
    (s := s) (s' := s') (F := F) (f := f) (b := b) (o' := o') (us := us) (Q := Q) (hp := hp)
    (ho := ho)

/-- A pinned body stays pinned inside its function label. -/
theorem pinned_label {H : Type} {P : Profile} {host : HostSemantics H} {n : Nat} {s s' : Store H}
    {F : Frame} {b : List Admin} {o' : Outcome}
    (hp : Pinned P host s F b s' o') (ho : Fits n o') :
    Pinned P host s F [.label n [] b] s' o' :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.pinned_label (H := H) (P := P) (host := host) (n := n) (s := s)
    (s' := s') (F := F) (b := b) (o' := o') (hp := hp) (ho := ho)

/-- **A call of a function whose body is pinned.** -/
theorem wp_call_pinned {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s s' : Store H}
    {f : Frame} {vs₀ args : List Val} {a : Nat}
    {c : Admin} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} {o' : Outcome}
    {Q : Post H} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hp : Pinned P host s (Frame.forCall fi.module args code.locals) (expression code.body) s' o')
    (ho : Fits rs.length o') :
    Wp m P host s f (vals vs₀ ++ vals args ++ [.ref (.func a), c]) Q ↔
      FrameOut rs.length f vs₀ Q s' o' :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.wp_call_pinned (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (vs₀ := vs₀) (args := args) (a := a) (c := c) (fi := fi) (code := code)
    (ps := ps) (rs := rs) (o' := o') (Q := Q) (hc := hc) (hf := hf) (hcode := hcode) (he := he)
    (hn := hn) (hp := hp) (ho := ho)

/-- **Call-level equivalence of two functions whose bodies are pinned to the same outcome.** -/
theorem callEquivAt_of_pinned {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {a₁ a₂ : Nat} {args : List Val}
    {fi₁ fi₂ : FuncInst H} {code₁ code₂ : Func} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)} {o' : Outcome}
    (hf₁ : s.funcs[a₁]? = some fi₁) (hcode₁ : fi₁.code = .wasm code₁)
    (he₁ : Expand fi₁.type (.func ps₁ rs₁)) (hn₁ : args.length = ps₁.length)
    (hf₂ : s.funcs[a₂]? = some fi₂) (hcode₂ : fi₂.code = .wasm code₂)
    (he₂ : Expand fi₂.type (.func ps₂ rs₂)) (hn₂ : args.length = ps₂.length)
    (hrs : rs₁.length = rs₂.length)
    (hp₁ : Pinned P host s (Frame.forCall fi₁.module args code₁.locals) (expression code₁.body) s' o')
    (hp₂ : Pinned P host s (Frame.forCall fi₂.module args code₂.locals) (expression code₂.body) s' o')
    (ho : Fits rs₁.length o') :
    CallEquivAt P host s a₁ a₂ args :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.callEquivAt_of_pinned (H := H) (P := P) (host := host) (s := s)
    (s' := s') (a₁ := a₁) (a₂ := a₂) (args := args) (fi₁ := fi₁) (fi₂ := fi₂) (code₁ := code₁)
    (code₂ := code₂) (ps₁ := ps₁) (rs₁ := rs₁) (ps₂ := ps₂) (rs₂ := rs₂) (o' := o') (hf₁ := hf₁)
    (hcode₁ := hcode₁) (he₁ := he₁) (hn₁ := hn₁) (hf₂ := hf₂) (hcode₂ := hcode₂) (he₂ := he₂)
    (hn₂ := hn₂) (hrs := hrs) (hp₁ := hp₁) (hp₂ := hp₂) (ho := ho)

/-- **A pinned body gives a total specification** of the call. -/
theorem tfspec_of_pinned {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {args : List Val} {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} {o' : Outcome}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hp : Pinned P host s (Frame.forCall fi.module args code.locals) (expression code.body) s' o')
    (ho : Fits rs.length o') :
    TFSpecAt P host a (pinSpec s args s' o') :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.tfspec_of_pinned (H := H) (P := P) (host := host) (s := s)
    (s' := s') (args := args) (a := a) (fi := fi) (code := code) (ps := ps) (rs := rs) (o' := o')
    (hf := hf) (hcode := hcode) (he := he) (hn := hn) (hp := hp) (ho := ho)

theorem result_eq_of_vals {r : Result} {rs : List Val} (h : r.toAdmin = vals rs) :
    r = .values rs :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.result_eq_of_vals (r := r) (rs := rs) (h := h)

theorem not_step_result {H : Type} {P : Profile} {host : HostSemantics H} {r : Result}
    {c c' : Config H} (h : c.code = r.toAdmin) :
    ¬ Step P host c c' :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.not_step_result (H := H) (P := P) (host := host) (r := r) (c := c)
    (c' := c') (h := h)

/-- **The behaviours of a pinned call**: exactly `outBeh o'`. -/
theorem behaviours_of_pinned {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {args : List Val} {a : Nat} {o' : Outcome}
    (h : TFSpecAt P host a (pinSpec s args s' o')) (ho : o' = .trap ∨ ∃ res, o' = .normal res) :
    behaviours P host s a args = {outBeh o'} :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.behaviours_of_pinned (H := H) (P := P) (host := host) (s := s)
    (s' := s') (args := args) (a := a) (o' := o') (h := h) (ho := ho)

end

section
-- from Silmaril/Proofs/Wasm/Auto/EquivFn/X.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivFn
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Validation

/-- **The executor pins the bodies it runs.** -/
theorem pinned_of_xsexec {H : Type} {P : Profile} {host : HostSemantics H} {lt gt : List IntType}
    {mem : Bool} {c : XCtx H}
    (hc : c.Ok lt [] gt mem) {a : List Instr} {A : XState}
    (ha : xsexec mem (initX lt [] gt) a = some A) :
    Pinned P host c.s c.f (expression a) (xOutcome c mem A).1 (xOutcome c mem A).2 :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.pinned_of_xsexec (H := H) (P := P) (host := host) (lt := lt)
    (gt := gt) (mem := mem) (c := c) (hc := hc) (a := a) (A := A) (ha := ha)

/-- **`OutEquivX` transfers pinning.** -/
theorem Pinned.of_outEquivX {H : Type} {P : Profile} {host : HostSemantics H} {lt gt : List IntType}
    {mem : Bool} {a b : List Instr}
    (h : OutEquivX lt [] gt mem a b) {c : XCtx H} (hc : c.Ok lt [] gt mem) {s' : Store H}
    {o' : Outcome} (hp : Pinned P host c.s c.f (expression a) s' o') :
    Pinned P host c.s c.f (expression b) s' o' :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.Pinned.of_outEquivX (H := H) (P := P) (host := host) (lt := lt)
    (gt := gt) (mem := mem) (a := a) (b := b) (h := h) (c := c) (hc := hc) (s' := s') (o' := o')
    (hp := hp)

/-- **Function-level equivalence from body equivalence**, in one store. -/
theorem callEquivAt_of_outEquivX {H : Type} {P : Profile} {host : HostSemantics H}
    {lt gt : List IntType} {mem : Bool} {s : Store H} {a₁ a₂ : Nat}
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
    CallEquivAt P host s a₁ a₂ args :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.callEquivAt_of_outEquivX (H := H) (P := P) (host := host)
    (lt := lt) (gt := gt) (mem := mem) (s := s) (a₁ := a₁) (a₂ := a₂) (args := args) (fi₁ := fi₁)
    (fi₂ := fi₂) (code₁ := code₁) (code₂ := code₂) (ps := ps) (rs := rs) (A := A) (heq := heq)
    (hf₁ := hf₁) (hcode₁ := hcode₁) (he₁ := he₁) (hf₂ := hf₂) (hcode₂ := hcode₂) (he₂ := he₂)
    (hn := hn) (hF := hF) (c := c) (hc := hc) (hs := hs) (hf := hf) (hA := hA) (hlen := hlen)

/-- **Equal behaviours from body equivalence**, in two stores. -/
theorem behaviours_eq_of_outEquivX {H : Type} {P : Profile} {host : HostSemantics H}
    {lt gt : List IntType} {mem : Bool} {s₁ s₂ : Store H}
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
    behaviours P host s₁ a₁ args = behaviours P host s₂ a₂ args :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.behaviours_eq_of_outEquivX (H := H) (P := P) (host := host)
    (lt := lt) (gt := gt) (mem := mem) (s₁ := s₁) (s₂ := s₂) (a₁ := a₁) (a₂ := a₂) (args := args)
    (fi₁ := fi₁) (fi₂ := fi₂) (code₁ := code₁) (code₂ := code₂) (ps₁ := ps₁) (rs₁ := rs₁)
    (ps₂ := ps₂) (rs₂ := rs₂) (A := A) (heq := heq) (hf₁ := hf₁) (hcode₁ := hcode₁) (he₁ := he₁)
    (hn₁ := hn₁) (hf₂ := hf₂) (hcode₂ := hcode₂) (he₂ := he₂) (hn₂ := hn₂) (c₁ := c₁) (c₂ := c₂)
    (hc₁ := hc₁) (hc₂ := hc₂) (hs₁ := hs₁) (hF₁ := hF₁) (hs₂ := hs₂) (hF₂ := hF₂) (hρ := hρ)
    (hb := hb) (hA := hA) (hlen₁ := hlen₁) (hlen₂ := hlen₂)

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
    ∀ P, ExportRefines R P s₁ a₁ s₂ a₂ :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.exportRefines_of_outEquivX (R := R) (hR := hR) (lt := lt)
    (gt := gt) (mem := mem) (s₁ := s₁) (s₂ := s₂) (a₁ := a₁) (a₂ := a₂) (fi₁ := fi₁) (fi₂ := fi₂)
    (code₁ := code₁) (code₂ := code₂) (ps₁ := ps₁) (rs₁ := rs₁) (ps₂ := ps₂) (rs₂ := rs₂) (A := A)
    (heq := heq) (hf₁ := hf₁) (hcode₁ := hcode₁) (he₁ := he₁) (hf₂ := hf₂) (hcode₂ := hcode₂)
    (he₂ := he₂) (hps := hps) (hA := hA) (hlen₁ := hlen₁) (hlen₂ := hlen₂) (hctx := hctx)

end

/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- A lemma of `Silmaril.Proofs.Wasm.Auto.EquivFn` that the proofs of `Silmaril.Wasm.Auto2` use.

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivFn
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Validation

theorem fits_xOutcome {H : Type} {mem : Bool} {c : XCtx H} {A : XState} {n : Nat}
    (hlen : A.stack.length = n) : Fits n (xOutcome c mem A).2 :=
  Silmaril.Proofs.Wasm.Auto.EquivFn.fits_xOutcome hlen

end

end Silmaril.Wasm.Auto.EquivFn

