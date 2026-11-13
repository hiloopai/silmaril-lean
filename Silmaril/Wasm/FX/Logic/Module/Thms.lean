module

public import Silmaril.Proofs.Wasm.FX.Logic.Module.Spec

/-!
# Function specifications for WasmFX functions: statements

The module rules for FX functions (`Silmaril.Wasm.FX.Logic.Module.Defs`; proofs in
`Silmaril.Proofs.Wasm.FX.Logic.Module.Spec`), over `StepFX'` without host calls, at every profile:

* **`FSpecAt.of_body`**: a specification of an FX function from its body;
* **`Safe.callIdx_spec`**: the call rule for `call x` (and through `CALL_REF`,
  `safe_call_spec`; total versions `tsafe_call_spec`, `tsafe_callIdx_spec`);
* **`Ctx.valid_of_step`** (mutual recursion), `CtxSat.valid`, `CtxSat.weaken`, `CtxSat.link`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Module

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Safe Inv safeJ)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- **A specification from the body.** -/
theorem FSpecAt.of_body {n a : Nat} {S : FSpec H} {fi : FuncInst H} {hh : H} {F : FuncFX}
    (hfi : ∀ s K args, S.pre s K args → s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hfx : fx hh = some F)
    (hlen : ∀ s K args, S.pre s K args → args.length = F.nparams)
    (hinv : ∀ s K args, S.pre s K args → InvO (S.post s K args))
    (hbody : ∀ s K args, S.pre s K args → ∀ (f : Frame) (vs₀ : List FVal),
      Safe P fx (bodyPost P fx F.nresults f vs₀ (callPost f vs₀ (S.post s K args)) n) n
        ⟨s, K, Frame.forCall F.module args F.locals, F.body.map InstrFX.toAdmin⟩) :
    FSpecAt P fx (n + 1) a S :=
  Silmaril.Proofs.Wasm.FX.Logic.Module.fspecAt_of_body hfi hcode hfx hlen hinv hbody

/-- **The call rule for `call x`.** -/
theorem Safe.callIdx_spec {n a : Nat} {S : FSpec H} {Q : PostFX H} {s : Store H} {K : Conts}
    {f : Frame} {vs₀ : List FVal} {args : List Val} {rest : List AdminFX} {x : FuncIdx}
    {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hQ : Inv Q) (hS : FSpecAt P fx n a S) (hpre : S.pre s K args)
    (hpost : ∀ s' K' o, callPost f vs₀ (S.post s K args) s' K' f o →
      EveryRun.seqPost (safeJ P fx Q n) rest Q s' K' f o) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (vs₀ ++ liftV args) ++ .core (.plain (.call x)) :: rest⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.Module.safe_callIdx_spec hx hf hQ hS hpre hpost

/-- info: 'Silmaril.Wasm.FX.Logic.Module.FSpecAt.of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FSpecAt.of_body

/-- info: 'Silmaril.Wasm.FX.Logic.Module.CtxSat.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CtxSat.link

end Silmaril.Wasm.FX.Logic.Module
