module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.ReturnCall

/-!
# The forward field of obstruction 1, up to call annotations

`fwdUpTo_returnCallRefFrameAddr`: Core's `returnCallRefFrameAddr` step, between typed
configurations, is a SpecTec step to the image of a configuration `ConfigEq`-related to Core's
successor (SpecTec's own `c.retToCall`). This is the `Forward.returnCallRefFrameAddr` field
restated up to `ConfigEq`; the exact field is false (`adminToV_retToCallIn_ne`). Family C's
`fwd_returnCallRefFrameAddr_retToCall` does the SpecTec construction; what is added here is the
typing of SpecTec's successor, from the typing of Core's successor and of the left-hand side,
through `CallRefTyping` (assumed).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B))
  (S : CtrlState (simEnv B) hn) (C : CtrlCall (simEnv B)) (Ct : CallRefTyping (simEnv B))

include T Tg in
/-- The annotation of the `RETURN_CALL_REF` in a typed frame body is a typed `typeuse`. -/
theorem typed_retAnnot {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} {yy : Value} (hyy : adminToV c = .case "RETURN_CALL_REF" yy)
    (h : Typed (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++
      rest)]⟩) : TypedV (simEnv B) typeuseT yy := by
  obtain ⟨-, hcode⟩ := (T.config _).1 h
  have hb := (T.frame k fi _ hcode).2.2
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs' ++ vals vs ++
      [.ref (.func a)]) ++ [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  have hcv : TypedV (simEnv B) instrsT (.list [adminToV c]) :=
    (typedV_list_append.1 (typedV_list_append.1 hb').1).2
  exact Tg.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)

include T Ct in
/-- SpecTec's successor is typed when Core's is and the annotation is. -/
theorem typed_retToCall {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {c c₀ : Admin}
    {yy : Value} (hyy : adminToV c₀ = .case "CALL_REF" yy) (hy : TypedV (simEnv B) typeuseT yy)
    (h : Typed (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    Typed (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c₀]⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 h
  have hc' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs ++ [.ref (.func a)]) ++
      [adminToV c])) := by
    simpa [adminsToV_append] using hcode
  have hpre := (typedV_list_append.1 hc').1
  have hcall : TypedV (simEnv B) instrsT (.list [adminToV c₀]) :=
    typedV_list_single.2 (hyy ▸ Ct.callRef yy hy)
  have hnew : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs ++ [.ref (.func a), c₀]))) := by
    simpa [adminsToV_append] using typedV_list_append.2 ⟨hpre, hcall⟩
  exact (T.config _).2 ⟨hst, hnew⟩

include T Tg S C Ct in
/-- **`Forward.returnCallRefFrameAddr`, up to `ConfigEq`.** -/
theorem fwdUpTo_returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
    {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef) (hfn : s.funcs[a]? = some fn)
    (hex : Expand fn.type (.func ps rs)) (hlen : vs.length = ps.length)
    (h₁ : Typed (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++
      rest)]⟩)
    (h₂ : Typed (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩) :
    ∃ d', ConfigEq ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ d' ∧
      SStep (simEnv B) (configV hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++
        [.ref (.func a), c] ++ rest)]⟩) (configV hn d') := by
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  have hy : TypedV (simEnv B) typeuseT yy := typed_retAnnot B T Tg hyy h₁
  have h₃ : Typed (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩ :=
    typed_retToCall B T Ct hyy' hy h₂
  exact ⟨⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩,
    ⟨rfl, rfl, codeEq_retToCall hc fi.module vs a⟩,
    fwd_returnCallRefFrameAddr_retToCall B T Tg S C hc hfn hex hlen h₁ h₃⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd
