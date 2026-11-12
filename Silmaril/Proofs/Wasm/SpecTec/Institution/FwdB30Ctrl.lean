module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# The forward direction at every `B`: the primitive-free control rules of `Step_read`

A copy of part of `FwdX30Ctrl` (whose leaves are stated at `Round4Int.BI`) at an arbitrary
evaluator `simEnv B`: `call`, `return_call`, `return_call_ref` out of a label, a handler or a frame
at `null`, and `throw_ref` past values or instructions use no primitive, so their bodies go
through unchanged with `BI P hn host` replaced by `B`. Not copied: `block`, `loop` and `try_table`
evaluate `$blocktype_` through `Round5.Fwd.blocktypeB`, and the `catch`, `catch_ref` and `next`
handler cases of `throw_ref` read `Round5.Fwd.helpersC_builtins`; both are stated at `BI`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round4 (ModuleBnd)

variable {H : Type} (B : Builtins) (hn : H → String)

/-- The environment at the primitives `B`. -/
local notation "EB" => simEnv B

/-- `call` (`Round5.Fwd.fwd_call5`, before the lift). -/
theorem sreadC_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi)
    (hz : TypedV EB stateT (stateV hn s f)) :
    SRead EB (configV hn ⟨s, f, [.plain (.call x)]⟩)
      (adminsToV [.ref (.func a), .callRefType fi.type]) :=
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  have Pd := Prims.projDefs_simEnv B
  sread_call (simEnv_readRules _).call (k := x.toNat) hz (Silmaril.Wasm.Validation.Ty.idx x) (Silmaril.Wasm.Validation.Ty.addr a)
    (Prims.applies_funcinst Pd hn s f) (funcs_getElem_map hfi) rfl
    (Prims.applies_moduleinst Pd hn s f) rfl (moduleFuncs_getElem_map hx)

/-- `return_call` (`Round5.Fwd.fwd_returnCall5`, before the lift). -/
theorem sreadC_returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi)
    (hz : TypedV EB stateT (stateV hn s f)) :
    SRead EB (configV hn ⟨s, f, [.plain (.returnCall x)]⟩)
      (adminsToV [.ref (.func a), .returnCallRefType fi.type]) :=
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  have Pd := Prims.projDefs_simEnv B
  sread_returnCall (simEnv_readRules _).returnCall (k := x.toNat) hz (Silmaril.Wasm.Validation.Ty.idx x)
    (Silmaril.Wasm.Validation.Ty.addr a) (Prims.applies_funcinst Pd hn s f) (funcs_getElem_map hfi) rfl
    (Prims.applies_moduleinst Pd hn s f) rfl (moduleFuncs_getElem_map hx)

/-- `return_call_ref` out of a label (`Sim.fwd_returnCallRefLabel`, before the lift). -/
theorem sreadC_returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT (.list (adminsToV [.label k cont (vals vs ++ [c] ++ rest)]))) :
    SRead EB (configV hn ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩)
      (adminsToV (vals vs ++ [c])) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  obtain ⟨hk, hct, hb⟩ := T.label _ cont _ h
  have hb' : TypedV EB instrsT
      (.list (adminsToV (vals vs) ++ [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, hcv⟩ := typedV_list_append.1 hab
  have hy : TypedV EB typeuseT yy :=
    Silmaril.Wasm.Validation.Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefLabel (simEnv_readRules _).returnCallRefLabel
    (z := stateV hn s f) (k := .num (.natN k)) (cont := instrsToV cont) (ws := adminsToV (vals vs))
    (is := adminsToV rest) hz hk hct (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

/-- `return_call_ref` out of a handler (`Sim.fwd_returnCallRefHandler`, before the lift). -/
theorem sreadC_returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch}
    {vs : List Val} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT (.list (adminsToV [.handler k cs (vals vs ++ [c] ++ rest)]))) :
    SRead EB (configV hn ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩)
      (adminsToV (vals vs ++ [c])) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  obtain ⟨hk, hcs, hb⟩ := T.handler _ cs _ h
  have hb' : TypedV EB instrsT
      (.list (adminsToV (vals vs) ++ [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, hcv⟩ := typedV_list_append.1 hab
  have hy : TypedV EB typeuseT yy :=
    Silmaril.Wasm.Validation.Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefHandler (simEnv_readRules _).returnCallRefHandler
    (z := stateV hn s f) (k := .num (.natN k)) (cs := cs.map Encode.toValue)
    (ws := adminsToV (vals vs)) (is := adminsToV rest) hz hk hcs
    (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

/-- `return_call_ref` out of a frame at `null` (`Sim.fwd_returnCallRefFrameNull`, before the
lift). -/
theorem sreadC_returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT
      (.list (adminsToV [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]))) :
    SRead EB (configV hn ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩)
      (adminsToV [.trap]) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨yy, hyy⟩ := adminToV_of_isReturnCallRef hc
  obtain ⟨hk, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV EB instrsT
      (.list (adminsToV (vals vs) ++ [caseNilV "REF.NULL_ADDR"] ++ [adminToV c] ++
        adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨habc, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hab, hcv⟩ := typedV_list_append.1 habc
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have hy : TypedV EB typeuseT yy :=
    Silmaril.Wasm.Validation.Ty.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have key := sread_returnCallRefFrameNull (simEnv_readRules _).returnCallRefFrameNull
    (z := stateV hn s f) (k := .num (.natN k)) (f := frameV fi)
    (ws := adminsToV (vals vs)) (is := adminsToV rest) hz hk hfi
    (typedV_vals_prefix T (b := []) (by simpa using hv)) hy hrest
  simpa [configV, adminsToV_append, hyy] using key

/-- `throw_ref` past values or before instructions (`Exn.fwd_throwRefInstrs`, before the
lift). -/
theorem sreadC_throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (hz : TypedV EB stateT (stateV hn s f))
    (his : TypedV EB instrsT (.list (adminsToV (vals vs ++ throwing a ++ rest)))) :
    SRead EB (configV hn ⟨s, f, vals vs ++ throwing a ++ rest⟩) (adminsToV (throwing a)) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing EB := Typing.exnTyping_simEnv' _
  have his₁ : TypedV EB instrsT (.list (adminsToV (vals vs ++ (throwing a ++ rest)))) := by
    rwa [List.append_assoc] at his
  obtain ⟨hvs, htr⟩ := Exn.typed_vals_append _ T his₁
  have htr' : TypedV EB instrsT (.list (adminsToV (throwing a) ++ adminsToV rest)) := by
    rwa [adminsToV_append] at htr
  obtain ⟨-, hrest⟩ := (T.append _ _).1 htr'
  have hne' : vs.map valV ≠ [] ∨ adminsToV rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (by simpa using h)
    · exact .inr (adminsToV_ne_nil h)
  have h := Exn.sread_throwRefInstrs (Exn.hasReadRules_simEnv _).throwRefInstrs hz hvs (X.addr a)
    hrest hne'
  show SRead _ (cfgV (stateV hn s f) (adminsToV (vals vs ++ throwing a ++ rest)))
    (adminsToV (throwing a))
  rwa [adminsToV_append, adminsToV_append, Exn.adminsToV_vals]

end Silmaril.Wasm.SpecTec.Institution.FwdB30
