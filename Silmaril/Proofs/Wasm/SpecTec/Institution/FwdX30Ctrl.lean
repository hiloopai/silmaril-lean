module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# The forward direction at wasm-3.0, extended: the control rules of `Step_read`

At the concrete primitives `Round4Int.BI`, every `CtrlRead c is'` (`block`, `loop`, `call`,
`return_call`, `return_call_ref` out of a label, a handler or a frame at `null`, `throw_ref`,
`try_table`) from a typed state and code to typed code, with a bounded frame module, is a
`Step_read` fact of the declarative reading.

The leaves are the bodies of the forward leaves of rounds 3–5 (`Round5.Fwd.fwd_block5`,
`fwd_loop5`, `fwd_call5`, `fwd_returnCall5`, `fwd_tryTable5`, `fwd_throwRefHandler*5`;
`Sim.fwd_returnCallRef*`; `Exn.fwd_throwRef*`), stopped before they lift the fact with
`Step/read`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

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
open Round4Int (BI)

variable {H : Type} {P : Profile} (hn : H → String) (host : HostSemantics H)

/-- The environment at the concrete primitives. -/
local notation "EB" => simEnv (BI P hn host)

/-- `block` (`Round5.Fwd.fwd_block5`, before the lift). -/
theorem sreadC_block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hlen : vs.length = t₁.length) (hM : ModuleBnd f.module)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT (.list (adminsToV (vals vs ++ [.plain (.block bt body)])))) :
    SRead EB (configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩)
      (adminsToV [.label t₂.length [] (vals vs ++ expression body)]) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := Round5.Fwd.blocktypeB (Round5.Int.typesB _) s f hM bt t₁ t₂ hbt
  have hv : TypedV EB valsT (.list (adminsToV (vals vs))) := typedV_vals_prefix T h
  have hblk : TypedV EB instrT (adminToV (.plain (.block bt body))) :=
    typedV_code h (.plain (.block bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Silmaril.Wasm.Validation.Ty.blockInv _ _ hblk
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_block (simEnv_readRules _).block (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Silmaril.Wasm.Validation.Ty.natM _) hv hbtT hbody
    (Silmaril.Wasm.Validation.Ty.nat _) h₁ h₂ hb
  rw [hl₂] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.block bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.block bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.block bt body)])))
    [adminToV (.label t₂.length [] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

/-- `loop` (`Round5.Fwd.fwd_loop5`, before the lift). -/
theorem sreadC_loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hlen : vs.length = t₁.length) (hM : ModuleBnd f.module)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT (.list (adminsToV (vals vs ++ [.plain (.loop bt body)])))) :
    SRead EB (configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩)
      (adminsToV [.label t₁.length [.loop bt body] (vals vs ++ expression body)]) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := Round5.Fwd.blocktypeB (Round5.Int.typesB _) s f hM bt t₁ t₂ hbt
  have hv : TypedV EB valsT (.list (adminsToV (vals vs))) := typedV_vals_prefix T h
  have hlp : TypedV EB instrT (adminToV (.plain (.loop bt body))) :=
    typedV_code h (.plain (.loop bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Silmaril.Wasm.Validation.Ty.loopInv _ _ hlp
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_loop (simEnv_readRules _).loop (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Silmaril.Wasm.Validation.Ty.natM _) hv hbtT hbody
    (Silmaril.Wasm.Validation.Ty.nat _) h₁ h₂ hb
  rw [hl₁] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.loop bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.loop bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.loop bt body)])))
    [adminToV (.label t₁.length [.loop bt body] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

/-- `call` (`Round5.Fwd.fwd_call5`, before the lift). -/
theorem sreadC_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi)
    (hz : TypedV EB stateT (stateV hn s f)) :
    SRead EB (configV hn ⟨s, f, [.plain (.call x)]⟩)
      (adminsToV [.ref (.func a), .callRefType fi.type]) :=
  have Silmaril.Wasm.Validation.Ty : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  have Pd := Prims.projDefs_simEnv (BI P hn host)
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
  have Pd := Prims.projDefs_simEnv (BI P hn host)
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

/-- `try_table` (`Round5.Fwd.fwd_tryTable5`, before the lift). -/
theorem sreadC_tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (hM : ModuleBnd f.module) (hz : TypedV EB stateT (stateV hn s f))
    (his : TypedV EB instrsT (.list (adminsToV (vals vs ++ [.plain (.tryTable bt cs body)]))))
    (his' : TypedV EB instrsT
      (.list (adminsToV [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]))) :
    SRead EB (configV hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩)
      (adminsToV [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing EB := Typing.exnTyping_simEnv' _
  obtain ⟨hvs, -⟩ := Exn.typed_vals_append _ T his
  obtain ⟨hn₀, hcs, hb⟩ := T.handler _ cs _ his'
  obtain ⟨-, -, hl⟩ := T.label _ [] _ hb
  obtain ⟨-, hbody⟩ := Exn.typed_vals_append _ T hl
  have hbody' : TypedV EB instrsT (.list (instrsToV body)) := by
    rwa [adminsToV_expression] at hbody
  have h := Round5.Fwd.sread_tryTableC (Round5.Fwd.helpersC_builtins hn host)
    (Exn.hasReadRules_simEnv _).tryTable hbt hm hz (X.m _) hvs (X.blocktype bt) hcs hbody' hn₀
    (Round5.Fwd.blocktypeB (Round5.Int.typesB _) s f hM bt t₁ t₂ hbt)
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.tryTable bt cs body)]))) _
  rw [adminsToV_append, Exn.adminsToV_vals]
  simpa [adminsToV, adminToV, instrsToV, adminsToV_append, Exn.adminsToV_vals,
    adminsToV_expression] using h

/-- **The control rules of `Step_read`** at `BI`: every `CtrlRead c is'` from a typed state and
code to typed code, with a bounded frame module, is a `Step_read` fact. The `throw_ref` arms are
the terms of `Exn.fwd_throwRef*` and `Round5.Fwd.fwd_throwRefHandler*5`. -/
theorem sread_of_ctrlRead {c : Config H} {is' : List Admin} (hr : CtrlRead c is')
    (hM : ModuleBnd c.frame.module) (hz : TypedV EB stateT (stateV hn c.store c.frame))
    (his : TypedV EB instrsT (.list (adminsToV c.code)))
    (his' : TypedV EB instrsT (.list (adminsToV is'))) :
    SRead EB (configV hn c) (adminsToV is') := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing EB := Typing.exnTyping_simEnv' _
  have R : Equiv.ExecRead.HasReadRules EB := Exn.hasReadRules_simEnv _
  cases hr with
  | block hbt hm => exact sreadC_block hn host hbt hm hM hz his
  | loop hbt hm => exact sreadC_loop hn host hbt hm hM hz his
  | call hx hf => exact sreadC_call hn host hx hf hz
  | returnCall hx hf => exact sreadC_returnCall hn host hx hf hz
  | returnCallRefLabel hc => exact sreadC_returnCallRefLabel hn host hc hz his
  | returnCallRefHandler hc => exact sreadC_returnCallRefHandler hn host hc hz his
  | returnCallRefFrameNull hc => exact sreadC_returnCallRefFrameNull hn host hc hz his
  | throwRefNull => exact Exn.sread_throwRefNull R.throwRefNull hz
  | throwRefInstrs hne => exact sreadC_throwRefInstrs hn host hne hz his
  | @throwRefLabel s f n cont a =>
    exact Exn.sread_throwRefLabel R.throwRefLabel hz (T.label n cont _ his).1
      (T.label n cont _ his).2.1 (X.addr a)
  | @throwRefFrame s f fi n a =>
    exact Exn.sread_throwRefFrame R.throwRefFrame hz (T.frame n fi _ his).1
      (T.frame n fi _ his).2.1 (X.addr a)
  | @throwRefHandlerEmpty s f n a =>
    exact Exn.sread_throwRefHandlerEmpty R.throwRefHandlerEmpty hz (T.handler n [] _ his).1
      (X.addr a)
  | @throwRefHandlerCatch s f n x l cs a e he ht =>
    exact Round5.Fwd.sread_throwRefHandlerCatchC (Round5.Fwd.helpersC_builtins hn host)
      R.throwRefHandlerCatch he ht hz (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a) (Exn.typed_vals_append _ T his').1
  | @throwRefHandlerCatchRef s f n x l cs a e he ht =>
    exact Round5.Fwd.sread_throwRefHandlerCatchRefC (Round5.Fwd.helpersC_builtins hn host)
      R.throwRefHandlerCatchRef he ht hz (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a) (Exn.typed_vals_append _ T his').1
  | @throwRefHandlerCatchAll s f n l cs a =>
    exact Exn.sread_throwRefHandlerCatchAll R.throwRefHandlerCatchAll hz (T.handler n _ _ his).1
      (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
  | @throwRefHandlerCatchAllRef s f n l cs a =>
    exact Exn.sread_throwRefHandlerCatchAllRef R.throwRefHandlerCatchAllRef hz
      (T.handler n _ _ his).1 (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
  | @throwRefHandlerNext s f n c cs a hnm =>
    exact Round5.Fwd.sread_throwRefHandlerNextC R (Round5.Fwd.helpersC_builtins hn host)
      R.throwRefHandlerNext hnm hz (T.handler n _ _ his).1 (X.catch_ c cs (T.handler n _ _ his).2.1).1
      (X.catch_ c cs (T.handler n _ _ his).2.1).2 (X.addr a)
  | tryTable hbt hm => exact sreadC_tryTable hn host hbt hm hM hz his his'

end Silmaril.Wasm.SpecTec.Institution.FwdX30
