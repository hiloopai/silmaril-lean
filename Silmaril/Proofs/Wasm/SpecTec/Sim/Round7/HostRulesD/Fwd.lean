module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostRulesD.Prims

/-!
# Round 7, `BD`: the host-call rules forward, at `configVD`

Round 5's `FwdRef.fwd_callRefHostT` and `fwd_callRefHostDivT` prove that Core's host-call steps
(`call_ref` into a host function that returns or diverges) are SpecTec steps (`Step` rules 8 and
9) between `configV` images, at `BI`. Pass 1 of round 5 showed that `BM`, the round-7 target's
builtins, answers no `$hostcall` from a `storeVD` image of a store with memory SIMD code
(`MSPres.bm_hostcall_none`), so the same steps fail at `configVD` there. Here they are proved
at `configVD` and `BD`, for **every** store, memory SIMD code included:

* `adminsMS_vals`, `adminsMS_result`: the code of a host call and of its result has no memory
  SIMD instruction, so its `adminsToVD` image is its `adminsToV` image;
* `funcinstD_of_store`, `applies_funcinstD`, `funcInstVD_code_host`: the function instances of a
  typed `storeVD` image are typed, `$funcinst(s; f)` reads them, and a host function's `CODE`
  field is `_HOSTFUNC (hn h)`;
* `fwd_callRefHostD` (rule 8) and `fwd_callRefHostDivD` (rule 9): the SpecTec step at
  `simEnv (BD …)` between the `configVD` images, for typed images and a bounded callee type, from
  `HostD.hostcallD_typed` (`BD`'s `$hostcall` lists the `outcomeVD` images of the outcomes).

The value-level rule lemmas (`sstep_callRefHostRes`, `sstep_callRefHostDiv`) are round 3's,
stated at arbitrary values, so they apply to `storeVD` images unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd)
open Round7.HostD (BD hostArgsD outcomeVD hostcallD_typed)
open Round7.MemSimd (storeVD stateVD configVD funcInstVD adminsToVD adminToVD TypedD
  typingFactsD_simEnv adminsToVD_eq)
open Round6.MemSimd (AdminMS AdminsMS instrMS memSimd)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Code without memory SIMD instructions -/

theorem adminMS_val (v : Val) : AdminMS v.toAdmin := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t <;> simp [Val.toAdmin, AdminMS, instrMS, memSimd]
  · simp [Val.toAdmin, AdminMS, instrMS, memSimd]
  · simp [Val.toAdmin, AdminMS]

theorem adminsMS_append : ∀ {l l' : List Admin}, AdminsMS l → AdminsMS l' → AdminsMS (l ++ l')
  | [], _, _, h' => h'
  | _ :: _, _, h, h' => ⟨h.1, adminsMS_append h.2 h'⟩

theorem adminsMS_vals : ∀ vs : List Val, AdminsMS (vals vs)
  | [] => trivial
  | v :: vs => ⟨adminMS_val v, adminsMS_vals vs⟩

theorem adminsMS_result (r : Result) : AdminsMS r.toAdmin := by
  cases r with
  | values vs => exact adminsMS_vals vs
  | throw a => exact ⟨trivial, by simp [AdminMS, instrMS, memSimd], trivial⟩
  | trap => exact ⟨trivial, trivial⟩

theorem adminMS_callRef {c : Admin} (hc : c.IsCallRef) : AdminMS c := by
  match c, hc with
  | .plain (.callRef _), _ => simp [AdminMS, instrMS, memSimd]
  | .callRefType _, _ => trivial

/-- The code of a host call has no memory SIMD instruction. -/
theorem adminsMS_hostCode (vs : List Val) (a : Nat) {c : Admin} (hc : c.IsCallRef) :
    AdminsMS (vals vs ++ [.ref (.func a), c]) :=
  adminsMS_append (adminsMS_vals vs) ⟨trivial, adminMS_callRef hc, trivial⟩

/-! ## Function instances of a `storeVD` image -/

/-- **A function instance of a typed `storeVD` image is a typed `funcinst`.** -/
theorem funcinstD_of_store (B : Builtins) (s : Store H) {a : Nat} {fi : FuncInst H}
    (h : TypedV (simEnv B) storeT (storeVD hn s)) (hfi : s.funcs[a]? = some fi) :
    TypedV (simEnv B) funcinstT (funcInstVD hn fi) := by
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty ConfigOk.findTyp_store'
    (h _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  exact ConfigOk.typedV_of_mem_list hF.2.2.2.2.1
    (List.mem_map_of_mem (List.mem_of_getElem? hfi))

/-- `$funcinst(s; f)` at a `stateVD` image reads the `funcInstVD` images. -/
theorem applies_funcinstD (B : Builtins) (s : Store H) (f : Frame) :
    Applies (simEnv B) "funcinst" [.val (stateVD hn s f)]
      (.list (s.funcs.map (funcInstVD hn))) :=
  Prims.applies_of_clause1 (Prims.projDefs_simEnv B).funcinst State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, rfl⟩)

theorem funcInstVD_code_host {fi : FuncInst H} {h : H} (hc : fi.code = .host h) :
    (funcInstVD hn fi).field? "CODE" = some (.case "_HOSTFUNC" (.text (hn h))) := by
  simp [funcInstVD, Value.field?, hc]

theorem funcsD_getElem_map {s : Store H} {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
    (s.funcs.map (funcInstVD hn))[a]? = some (funcInstVD hn fi) := by
  simp [h]

/-! ## The two rules -/

/-- **`call_ref` into a host function that returns, at `configVD` and `BD`** (`Step` rule 8), for
typed images and a bounded callee type. The store may hold memory SIMD code. -/
theorem fwd_callRefHostD (hinj : Function.Injective hn) (hf : HostFinite host)
    {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) (hd : tyBnd fi.type = true)
    (hc₁ : TypedD (simEnv (BD P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc₂ : TypedD (simEnv (BD P hn host)) hn ⟨s', f, r.toAdmin⟩) :
    SStep (simEnv (BD P hn host)) (configVD hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
      (configVD hn ⟨s', f, r.toAdmin⟩) := by
  have TD := typingFactsD_simEnv (BD P hn host) hn
  have T : TypingFacts (simEnv (BD P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BD P hn host)) := Typing.ctrlTyping_simEnv _
  have hms := adminsMS_hostCode vs a hc
  obtain ⟨hps, hrs, hexp⟩ := callTypesD (P := P) (hn := hn) (host := host) hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (TD.config _).1 hc₁
  have hst' : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s') :=
    ((TD.state _ _).1 ((TD.config _).1 hc₂).1).1
  obtain ⟨hst, hfr⟩ := (TD.state _ _).1 hz
  rw [adminsToVD_eq _ hms] at hcode₁
  obtain ⟨os, hcall, hall, -⟩ :=
    hostcallD_typed (P := P) hinj hf h s vs hst
  have hcv : TypedV (simEnv (BD P hn host)) instrT (adminToV c) :=
    typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BD P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BD P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeVD hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostRes (hasStepRules_simEnv _).callRefHostfuncRes
    (fs := s.funcs.map (funcInstVD hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy hst' (ConfigOk.typedV_result r)
    (funcinstD_of_store _ s hst hfa) hps (Tg.natM _) hrs (typedV_text (hn h))
    (applies_funcinstD _ s f) (funcsD_getElem_map hfa) rfl (funcInstVD_code_host hcode) hexp
    hcall' (hall _ hhost) (Prims.applies_liftResult _ r)
  have e₁ : adminsToVD (vals vs ++ [.ref (.func a), c]) =
      adminsToV (vals vs) ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy] := by
    rw [adminsToVD_eq _ hms, adminsToV_append]
    simp [adminsToV, adminToV, hyy, Equiv.RuntimeBridge.refToValue]
  have e₂ : adminsToVD r.toAdmin = adminsToV r.toAdmin := adminsToVD_eq _ (adminsMS_result r)
  change SStep _ (cfgV (stV (storeVD hn s) (frameV f)) (adminsToVD _))
    (cfgV (stV (storeVD hn s') (frameV f)) (adminsToVD _))
  rw [e₁, e₂]
  exact key

/-- **`call_ref` into a host function that diverges, at `configVD` and `BD`** (`Step` rule 9),
for a typed image and a bounded callee type. -/
theorem fwd_callRefHostDivD (hinj : Function.Injective hn) (hf : HostFinite host)
    {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged)
    (hd : tyBnd fi.type = true)
    (hc₁ : TypedD (simEnv (BD P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    SStep (simEnv (BD P hn host)) (configVD hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
      (configVD hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) := by
  have TD := typingFactsD_simEnv (BD P hn host) hn
  have T : TypingFacts (simEnv (BD P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BD P hn host)) := Typing.ctrlTyping_simEnv _
  have hms := adminsMS_hostCode vs a hc
  obtain ⟨hps, hrs, hexp⟩ := callTypesD (P := P) (hn := hn) (host := host) hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (TD.config _).1 hc₁
  obtain ⟨hst, hfr⟩ := (TD.state _ _).1 hz
  rw [adminsToVD_eq _ hms] at hcode₁
  obtain ⟨os, hcall, hall, -⟩ := hostcallD_typed (P := P) hinj hf h s vs hst
  have hcv : TypedV (simEnv (BD P hn host)) instrT (adminToV c) :=
    typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BD P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BD P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeVD hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostDiv (hasStepRules_simEnv _).callRefHostfuncDiv
    (fs := s.funcs.map (funcInstVD hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (funcinstD_of_store _ s hst hfa) hps
    (Tg.natM _) hrs (typedV_text (hn h)) (applies_funcinstD _ s f) (funcsD_getElem_map hfa) rfl
    (funcInstVD_code_host hcode) hexp hcall' (hall _ hhost)
  have e₁ : adminsToVD (vals vs ++ [.ref (.func a), c]) =
      adminsToV (vals vs) ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy] := by
    rw [adminsToVD_eq _ hms, adminsToV_append]
    simp [adminsToV, adminToV, hyy, Equiv.RuntimeBridge.refToValue]
  change SStep _ (cfgV (stV (storeVD hn s) (frameV f)) (adminsToVD _))
    (cfgV (stV (storeVD hn s) (frameV f)) (adminsToVD _))
  rw [e₁]
  exact key

end Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD
