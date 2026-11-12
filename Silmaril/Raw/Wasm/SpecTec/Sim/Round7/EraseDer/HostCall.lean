module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.GrowRule
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckHost

/-!
# Round 7, moving derivations across erasure: `$hostcall` in a rule of `Step` (unrefined)

The facts about `$hostcall` that the host-call rules of `Step` need, in the round-7 environment at
round 6's primitives:

* `hostFacts`: what the kernel check `xHostOk_fixed` says about `call_ref-hostfunc-res`/`-div`.
* `evalExp_hostMem_iff`: the premise `pat <- $hostcall(args)` holds exactly when the arguments
  evaluate to `ws`, round 4's primitive answers a list at `ws`, and the pattern's value is in it.
* `hostcallCall_inv`: an answer of the primitive lists the outcomes of a host call whose image the
  arguments are.
* `storeV_uniq_typed`: the image of an export-free store, typed `store` in the round-7
  environment, has one preimage (`Round5.FwdRef2.storeV_inj_typed`, through
  `TypAgree.hasTyp_utf8Env_iff_B`).
* `storeNE_of_eImg`: a store whose image is in the erased swap set is export-free.
* `storeV_unstrip`: **the store form of `Round7.Swap.eq_configV_unstrip`**: under `StripInj c`, a
  value in `AllIn (QC c)` that erases to the image of an export-free store `s₁` is the image of
  `mapStore (unstrip c) s₁`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (xPrem xExp xArgs grB gdB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (detFacts quantNames ruleK premDetOk invVars)
open Round6.Reading (conclAlts)
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff)

/-! ## The shape of a host-call rule -/

/-- The arguments of the `$hostcall` premise. -/
def hostArgsE (a₁ : Arg) (z : IL.Id) (a₃ : Arg) : List Arg := [a₁, .expA (.varE z), a₃]

/-- The `$hostcall` premise `pat <- $hostcall(a₁, z, a₃)`. -/
def hostPr (pat : Exp) (a₁ : Arg) (z : IL.Id) (a₃ : Arg) : Prem :=
  .ifPr (.memE pat (.callE "hostcall" (hostArgsE a₁ z a₃)))

/-- What the kernel check says about the premises of a host-call rule. -/
structure HostShape (qs : List Param) (e : Exp) (prems ps : List Prem) (pat : Exp) (a₁ : Arg)
    (z : IL.Id) (a₃ : Arg) : Prop where
  eq : prems = ps ++ [hostPr pat a₁ z a₃]
  checked : ∀ pr ∈ ps, (xPrem grB gdB pr = true ∧ noElseP pr = true) ∧
    premDetOk (ruleK qs e ps) pr = true
  xpat : xExp grB gdB pat = true
  args : xArgs grB gdB (hostArgsE a₁ z a₃) = true
  argsK : varsIn (ruleK qs e ps) (freeArgs (hostArgsE a₁ z a₃)) = true
  store : Param.expP z (.varT "store" []) ∈ qs
  storeK : z ∈ ruleK qs e ps
  quants : ∀ x ∈ quantNames qs, x ∈ ruleK qs e ps ∨ x ∈ invVars pat

theorem hasStoreQ_mem {z : IL.Id} {qs : List Param} (h : hasStoreQ z qs = true) :
    Param.expP z (.varT "store" []) ∈ qs := by
  obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h
  split at hq'
  · obtain rfl := beq_iff_eq.1 hq'
    exact hq
  · exact absurd hq' (by simp)

theorem hostPrems_inv {qs : List Param} {e : Exp} {prems : List Prem}
    (h : hostPrems qs e prems = true) :
    ∃ ps pat a₁ z a₃, HostShape qs e prems ps pat a₁ z a₃ := by
  unfold hostPrems at h
  split at h
  · rename_i p₁ p₂ p₃ pat a₁ z a₃
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hps, hpat⟩, hargs⟩, hK⟩, hz⟩, hzK⟩, hq⟩ := h
    refine ⟨[p₁, p₂, p₃], pat, a₁, z, a₃, ⟨rfl, fun pr hpr => ?_, hpat, hargs, hK,
      hasStoreQ_mem hz, by simpa using hzK, fun x hx => ?_⟩⟩
    · exact hps pr hpr
    · simpa using hq x hx
  · exact absurd h (by simp)

/-- What the kernel checks say about a host-call rule. -/
structure HostFacts (ps qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  params : ps = []
  alts : conclAlts e = [e]
  concl : xExp grB gdB e = true
  shape : ∃ ps₃ pat a₁ z a₃, HostShape qs e prems ps₃ pat a₁ z a₃
  premsClosed : ∀ pr ∈ prems, varsIn (quantNames qs) (freePrem pr) = true
  closed : varsIn (quantNames qs) (freeExp e) = true
  quants : ∀ y t, Param.expP y t ∈ qs →
    xTy TypAgree.tyB t = true ∧ varsIn (quantNames qs) (freeTyp t) = true

theorem hostFacts {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hrel : (utf8Env B).findRel? "Step" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∈ hostNames) :
    HostFacts ps qs e prems := by
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hF := detFacts step_reach hrel' hrule
  have hm := EraseAll.mem_rels_of_findRel' hrel'
  obtain ⟨d', hd', hm'⟩ := EraseAll.mem_relsOfDefs hm
  have hS := List.all_eq_true.1 (List.all_eq_true.1 xHostOk_fixed d' hd') _ hm'
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at hS
  have hS' := hS _ hr
  have hnm' : hostNames.contains nm = true := by simpa using hnm
  simp only [xHostRule, hnm', Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.not_eq_true'] at hS'
  obtain ⟨⟨hno, hx⟩, hsh⟩ := hS'
  have hreach' : Script.stepReach.contains (0, "Step") = true := List.contains_iff_mem.2 step_reach
  have hc := List.all_eq_true.1 closedRels_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have hq := List.all_eq_true.1 xRelQuants_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or, List.all_eq_true] at hq
  have hq' := hq _ hr
  simp only [List.all_eq_true] at hq'
  have halts : conclAlts e = [e] := by simp [conclAlts, hno]
  refine ⟨hF.params, halts, hx, hostPrems_inv hsh, hcl.1.2, hcl.1.1 e (by simp [halts]),
    fun y ty hy => ⟨?_, ?_⟩⟩
  · simpa using hq' _ hy
  · simpa using hcl.2 _ hy

/-- **An answer of `$hostcall` lists the outcomes of a host call** whose image the arguments are. -/
theorem hostcallCall_inv {H : Type} {hn : H → String} {host : HostSemantics H} {ws : List ArgV}
    {v : Value} (h : Prims.hostcallCall hn host ws = some v) :
    ∃ (hf : H) (s : Store H) (vs : List Val)
      (os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result)),
      ws = Prims.hostArgs hn hf s vs ∧ (∀ o, host hf s vs o ↔ o ∈ os) ∧
        v = .list (os.map (outcomeV hn)) := by
  unfold Prims.hostcallCall at h
  split at h
  · rename_i hex
    cases h
    exact ⟨_, _, _, _, hex.choose_spec.1, hex.choose_spec.2.choose_spec, rfl⟩
  · cases h

/-! ## The `$hostcall` premise -/

section Call

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : HostSemantics H)

set_option maxRecDepth 100000 in
theorem findDef_hostcall_utf8 (B : Builtins) :
    ∃ ps t, (utf8Env B).findDef? "hostcall" = some (ps, t, []) := by
  rw [findDef?_utf8Env_of_ne B (by decide)]
  exact ⟨_, _, rfl⟩

theorem intCall_hostcall (ws : List ArgV) : IntNumeric.intCall "hostcall" ws = none := by
  unfold IntNumeric.intCall
  split <;> simp_all

theorem call_hostcall_BI (ws : List ArgV) :
    (utf8Env (Round4Int.BI P hn host)).builtins.call "hostcall" ws =
      Prims.hostcallCall hn host ws := by
  show (if "hostcall" = "utf8" then Round6.MemSimd.utf8Call ws
    else Prims.call P hn host "hostcall" ws) = _
  simp [Prims.call, Floats.floatCall, Floats.floatNames, intCall_hostcall]

/-- **The `$hostcall` premise, read**: at a scope without definition variables, the premise
`pat <- $hostcall(args)` holds exactly when the arguments evaluate to `ws`, the primitive answers
a list at `ws`, and the value of `pat` is in it. -/
theorem evalExp_hostMem_iff {ρ : VarEnv} (hd : ρ.defs = []) {pat : Exp} {args : List Arg} :
    EvalExp (utf8Env (Round4Int.BI P hn host)) ρ (.memE pat (.callE "hostcall" args))
        (.bool true) ↔
      ∃ v ws l, EvalExp (utf8Env (Round4Int.BI P hn host)) ρ pat v ∧
        EvalArgs (utf8Env (Round4Int.BI P hn host)) ρ args ws ∧
        Prims.hostcallCall hn host ws = some (.list l) ∧ v ∈ l := by
  have hfd : ρ.findDef? "hostcall" = none := by simp [VarEnv.findDef?, hd]
  obtain ⟨ps₀, t₀, hdef⟩ := findDef_hostcall_utf8 (Round4Int.BI P hn host)
  constructor
  · intro h
    obtain ⟨v, u, hv, hu, hm⟩ := evalExp_memE_iff.1 h
    obtain ⟨ws, ps, t, cs, ha, hf, hc⟩ := callDef_iff.1 (evalExp_callE_iff.1 hu)
    rw [hfd, Option.getD_none, hdef] at hf
    cases hf
    rcases hc with ⟨n, hn'⟩ | ⟨-, hb⟩
    · cases n <;> simp [tryClauses] at hn'
    rw [hfd, Option.getD_none, call_hostcall_BI] at hb
    obtain ⟨_, _, _, os, -, -, rfl⟩ := hostcallCall_inv hb
    exact ⟨v, ws, _, hv, ha, hb, by simpa [memValue] using hm⟩
  · rintro ⟨v, ws, l, hv, ha, hc, hm⟩
    refine evalExp_memE_iff.2 ⟨v, .list l, hv, evalExp_callE_iff.2 (callDef_iff.2
      ⟨ws, ps₀, t₀, [], ha, by rw [hfd, Option.getD_none, hdef], Or.inr ⟨⟨1, by simp [tryClauses]⟩,
        by rw [hfd, Option.getD_none, call_hostcall_BI, hc]⟩⟩), ?_⟩
    simp [memValue, hm]

end Call

/-! ## Stores -/

section Stores

variable {H : Type}

open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (StoreNE) in
/-- **The image of an export-free store, typed `store` in the round-7 environment, has one
preimage.** -/
theorem storeV_uniq_typed (P : Silmaril.Wasm.Numerics.Profile) {hn : H → String}
    (hinj : Function.Injective hn) {host : HostSemantics H} {σ : List (IL.Id × Value)}
    {s : Store H} (ht : HasTyp (utf8Env (Round4Int.BI P hn host)) (VarEnv.empty.bindVals σ)
      (.varT "store" []) (storeV hn s)) (hne : StoreNE s) :
    ∀ s', storeV hn s' = storeV hn s → s' = s := by
  have hv : TypAgree.ExpFree (storeV hn s) := ExpEnc.expFree_of_efB _ (ExpEnc.efB_storeV hn hne)
  have hD : Script.DefsOk (VarEnv.empty.bindVals σ) := Script.defsOk_bindVals Script.defsOk_empty σ
  have hT : TypAgree.TypsOk TypAgree.tyA (VarEnv.empty.bindVals σ) :=
    TypAgree.typsOk_of_typs (TypAgree.typsOk_empty TypAgree.tyA) rfl
  have hs := (TypAgree.hasTyp_utf8Env_iff_B (BI_utf8 P hn host) hD hT (by decide) hv).1 ht
  have hty : TypedV (simEnv (Round4Int.BI P hn host)) storeT (storeV hn s) :=
    Typing.typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ hs
  exact fun s' he => (Round5.FwdRef2.storeV_inj_typed hinj hty he.symm).symm

theorem mapStore_stripModule (s : Store H) : mapStore stripModule s = stripStore s := rfl

open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (StoreNE) in
/-- **A store whose image is in the erased swap set is export-free.** -/
theorem storeNE_of_eImg {Q : Value → Prop} (hQA : ∀ r, Q r → AllIn Q r) (hn : H → String)
    {s : Store H} (h : AllIn (EImg Q) (storeV hn s)) : StoreNE s := by
  have he : eraseV (storeV hn s) = storeV hn s := by
    have hu := (unerase_eImg hQA _ h).2
    conv_lhs => rw [← hu]
    rw [eraseV_idem, hu]
  rw [eraseV_storeV, mapStore_stripModule] at he
  have hb := ExpEnc.efB_storeV hn (ExpEnc.storeNE_stripStore s)
  rw [he] at hb
  exact ExpEnc.storeNE_of_efB hn hb

theorem mapStore_comp (μ ν : ModuleInst → ModuleInst) (s : Store H) :
    mapStore μ (mapStore ν s) = mapStore (μ ∘ ν) s := by
  simp [mapStore, mapFI, List.map_map, Function.comp_def]

open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (StoreNE) in
/-- **The store form of `Round7.Swap.eq_configV_unstrip`**: under `StripInj c`, a value in
`AllIn (QC c)` that erases to the image of an export-free store `s₁` is the image of
`mapStore (unstrip c) s₁`. -/
theorem storeV_unstrip (hn : H → String) {c : Config H} (hinj : StripInj c) {s₁ : Store H}
    (hne : StoreNE s₁) {w : Value} (hw : AllIn (QC c) w) (he : eraseV w = storeV hn s₁) :
    w = storeV hn (mapStore (unstrip c) s₁) := by
  refine eraseV_inj (qInj_QC hinj) hw (allIn_storeV hn fun fi hfi => ?_) ?_
  · simp only [mapStore, List.mem_map] at hfi
    obtain ⟨fi₁, hfi₁, rfl⟩ := hfi
    have hex : fi₁.module.exports = [] := hne fi₁ hfi₁
    simp only [mapFI]
    by_cases hx : ∃ m ∈ mods c, stripModule m = fi₁.module
    · have hu : unstrip c fi₁.module = hx.choose := by simp only [unstrip, dite_eq_left hx]
      exact Or.inl ⟨_, hu ▸ hx.choose_spec.1, by rw [hu]⟩
    · have hu : unstrip c fi₁.module = fi₁.module := by simp only [unstrip, dite_eq_right hx]
      refine Or.inr ⟨fi₁.module, hex, by rw [hu], ?_⟩
      exact fun m' hm' hs => absurd ⟨m', hm', hs⟩ hx
  · rw [he, eraseV_storeV, mapStore_comp]
    congr 1
    conv_lhs => rw [← ExpEnc.stripStore_of_storeNE hne, ← mapStore_stripModule]
    simp only [mapStore, Function.comp_def, stripModule_unstrip]

end Stores

/-! ## The arguments of the `$hostcall` premise -/

theorem evalArgs_var2 {env : Env} {ρ : VarEnv} {a₁ a₃ : Arg} {z : IL.Id} {ws : List ArgV}
    (h : EvalArgs env ρ (hostArgsE a₁ z a₃) ws) :
    ∃ w₁ v w₃, ρ.findVal? z = some v ∧ ws = [w₁, .val v, w₃] := by
  obtain ⟨k, h⟩ := h
  cases k with
  | zero => simp [evalArgs] at h
  | succ k =>
    simp only [hostArgsE, evalArgs, List.mapM_cons, List.mapM_nil, Res.bind_eq_ok, pure,
      Except.pure] at h
    obtain ⟨b₁, -, l₁, ⟨b₂, h₂, l₂, ⟨b₃, -, l₃, hl₃, hl₂⟩, hl₁⟩, hws⟩ := h
    obtain ⟨v, hv, rfl⟩ := evalArg_var h₂
    cases Except.ok.inj hl₃
    cases Except.ok.inj hl₂
    cases Except.ok.inj hl₁
    exact ⟨b₁, v, b₃, hv, (Except.ok.inj hws).symm⟩

/-- An argument whose erasure is a value without `EXPORTS` records is that value. -/
theorem eq_of_eraseA_nxB {w : ArgV} {u : Value} (h : eraseA w = .val u) (hu : nxB u = true) :
    w = .val u := by
  cases w with
  | val v =>
    simp only [eraseA, ArgV.val.injEq] at h
    subst h
    rw [EraseAll.nxB_eraseV] at hu
    rw [eraseV_of_nxB v hu]
  | _ => simp [eraseA] at h

theorem nxB_hostfunc (t : String) : nxB (.case "_HOSTFUNC" (.text t)) = true := rfl

theorem nxB_vals (vs : List Val) : nxB (.list (vs.map valV)) = true := by
  simp [nxB, nxBs_eq_all, nxB_valV]

/-- The arguments of a host call determine the call, up to the image of its store. -/
theorem hostArgs_inj {H : Type} {hn : H → String} (hinj : Function.Injective hn) {h h' : H}
    {s s' : Store H} {vs vs' : List Val}
    (he : Prims.hostArgs hn h s vs = Prims.hostArgs hn h' s' vs') :
    h = h' ∧ storeV hn s = storeV hn s' ∧ vs = vs' := by
  have he' : hn h = hn h' ∧ storeV hn s = storeV hn s' ∧ vs.map valV = vs'.map valV := by
    simpa only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq, Value.case.injEq,
      Value.text.injEq, Value.list.injEq, true_and, and_true] using he
  exact ⟨hinj he'.1, he'.2.1, (List.map_injective_iff.2 Typing.valV_injective) he'.2.2⟩

/-- **A finite host's call has an answer.** -/
theorem hostcallCall_some {H : Type} (hn : H → String) {host : HostSemantics H}
    (hf : HostFinite host) (h : H) (s : Store H) (vs : List Val) :
    ∃ l, Prims.hostcallCall hn host (Prims.hostArgs hn h s vs) = some (.list l) := by
  unfold Prims.hostcallCall
  have hex : ∃ p : H × Store H × List Val,
      Prims.hostArgs hn h s vs = Prims.hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os :=
    ⟨(h, s, vs), rfl, hf h s vs⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact ⟨_, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
