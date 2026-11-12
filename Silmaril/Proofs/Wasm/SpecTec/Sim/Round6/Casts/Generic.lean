module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Invert
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Obl

/-!
# Round 6: the backward recursion under the new reading

`Target.backward_upToVC` (`Round6/Target/Generic.lean`) for `SStepB`: the four
context cases are copied with the new reading's inversions (`inv_*B`, `Invert.lean`); rule 0 and
the rules from 6 on transfer to the old reading (`Reading.firesB_step_iff`) and use round 5's
obligations (`pureDecl`, `stepDecl`); rule 1 uses `readB`, which covers the cast rules of
`Step_read` from `RefOkBB`. The predicate is `ReadValidS`, closed under SpecTec's context
decompositions (`Round5.Read.readValidS_ctxClosed`). No cast redex is assumed: `backwardB` is the
backward simulation of the new reading from every typed `ReadValidS` configuration.

Round 6, track casts-v: `bwdG_read`, `bwdG_dispatch`, `bwdG_all` and `backwardG` run the same
recursion under `ReadValidS c ∧ W c`, for `W` closed under the context decompositions, from
`CastRefOk` at that predicate. `backwardB` is the instance at `W := True`, with an unchanged
statement.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Bwd (codeSize adminsToV_split3 configV_eq configV_cfgV cfgV_of_configEq CodeEq ConfigEq
  BwdUpTo StructDecode stV_inj findRel_of_ruleAt)
open Reading (SStepB SReadB FiresB RefOkBB)

variable {H : Type}

section Ctxt

variable {V : Config H → Prop} {env : Env} {hn : H → String} {P : Numerics.Profile}
  {host : HostSemantics H}

/-- The induction hypothesis, for code smaller than `n`, under `V` and the new reading. -/
def IHVB (V : Config H → Prop) (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), codeSize c.code < n → V c → Typed env hn c →
    SStepB env (configV hn c) w → BwdUpTo hn P host c w

/-- `ctxt-instrs` backwards, under `V`. -/
theorem bwdB_ctxtInstrs (CV : Target.CtxClosedVals V) (D : StructDecode env)
    (T : TypingFacts env hn)
    {n : Nat} (ih : IHVB V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtInstrsInvB env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, h₂, hs⟩ := hinv
  have e₁ : z = stateV hn s f ∧ vs ++ is ++ rest = adminsToV code := configV_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := adminsToV_split3 e₁.2.symm
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := D.vals ρ A hρ (hA ▸ hvs)
  have hneA' : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have hneA : vs₀ ≠ [] ∨ R ≠ [] := hneA'.imp (fun h he => h (by rw [hv₀, he]; rfl)) id
  have hT : Typed env hn ⟨s, f, I⟩ := Target.typed_midC T (hcode ▸ hc)
  have hV : V ⟨s, f, I⟩ := CV.mid s f vs₀ I R (hv₀ ▸ hcode ▸ hv)
  have hsz : codeSize I < n := by
    have h₁ : codeSize I < codeSize (A ++ I ++ R) := Bwd.codeSize_mid hneA'
    have h₂ : codeSize (A ++ I ++ R) < n + 1 := hcode ▸ hlt
    omega
  have e₂ : cfgV z is = configV hn ⟨s, f, I⟩ := by rw [configV_eq, e₁.1, hI]
  have hs' : SStepB env (configV hn ⟨s, f, I⟩) (cfgV z' is') := e₂ ▸ hs
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ := ih _ _ hsz hV hT hs'
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, vals vs₀ ++ K ++ R⟩, ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩,
    ⟨rfl, rfl, (CodeEq.refl _).append hE.2.2 |>.append (CodeEq.refl _)⟩, ?_, ?_⟩
  · show w = configV hn ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩
    rw [h₂, hz', his', configV_eq, adminsToV_append, adminsToV_append, ← hv₀, hA, hR]
  · show Step P host ⟨s, f, code⟩ ⟨s₂, f₂, vals vs₀ ++ K ++ R⟩
    rw [hcode, hv₀]
    exact .ctxtInstrs hst hneA

/-- `ctxt-label` backwards, under `V`. -/
theorem bwdB_ctxtLabel (CV : Target.CtxClosedVals V) (D : StructDecode env)
    (T : TypingFacts env hn)
    {n : Nat} (ih : IHVB V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cont is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is])] ∧
      w = cfgV z' [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is'])] ∧
      SStepB env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := D.label a _ ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, f, body⟩ :=
    Bwd.typed_inner T hc fun h => (T.label k cont₀ body h).2.2
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_label k cont₀ body) (Nat.le_of_lt_succ hlt))
      (CV.label s f k cont₀ body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ⟨s₂, f₂, [.label k cont₀ K']⟩,
    ⟨rfl, rfl, .cons (.label hE.2.2) .nil⟩, ?_, .ctxtLabel hst⟩
  show w = configV hn ⟨s₂, f₂, [.label k cont₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-handler` backwards, under `V`. -/
theorem bwdB_ctxtHandler (CV : Target.CtxClosedVals V) (D : StructDecode env)
    (T : TypingFacts env hn)
    {n : Nat} (ih : IHVB V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cs is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is])] ∧
      w = cfgV z' [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is'])] ∧
      SStepB env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cs, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cs₀, body, rfl⟩ := D.handler a _ ha
  have hp : Value.num (.natN k) = m ∧ cs₀.map Encode.toValue = cs ∧ adminsToV body = is := by
    simpa only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, f, body⟩ :=
    Bwd.typed_inner T hc fun h => (T.handler k cs₀ body h).2.2
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_handler k cs₀ body) (Nat.le_of_lt_succ hlt))
      (CV.handler s f k cs₀ body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, [.handler k cs₀ K]⟩, ⟨s₂, f₂, [.handler k cs₀ K']⟩,
    ⟨rfl, rfl, .cons (.handler hE.2.2) .nil⟩, ?_, .ctxtHandler hst⟩
  show w = configV hn ⟨s₂, f₂, [.handler k cs₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-frame` backwards, under `V`. -/
theorem bwdB_ctxtFrame (CV : Target.CtxClosedVals V) (D : StructDecode env)
    (T : TypingFacts env hn)
    {n : Nat} (ih : IHVB V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtFrameInvB env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := D.frame a _ ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, fi, body⟩ := Target.typed_frameC T hc
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq, e₀.1, ← hp.2.1, hp.2.2]
    rfl
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_frame k fi body) (Nat.le_of_lt_succ hlt))
      (CV.frame s f fi k body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  have hz'' : sv' = storeV hn s₂ ∧ fr' = frameV f₂ := stV_inj hz'
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ⟨s₂, f, [.frame k f₂ K']⟩,
    ⟨rfl, rfl, .cons (.frame hE.2.2) .nil⟩, ?_, .ctxtFrame hst⟩
  show w = configV hn ⟨s₂, f, [.frame k f₂ K']⟩
  rw [h₂, hz''.1, hz''.2, his', e₀.2, ← hp.1]
  rfl

end Ctxt

section Dispatch

open Round4Int (BI)
open Round5.Read (ReadValidS)

variable {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- `Step/pure` backwards, under `ReadValidS`: the old reading's `Step_pure` (`pureDecl`). -/
theorem bwdB_pure (hinj : Function.Injective hn) (hfh : HostFinite host) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hv : ReadValidS ⟨s, f, code⟩)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, code⟩)
    (hinv : ∃ z is js, configV hn ⟨s, f, code⟩ = cfgV z is ∧ w = cfgV z js ∧
      SPure (simEnv (BI P hn host)) is js) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt (simEnv_execRules (BI P hn host)).unreachable
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hfi⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires (simEnv (BI P hn host)) "Step_pure" i
      (.tuple [.list (adminsToV code), .list js]) := e₁.2 ▸ hfi
  obtain ⟨is', js', hE, hw, hst⟩ := pureDecl hinj hfh i s f code (.list js) hv hc hf'
  refine ⟨⟨s, f, is'⟩, ⟨s, f, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- `Step/read` backwards, under `ReadValidS c ∧ W c` and the new reading (`readG`). -/
theorem bwdG_read (hinj : Function.Injective hn) (hfh : HostFinite host) {W : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => ReadValidS c ∧ W c))
    {c : Config H} {w : Value} (hv : ReadValidS c ∧ W c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hinv : ∃ z is js, configV hn c = cfgV z is ∧ w = cfgV z js ∧
      SReadB (simEnv (BI P hn host)) (cfgV z is) js) : BwdUpTo hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := Reading.findRel_read (BI P hn host)
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hfi⟩ := (Reading.dderivesB_iff_firesB hrel).1 hp
  have hf' : FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, .list js]) :=
    h₁ ▸ hfi
  obtain ⟨is', js', hE, hw, hst⟩ := readG hinj hfh K i c (.list js) hv hc hf'
  refine ⟨⟨c.store, c.frame, is'⟩, ⟨c.store, c.frame, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- One step of the recursion, under `ReadValidS c ∧ W c` and the new reading. -/
theorem bwdG_dispatch (hinj : Function.Injective hn) (hfh : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {W : Config H → Prop} (CW : Target.CtxClosedVals W)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => ReadValidS c ∧ W c)) {n : Nat}
    (ih : IHVB (fun c => ReadValidS c ∧ W c) (simEnv (BI P hn host)) hn P host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hlt : codeSize code < n + 1)
    (hv : ReadValidS ⟨s, f, code⟩ ∧ W ⟨s, f, code⟩)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, code⟩)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn ⟨s, f, code⟩) w) :
    BwdUpTo hn P host ⟨s, f, code⟩ w := by
  have R : HasStepRules (simEnv (BI P hn host)) := hasStepRules_simEnv _
  have CV : Target.CtxClosedVals (fun c : Config H => ReadValidS c ∧ W c) :=
    ctxClosedVals_and (Target.ctxClosedVals_of Round5.Read.readValidS_ctxClosed) CW
  have D : StructDecode (simEnv (BI P hn host)) :=
    Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt R.pure
  obtain ⟨i, hfi⟩ := (Reading.dderivesB_iff_firesB hrel).1 hs
  rcases i with _ | _ | _ | _ | _ | _ | k
  · exact bwdB_pure hinj hfh hv.1 hc
      (Bwd.inv_pure R.pure ((Reading.firesB_step_iff _ (.inl rfl)).1 hfi))
  · exact bwdG_read hinj hfh K hv hc (inv_readB R.read hfi)
  · exact bwdB_ctxtInstrs CV D T ih hlt hv hc (inv_ctxtInstrsB R.ctxtInstrs hfi)
  · exact bwdB_ctxtLabel CV D T ih hlt hv hc (inv_ctxtLabelB R.ctxtLabel hfi)
  · exact bwdB_ctxtHandler CV D T ih hlt hv hc (inv_ctxtHandlerB R.ctxtHandler hfi)
  · exact bwdB_ctxtFrame CV D T ih hlt hv hc (inv_ctxtFrameB R.ctxtFrame hfi)
  · exact stepDecl hinj hfh hPs hPf (k + 6) (by omega) _ w hv.1 hc
      ((Reading.firesB_step_iff _ (.inr (by omega))).1 hfi)

/-- The recursion on the size of the code, under `ReadValidS c ∧ W c` and the new reading. -/
theorem bwdG_all (hinj : Function.Injective hn) (hfh : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {W : Config H → Prop} (CW : Target.CtxClosedVals W)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => ReadValidS c ∧ W c)) :
    ∀ n, IHVB (fun c => ReadValidS c ∧ W c) (simEnv (BI P hn host)) hn P host n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨_, _, _⟩ _ hlt hv hc hs =>
      bwdG_dispatch hinj hfh hPs hPf CW K (bwdG_all hinj hfh hPs hPf CW K n) hlt hv hc hs

/-- **The backward simulation of the new reading, from `CastRefOk`** at `ReadValidS c ∧ W c`,
for `W` closed under the context decompositions (SpecTec → Core, up to `ConfigEq`). -/
theorem backwardG (hinj : Function.Injective hn) (hfh : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    {W : Config H → Prop} (CW : Target.CtxClosedVals W)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => ReadValidS c ∧ W c))
    (c : Config H) (w : Value) (hv : ReadValidS c) (hw : W c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  bwdG_all hinj hfh hPs hPf CW K (codeSize c.code + 1) c w (Nat.lt_succ_self _) ⟨hv, hw⟩ hc hs

/-- **The backward simulation of the new reading, from `RefOkBB`** (SpecTec → Core, up to
`ConfigEq`): every `SStepB` step from the image of a typed `ReadValidS` configuration is the
image of a Core step, at the concrete builtins, for an injective encoding, a finite host and a
profile in which growth may both succeed and fail. -/
theorem backwardB (hinj : Function.Injective hn) (hfh : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (KB : RefOkBB (simEnv (BI P hn host))) (c : Config H) (w : Value) (hv : ReadValidS c)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backwardG hinj hfh hPs hPf true_closed (Reading.castRefOk_bnd KB fun _ h => h.1.frame) c w hv
    trivial hc hs

end Dispatch

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
