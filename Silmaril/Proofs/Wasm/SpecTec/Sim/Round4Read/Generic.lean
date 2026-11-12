module

public import Silmaril.Wasm.SpecTec.Sim.Round4Read.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Generic

/-!
# The generic backward recursion under a configuration predicate

`backward_upToV` is `Bwd.backward_upTo` with the per-rule obligations relativised to a predicate
`V` on configurations (`BackwardUpToV`), for any `V` closed under the context decompositions
(`CtxClosed`). The recursion is the same as round 1's (on `Bwd.codeSize`); the only change is that
`V` is carried from a configuration to the redex of each context rule. `readValid_ctxClosed`
shows `ReadValid` is such a predicate.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Bwd (codeSize adminsToV_split3 configV_eq configV_cfgV cfgV_of_configEq CodeEq ConfigEq
  BwdUpTo StructDecode CtxtInstrsInv CtxtFrameInv stV_inj findRel_of_ruleAt)

variable {H : Type}

/-! ## `ReadValid` is closed under the context decompositions -/

/-- `codeIdx` splits along an append. -/
theorem codeIdx_append {s : Store H} {f : Frame} :
    ∀ (a b : List Admin), codeIdx s f (a ++ b) ↔ codeIdx s f a ∧ codeIdx s f b
  | [], b => by simp [codeIdx]
  | x :: a, b => by
    simp only [List.cons_append, codeIdx, codeIdx_append a b, and_assoc]

/-- **`ReadValid` is closed under the context decompositions.** -/
theorem readValid_ctxClosed : CtxClosed (ReadValid (H := H)) where
  mid _ _ _ _ _ h :=
    ⟨h.store, (((codeIdx_append _ _).1 ((codeIdx_append _ _).1 h.idx).1).2)⟩
  label _ _ _ _ _ h := ⟨h.store, h.idx.1⟩
  handler _ _ _ _ _ h := ⟨h.store, h.idx.1⟩
  frame _ _ _ _ _ h := ⟨h.store, h.idx.1⟩

/-! ## The recursion -/

section Ctxt

variable {V : Config H → Prop} {env : Env} {hn : H → String} {P : Numerics.Profile}
  {host : HostSemantics H}

/-- The induction hypothesis, for code smaller than `n`, under `V`. -/
def IHV (V : Config H → Prop) (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), codeSize c.code < n → V c → Typed env hn c →
    SStep env (configV hn c) w → BwdUpTo hn P host c w

/-- The redex of a typed split is typed. -/
theorem typed_mid (T : TypingFacts env hn) {s : Store H} {f : Frame} {A I R : List Admin}
    (hc : Typed env hn ⟨s, f, A ++ I ++ R⟩) : Typed env hn ⟨s, f, I⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  have h₁ : TypedV env instrsT (.list (adminsToV A ++ adminsToV I ++ adminsToV R)) := by
    simpa only [adminsToV_append] using hcode
  have h₂ := ((T.append _ _).1 ((T.append _ _).1 h₁).1).2
  exact (T.config _).2 ⟨hst, h₂⟩

/-- The inner configuration of a typed frame is typed. -/
theorem typed_frame (T : TypingFacts env hn) {s : Store H} {f fi : Frame} {k : Nat}
    {body : List Admin} (hc : Typed env hn ⟨s, f, [.frame k fi body]⟩) :
    Typed env hn ⟨s, fi, body⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  have hfr := T.frame k fi body hcode
  have hs := ((T.state s f).1 hst).1
  exact (T.config _).2 ⟨(T.state s fi).2 ⟨hs, hfr.2.1⟩, hfr.2.2⟩

/-- `ctxt-instrs` backwards, under `V`. -/
theorem bwdV_ctxtInstrs (CV : CtxClosed V) (D : StructDecode env) (T : TypingFacts env hn)
    {n : Nat} (ih : IHV V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtInstrsInv env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, h₂, hs⟩ := hinv
  have e₁ : z = stateV hn s f ∧ vs ++ is ++ rest = adminsToV code := configV_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := adminsToV_split3 e₁.2.symm
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := D.vals ρ A hρ (hA ▸ hvs)
  have hneA' : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have hneA : vs₀ ≠ [] ∨ R ≠ [] := hneA'.imp (fun h he => h (by rw [hv₀, he]; rfl)) id
  have hT : Typed env hn ⟨s, f, I⟩ := typed_mid T (hcode ▸ hc)
  have hV : V ⟨s, f, I⟩ := CV.mid s f A I R (hcode ▸ hv)
  have hsz : codeSize I < n := by
    have h₁ : codeSize I < codeSize (A ++ I ++ R) := Bwd.codeSize_mid hneA'
    have h₂ : codeSize (A ++ I ++ R) < n + 1 := hcode ▸ hlt
    omega
  have e₂ : cfgV z is = configV hn ⟨s, f, I⟩ := by rw [configV_eq, e₁.1, hI]
  have hs' : SStep env (configV hn ⟨s, f, I⟩) (cfgV z' is') := e₂ ▸ hs
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
theorem bwdV_ctxtLabel (CV : CtxClosed V) (D : StructDecode env) (T : TypingFacts env hn)
    {n : Nat} (ih : IHV V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cont is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is])] ∧
      w = cfgV z' [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
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
theorem bwdV_ctxtHandler (CV : CtxClosed V) (D : StructDecode env) (T : TypingFacts env hn)
    {n : Nat} (ih : IHV V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cs is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is])] ∧
      w = cfgV z' [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
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
theorem bwdV_ctxtFrame (CV : CtxClosed V) (D : StructDecode env) (T : TypingFacts env hn)
    {n : Nat} (ih : IHV V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtFrameInv env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := D.frame a _ ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, fi, body⟩ := typed_frame T hc
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

/-- `Step/pure` backwards, under `V`. -/
theorem bwdV_pure (Bk : BackwardUpToV V env hn P host)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    {s : Store H} {f : Frame} {code : List Admin} {w : Value} (hv : V ⟨s, f, code⟩)
    (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z is js, configV hn ⟨s, f, code⟩ = cfgV z is ∧ w = cfgV z js ∧ SPure env is js) :
    BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hP
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_pure" i (.tuple [.list (adminsToV code), .list js]) := e₁.2 ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.pure i s f code (.list js) hv hc hf'
  refine ⟨⟨s, f, is'⟩, ⟨s, f, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- `Step/read` backwards, under `V`. -/
theorem bwdV_read (Bk : BackwardUpToV V env hn P host)
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    {c : Config H} {w : Value} (hv : V c) (hc : Typed env hn c)
    (hinv : ∃ z is js, configV hn c = cfgV z is ∧ w = cfgV z js ∧ SRead env (cfgV z is) js) :
    BwdUpTo hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hR
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_read" i (.tuple [configV hn c, .list js]) := h₁ ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.read i c (.list js) hv hc hf'
  refine ⟨⟨c.store, c.frame, is'⟩, ⟨c.store, c.frame, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- One step of the recursion, under `V`. -/
theorem bwdV_dispatch (CV : CtxClosed V) (Bk : BackwardUpToV V env hn P host)
    (D : StructDecode env) (T : TypingFacts env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) {n : Nat}
    (ih : IHV V env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩) (hc : Typed env hn ⟨s, f, code⟩)
    (hs : SStep env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt R.pure
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact bwdV_pure Bk hP hv hc (Bwd.inv_pure R.pure hf)
  | 1, hf => exact bwdV_read Bk hR hv hc (Bwd.inv_read R.read hf)
  | 2, hf => exact bwdV_ctxtInstrs CV D T ih hlt hv hc (Bwd.inv_ctxtInstrs R.ctxtInstrs hf)
  | 3, hf => exact bwdV_ctxtLabel CV D T ih hlt hv hc (Bwd.inv_ctxtLabel R.ctxtLabel hf)
  | 4, hf => exact bwdV_ctxtHandler CV D T ih hlt hv hc (Bwd.inv_ctxtHandler R.ctxtHandler hf)
  | 5, hf => exact bwdV_ctxtFrame CV D T ih hlt hv hc (Bwd.inv_ctxtFrame R.ctxtFrame hf)
  | k + 6, hf => exact Bk.step (k + 6) (by omega) _ w hv hc hf

/-- The recursion on the size of the code, under `V`. -/
theorem bwdV_all (CV : CtxClosed V) (Bk : BackwardUpToV V env hn P host)
    (D : StructDecode env) (T : TypingFacts env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) :
    ∀ n, IHV V env hn P host n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨_, _, _⟩ _ hlt hv hc hs =>
      bwdV_dispatch CV Bk D T R hP hR (bwdV_all CV Bk D T R hP hR n) hlt hv hc hs

end Ctxt

/-- **The backward simulation under a context-closed predicate `V`** (SpecTec → Core, up to
`ConfigEq`): `Bwd.backward_upTo` with every per-rule obligation, and the source configuration,
restricted to `V`. -/
theorem backward_upToV {V : Config H → Prop} {env : Env} {hn : H → String}
    {P : Numerics.Profile} {host : HostSemantics H} (CV : CtxClosed V)
    (Bk : BackwardUpToV V env hn P host) (D : StructDecode env) (T : TypingFacts env hn)
    (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    (c : Config H) (w : Value) (hv : V c) (hc : Typed env hn c)
    (hs : SStep env (configV hn c) w) :
    ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  bwdV_all CV Bk D T R hP hR (codeSize c.code + 1) c w (Nat.lt_succ_self _) hv hc hs

/-- `Bwd.BackwardUpTo` is `BackwardUpToV` at any `V`. -/
theorem backwardUpToV_of {V : Config H → Prop} {env : Env} {hn : H → String}
    {P : Numerics.Profile} {host : HostSemantics H} (Bk : Bwd.BackwardUpTo env hn P host) :
    BackwardUpToV V env hn P host where
  pure i s f is w _ hc hf := Bk.pure i s f is w hc hf
  read i c w _ hc hf := Bk.read i c w hc hf
  step i h6 c w _ hc hf := Bk.step i h6 c w hc hf

end Silmaril.Wasm.SpecTec.Sim.Round4Read
