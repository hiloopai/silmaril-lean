module

public import Silmaril.Wasm.Binaryen.InlDeadFuncRun

@[expose] public section

/-! # Appending a dead function: sessions and module observations

An invocation of an exported function runs from related stores in related configurations
(`rel_invoke`). Its arguments are typed in both stores alike when the function takes numeric
parameters (`SessInv`); otherwise a reference to the extra function would be typed in the
extended store only. Sessions then correspond in both directions (`df_session₁`,
`df_session₂`), and so do the observations of corresponding instantiations (`df_obs_corr`).
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The function at `a`, if any, takes numeric parameters. -/
def NumParamsAt (fs : List (FuncInst H)) (a : Nat) : Prop :=
  ∀ fi, fs[a]? = some fi → ∀ ps rs, Expand fi.type (.func ps rs) →
    ∀ p ∈ ps.toList, ∃ t, p = .num t

/-- The exported functions of `mi` exist in `s` and take numeric parameters. -/
def SessInv (s : Store H) (mi : ModuleInst) : Prop :=
  ∀ x a, exportFunc? mi x = some a → a < s.funcs.length ∧ NumParamsAt s.funcs a

theorem SessInv.of_funcs {s s' : Store H} {mi : ModuleInst} (h : SessInv s mi)
    (hf : s'.funcs = s.funcs) : SessInv s' mi := by
  intro x a ha
  rw [hf]
  exact h x a ha

theorem exportFunc?_mext (mi : ModuleInst) (l : List Nat) (x : String) :
    exportFunc? (mext mi l) x = exportFunc? mi x := rfl

/-! ## Invocations -/

theorem invokeOk_fwd {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {a : Nat}
    {vs : List Val} (h : InvokeOk s a vs) : InvokeOk (withFuncs s X) a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  obtain ⟨fi', h1, h2⟩ := hX.get hfi
  exact ⟨fi', ps, rs, h1, by rw [h2.type]; exact he, hvs.imp fun _ _ h => valOk_fl hX h⟩

theorem valOk_num {s t : Store H} {v : Val} {nt : NumType} (h : ValOk s v (.num nt)) :
    ValOk t v (.num nt) := by
  cases h with
  | num v => exact .num v

theorem invokeOk_back {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {a : Nat}
    (ha : a < s.funcs.length) (hnp : NumParamsAt s.funcs a) {vs : List Val}
    (h : InvokeOk (withFuncs s X) a vs) : InvokeOk s a vs := by
  obtain ⟨fi', ps, rs, h1, he, hvs⟩ := h
  obtain ⟨fi'', h1', h2⟩ := hX.get (List.getElem?_eq_getElem ha)
  have h1x : X[a]? = some fi' := h1
  rw [h1x] at h1'
  cases h1'
  have he' : Expand (s.funcs[a]'ha).type (.func ps rs) := by rw [← h2.type]; exact he
  refine ⟨_, ps, rs, List.getElem?_eq_getElem ha, he', ?_⟩
  have hnum := hnp _ (List.getElem?_eq_getElem ha) ps rs he'
  clear he he' h2 h1 h1x
  revert hvs hnum
  generalize ps.toList = pl
  intro hvs hnum
  induction hvs with
  | nil => exact .nil
  | @cons v p vs' ps' hv _ ih =>
    obtain ⟨t, rfl⟩ := hnum p (by simp)
    exact .cons (valOk_num hv) (ih fun q hq => hnum q (by simp [hq]))

theorem rel_invoke {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {a : Nat}
    (ha : a < s.funcs.length) (vs : List Val) :
    Rel (invoke s a vs) (invoke (withFuncs s X) a vs) := by
  have ht : (withFuncs s X).funcs[a]?.map FuncInst.type = s.funcs[a]?.map FuncInst.type :=
    hX.type ha
  refine ⟨⟨X, rfl, hX⟩, ⟨[], by simp [invoke]⟩, ?_⟩
  simp only [invoke]
  rw [ht]
  exact CRel.refl _

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

theorem storeOk_of_steps {host : HostSemantics H} (hok : HostOk host) {c x : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) (h : Steps PD host c x) : StoreOk x.store :=
  ConfigOk.storeOk (Steps.safe hok hc h).1

/-- **Sessions of the extended module are sessions of the original one.** -/
theorem df_session₁ {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {mi mi' : ModuleInst} (hexp : ∀ x, exportFunc? mi' x = exportFunc? mi x) {t : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (h : Session PD host mi' t script bs) :
    ∀ {s : Store H} {X : List (FuncInst H)}, t = withFuncs s X → FL s.funcs X → StoreOk s →
      StoreOk t → SessInv s mi →
      Session PD host mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ _ _ => .nil
  | stop h =>
    intro s X ht hX _ _ _
    subst ht
    exact .stop fun a ha hok' => h a (by rw [hexp]; exact ha) (invokeOk_fwd hX hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s X ht hX hs ht' hinv
    subst ht
    rw [hexp] at ha
    obtain ⟨hlt, hnp⟩ := hinv x a ha
    have hokO := invokeOk_back hX hlt hnp hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht' hok'
    obtain ⟨-, -, R3, -⟩ := df_runs_corr hR hok hcO hcN (rel_invoke hX hlt vs)
    obtain ⟨y, hy, hrel⟩ := R3 c run ⟨r, hr⟩
    have hfs := (reach_classif_any (o := o) hR hok hcO y hy).2
    obtain ⟨X', hX'eq, hX'⟩ := hrel.1
    exact .done ha hokO hy (hrel.result' hr) (ih hX'eq hX' (storeOk_of_steps hok hcO hy)
      (storeOk_of_steps hok hcN run) (hinv.of_funcs hfs))
  | @diverge t x vs rest a ha hok' hd =>
    intro s X ht hX hs ht' hinv
    subst ht
    rw [hexp] at ha
    obtain ⟨hlt, hnp⟩ := hinv x a ha
    have hokO := invokeOk_back hX hlt hnp hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht' hok'
    obtain ⟨-, -, -, R4⟩ := df_runs_corr hR hok hcO hcN (rel_invoke hX hlt vs)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the original module are sessions of the extended one.** -/
theorem df_session₂ {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {mi mi' : ModuleInst} (hexp : ∀ x, exportFunc? mi' x = exportFunc? mi x) {s : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (h : Session PD host mi s script bs) :
    ∀ {X : List (FuncInst H)}, FL s.funcs X → StoreOk s → StoreOk (withFuncs s X) →
      SessInv s mi →
      Session PD host mi' (withFuncs s X) script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | @stop s x vs rest h =>
    intro X hX _ _ hinv
    refine .stop fun a ha hok' => ?_
    rw [hexp] at ha
    obtain ⟨hlt, hnp⟩ := hinv x a ha
    exact h a ha (invokeOk_back hX hlt hnp hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro X hX hs ht' hinv
    obtain ⟨hlt, -⟩ := hinv x a ha
    have hokN := invokeOk_fwd hX hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht' hokN
    obtain ⟨R1, -, -, -⟩ := df_runs_corr hR hok hcO hcN (rel_invoke hX hlt vs)
    obtain ⟨y', hy', hrel⟩ := R1 c run ⟨r, hr⟩
    have hfs := (reach_classif_any (o := o) hR hok hcO c run).2
    obtain ⟨X', hX'eq, hX'⟩ := hrel.1
    have hy'ok := storeOk_of_steps hok hcN hy'
    rw [hX'eq] at hy'ok
    have := ih hX' (storeOk_of_steps hok hcO run) hy'ok (hinv.of_funcs hfs)
    rw [← hX'eq] at this
    exact .done (by rw [hexp]; exact ha) hokN hy' (hrel.result hr) this
  | @diverge s x vs rest a ha hok' hd =>
    intro X hX hs ht' hinv
    obtain ⟨hlt, -⟩ := hinv x a ha
    have hokN := invokeOk_fwd hX hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht' hokN
    obtain ⟨-, R2, -, -⟩ := df_runs_corr hR hok hcO hcN (rel_invoke hX hlt vs)
    exact .diverge (by rw [hexp]; exact ha) hokN (R2 hd)

/-- The observation of an instantiation run followed by a session. -/
abbrev Obs (host : HostSemantics H) (c : Config H) (script : List Call)
    (bs : List (Behaviour Val)) : Prop :=
  (∃ c₁ bs', Steps PD host c c₁ ∧ c₁.code = [] ∧
      Session PD host c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
    (∃ (c₁ : Config H) (r : Result), Steps PD host c c₁ ∧ c₁.code = r.toAdmin ∧
      r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
    (Diverges PD host c ∧ bs = [.diverges])

/-- **Observations of corresponding instantiations agree.** -/
theorem df_obs_corr {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {c c' : Config H} (hc : ConfigOk c []) (hc' : ConfigOk c' []) (hrel : Rel c c')
    (hinv : SessInv c.store c.frame.module) (script : List Call)
    (bs : List (Behaviour Val)) :
    Obs (o := o) host c script bs ↔ Obs (o := o) host c' script bs := by
  obtain ⟨R1, R2, R3, R4⟩ := df_runs_corr hR hok hc hc' hrel
  have hclL := reach_classif_any (o := o) hR hok hc
  have hexp : ∀ x, exportFunc? c'.frame.module x = exportFunc? c.frame.module x := by
    obtain ⟨l, hl⟩ := hrel.2.1
    intro x
    rw [hl]
    rfl
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x', hx', hrel'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      obtain ⟨X, hXeq, hX⟩ := hrel'.1
      have hfs := (hclL c₁ h₁).2
      have hx'ok := storeOk_of_steps hok hc' hx'
      rw [hXeq] at hx'ok
      have hs := df_session₂ (o := o) hR hok hexp h₃ hX (storeOk_of_steps hok hc h₁) hx'ok
        (hinv.of_funcs hfs)
      rw [← hXeq] at hs
      exact .inl ⟨x', bs', hx', hrel'.result (r := .values []) h₂, hs, rfl⟩
    · obtain ⟨x', hx', hrel'⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x', r, hx', hrel'.result h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x, hx, hrel'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      obtain ⟨X, hXeq, hX⟩ := hrel'.1
      have hfs := (hclL x hx).2
      have hc₁ok := storeOk_of_steps hok hc' h₁
      have hs := df_session₁ (o := o) hR hok hexp h₃ hXeq hX (storeOk_of_steps hok hc hx) hc₁ok
        (hinv.of_funcs hfs)
      exact .inl ⟨x, bs', hx, hrel'.result' (r := .values []) h₂, hs, rfl⟩
    · obtain ⟨x, hx, hrel'⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, hrel'.result' h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)

end det

end Silmaril.Wasm.Binaryen.InlDF
