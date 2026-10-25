module

public import Silmaril.Wasm.Binaryen.InlInst
public import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-! # The inlining simulation: observations

Typed runs of both modules are classified (`reach_classif`), so the simulation of the
original module by the inlined one (`run_sim`, `div_sim`) and the determinism of the
inlined one (`nf_unique_classif`, `term_not_div`), together with the safety of the
original one, relate their terminating results and divergences in both directions
(`runs_corr`). Sessions and module observations follow (`session_corr`, `obs_corr`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The facts the simulation needs about one instantiation. -/
structure Good (p : Prm) : Prop where
  ok : PrmOk p
  callee : Nonempty (PrmC p)
  fx : p.mi.funcs[p.fx.toNat]? = some p.af

theorem noHost_funcs {c c' : Config H} (h : Step P Det.noHost c c') :
    c'.store.funcs = c.store.funcs :=
  (SingleThreaded.Step.framesLocal h).1

/-- **Typed runs from a store with a Wasm function are classified.** -/
theorem reach_classif {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) {aw : Nat} {fw : FuncInst H}
    {cw : Func} (hfw : c.store.funcs[aw]? = some fw) (hcw : fw.code = .wasm cw) :
    ∀ x, Steps P host c x → Classif P host x ∧ x.store.funcs = c.store.funcs := by
  intro x hx
  induction hx with
  | refl => exact ⟨classif_of_ok hR hok hc hfw hcw, rfl⟩
  | @tail y z hy hst ih =>
    obtain ⟨hcl, hfs⟩ := ih
    have hfz : z.store.funcs = c.store.funcs := by
      rcases hcl z hst with hn | ⟨rfl, -⟩
      · rw [noHost_funcs hn, hfs]
      · exact hfs
    have hz := (Steps.safe hok hc (hy.tail hst)).1
    exact ⟨classif_of_ok hR hok hz (by rw [hfz]; exact hfw) hcw, hfz⟩

/-- A never-stuck configuration from which no terminal configuration is reachable diverges. -/
theorem div_of_safe {host : HostSemantics H} {c : Config H}
    (hsafe : ∀ x, Steps P host c x → x.Terminal ∨ ∃ y, Step P host x y)
    (hno : ∀ x, Steps P host c x → ¬ x.Terminal) : Diverges P host c := by
  refine InfiniteTrace.coinduct (fun x => Steps P host c x) (fun x hx => ?_) .refl
  rcases hsafe x hx with ht | ⟨y, hy⟩
  · exact absurd ht (hno x hx)
  · exact ⟨y, hy, hx.tail hy⟩

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Runs correspond.** -/
theorem runs_corr (hG : Good p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts)
    (hc' : ConfigOk c' ts') (hMR : MR p .gen c c') (hSR : SR p c.store c'.store) :
    (∀ x, Steps PD host c x → x.Terminal →
      ∃ x', Steps PD host c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges PD host c → Diverges PD host c') ∧
    (∀ x', Steps PD host c' x' → x'.Terminal →
      ∃ x, Steps PD host c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges PD host c' → Diverges PD host c) := by
  obtain ⟨hpok, ⟨hC⟩, hfx⟩ := hG
  have hclO : ∀ x, Steps PD host c x → Classif PD host x :=
    fun x hx => (reach_classif hR hok hc hSR.hg rfl x hx).1
  have hgN : c'.store.funcs[p.ag]? = some (gN p) := by
    rw [hSR.get]; simp
  have hclN : ∀ x, Steps PD host c' x → Classif PD host x :=
    fun x hx => (reach_classif hR hok hc' hgN rfl x hx).1
  have R1 : ∀ x, Steps PD host c x → x.Terminal →
      ∃ x', Steps PD host c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store := by
    intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hpok hfx hC hx hclO hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  have R2 : Diverges PD host c → Diverges PD host c' := fun hd =>
    div_sim hpok hfx hC hR hd hclO hMR hSR
  refine ⟨R1, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, hSR''⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      have := nf_unique_classif hx'' hx' hxT'' hxT' hclN
      subst this
      exact ⟨x, hx, hcode.symm, hSR''⟩
    · exact absurd (R2 (div_of_safe (fun x hx => (Steps.safe hok hc hx).2)
        (fun x hx hxT => hterm ⟨x, hx, hxT⟩))) (term_not_div hx' hxT' hclN)
  · intro hd'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, -⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      exact absurd hd' (term_not_div hx'' hxT'' hclN)
    · exact div_of_safe (fun x hx => (Steps.safe hok hc hx).2) (fun x hx hxT => hterm ⟨x, hx, hxT⟩)

end det

/-! ## Invocations and sessions -/

theorem funcType_eq {s t : Store H} (hSR : SR p s t) (a : Nat) :
    (t.funcs[a]?.map FuncInst.type) = (s.funcs[a]?.map FuncInst.type) := by
  have := congrArg (fun l => l[a]?) hSR.sameTypes
  simp only [List.getElem?_map] at this
  rw [hSR.ht]
  exact this

theorem invoke_rel {s t : Store H} (hSR : SR p s t) (a : Nat) (vs : List Val) :
    MR p .gen (invoke s a vs) (invoke t a vs) := by
  refine ⟨rfl, ?_⟩
  simp only [invoke]
  rw [funcType_eq hSR a]
  exact LN.refl p _

theorem invokeOk_of {s t : Store H} (hSR : SR p s t) {a : Nat} {vs : List Val}
    (h : InvokeOk s a vs) : InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  obtain ⟨fi', hfi', ht⟩ := hSR.sameTypes.get hfi
  refine ⟨fi', ps, rs, by rw [hSR.ht]; exact hfi', ht ▸ he, ?_⟩
  rw [hSR.ht]
  exact hvs.imp fun _ _ h => valOk_withFuncs hSR.sameTypes h

theorem invokeOk_of' {s t : Store H} (hSR : SR p s t) {a : Nat} {vs : List Val}
    (h : InvokeOk t a vs) : InvokeOk s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := h
  rw [hSR.ht] at hfi hvs
  obtain ⟨fi', hfi', ht⟩ := hSR.sameTypes.symm.get hfi
  refine ⟨fi', ps, rs, hfi', ht ▸ he, ?_⟩
  have e : s = withFuncs (withFuncs s (newFuncs p s.funcs)) s.funcs := rfl
  rw [e]
  exact hvs.imp fun _ _ h => valOk_withFuncs (s := withFuncs s (newFuncs p s.funcs))
    hSR.sameTypes.symm h

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

theorem terminal_of_code {x : Config H} {r : Result} (h : x.code = r.toAdmin) : x.Terminal :=
  ⟨r, h⟩

/-- **Sessions of the inlined module are sessions of the original one.** -/
theorem session_corr₁ (hG : Good p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD host mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → SR p s t → Session PD host mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr hG hR hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Steps.safe hok hcO hx').1)
      (ConfigOk.storeOk (Steps.safe hok hcN run).1) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr hG hR hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the original module are sessions of the inlined one.** -/
theorem session_corr₂ (hG : Good p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session PD host mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SR p s t → Session PD host mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr hG hR hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Steps.safe hok hcO run).1)
      (ConfigOk.storeOk (Steps.safe hok hcN hx').1) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr hG hR hok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

/-- A correspondence between the instantiations of the original module `M` and the inlined
module `M'`. -/
def InstCorr (host : HostSemantics H) (M M' : Module) : Prop :=
  (∀ s xas c, StoreOk s → Instantiate PD host s M xas c →
    ∃ c' p, Good p ∧ Instantiate PD host s M' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store) ∧
  (∀ s xas c', StoreOk s → Instantiate PD host s M' xas c' →
    ∃ c p, Good p ∧ Instantiate PD host s M xas c ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store)

theorem obs_corr {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate PD host s M xas c) (hi' : Instantiate PD host s M' xas c')
    (hG : Good p) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : SR p c.store c'.store) (script : List Call) :
    (∀ bs, ((∃ c₁ bs', Steps PD host c' c₁ ∧ c₁.code = [] ∧
        Session PD host c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD host c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD host c' ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD host c c₁ ∧ c₁.code = [] ∧
        Session PD host c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD host c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD host c ∧ bs = [.diverges]))) ∧
    (∀ bs, ((∃ c₁ bs', Steps PD host c c₁ ∧ c₁.code = [] ∧
        Session PD host c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD host c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD host c ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps PD host c' c₁ ∧ c₁.code = [] ∧
        Session PD host c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps PD host c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges PD host c' ∧ bs = [.diverges]))) := by
  have hc := Instantiate.ok hok hs hi
  have hc' := Instantiate.ok hok hs hi'
  have hMR : MR p .gen c c' := ⟨hfr, by rw [hcode]; exact LN.refl p _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr hG hR hok hc hc' hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁ hG hR hok h₃ (ConfigOk.storeOk (Steps.safe hok hc hx).1)
        (ConfigOk.storeOk (Steps.safe hok hc' h₁).1) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂ hG hR hok h₃ (ConfigOk.storeOk (Steps.safe hok hc h₁).1)
        (ConfigOk.storeOk (Steps.safe hok hc' hx).1) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {M M' : Module} (h : InstCorr (o := o) host M M') :
    ExportEquiv (· = ·) PD host M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hG, hi, hfr, hcode, hSR⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr hR hok hs hi hi' hG hfr hcode hSR script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hG, hi', hfr, hcode, hSR⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr hR hok hs hi hi' hG hfr hcode hSR script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end det

end Silmaril.Wasm.Binaryen.InlR
