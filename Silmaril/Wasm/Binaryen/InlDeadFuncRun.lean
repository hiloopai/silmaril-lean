module

public import Silmaril.Wasm.Binaryen.InlDeadFuncSim
public import Silmaril.Wasm.Binaryen.InlAssemble
public import Silmaril.Wasm.Binaryen.InlDeadFuncHost

@[expose] public section

/-! # Appending a dead function: runs and sessions

Typed related configurations run in lockstep: a host-free step is simulated (`sim`), and a
diverging host call of the left side is a diverging host call of the right side
(`hostdiv_right`: the right store is valid, so a code-respecting typed host can only
diverge there too, `host_never_returns`).
The runs therefore correspond (`df_runs_corr`), using the determinism of classified runs of
the right side and the safety of the left side, and so do sessions (`df_session₁`,
`df_session₂`) and module observations (`df_obs_corr`), as long as every exported function
takes numeric parameters, so that the arguments of an invocation are typed in both stores
alike (`SessInv`).
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-! ## Callout contexts -/

theorem ctx_transport {X : List Admin} (hX : ∀ x ∈ X, isFlat x = true) :
    ∀ (E : Ctx) {ys : List Admin}, CRel (E.fill X) ys → ∃ E' : Ctx, ys = E'.fill X
  | .top pre rest, ys, h => by
    simp only [Ctx.fill] at h
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append h (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact flat_vals pre x hx
      · exact hX x hx)
    exact ⟨.top pre rest', rfl⟩
  | .label pre n cont E rest, ys, h => by
    simp only [Ctx.fill] at h
    obtain ⟨y₁, y₃, rfl, h₁, -⟩ := CRel.split h
    obtain ⟨y₂, rfl, h₂⟩ := CRel.flat_append h₁ (flat_vals pre)
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv h₂
    obtain ⟨E', rfl⟩ := ctx_transport hX E hb
    exact ⟨.label pre n cont E' y₃, rfl⟩
  | .handler pre n cs E rest, ys, h => by
    simp only [Ctx.fill] at h
    obtain ⟨y₁, y₃, rfl, h₁, -⟩ := CRel.split h
    obtain ⟨y₂, rfl, h₂⟩ := CRel.flat_append h₁ (flat_vals pre)
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv h₂
    obtain ⟨E', rfl⟩ := ctx_transport hX E hb
    exact ⟨.handler pre n cs E' y₃, rfl⟩
  | .frame pre n f E rest, ys, h => by
    simp only [Ctx.fill] at h
    obtain ⟨y₁, y₃, rfl, h₁, -⟩ := CRel.split h
    obtain ⟨y₂, rfl, h₂⟩ := CRel.flat_append h₁ (flat_vals pre)
    obtain ⟨f', b', rfl, -, hb⟩ := CRel.frame_inv h₂
    obtain ⟨E', rfl⟩ := ctx_transport hX E hb
    exact ⟨.frame pre n f' E' y₃, rfl⟩

/-- The arguments of a host call stay typed in a related store. -/
theorem argsOk_fl {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {hh : H}
    {args : List Val} (h : ArgsOk s hh args) : ArgsOk (withFuncs s X) hh args := by
  obtain ⟨fi, hfi, hc, ps, rs, he, hvs⟩ := h
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hfi
  obtain ⟨fi', h1, h2⟩ := hX.get hi
  exact ⟨fi', List.mem_of_getElem? h1, by rw [h2.code]; exact hc, ps, rs,
    by rw [h2.type]; exact he, hvs.imp fun _ _ h => valOk_fl hX h⟩

/-- **A diverging host call of the left side is one of the right side.** -/
theorem hostdiv_right {P : Numerics.Profile} {host : HostSemantics H} (hR : HostRespectsCode host)
    (hok : HostOk host) {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X)
    {code code' : List Admin} (hc : CRel code code') {E : Ctx} {a : Nat} {hh : H}
    {args : List Val} (hd : decompose? s code = some (E, a, hh, args))
    (hargs : ArgsOk s hh args) (ht : StoreOk (withFuncs s X)) (g : Frame) :
    Step P host ⟨withFuncs s X, g, code'⟩ ⟨withFuncs s X, g, code'⟩ := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, rfl⟩ := decompose?_sound hd
  obtain ⟨E', rfl⟩ := ctx_transport (by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact flat_vals args x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact isFlat_of_isCallRef hyy) E hc
  obtain ⟨fi', h1, h2⟩ := hX.get hfi
  have hargs' := argsOk_fl hX hargs
  obtain ⟨fj, hfj, hcj, ps', rs', hej, hvs⟩ := hargs'
  obtain ⟨⟨out, hout⟩, -⟩ := hok _ fj hh args ps' rs' ht hfj hcj hej hvs
  have hdiv : host hh (withFuncs s X) args .diverged := by
    cases out with
    | diverged => exact hout
    | returned s' r =>
      exact (host_never_returns hR hok ht (argsOk_fl hX hargs) hout).elim
  exact Ctx.step_fill E' (fun g => .callRefHostDiv hyy h1 (by rw [h2.type]; exact he) hlen
    (by rw [h2.code]; exact hcode) hdiv) g

/-! ## Runs -/

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

theorem rel_store {c c' : Config H} (h : Rel c c') :
    ∃ X, c'.store = withFuncs c.store X ∧ FL c.store.funcs X := h.1

/-- **Left runs are simulated.** -/
theorem df_run_sim {host : HostSemantics H} (hok : HostOk host) {c c' : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) {x : Config H} (h : Steps PD host c x)
    (hcl : ∀ y, Steps PD host c y → Classif PD host y) (hrel : Rel c c') :
    ∃ x', Steps PD host c' x' ∧ Rel x x' := by
  induction h with
  | refl => exact ⟨c', .refl, hrel⟩
  | @tail y y₁ hy hst ih =>
    obtain ⟨y', hy', hR⟩ := ih
    rcases hcl y hy y₁ hst with hn | ⟨rfl, -⟩
    · obtain ⟨y₁', hs', hR'⟩ := sim hn (refsIn_of_configOk (Steps.safe hok hc hy).1) hR
      exact ⟨y₁', hy'.tail (Step.of_noHost host hs'), hR'⟩
    · exact ⟨y', hy', hR⟩

/-- **Left divergence is simulated.** -/
theorem df_div_sim {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts) (hc' : ConfigOk c' ts')
    (hcl : ∀ y, Steps PD host c y → Classif PD host y)
    (hrel : Rel c c') (hdiv : Diverges PD host c) : Diverges PD host c' := by
  refine InfiniteTrace.coinduct
    (fun y' => ∃ y, Steps PD host c y ∧ Diverges PD host y ∧ Steps PD host c' y' ∧ Rel y y')
    ?_ ⟨c, .refl, hdiv, .refl, hrel⟩
  rintro y' ⟨y, hy, hdy, hy', hRel⟩
  obtain ⟨y₁, hst, hdy₁⟩ := InfiniteTrace.unfold hdy
  rcases hcl y hy y₁ hst with hn | ⟨-, E, a, hh, args, hd, -⟩
  · obtain ⟨y₁', hs', hR'⟩ := sim hn (refsIn_of_configOk (Steps.safe hok hc hy).1) hRel
    exact ⟨y₁', Step.of_noHost host hs', y₁, hy.tail hst, hdy₁, hy'.tail (Step.of_noHost host hs'),
      hR'⟩
  · obtain ⟨ys, yf, ycode⟩ := y
    obtain ⟨ts', tf, tcode⟩ := y'
    obtain ⟨X, l, code', heq, hX, hcr⟩ := rel_inv hRel
    simp only [Config.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hyok := (Steps.safe hok hc hy).1
    have hargs := argsOk_of_redex (P := PD) hyok hd
    have ht := ConfigOk.storeOk (Steps.safe hok hc' hy').1
    have hst' := hostdiv_right (P := PD) hR hok hX hcr hd hargs ht (fext yf l)
    exact ⟨_, hst', ⟨ys, yf, ycode⟩, hy, hdy, hy'.tail hst', rel_mk hX hcr⟩

/-- **Runs correspond.** -/
theorem df_runs_corr {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts) (hc' : ConfigOk c' ts')
    (hrel : Rel c c') :
    (∀ x, Steps PD host c x → x.Terminal → ∃ x', Steps PD host c' x' ∧ Rel x x') ∧
    (Diverges PD host c → Diverges PD host c') ∧
    (∀ x', Steps PD host c' x' → x'.Terminal → ∃ x, Steps PD host c x ∧ Rel x x') ∧
    (Diverges PD host c' → Diverges PD host c) := by
  have hclL := reach_classif_any (o := o) hR hok hc
  have hclR := reach_classif_any (o := o) hR hok hc'
  have R1 : ∀ x, Steps PD host c x → ∃ x', Steps PD host c' x' ∧ Rel x x' :=
    fun x hx => df_run_sim hok hc hx (fun y hy => (hclL y hy).1) hrel
  have R2 : Diverges PD host c → Diverges PD host c' :=
    df_div_sim hR hok hc hc' (fun y hy => (hclL y hy).1) hrel
  refine ⟨fun x hx _ => R1 x hx, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, ⟨r, hr⟩⟩ := hterm
      obtain ⟨x'', hx'', hR''⟩ := R1 x hx
      have hxT'' : x''.Terminal := ⟨r, hR''.result hr⟩
      have := nf_unique_classif hx'' hx' hxT'' hxT' (fun z hz => (hclR z hz).1)
      subst this
      exact ⟨x, hx, hR''⟩
    · exact absurd (R2 (div_of_safe (fun x hx => (Steps.safe hok hc hx).2)
        (fun x hx hxT => hterm ⟨x, hx, hxT⟩))) (term_not_div hx' hxT' (fun z hz => (hclR z hz).1))
  · intro hd'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, ⟨r, hr⟩⟩ := hterm
      obtain ⟨x'', hx'', hR''⟩ := R1 x hx
      exact absurd hd' (term_not_div hx'' ⟨r, hR''.result hr⟩ (fun z hz => (hclR z hz).1))
    · exact div_of_safe (fun x hx => (Steps.safe hok hc hx).2) (fun x hx hxT => hterm ⟨x, hx, hxT⟩)

end det

end Silmaril.Wasm.Binaryen.InlDF
