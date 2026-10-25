module

public import Silmaril.Wasm.Binaryen.InlUnwrapSim

@[expose] public section

/-! # Unwrapping a branch-free block: runs, sessions and observations

Diverging host calls of the left side are diverging host calls of the right side
(`hostdiv_step`). With the one-step simulation (`Binaryen/InlUnwrapSim.lean`), terminating
and diverging left runs are simulated (`run_sim`, `div_sim`); determinism of the right side
and safety of the left side give the converse (`runs_corr`). Sessions and module
observations follow, as for inlining (`Binaryen/InlAssemble.lean`).
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm}

/-! ## Diverging host calls -/

/-- The nesting depth of an evaluation context. -/
def ctxDepth : Ctx → Nat
  | .top .. => 0
  | .label _ _ _ E _ | .handler _ _ _ E _ | .frame _ _ _ E _ => ctxDepth E + 1

/-- A filled context whose code is `C ++ Xa`, with `C` not done, fills `C` alone. -/
theorem fill_split {W : List Val} {y : Admin} (hy : y.val? = none) {C Xa : List Admin} :
    ∀ E : Ctx, E.fill (vals W ++ [y]) = C ++ Xa → C.all Admin.isVal = false →
      ∃ E₀ : Ctx, E₀.fill (vals W ++ [y]) = C ∧ ctxDepth E₀ = ctxDepth E
  | .top pre rest, h, hv => by
    have h' : C ++ Xa = vals (pre ++ W) ++ y :: rest := by rw [← h]; simp [Ctx.fill]
    obtain ⟨R₁, rfl, rfl⟩ := split_nonval h' hy hv
    exact ⟨.top pre R₁, by simp [Ctx.fill], rfl⟩
  | .label pre n cont E rest, h, hv => by
    have h' : C ++ Xa = vals pre ++ Admin.label n cont (E.fill (vals W ++ [y])) :: rest := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨R₁, rfl, rfl⟩ := split_nonval h' rfl hv
    exact ⟨.label pre n cont E R₁, by simp [Ctx.fill], rfl⟩
  | .handler pre n cs E rest, h, hv => by
    have h' : C ++ Xa = vals pre ++ Admin.handler n cs (E.fill (vals W ++ [y])) :: rest := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨R₁, rfl, rfl⟩ := split_nonval h' rfl hv
    exact ⟨.handler pre n cs E R₁, by simp [Ctx.fill], rfl⟩
  | .frame pre n F E rest, h, hv => by
    have h' : C ++ Xa = vals pre ++ Admin.frame n F (E.fill (vals W ++ [y])) :: rest := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨R₁, rfl, rfl⟩ := split_nonval h' rfl hv
    exact ⟨.frame pre n F E R₁, by simp [Ctx.fill], rfl⟩

/-- The first non-value of a filled context is the hole's or a context's. -/
theorem fill_first {W : List Val} {y : Admin} (hy : y.val? = none) :
    ∀ (E : Ctx) {V : List Val} {e : Admin} {R : List Admin}, e.val? = none →
      E.fill (vals W ++ [y]) = vals V ++ e :: R →
      e = y ∨ (∃ n c b, e = .label n c b) ∨ (∃ n cs b, e = .handler n cs b) ∨
        ∃ n F b, e = .frame n F b
  | .top pre rest, V, e, R, he, h => by
    have h' : vals (pre ++ W) ++ y :: rest = vals V ++ e :: R := by rw [← h]; simp [Ctx.fill]
    obtain ⟨-, rfl, -⟩ := Det.vals_append_cons_inj h' hy he
    exact .inl rfl
  | .label pre n cont E rest, V, e, R, he, h => by
    have h' : vals pre ++ Admin.label n cont (E.fill (vals W ++ [y])) :: rest = vals V ++ e :: R := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨-, rfl, -⟩ := Det.vals_append_cons_inj h' rfl he
    exact .inr (.inl ⟨_, _, _, rfl⟩)
  | .handler pre n cs E rest, V, e, R, he, h => by
    have h' : vals pre ++ Admin.handler n cs (E.fill (vals W ++ [y])) :: rest = vals V ++ e :: R := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨-, rfl, -⟩ := Det.vals_append_cons_inj h' rfl he
    exact .inr (.inr (.inl ⟨_, _, _, rfl⟩))
  | .frame pre n F E rest, V, e, R, he, h => by
    have h' : vals pre ++ Admin.frame n F (E.fill (vals W ++ [y])) :: rest = vals V ++ e :: R := by
      rw [← h]; simp [Ctx.fill]
    obtain ⟨-, rfl, -⟩ := Det.vals_append_cons_inj h' rfl he
    exact .inr (.inr (.inr ⟨_, _, _, rfl⟩))

theorem callout_transport {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) :
    ∀ (E : Ctx) {ns : List Admin}, UL p.R (E.fill (vals args ++ [.ref (.func a), yy])) ns →
      ∃ E' : Ctx, ns = E'.fill (vals args ++ [.ref (.func a), yy])
  | .top pre rest, ns, h => by
    obtain ⟨hL, hH, hF, -, -, -⟩ := callRef_flat hyy
    have e : (Ctx.top pre rest).fill (vals args ++ [.ref (.func a), yy]) =
        vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest := by
      simp [Ctx.fill, vals, Val.toAdmin]
    rw [e] at h
    obtain ⟨rest', rfl, -⟩ := UL.flat_inv hL hH hF (fun i hi => by
      subst hi; cases i <;> simp_all [Admin.IsCallRef, structuredInstr]) h
    exact ⟨.top pre rest', by simp [Ctx.fill, vals, Val.toAdmin]⟩
  | .label pre n cont E rest, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := UL.vals_append_inv h
    have hyv : yy.val? = none := Det.IsCallRef.val_none hyy
    have hX : vals args ++ [Admin.ref (.func a), yy] = vals (args ++ [.ref (.func a)]) ++ [yy] := by
      simp [vals, Val.toAdmin]
    generalize hEf : E.fill (vals args ++ [.ref (.func a), yy]) = body at hB
    cases hB with
    | @cons _ _ _ ns' hl hr =>
      cases hl with
      | @label _ _ c' _ _ hc hb =>
        subst hEf
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.label pre n c' E' ns', by simp [Ctx.fill]⟩
    | @run _ _ _ _ ns' hX' hX hr =>
      subst hEf
      obtain ⟨E', rfl⟩ := callout_transport hyy E hX'
      exact ⟨E'.wrap pre ns', by rw [Ctx.fill_wrap]; simp⟩
    | @foldLabel _ C C' Xa _ ns' hC hXe hv hr =>
      rw [hX] at hEf
      obtain ⟨E₀, hE₀, hd⟩ := fill_split hyv E hEf hv
      rw [← hX] at hE₀
      subst hE₀
      obtain ⟨E', rfl⟩ := callout_transport hyy E₀ hC
      exact ⟨.label pre n [] E' (Xa ++ ns'), by simp [Ctx.fill]⟩
    | @foldExit _ ws K J _ ns' hK hr =>
      rw [hX] at hEf
      obtain ⟨V, e, R, he, hVe⟩ := exists_first_nonval (bubble_not_all (ws := ws) (J := J) hK)
      rcases bubble_head hK he hVe with ⟨rfl, -⟩ | ⟨b, rfl, -⟩ <;>
        rcases fill_first hyv E rfl (hEf.trans hVe) with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ |
          ⟨_, _, _, h⟩ <;>
        first
          | (subst h; exact absurd hyy (by simp [Admin.IsCallRef]))
          | cases h
  | .handler pre n cs E rest, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := UL.vals_append_inv h
    cases hB with
    | @cons _ _ _ ns' hl hr =>
      cases hl with
      | handler hb =>
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.handler pre n cs E' ns', by simp [Ctx.fill]⟩
  | .frame pre n F E rest, ns, h => by
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨nB, rfl, hB⟩ := UL.vals_append_inv h
    cases hB with
    | @cons _ _ _ ns' hl hr =>
      cases hl with
      | frame hb =>
        obtain ⟨E', rfl⟩ := callout_transport hyy E hb
        exact ⟨.frame pre n F E' ns', by simp [Ctx.fill]⟩
termination_by E => ctxDepth E
decreasing_by all_goals simp [ctxDepth, *]

/-- **A diverging host call of the left side is a diverging host call of the right side.** -/
theorem hostdiv_step {P : Numerics.Profile} {host : HostSemantics H} (hR : HostRespectsCode host)
    {s t : Store H} (hSR : SR p s t) {code ns : List Admin} (hcr : UL p.R code ns) {E : Ctx}
    {a : Nat} {hh : H} {args : List Val} (hd : decompose? s code = some (E, a, hh, args))
    (hdiv : host hh s args .diverged) (fn : Frame) :
    Step P host ⟨t, fn, ns⟩ ⟨t, fn, ns⟩ := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, rfl⟩ := decompose?_sound hd
  have hag : a ≠ p.ag := by
    rintro rfl; rw [hSR.hg] at hfi; cases hfi; simp [gL] at hcode
  have hfi' : t.funcs[a]? = some fi := by
    rw [hSR.get a]; simp only [hag, ↓reduceIte]; exact hfi
  obtain ⟨E', rfl⟩ := callout_transport hyy E hcr
  have hdiv' : host hh t args .diverged := by
    refine hR hh s t args _ ⟨?_, ?_⟩ hdiv
    · rw [hSR.ht]; exact hSR.sameTypes.symm
    · rw [hSR.ht]; rfl
  exact Ctx.step_fill E' (fun g => .callRefHostDiv hyy hfi' he hlen hcode hdiv') fn

/-! ## Runs -/

section runs

variable {P : Numerics.Profile}

/-- **Terminating left runs are simulated.** -/
theorem run_sim (hok : PrmOk p) {host : HostSemantics H}
    {c c' : Config H} (h : Steps P host c c')
    (hcl : ∀ x, Steps P host c x → Classif P host x) {d : Config H} (hMR : MR p c d)
    (hSR : SR p c.store d.store) :
    ∃ d', Steps P host d d' ∧ MR p c' d' ∧ SR p c'.store d'.store := by
  induction h with
  | refl => exact ⟨d, .refl, hMR, hSR⟩
  | @tail x x' hx hstep ih =>
    obtain ⟨dx, hd, hMRx, hSRx⟩ := ih
    rcases hcl x hx x' hstep with hn | ⟨hxx, -⟩
    · obtain ⟨n', hMR', hSR', hprog⟩ := sim hok (sizeOf x.code + 1) x x' dx (by omega) hn hMRx hSRx
      rcases hprog with hp | ⟨hn', -⟩
      · exact ⟨n', hd.trans (steps_of_tg hp host), hMR', hSR'⟩
      · rw [hn'] at hMR' hSR'
        exact ⟨dx, hd, hMR', hSR'⟩
    · rw [hxx]
      exact ⟨dx, hd, hMRx, hSRx⟩

/-- Terminal left configurations: the right configuration has the same code. -/
theorem terminal_code {c d : Config H} (hMR : MR p c d) {r : Result}
    (hr : c.code = r.toAdmin) : d.code = r.toAdmin := by
  have h := hMR.2
  rw [hr] at h
  exact UL.result_inv h

/-- One step of the right side for a diverging left side. -/
theorem div_step (hok : PrmOk p) {host : HostSemantics H} (hR : HostRespectsCode host)
    {c₀ : Config H} (hcl : ∀ x, Steps P host c₀ x → Classif P host x) :
    ∀ (w : Nat) (x z : Config H), aszs x.code = w → Steps P host c₀ x → Diverges P host x →
      MR p x z → SR p x.store z.store →
      ∃ z₁ x' z', Step P host z z₁ ∧ Steps P host c₀ x' ∧ Diverges P host x' ∧ MR p x' z' ∧
        SR p x'.store z'.store ∧ Steps P host z₁ z' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x z hw hx hdiv hMR hSR
  obtain ⟨x₁, hst, hdiv₁⟩ := InfiniteTrace.unfold hdiv
  have hx₁ : Steps P host c₀ x₁ := hx.tail hst
  rcases hcl x hx x₁ hst with hn | ⟨hxx, E, a, hh, args, hd, hdv⟩
  · obtain ⟨n', hMR', hSR', hprog⟩ := sim hok (sizeOf x.code + 1) x x₁ z (by omega) hn hMR hSR
    rcases hprog with hp | ⟨hn', hw'⟩
    · obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
      exact ⟨z₁, x₁, n', Step.of_noHost host h₁, hx₁, hdiv₁, hMR', hSR',
        h₂.lift id (fun _ _ h => Step.of_noHost host h)⟩
    · rw [hn'] at hMR' hSR'
      exact ih (aszs x₁.code) (by omega) x₁ z rfl hx₁ hdiv₁ hMR' hSR'
  · obtain ⟨zs, zf, zc⟩ := z
    have hstep : Step P host ⟨zs, zf, zc⟩ ⟨zs, zf, zc⟩ :=
      hostdiv_step hR hSR hMR.2 hd hdv zf
    exact ⟨_, x, _, hstep, hx, hdiv, hMR, hSR, .refl⟩

/-- **Diverging left runs are simulated.** -/
theorem div_sim (hok : PrmOk p) {host : HostSemantics H} (hR : HostRespectsCode host)
    {c : Config H} (hdiv : Diverges P host c) (hcl : ∀ x, Steps P host c x → Classif P host x)
    {d : Config H} (hMR : MR p c d) (hSR : SR p c.store d.store) : Diverges P host d := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P host c x ∧ Diverges P host x ∧ MR p x z ∧
      SR p x.store z.store ∧ Steps P host y z) ?_ ⟨c, d, .refl, hdiv, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hx, hdx, hMRx, hSRx, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨z₁, x', z', hs, hx', hdx', hMR', hSR', hz⟩ :=
      div_step hok hR hcl (aszs x.code) x y rfl hx hdx hMRx hSRx
    exact ⟨z₁, hs, x', z', hx', hdx', hMR', hSR', hz⟩
  · exact ⟨y₁, h₁, x, z, hx, hdx, hMRx, hSRx, h₂⟩

end runs

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Runs correspond.** -/
theorem runs_corr (hok : PrmOk p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hhok : HostOk host) {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts)
    (hc' : ConfigOk c' ts') (hMR : MR p c c') (hSR : SR p c.store c'.store) :
    (∀ x, Steps PD host c x → x.Terminal →
      ∃ x', Steps PD host c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges PD host c → Diverges PD host c') ∧
    (∀ x', Steps PD host c' x' → x'.Terminal →
      ∃ x, Steps PD host c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges PD host c' → Diverges PD host c) := by
  have hclO : ∀ x, Steps PD host c x → Classif PD host x :=
    fun x hx => (reach_classif hR hhok hc hSR.hg rfl x hx).1
  have hgN : c'.store.funcs[p.ag]? = some (gR p) := by
    rw [hSR.get]; simp
  have hclN : ∀ x, Steps PD host c' x → Classif PD host x :=
    fun x hx => (reach_classif hR hhok hc' hgN rfl x hx).1
  have R1 : ∀ x, Steps PD host c x → x.Terminal →
      ∃ x', Steps PD host c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store := by
    intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hok hx hclO hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  have R2 : Diverges PD host c → Diverges PD host c' := fun hd =>
    div_sim hok hR hd hclO hMR hSR
  refine ⟨R1, R2, ?_, ?_⟩
  · intro x' hx' hxT'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, hSR''⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      have := nf_unique_classif hx'' hx' hxT'' hxT' hclN
      subst this
      exact ⟨x, hx, hcode.symm, hSR''⟩
    · exact absurd (R2 (div_of_safe (fun x hx => (Steps.safe hhok hc hx).2)
        (fun x hx hxT => hterm ⟨x, hx, hxT⟩))) (term_not_div hx' hxT' hclN)
  · intro hd'
    by_cases hterm : ∃ x, Steps PD host c x ∧ x.Terminal
    · obtain ⟨x, hx, hxT⟩ := hterm
      obtain ⟨x'', hx'', hcode, -⟩ := R1 x hx hxT
      have hxT'' : x''.Terminal := by obtain ⟨r, hr⟩ := hxT; exact ⟨r, by rw [hcode, hr]⟩
      exact absurd hd' (term_not_div hx'' hxT'' hclN)
    · exact div_of_safe (fun x hx => (Steps.safe hhok hc hx).2)
        (fun x hx hxT => hterm ⟨x, hx, hxT⟩)

end det

/-! ## Invocations and sessions -/

theorem funcType_eq {s t : Store H} (hSR : SR p s t) (a : Nat) :
    (t.funcs[a]?.map FuncInst.type) = (s.funcs[a]?.map FuncInst.type) := by
  have := congrArg (fun l => l[a]?) hSR.sameTypes
  simp only [List.getElem?_map] at this
  rw [hSR.ht]
  exact this

theorem invoke_rel {s t : Store H} (hSR : SR p s t) (a : Nat) (vs : List Val) :
    MR p (invoke s a vs) (invoke t a vs) := by
  refine ⟨rfl, ?_⟩
  simp only [invoke]
  rw [funcType_eq hSR a]
  exact UL.refl _

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
  have e : s = withFuncs (withFuncs s (s.funcs.set p.ag (gR p))) s.funcs := rfl
  rw [e]
  exact hvs.imp fun _ _ h => valOk_withFuncs (s := withFuncs s (s.funcs.set p.ag (gR p)))
    hSR.sameTypes.symm h

section det

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁ (hok : PrmOk p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hhok : HostOk host) {mi : ModuleInst} {t : Store H} {script : List Call}
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
    obtain ⟨-, -, R3, -⟩ := runs_corr hok hR hhok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Steps.safe hhok hcO hx').1)
      (ConfigOk.storeOk (Steps.safe hhok hcN run).1) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr hok hR hhok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂ (hok : PrmOk p) {host : HostSemantics H} (hR : HostRespectsCode host)
    (hhok : HostOk host) {mi : ModuleInst} {s : Store H} {script : List Call}
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
    obtain ⟨R1, -, -, -⟩ := runs_corr hok hR hhok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Steps.safe hhok hcO run).1)
      (ConfigOk.storeOk (Steps.safe hhok hcN hx').1) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr hok hR hhok hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

/-- A correspondence between the instantiations of the left module `M` and the right module
`M'`. -/
def InstCorr (host : HostSemantics H) (M M' : Module) : Prop :=
  (∀ s xas c, StoreOk s → Instantiate PD host s M xas c →
    ∃ c' p, PrmOk p ∧ Instantiate PD host s M' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store) ∧
  (∀ s xas c', StoreOk s → Instantiate PD host s M' xas c' →
    ∃ c p, PrmOk p ∧ Instantiate PD host s M xas c ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store)

theorem obs_corr {host : HostSemantics H} (hR : HostRespectsCode host) (hhok : HostOk host)
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate PD host s M xas c) (hi' : Instantiate PD host s M' xas c')
    (hok : PrmOk p) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
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
  have hc := Instantiate.ok hhok hs hi
  have hc' := Instantiate.ok hhok hs hi'
  have hMR : MR p c c' := ⟨hfr.symm, by rw [hcode]; exact UL.refl _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr hok hR hhok hc hc' hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁ hok hR hhok h₃ (ConfigOk.storeOk (Steps.safe hhok hc hx).1)
        (ConfigOk.storeOk (Steps.safe hhok hc' h₁).1) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂ hok hR hhok h₃ (ConfigOk.storeOk (Steps.safe hhok hc h₁).1)
        (ConfigOk.storeOk (Steps.safe hhok hc' hx).1) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr {host : HostSemantics H} (hR : HostRespectsCode host)
    (hhok : HostOk host) {M M' : Module} (h : InstCorr (o := o) host M M') :
    ExportEquiv (· = ·) PD host M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hok, hi, hfr, hcode, hSR⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr hR hhok hs hi hi' hok hfr hcode hSR script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hok, hi', hfr, hcode, hSR⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr hR hhok hs hi hi' hok hfr hcode hSR script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end det

end Silmaril.Wasm.Binaryen.Unwrap
