module

public import Silmaril.Wasm.Binaryen.InlHostDiv

@[expose] public section

/-! # The inlining simulation: runs

`Classif host c`: every step from `c` is host-free, or a diverging host call that stays
at `c`. Typed configurations are classified when the host is code-respecting and typed
(`classif_of_ok`, from `host_no_return`). On classified left runs, `sim` and
`hostdiv_step` give the simulation of terminating runs (`run_sim`) and of divergence
(`div_sim`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Steps from `c` are host-free, or diverging host calls staying at `c`. -/
def Classif (P : Numerics.Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Step P host c c' → Step P Det.noHost c c' ∨
    (c' = c ∧ ∃ E a hh args, decompose? c.store c.code = some (E, a, hh, args) ∧
      host hh c.store args .diverged)

/-- **Typed configurations are classified.** -/
theorem classif_of_ok {host : HostSemantics H} (hR : HostRespectsCode host) (hok : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) {aw : Nat} {fw : FuncInst H}
    {cw : Func} (hfw : c.store.funcs[aw]? = some fw) (hcw : fw.code = .wasm cw) :
    Classif P host c := by
  intro c' hs
  rcases Step.split_host hs with hn | ⟨E, a, hh, args, hd, ⟨s', r, hret, -⟩ | ⟨hdiv, rfl⟩⟩
  · exact .inl hn
  · exact absurd hret fun h => host_no_return hR hok (ConfigOk.storeOk hc) hfw hcw
      (argsOk_of_redex (P := P) hc hd) h
  · exact .inr ⟨rfl, E, a, hh, args, hd, hdiv⟩

/-! ## Terminating runs -/

theorem steps_of_tg {a b : Config H} (h : Relation.TransGen (Step P Det.noHost) a b)
    (host : HostSemantics H) : Steps P host a b :=
  (h.lift id fun _ _ h => Step.of_noHost host h).to_reflTransGen

/-- **Terminating left runs are simulated.** -/
theorem run_sim (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) (hC : PrmC p)
    {host : HostSemantics H} {c c' : Config H} (h : Steps P host c c')
    (hcl : ∀ x, Steps P host c x → Classif P host x) {d : Config H} (hMR : MR p .gen c d)
    (hSR : SR p c.store d.store) :
    ∃ d', Steps P host d d' ∧ MR p .gen c' d' ∧ SR p c'.store d'.store := by
  induction h with
  | refl => exact ⟨d, .refl, hMR, hSR⟩
  | @tail x x' hx hstep ih =>
    obtain ⟨dx, hd, hMRx, hSRx⟩ := ih
    rcases hcl x hx x' hstep with hn | ⟨hxx, -⟩
    · obtain ⟨n', hMR', hSR', hprog⟩ := sim hok hfx hC (sizeOf x.code + 1) .gen x x' dx
        (by omega) hn hMRx hSRx
      rcases hprog with hp | ⟨hn', -⟩
      · exact ⟨n', hd.trans (steps_of_tg hp host), hMR', hSR'⟩
      · rw [hn'] at hMR' hSR'
        exact ⟨dx, hd, hMR', hSR'⟩
    · rw [hxx]
      exact ⟨dx, hd, hMRx, hSRx⟩

/-- Terminal left configurations: the right configuration has the same code. -/
theorem terminal_code {c d : Config H} (hMR : MR p .gen c d) {r : Result}
    (hr : c.code = r.toAdmin) : d.code = r.toAdmin := by
  obtain ⟨ds, df, dc⟩ := d
  have h := hMR.2
  simp only at h ⊢
  rw [hr] at h
  cases r with
  | values vs => exact LN.vals_inv h
  | trap => cases h with | cons h t => cases h; cases t; rfl
  | throw a =>
    cases h with
    | cons h t => cases h; cases t with | cons h' t' => cases h'; cases t'; rfl

/-! ## Divergence -/

/-- One step of the right side for a diverging left side. -/
theorem div_step (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) (hC : PrmC p)
    {host : HostSemantics H} (hR : HostRespectsCode host) {c₀ : Config H}
    (hcl : ∀ x, Steps P host c₀ x → Classif P host x) :
    ∀ (w : Nat) (x z : Config H), wL x.code = w → Steps P host c₀ x → Diverges P host x →
      MR p .gen x z → SR p x.store z.store →
      ∃ z₁ x' z', Step P host z z₁ ∧ Steps P host c₀ x' ∧ Diverges P host x' ∧ MR p .gen x' z' ∧
        SR p x'.store z'.store ∧ Steps P host z₁ z' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x z hw hx hdiv hMR hSR
  obtain ⟨x₁, hst, hdiv₁⟩ := InfiniteTrace.unfold hdiv
  have hx₁ : Steps P host c₀ x₁ := hx.tail hst
  rcases hcl x hx x₁ hst with hn | ⟨hxx, E, a, hh, args, hd, hdv⟩
  · obtain ⟨n', hMR', hSR', hprog⟩ := sim hok hfx hC (sizeOf x.code + 1) .gen x x₁ z
      (by omega) hn hMR hSR
    rcases hprog with hp | ⟨hn', hw'⟩
    · obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
      exact ⟨z₁, x₁, n', Step.of_noHost host h₁, hx₁, hdiv₁, hMR', hSR',
        h₂.lift id (fun _ _ h => Step.of_noHost host h)⟩
    · rw [hn'] at hMR' hSR'
      exact ih (wL x₁.code) (by omega) x₁ z rfl hx₁ hdiv₁ hMR' hSR'
  · obtain ⟨zs, zf, zc⟩ := z
    have hstep : Step P host ⟨zs, zf, zc⟩ ⟨zs, zf, zc⟩ :=
      hostdiv_step hR hSR hMR.cr hd hdv zf
    exact ⟨_, x, _, hstep, hx, hdiv, hMR, hSR, .refl⟩

/-- **Diverging left runs are simulated.** -/
theorem div_sim (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) (hC : PrmC p)
    {host : HostSemantics H} (hR : HostRespectsCode host) {c : Config H}
    (hdiv : Diverges P host c) (hcl : ∀ x, Steps P host c x → Classif P host x) {d : Config H}
    (hMR : MR p .gen c d) (hSR : SR p c.store d.store) : Diverges P host d := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P host c x ∧ Diverges P host x ∧ MR p .gen x z ∧
      SR p x.store z.store ∧ Steps P host y z) ?_ ⟨c, d, .refl, hdiv, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hx, hdx, hMRx, hSRx, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨z₁, x', z', hs, hx', hdx', hMR', hSR', hz⟩ :=
      div_step hok hfx hC hR hcl (wL x.code) x y rfl hx hdx hMRx hSRx
    exact ⟨z₁, hs, x', z', hx', hdx', hMR', hSR', hz⟩
  · exact ⟨y₁, h₁, x, z, hx, hdx, hMRx, hSRx, h₂⟩

end Silmaril.Wasm.Binaryen.InlR
