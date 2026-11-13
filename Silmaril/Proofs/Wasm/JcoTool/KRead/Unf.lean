module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.Determinism.Join

/-!
# Core with the built-ins as host calls has unique value results

`KCoreRun.HStep` is Core 3.0 reduction with the canonical built-ins answered as host calls. In the
deterministic profile, and when distinct built-ins are distinct host functions (`hb` injective):

* `hstep_cases`: an `HStep` is a host-free Core step that keeps the host state, or the host call
  at the redex silmaril's `decompose?` finds, answered by `bans`;
* `host_det`: two host-call steps from one configuration are equal (`decompose?` is a function,
  `bans` is a function, `hb` is injective); `host_not_core`: a configuration with a host-call
  redex has no host-free step (`Step.noRedex`);
* `hstep_join`: `HStep` is **subcommutative** (silmaril's `Det.DStep.join'` for host-free steps);
* `val_nf`: a value configuration has no `HStep` (`Step.not_quiet`, `decompose?_vals_nil`);
* **`unique_val`**: two runs from one configuration to value configurations end in the same one
  (Church–Rosser, `Relation.church_rosser`).
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.FX.Asyncify.Tool (W)
open Silmaril.Wasm.JcoTool.KRead
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat} {α : Type _}

/-- The host-call step at the `decompose?` redex. -/
def HostAt (hb : BI → H) (ma : Nat) (q : HQ) (C : Config H) (q' : HQ) (C' : Config H) : Prop :=
  ∃ (E : Ctx) (a : Nat) (b : BI) (args : List W) (s' : Store H) (res : List W), decompose? C.store C.code = some (E, a, hb b, args.map Val.i32) ∧
    bans ma b q C.store args = some (q', s', res) ∧ C' = ⟨s', C.frame, E.fill (vals (res.map Val.i32))⟩

theorem decompose?_label (s : Store H) (n : Nat) (cont : List Instr) (is : List Admin) :
    decompose? s [.label n cont is] =
      (decompose? s is).map fun (E, a, h, args) => (.label [] n cont E [], a, h, args) := by
  rw [decompose?_of_split (splitVals_cons_nonval rfl [])]
  rfl

theorem decompose?_frame (s : Store H) (n : Nat) (fi : Frame) (is : List Admin) :
    decompose? s [.frame n fi is] =
      (decompose? s is).map fun (E, a, h, args) => (.frame [] n fi E [], a, h, args) := by
  rw [decompose?_of_split (splitVals_cons_nonval rfl [])]
  rfl

theorem host_instrs {q q' : HQ} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (h : HostAt hb ma q ⟨s, f, is⟩ q' ⟨s', f', is'⟩) :
    HostAt hb ma q ⟨s, f, vals vs ++ is ++ rest⟩ q' ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨E, a, b, args, s'', res, hd, hans, heq⟩ := h
  have e : s' = s'' ∧ f' = f ∧ is' = E.fill (vals (res.map Val.i32)) := by
    simpa only [Config.mk.injEq] using heq
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨E.wrap vs rest, a, b, args, s', res, decompose?_wrap vs rest hd, hans,
    by simp [Ctx.fill_wrap]⟩

theorem host_label {q q' : HQ} {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (h : HostAt hb ma q ⟨s, f, is⟩ q' ⟨s', f', is'⟩) :
    HostAt hb ma q ⟨s, f, [.label n cont is]⟩ q' ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨E, a, b, args, s'', res, hd, hans, heq⟩ := h
  have e : s' = s'' ∧ f' = f ∧ is' = E.fill (vals (res.map Val.i32)) := by
    simpa only [Config.mk.injEq] using heq
  obtain ⟨rfl, rfl, rfl⟩ := e
  have hd' : decompose? s [.label n cont is] = some (.label [] n cont E [], a, hb b, args.map Val.i32) := by
    rw [decompose?_label, show decompose? s is = _ from hd]; rfl
  exact ⟨.label [] n cont E [], a, b, args, s', res, hd', hans, by simp [Ctx.fill]⟩

theorem host_frame {q q' : HQ} {s s' : Store H} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (h : HostAt hb ma q ⟨s, fi, is⟩ q' ⟨s', fi', is'⟩) :
    HostAt hb ma q ⟨s, f, [.frame n fi is]⟩ q' ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨E, a, b, args, s'', res, hd, hans, heq⟩ := h
  have e : s' = s'' ∧ fi' = fi ∧ is' = E.fill (vals (res.map Val.i32)) := by
    simpa only [Config.mk.injEq] using heq
  obtain ⟨rfl, rfl, rfl⟩ := e
  have hd' : decompose? s [.frame n fi' is] = some (.frame [] n fi' E [], a, hb b, args.map Val.i32) := by
    rw [decompose?_frame, show decompose? s is = _ from hd]; rfl
  exact ⟨.frame [] n fi' E [], a, b, args, s', res, hd', hans, by simp [Ctx.fill]⟩

/-- **An `HStep` is a host-free step or the host call at the redex.** -/
theorem hstep_cases {x y : HQ × Config H} (h : HStep Pf hb ma x y) :
    (y.1 = x.1 ∧ Step Pf (fun _ _ _ _ => False) x.2 y.2) ∨ HostAt hb ma x.1 x.2 y.1 y.2 := by
  induction h with
  | core h => exact .inl ⟨rfl, h⟩
  | @host q q' s s' f c args res a fi ps rs b hc hf he hn hcode hans =>
    exact .inr ⟨.top [] [], a, b, args, s', res,
      decompose?_redex hc hf he (by simpa using hn) hcode, hans, by simp [Ctx.fill]⟩
  | instrs _ hne ih =>
    rcases ih with ⟨hq, hs⟩ | hh
    · exact .inl ⟨hq, .ctxtInstrs hs hne⟩
    · exact .inr (host_instrs hh)
  | label _ ih =>
    rcases ih with ⟨hq, hs⟩ | hh
    · exact .inl ⟨hq, .ctxtLabel hs⟩
    · exact .inr (host_label hh)
  | frame _ ih =>
    rcases ih with ⟨hq, hs⟩ | hh
    · exact .inl ⟨hq, .ctxtFrame hs⟩
    · exact .inr (host_frame hh)

theorem map_i32_inj {xs ys : List W} (h : xs.map Val.i32 = ys.map Val.i32) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have : x = y := by injection h1 with h1; injection h1
      rw [this, ih h2]

/-- **The host call at the redex is determined** (with `hb` injective). -/
theorem host_det (hinj : Function.Injective hb) {q q₁ q₂ : HQ} {C C₁ C₂ : Config H}
    (h₁ : HostAt hb ma q C q₁ C₁) (h₂ : HostAt hb ma q C q₂ C₂) : q₁ = q₂ ∧ C₁ = C₂ := by
  obtain ⟨E, a, b, args, s', res, hd, hans, rfl⟩ := h₁
  obtain ⟨E', a', b', args', s'', res', hd', hans', rfl⟩ := h₂
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨rfl, rfl, hbb, hargs⟩ := hd'
  have hb' := hinj hbb
  subst hb'
  have ha := map_i32_inj hargs
  subst ha
  rw [hans] at hans'
  simp only [Option.some.injEq, Prod.mk.injEq] at hans'
  obtain ⟨rfl, rfl, rfl⟩ := hans'
  exact ⟨rfl, rfl⟩

/-- A configuration with a host-call redex has no host-free step. -/
theorem host_not_core {q q' : HQ} {C C' D : Config H} (h : HostAt hb ma q C q' C')
    (hs : Step Pf (fun _ _ _ _ => False) C D) : False := by
  obtain ⟨E, a, b, args, s', res, hd, -, -⟩ := h
  have hn := decompose?_none_of_noRedex (Step.noRedex hs)
  rw [hd] at hn
  cases hn

/-- `HStep`, in the deterministic profile, **is subcommutative**. -/
theorem hstep_join (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool)
    {x y z : HQ × Config H} (hy : HStep (Profile.deterministic o) hb ma x y)
    (hz : HStep (Profile.deterministic o) hb ma x z) :
    ∃ u, Relation.ReflGen (HStep (Profile.deterministic o) hb ma) y u ∧
      Relation.ReflTransGen (HStep (Profile.deterministic o) hb ma) z u := by
  rcases hstep_cases hy with ⟨hqy, hsy⟩ | hy' <;> rcases hstep_cases hz with ⟨hqz, hsz⟩ | hz'
  · obtain ⟨qy, Cy⟩ := y
    obtain ⟨qz, Cz⟩ := z
    simp only at hqy hqz hsy hsz
    subst hqy hqz
    obtain ⟨u, hu₁, hu₂⟩ := Det.DStep.join' (o := o) hsy hsz
    refine ⟨(x.1, u), ?_, ?_⟩
    · cases hu₁ with
      | refl => exact .refl
      | single h => exact .single (.core h)
    · cases hu₂ with
      | refl => exact .refl
      | single h => exact .single (.core h)
  · exact (host_not_core hz' hsy).elim
  · exact (host_not_core hy' hsz).elim
  · obtain ⟨h1, h2⟩ := host_det hinj hy' hz'
    have : y = z := Prod.ext h1 h2
    subst this
    exact ⟨y, .refl, .refl⟩

/-- **A value configuration has no `HStep`.** -/
theorem val_nf {y z : HQ × Config H} (hv : ValCfg y) (h : HStep Pf hb ma y z) : False := by
  obtain ⟨cs, vs, hy⟩ := hv
  rcases hstep_cases h with ⟨-, hs⟩ | ⟨E, a, b, args, s', res, hd, -, -⟩
  · rw [hy] at hs
    exact Step.not_quiet hs (quiet_vals vs)
  · rw [hy] at hd
    simp only [decompose?_vals_nil] at hd
    cases hd

theorem eq_of_nf {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b)
    (hn : ∀ c, ¬ R a c) : a = b := by
  rcases h.cases_head with rfl | ⟨c, hc, -⟩
  · rfl
  · exact absurd hc (hn c)

/-- **Unique value results** of Core with the built-ins as host calls. -/
theorem unique_val (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool)
    {x y z : HQ × Config H} (hy : HSteps (Profile.deterministic o) hb ma x y)
    (hz : HSteps (Profile.deterministic o) hb ma x z) (vy : ValCfg y) (vz : ValCfg z) : y = z := by
  obtain ⟨u, hu₁, hu₂⟩ := Relation.church_rosser (fun a b c h₁ h₂ => hstep_join hinj o h₁ h₂) hy hz
  rw [eq_of_nf hu₁ (fun c h => val_nf vy h), eq_of_nf hu₂ (fun c h => val_nf vz h)]

end Silmaril.Proofs.Wasm.JcoTool.KRead
