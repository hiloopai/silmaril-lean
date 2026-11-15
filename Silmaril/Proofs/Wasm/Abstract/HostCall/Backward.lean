module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Execution.Core.InversionHost.Thms
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# Reconstructing the host answer of a Core host call (proofs)

The first backward-simulation step for host calls. Take a Core run from a
call of a host function, `vals ws ++ vals us ++ [ref.func a, call_ref]` on
exactly its arguments, to a configuration with no further step
(`host_call_run`). Then exactly one of these holds:

* **blocked**: the run never left the call, and the host has no outcome for
  it;
* **answered**: the host returned `(s', r)` (an outcome the relation allows),
  and the rest of the run continues from `vals ws ++ r.toAdmin` in the host's
  store `s'`.

Host divergence only stutters at the call (`callRefHostDiv`), so it never
reaches a configuration with no step; a stuttering prefix is absorbed by the
induction. Nothing is assumed about the host: the answer is read off the run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

theorem split_args {ws us vs₁ vs₂ : List Val} (h : ws ++ us = vs₁ ++ vs₂)
    (hl : vs₂.length = us.length) : vs₁ = ws ∧ vs₂ = us := by
  have hl₁ : vs₁.length = ws.length := by
    have := congrArg List.length h
    simp only [List.length_append] at this
    omega
  obtain ⟨h₁, h₂⟩ := List.append_inj h.symm hl₁
  exact ⟨h₁, h₂⟩

/-- **The host answer of a Core host call, read off a run to a stuck
configuration.** -/
theorem host_call_run_seq {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : Steps P host
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        ∀ o, ¬ host hh s us o) ∨
      ∃ s' r, host hh s us (.returned s' r) ∧
        Steps P host ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c := by
  let start : Config H := ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
  have hstart : ∀ c₁, Step P host start c₁ →
      (∃ s' r, host hh s us (.returned s' r) ∧ c₁ = ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩) ∨
        c₁ = start := by
    intro c₁ h
    have h' : Step P host ⟨s, f, vals (ws ++ us) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
        c₁ := by
      simpa [start, vals_append, List.append_assoc] using h
    obtain ⟨vs₁, vs₂, ps', rs', hsplit, he', hn', hres⟩ :=
      Step.callRef_host_inv_seq (r := .callRefType fi.type) trivial hf hcode h'
    have := (Expand.iff.1 he).symm.trans (Expand.iff.1 he')
    simp only [Option.some.injEq, Ty.func.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨rfl, rfl⟩ := split_args hsplit (hn'.trans hn.symm)
    rcases hres with ⟨s', res, hhost, rfl⟩ | ⟨hhost, rfl⟩
    · exact .inl ⟨s', res, hhost, rfl⟩
    · exact .inr (by simp [start, List.append_assoc])
  -- induction on the run from `start`
  suffices key : ∀ x, Steps P host x c → x = start →
      (c = start ∧ ∀ o, ¬ host hh s us o) ∨
        ∃ s' r, host hh s us (.returned s' r) ∧
          Steps P host ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c from
    key _ hrun rfl
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hxs
    refine .inl ⟨hxs, fun o ho => ?_⟩
    subst hxs
    rcases o with ⟨s', r⟩ | _
    · apply hend ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩
      have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
        (Step.callRefHost (f := f) (c := .callRefType fi.type) trivial hf he hn hcode ho)
      simpa [start, vals_append, List.append_assoc] using this
    · apply hend start
      have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
        (Step.callRefHostDiv (f := f) (c := .callRefType fi.type) trivial hf he hn hcode ho)
      simpa [start, vals_append, List.append_assoc] using this
  | head hstep hrest ih =>
    intro hxs
    subst hxs
    rcases hstart _ hstep with ⟨s', r, hhost, rfl⟩ | rfl
    · exact .inr ⟨s', r, hhost, hrest⟩
    · exact ih rfl

/-- `host_call_run_seq` with nothing after the call. -/
theorem host_call_run {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {ws us : List Val} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : Steps P host ⟨s, f, vals ws ++ vals us ++ [.ref (.func a), .callRefType fi.type]⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ∧
        ∀ o, ¬ host hh s us o) ∨
      ∃ s' r, host hh s us (.returned s' r) ∧ Steps P host ⟨s', f, vals ws ++ r.toAdmin⟩ c := by
  simpa using host_call_run_seq (rest := []) hf hcode he hn hrun hend

/-- One step of a host call on exactly its arguments: an answer, or a stutter. -/
theorem host_call_step {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin} {c₁ : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (h : Step P host ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ c₁) :
    (∃ s' r, host hh s us (.returned s' r) ∧ c₁ = ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩) ∨
      c₁ = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ := by
  have h' : Step P host ⟨s, f, vals (ws ++ us) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
      c₁ := by
    simpa [vals_append, List.append_assoc] using h
  obtain ⟨vs₁, vs₂, ps', rs', hsplit, he', hn', hres⟩ :=
    Step.callRef_host_inv_seq (r := .callRefType fi.type) trivial hf hcode h'
  have := (Expand.iff.1 he).symm.trans (Expand.iff.1 he')
  simp only [Option.some.injEq, Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨rfl, rfl⟩ := split_args hsplit (hn'.trans hn.symm)
  rcases hres with ⟨s', res, hhost, rfl⟩ | ⟨hhost, rfl⟩
  · exact .inl ⟨s', res, hhost, rfl⟩
  · exact .inr (by simp [List.append_assoc])

/-- **`host_call_run_seq` on counted runs**: the answered continuation takes fewer
steps than the whole run. -/
theorem host_call_runN_seq {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : Silmaril.Wasm.Abstract.StepsN P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        ∀ o, ¬ host hh s us o) ∨
      ∃ s' r m, m < n ∧ host hh s us (.returned s' r) ∧
        Silmaril.Wasm.Abstract.StepsN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c := by
  let start : Config H := ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
  suffices key : ∀ n x, Silmaril.Wasm.Abstract.StepsN P host n x c → x = start →
      (c = start ∧ ∀ o, ¬ host hh s us o) ∨
        ∃ s' r m, m < n ∧ host hh s us (.returned s' r) ∧
          Silmaril.Wasm.Abstract.StepsN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c from
    key n _ hrun rfl
  clear hrun
  intro n x hx
  induction hx with
  | refl =>
    intro hxs
    subst hxs
    refine .inl ⟨rfl, fun o ho => ?_⟩
    rcases o with ⟨s', r⟩ | _
    · apply hend ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩
      have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
        (Step.callRefHost (f := f) (c := .callRefType fi.type) trivial hf he hn hcode ho)
      simpa [start, vals_append, List.append_assoc] using this
    · apply hend start
      have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
        (Step.callRefHostDiv (f := f) (c := .callRefType fi.type) trivial hf he hn hcode ho)
      simpa [start, vals_append, List.append_assoc] using this
  | @head m x y _ hstep hrest ih =>
    intro hxs
    subst hxs
    rcases host_call_step hf hcode he hn hstep with ⟨s', r, hhost, rfl⟩ | rfl
    · exact .inr ⟨s', r, m, by omega, hhost, hrest⟩
    · rcases ih hend rfl with h | ⟨s', r, k, hk, hhost, hr⟩
      · exact .inl h
      · exact .inr ⟨s', r, k, by omega, hhost, hr⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall
