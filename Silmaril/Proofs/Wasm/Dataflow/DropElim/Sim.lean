module

public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Struct
public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Pure
public import Silmaril.Foundations.ForwardSim

/-!
# an earlier step of the two-pass DCE: the simulation and its consequences

* `erase_step_sim`: every source step from an `ERel`-related pair is matched, by strong
  induction on `codeSize` and a split of the erasure at its first active rewrite
  (`Erase.split`); a label redex recurses into its body (`erase_label_match`);
* `eraseSim`: An earlier step as a stuttering forward simulation (`Silmaril.ForwardSim`);
* `dropElim_result`, `dropElim_returning`, `dropElim_diverges`: results, pending returns
  and divergence of a function body are preserved, with the same store and frame. An earlier step
  needs neither liveness nor the fragment: it holds for every function body, numerical
  profile and host.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Lift a match through unchanged values and an independently erased suffix. -/
theorem EraseMatched.context {c c' d : Config H} (hm : EraseMatched P host c c' d)
    (vs : List Val) {rest rest' : List Admin} (hr : Erase rest rest') :
    EraseMatched P host ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ d.code ++ rest'⟩ := by
  obtain ⟨⟨t', g', target'⟩, hh, hp⟩ := hm
  refine ⟨⟨t', g', vals vs ++ target' ++ rest'⟩,
    ⟨hh.store, hh.frame, ((Erase.refl _).append hh.code).append hr⟩, ?_⟩
  rcases hp with ht | ⟨he, hlt⟩
  · exact .inl (Sim.Closure.transGen_ctx ht vs rest')
  · cases he
    exact .inr ⟨rfl, by simpa only [codeSize_append, Nat.add_lt_add_iff_left,
      Nat.add_lt_add_iff_right] using hlt⟩

/-- Lift a match of a label body through the label. -/
theorem EraseMatched.label {s s' : Store H} {f f' : Frame} {n : Nat} {cont cont' : List Instr}
    {b b' code : List Admin} (hc : Erase (expression cont) (expression cont'))
    (hm : EraseMatched P host ⟨s, f, b⟩ ⟨s', f', code⟩ ⟨s, f, b'⟩) :
    EraseMatched P host ⟨s, f, [.label n cont b]⟩ ⟨s', f', [.label n cont code]⟩
      ⟨s, f, [.label n cont' b']⟩ := by
  obtain ⟨⟨t, g, code'⟩, hr, hp⟩ := hm
  refine ⟨⟨t, g, [.label n cont' code']⟩, ⟨hr.store, hr.frame, .label n hc hr.code⟩, ?_⟩
  rcases hp with ht | ⟨he, hlt⟩
  · exact .inl (Sim.Closure.transGen_label ht n cont')
  · cases he
    exact .inr ⟨rfl, by change 1 + _ + 0 < 1 + _ + 0; dsimp only at hlt; omega⟩

/-- A label redex whose result the target reaches in one step with equal code. -/
theorem EraseMatched.single {s s' : Store H} {f f' : Frame} {c d c' : List Admin}
    (hstep : Step P host ⟨s, f, d⟩ ⟨s', f', c'⟩) :
    EraseMatched P host ⟨s, f, c⟩ ⟨s', f', c'⟩ ⟨s, f, d⟩ :=
  ⟨⟨s', f', c'⟩, ⟨rfl, rfl, .refl _⟩, .inl (.single hstep)⟩

/-- A branch to the label: the erased body keeps the branch and the values it carries. -/
theorem erase_brZero {s : Store H} {f : Frame} {n : Nat} {cont cont' : List Instr}
    {b' : List Admin} {vs' vs : List Val} {l : LabelIdx} {rest : List Admin}
    (hc : Erase (expression cont) (expression cont')) (hl : l.toNat = 0) (hn : vs.length = n)
    (hb : Erase (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) b') :
    EraseMatched P host ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩ ⟨s, f, [.label n cont' b']⟩ := by
  have hb' : Erase (vals (vs' ++ vs) ++ .plain (.br l) :: rest) b' := by simpa using hb
  obtain ⟨rest', rfl⟩ := hb'.exit_prefix (.inl ⟨l, rfl⟩)
  refine ⟨⟨_, _, vals vs ++ expression cont'⟩, ⟨rfl, rfl, (Erase.refl _).append hc⟩,
    .inl (.single ?_)⟩
  simpa using (Step.brLabelZero (P := P) (host := host) (s := s) (f := f)
    (cont := cont') (vs' := vs') (vs := vs) (rest := rest') hl hn)

/-- Match a label redex. The only recursive obligation is the step of its body. -/
theorem erase_label_red {s s' : Store H} {f f' : Frame} {n : Nat} {cont cont' : List Instr}
    {b b' out : List Admin} (hc : Erase (expression cont) (expression cont')) (hb : Erase b b')
    (ih : ∀ {t : Store H} {g : Frame} {body : List Admin},
      Step P host ⟨s, f, b⟩ ⟨t, g, body⟩ →
      EraseMatched P host ⟨s, f, b⟩ ⟨t, g, body⟩ ⟨s, f, b'⟩)
    (h : Sim.Closure.LabelRed P host s f n cont b s' f' out) :
    EraseMatched P host ⟨s, f, [.label n cont b]⟩ ⟨s', f', out⟩ ⟨s, f, [.label n cont' b']⟩ := by
  cases h with
  | ctxt hstep => exact EraseMatched.label hc (ih hstep)
  | values vs =>
    have he : b' = vals vs := Erase.result (r := .values vs) hb
    rw [he]
    exact EraseMatched.single .labelVals
  | brZero hl hn => exact erase_brZero hc hl hn hb
  | brSucc hl =>
    obtain ⟨rest', rfl⟩ := hb.exit_prefix_append (.inl ⟨_, rfl⟩)
    exact EraseMatched.single (.brLabelSucc hl)
  | returnCallRef hcall =>
    obtain ⟨rest', rfl⟩ := hb.exit_prefix_append (.inr (.inr hcall))
    exact EraseMatched.single (.returnCallRefLabel hcall)
  | return_ =>
    obtain ⟨rest', rfl⟩ := hb.exit_prefix_append (.inr (.inl rfl))
    exact EraseMatched.single .returnLabel
  | throwRef a =>
    have he : b' = throwing a := Erase.result (r := .throw a) hb
    rw [he]
    exact EraseMatched.single .throwRefLabel
  | trap =>
    have he : b' = [.trap] := hb.eq_trap rfl
    rw [he]
    exact EraseMatched.single .trapLabel

/-- Label matching under any surrounding value prefix and erased suffix. -/
theorem erase_label_match {s s' : Store H} {f f' : Frame} {n : Nat} {cont cont' : List Instr}
    {b b' rest rest' out : List Admin} {vs : List Val}
    (hc : Erase (expression cont) (expression cont')) (hb : Erase b b') (hr : Erase rest rest')
    (ih : ∀ {t : Store H} {g : Frame} {body : List Admin},
      Step P host ⟨s, f, b⟩ ⟨t, g, body⟩ →
      EraseMatched P host ⟨s, f, b⟩ ⟨t, g, body⟩ ⟨s, f, b'⟩)
    (h : Step P host ⟨s, f, vals vs ++ [.label n cont b] ++ rest⟩ ⟨s', f', out⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ [.label n cont b] ++ rest⟩ ⟨s', f', out⟩
      ⟨s, f, vals vs ++ [.label n cont' b'] ++ rest'⟩ := by
  have hs : Step P host ⟨s, f, vals vs ++ Admin.label n cont b :: rest⟩ ⟨s', f', out⟩ := by
    simpa using h
  rcases Sim.Step.split_head rfl hs with ⟨ws, us, is', rfl, hh, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨out, hred, rfl⟩ := Sim.Closure.Step.label_inv hh
    simpa using (erase_label_red hc hb ih hred).context (ws ++ us) hr
  · cases he
  · cases he

/-- One step at the first active rewrite `x ⟶ y`, given the simulation for smaller code
(used for a label body). -/
theorem erase_atom_match {s s' : Store H} {f f' : Frame} {vs : List Val}
    {x y rest rest' c' : List Admin} (hxy : Erase.Atom x y) (hr : Erase rest rest')
    (ih : ∀ {body body' : List Admin}, codeSize body < codeSize (vals vs ++ x ++ rest) →
      Erase body body' → ∀ {t : Store H} {g : Frame} {code : List Admin},
      Step P host ⟨s, f, body⟩ ⟨t, g, code⟩ →
      EraseMatched P host ⟨s, f, body⟩ ⟨t, g, code⟩ ⟨s, f, body'⟩)
    (hs : Step P host ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', c'⟩) :
    EraseMatched P host ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', c'⟩
      ⟨s, f, vals vs ++ y ++ rest'⟩ := by
  cases hxy with
  | keep a ha => exact erase_keep_match ha hr hs
  | pure hp => exact erase_pure_match hp hr hs
  | block bt hb => exact erase_struct_match (.block bt hb) hr hs
  | loop bt hb => exact erase_struct_match (.loop bt hb) hr hs
  | if_ bt hb₁ hb₂ => exact erase_struct_match (.if_ bt hb₁ hb₂) hr hs
  | label n hc hb =>
    refine erase_label_match hc hb hr (ih ?_ hb) hs
    simp only [codeSize_append, codeSize_cons, adminSize]
    omega
  | trap junk =>
    simpa [EraseMatched] using erase_cut_match (P := P) (host := host) (U := vs)
      (k := [.trap]) (X := junk ++ rest) (.inl rfl) (by simpa using hs) rest'
  | throwRef a junk =>
    simpa [EraseMatched] using erase_cut_match (P := P) (host := host) (U := vs)
      (k := throwing a) (X := junk ++ rest) (.inr ⟨a, rfl⟩) (by simpa using hs) rest'

/-- One step from an erased pair, at a given `codeSize`, by strong induction. -/
theorem erase_step_sim_aux (m : Nat) :
    ∀ (c c' d : Config H), codeSize c.code = m → Step P host c c' → ERel c d →
      EraseMatched P host c c' d := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rintro ⟨s, f, c⟩ ⟨s', f', c'⟩ ⟨t, g, d⟩ hm hs ⟨ht, hg, hcode⟩
    obtain ⟨rfl, rfl⟩ : t = s ∧ g = f := ⟨ht, hg⟩
    rcases hcode.split with ⟨vs, rfl, rfl⟩ | ⟨vs, x, y, rest, rest', rfl, rfl, hxy, hr⟩
    · exact (Step.not_vals hs).elim
    · exact erase_atom_match hxy hr (fun hlt hb _ _ _ hstep =>
        ih _ (hm ▸ hlt) _ _ ⟨_, _, _⟩ rfl hstep ⟨rfl, rfl, hb⟩) hs

/-- **Pass-2 simulation.** A source step is matched by one or more target steps, or by
none with `codeSize` decreasing (the source computes or discards a value that the target
already discarded). -/
theorem erase_step_sim {c₁ c₂ d₁ : Config H} (h : Step P host c₁ c₂) (hr : ERel c₁ d₁) :
    ∃ d₂, ERel c₂ d₂ ∧
      (Relation.TransGen (Step P host) d₁ d₂ ∨ (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code)) :=
  erase_step_sim_aux (codeSize c₁.code) c₁ c₂ d₁ rfl h hr

/-- an earlier step as a stuttering forward simulation (`Silmaril.ForwardSim`). -/
def eraseSim (P : Profile) (host : HostSemantics H) :
    Silmaril.ForwardSim (Step P host) (Step P host) (ERel (H := H)) where
  measure c := codeSize c.code
  step hab hr := by
    obtain ⟨d₂, hr₂, hm⟩ := erase_step_sim hab hr
    exact ⟨d₂, hm, hr₂⟩

/-! ## Function bodies -/

theorem erase_rel_entry {s : Store H} {f : Frame} {n : Nat} {e : Expr} :
    ERel ⟨s, f, [.label n [] (expression e)]⟩ ⟨s, f, [.label n [] (expression (dropElim e))]⟩ :=
  ⟨rfl, rfl, .label n (cont := []) (cont' := []) .nil (dropElim_erase e)⟩

/-- **Pass-2 correctness.** If a function body, run under its outer label, reaches a result,
the pass-2 body reaches the same result, store and frame. -/
theorem dropElim_result {s s₁ : Store H} {f f₁ : Frame} {n : Nat} {e : Expr} {r : Result}
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩ ⟨s₁, f₁, r.toAdmin⟩) :
    Steps P host ⟨s, f, [.label n [] (expression (dropElim e))]⟩ ⟨s₁, f₁, r.toAdmin⟩ := by
  obtain ⟨⟨ds, df, dc⟩, hd, hs, hf, hc⟩ := (eraseSim P host).steps h erase_rel_entry
  have hc' : dc = r.toAdmin := hc.result
  have hs' : ds = s₁ := hs
  have hf' : df = f₁ := hf
  exact hc' ▸ hs' ▸ hf' ▸ hd

/-- an earlier step preserves a `return` out of the body, with its values. -/
theorem dropElim_returning {s s₁ : Store H} {f f₁ : Frame} {n : Nat} {e : Expr} {vs : List Val}
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩
      ⟨s₁, f₁, vals vs ++ [.plain .return_]⟩) :
    Steps P host ⟨s, f, [.label n [] (expression (dropElim e))]⟩
      ⟨s₁, f₁, vals vs ++ [.plain .return_]⟩ := by
  obtain ⟨⟨ds, df, dc⟩, hd, hs, hf, hc⟩ := (eraseSim P host).steps h erase_rel_entry
  have hc' : dc = vals vs ++ [.plain .return_] := hc.returning
  have hs' : ds = s₁ := hs
  have hf' : df = f₁ := hf
  exact hc' ▸ hs' ▸ hf' ▸ hd

/-- an earlier step preserves divergence. -/
theorem dropElim_diverges {s : Store H} {f : Frame} {n : Nat} {e : Expr}
    (h : Diverges P host ⟨s, f, [.label n [] (expression e)]⟩) :
    Diverges P host ⟨s, f, [.label n [] (expression (dropElim e))]⟩ :=
  (eraseSim P host).diverges h erase_rel_entry

end Silmaril.Wasm.Dataflow
