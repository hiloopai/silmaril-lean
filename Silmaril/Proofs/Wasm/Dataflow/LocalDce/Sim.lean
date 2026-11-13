module

public import Silmaril.Proofs.Wasm.Dataflow.LocalDce.Clean
public import Silmaril.Foundations.ForwardSim

/-!
# an earlier step of the two-pass DCE: the simulation and its consequences

* `localDce_step_sim`: every source step from an `LRel`-related pair is matched, by
  induction on `LCode`: clean code (`localDce_step_sim_clean`), a pending dead store
  (`lcode_pend_sim`: the source performs it, the target stutters) and a label whose body is
  related by `LCode` (`lcode_label_sim`);
* `localDceSim`: An earlier step as a stuttering forward simulation (`Silmaril.ForwardSim`);
* `localDce_result`, `localDce_returning`, `localDce_diverges`: results, pending returns
  and divergence of a fragment function body are preserved, from any frame that agrees
  with the original on the body's live-in locals.

The source proof inverted the label step by hand at the head level; here the inversion is
silmaril-lean's `Sim.Step.split_head` and `Sim.Closure.Step.label_inv`, which hold for every
host, and the inversion of a pending `local.set` uses `Step.head_inv` and `Head.fam_inv`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf noHost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Inversions -/

/-- A variable step of `local.set x` consumes one value and writes it. -/
theorem variableStep_localSet_inv {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx}
    {c : Config H} (h : VariableStep ⟨s, f, vals args ++ [.plain (.localSet x)]⟩ c) :
    ∃ v, args = [v] ∧ x.toNat < f.locals.length ∧ c = ⟨s, f.setLocal x v, []⟩ := by
  generalize hl : (⟨s, f, vals args ++ [Admin.plain (.localSet x)]⟩ : Config H) = cc at h
  cases h with
  | @localSet s' f' y v hx =>
    have hl' : s' = s ∧ f' = f ∧ vals [v] ++ [.plain (.localSet y)] =
        vals args ++ [Admin.plain (.localSet x)] := by
      simpa [vals, eq_comm] using hl
    obtain ⟨rfl, rfl, hc⟩ := hl'
    obtain ⟨hv, hxy⟩ := SingleThreaded.Det.append_singleton_inj.mp hc
    have hxy' : y = x := by simpa using hxy
    subst hxy'
    exact ⟨v, (SingleThreaded.Det.vals_inj.mp hv).symm, hx, rfl⟩
  | _ =>
    exfalso
    have := congrArg (fun c : Config H => c.code.getLast?) hl
    simp at this

/-- A pending `local.set` with its operand at the first non-value position can only
perform that store. -/
theorem Step.localSet_inv {s : Store H} {f : Frame} {vs : List Val} {w : Val} {x : LocalIdx}
    {rest : List Admin} {c : Config H}
    (h : Step P host ⟨s, f, vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest⟩ c)
    (hfrag : fragAdminSeq (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest) = true) :
    x.toNat < f.locals.length ∧ c = ⟨s, f.setLocal x w, vals vs ++ rest⟩ := by
  have h' : Step P host ⟨s, f, vals (vs ++ [w]) ++ .plain (.localSet x) :: rest⟩ c := by
    simpa [vals] using h
  have hn : Step P noHost ⟨s, f, vals (vs ++ [w]) ++ .plain (.localSet x) :: rest⟩ c :=
    Step.noHost_of_frag h' (by simp_all)
  obtain ⟨pre, args, c₀, hws, hh, rfl⟩ := Step.head_inv hn rfl (by simp) (by simp)
  have hv : VariableStep ⟨s, f, vals args ++ [.plain (.localSet x)]⟩ c₀ :=
    hh.fam_inv (by simp [famOf])
  obtain ⟨v, rfl, hx, rfl⟩ := variableStep_localSet_inv hv
  obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hws
  exact ⟨hx, by simp⟩

/-! ## The three `LCode` cases -/

/-- A pending dead store: the source performs it and the target stutters. -/
theorem lcode_pend_sim {env : List LiveSet} {out : LiveSet} {s : Store H} {f df : Frame}
    {c₂ : Config H} {vs : List Val} {w : Val} {x : LocalIdx} {rest : List Admin}
    (hx : (liveAdminSeq env out rest).mem x.toNat = false)
    (h : Step P host ⟨s, f, vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest⟩ c₂)
    (hfrag : fragAdminSeq (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest) = true)
    (hfrag₂ : fragAdminSeq c₂.code = true)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest))
      f df) :
    LMatched P host env out ⟨s, f, vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest⟩ c₂
      ⟨s, df, vals vs ++ localDceAdminSeq env out rest⟩ := by
  obtain ⟨-, rfl⟩ := Step.localSet_inv h hfrag
  have hk : liveAdminSeq env out (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest) =
      liveAdminSeq env out rest := by
    simp [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin, liveAdmin_toAdmin, Backward.instr,
      liveness, liveTransfer, LiveSet.kill_eq_of_mem_false hx]
  have hf' : FrameRel (liveAdminSeq env out (vals vs ++ rest)) (f.setLocal x w) df := by
    simpa [liveAdminSeq_append, liveAdminSeq_vals] using
      FrameRel.setLocal_dead w hx (hk ▸ hf)
  have hc : LCode env out (vals vs ++ rest) (vals vs ++ localDceAdminSeq env out rest) := by
    simpa [localDceAdminSeq_append, localDceAdminSeq_vals] using
      LCode.clean (env := env) (out := out) (vals vs ++ rest)
  refine LMatched.stutter ⟨rfl, hf', hfrag₂, hc⟩ ?_
  show codeSize (vals vs ++ rest) < codeSize (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest)
  simp [codeSize_cons, adminSize]
  omega

/-- A label redex is a step of the body or sees clean body code. -/
theorem lcode_label_clean {env : List LiveSet} {out : LiveSet} {n : Nat} {cont : List Instr}
    {s s' : Store H} {f f' : Frame} {body bd out' : List Admin}
    (hb : LCode env out body bd) (hfb : fragAdminSeq body = true)
    (hred : Sim.Closure.LabelRed P host s f n cont body s' f' out') :
    (∃ b', out' = [.label n cont b'] ∧ Step P host ⟨s, f, body⟩ ⟨s', f', b'⟩) ∨
      bd = localDceAdminSeq env out body := by
  cases hred with
  | ctxt hstep => exact .inl ⟨_, rfl, hstep⟩
  | values vs => exact .inr (hb.eq_of_inert (inert_vals vs))
  | brZero =>
    rw [← vals_append] at hb ⊢
    exact .inr (LCode.clean_of_head₂ hb rfl (by simp) (by simp))
  | brSucc => exact .inr (LCode.clean_of_head₂ hb rfl (by simp) (by simp))
  | returnCallRef hc => exact absurd hfb (by simp [IsReturnCallRef.fragAdmin_eq hc])
  | return_ => exact .inr (LCode.clean_of_head₂ hb rfl (by simp) (by simp))
  | throwRef a => exact absurd hfb (by simp [throwing, fragInstr])
  | trap => exact .inr (hb.eq_of_inert inert_trap)

/-- A step of `vals vs ++ LABEL :: rest` is a label redex in context. -/
theorem Step.label_split {s s' : Store H} {f f' : Frame} {vs : List Val} {n : Nat}
    {cont : List Instr} {body rest es' : List Admin}
    (h : Step P host ⟨s, f, vals vs ++ .label n cont body :: rest⟩ ⟨s', f', es'⟩) :
    ∃ ws us out', vs = ws ++ us ∧ Sim.Closure.LabelRed P host s f n cont body s' f' out' ∧
      es' = vals ws ++ (vals us ++ out') ++ rest := by
  rcases Sim.Step.split_head rfl h with ⟨ws, us, is', rfl, hh, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨out', hred, rfl⟩ := Sim.Closure.Step.label_inv hh
    exact ⟨ws, us, out', rfl, hred, rfl⟩
  · cases he
  · cases he

/-- A label with clean body code: the clean simulation. -/
theorem lcode_label_of_clean {env : List LiveSet} {out : LiveSet} {s : Store H} {f df : Frame}
    {c₂ : Config H} {vs : List Val} {n : Nat} {cont : List Instr} {body bd rest : List Admin}
    (hcl : bd = localDceAdminSeq (liveSeq env (liveAdminSeq env out rest) cont :: env)
      (liveAdminSeq env out rest) body)
    (h : Step P host ⟨s, f, vals vs ++ .label n cont body :: rest⟩ c₂)
    (hfrag : fragAdminSeq (vals vs ++ .label n cont body :: rest) = true)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ .label n cont body :: rest)) f df) :
    LMatched P host env out ⟨s, f, vals vs ++ .label n cont body :: rest⟩ c₂
      ⟨s, df, vals vs ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) bd ::
        localDceAdminSeq env out rest⟩ := by
  subst hcl
  have := localDce_step_sim_clean (env := env) (out := out) h hfrag (Step.frag h hfrag) hf
  simpa [localDceAdminSeq_append, localDceAdminSeq_vals, localDceAdmin] using this

/-- A label whose body is `LCode`-related: a body step is matched by the induction
hypothesis, every other label redex by the clean simulation. -/
theorem lcode_label_sim {env : List LiveSet} {out : LiveSet} {s s' : Store H} {f f' df : Frame}
    {es' : List Admin} {vs : List Val} {n : Nat} {cont : List Instr} {body bd rest : List Admin}
    (hb : LCode (liveSeq env (liveAdminSeq env out rest) cont :: env) (liveAdminSeq env out rest)
      body bd)
    (ih : ∀ {s : Store H} {f df : Frame} {c₂ : Config H}, Step P host ⟨s, f, body⟩ c₂ →
      fragAdminSeq body = true →
      FrameRel (liveAdminSeq (liveSeq env (liveAdminSeq env out rest) cont :: env)
        (liveAdminSeq env out rest) body) f df →
      LMatched P host (liveSeq env (liveAdminSeq env out rest) cont :: env)
        (liveAdminSeq env out rest) ⟨s, f, body⟩ c₂ ⟨s, df, bd⟩)
    (h : Step P host ⟨s, f, vals vs ++ .label n cont body :: rest⟩ ⟨s', f', es'⟩)
    (hfrag : fragAdminSeq (vals vs ++ .label n cont body :: rest) = true)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ .label n cont body :: rest)) f df) :
    LMatched P host env out ⟨s, f, vals vs ++ .label n cont body :: rest⟩ ⟨s', f', es'⟩
      ⟨s, df, vals vs ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) bd ::
        localDceAdminSeq env out rest⟩ := by
  have hfrag₂ : fragAdminSeq es' = true := Step.frag h hfrag
  have hfb : fragAdminSeq body = true := by simp_all
  have hf' : FrameRel (liveAdminSeq (liveSeq env (liveAdminSeq env out rest) cont :: env)
      (liveAdminSeq env out rest) body) f df := by
    simpa [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin] using hf
  obtain ⟨ws, us, out', rfl, hred, rfl⟩ := Step.label_split h
  rcases lcode_label_clean hb hfb hred with ⟨b', rfl, hstep⟩ | hcl
  · have hm : LMatched P host env out ⟨s, f, vals (ws ++ us) ++ .label n cont body :: rest⟩
        ⟨s', f', vals (ws ++ us) ++ .label n cont b' :: rest⟩
        ⟨s, df, vals (ws ++ us) ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) bd ::
          localDceAdminSeq env out rest⟩ :=
      LMatched.label (n := n) (ws ++ us) rest (ih hstep hfb hf') (by simpa using hfrag₂)
    simpa using hm
  · exact lcode_label_of_clean hcl h hfrag hf

/-! ## The simulation -/

/-- The simulation on `LCode`, by induction on it. -/
theorem lcode_sim {env : List LiveSet} {out : LiveSet} {code dcode : List Admin}
    (hc : LCode env out code dcode) :
    ∀ {s : Store H} {f df : Frame} {c₂ : Config H}, Step P host ⟨s, f, code⟩ c₂ →
      fragAdminSeq code = true → FrameRel (liveAdminSeq env out code) f df →
      LMatched P host env out ⟨s, f, code⟩ c₂ ⟨s, df, dcode⟩ := by
  induction hc with
  | clean c => exact fun h hfrag hf => localDce_step_sim_clean h hfrag (Step.frag h hfrag) hf
  | pend vs w x rest hx => exact fun h hfrag hf => lcode_pend_sim hx h hfrag (Step.frag h hfrag) hf
  | label vs n cont rest hb ih =>
    intro s f df c₂ h hfrag hf
    obtain ⟨s', f', es'⟩ := c₂
    exact lcode_label_sim hb ih h hfrag hf

/-- **Pass-1 simulation.** A source step is matched by one or more target steps, or (the
two steps of a dead `local.tee`) by none with `codeSize` decreasing. -/
theorem localDce_step_sim {env : List LiveSet} {out : LiveSet} {c₁ c₂ d₁ : Config H}
    (h : Step P host c₁ c₂) (hr : LRel env out c₁ d₁) :
    ∃ d₂, LRel env out c₂ d₂ ∧
      (Relation.TransGen (Step P host) d₁ d₂ ∨
        (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code)) := by
  obtain ⟨ds, df, dc⟩ := d₁
  obtain ⟨hs, hf, hfrag, hcode⟩ := hr
  have hs' : ds = c₁.store := hs
  subst hs'
  exact lcode_sim hcode h hfrag hf

/-- an earlier step as a stuttering forward simulation (`Silmaril.ForwardSim`). -/
def localDceSim (P : Profile) (host : HostSemantics H) (env : List LiveSet) (out : LiveSet) :
    Silmaril.ForwardSim (Step P host) (Step P host) (LRel env out) where
  measure c := codeSize c.code
  step hab hr := by
    obtain ⟨d₂, hr₂, hm⟩ := localDce_step_sim hab hr
    exact ⟨d₂, hm, hr₂⟩

/-! ## Function bodies -/

/-- The initial relation for a function body under its outer label. -/
theorem localDce_rel_entry {s : Store H} {f f' : Frame} {n : Nat} {e : Expr}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f') :
    LRel [] ⊥ ⟨s, f, [.label n [] (expression e)]⟩
      ⟨s, f', [.label n [] (expression (localDce e))]⟩ := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa [liveAdmin, liveAdminSeq_expression, liveEntry] using hf
  · simpa using he
  · have := LCode.clean (env := []) (out := ⊥) [.label n [] (expression e)]
    simpa [localDceAdmin, localDceAdminSeq_expression, localDce] using this

/-- A source run from a function body is matched by a target run to a related
configuration. -/
theorem localDce_steps {s : Store H} {f f' : Frame} {n : Nat} {e : Expr} {c : Config H}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩ c) :
    ∃ d, Steps P host ⟨s, f', [.label n [] (expression (localDce e))]⟩ d ∧ LRel [] ⊥ c d :=
  (localDceSim P host [] ⊥).steps h (localDce_rel_entry he hf)

/-- **Pass-1 correctness.** If a fragment function body, run under its outer label,
reaches a result, the pass-1 body reaches the same result and store from any frame that
agrees with the original on the body's live-in locals. -/
theorem localDce_result {s s₁ : Store H} {f f' f₁ : Frame} {n : Nat} {e : Expr} {r : Result}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩ ⟨s₁, f₁, r.toAdmin⟩) :
    ∃ f₁', Steps P host ⟨s, f', [.label n [] (expression (localDce e))]⟩
      ⟨s₁, f₁', r.toAdmin⟩ := by
  obtain ⟨⟨ds, df, dc⟩, hd, hr⟩ := localDce_steps he hf h
  have hc : dc = r.toAdmin := hr.code.result
  have hs : ds = s₁ := hr.store
  exact ⟨df, hc ▸ hs ▸ hd⟩

/-- an earlier step preserves a `return` out of the body, with its values. -/
theorem localDce_returning {s s₁ : Store H} {f f' f₁ : Frame} {n : Nat} {e : Expr}
    {vs : List Val} (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩
      ⟨s₁, f₁, vals vs ++ [.plain .return_]⟩) :
    ∃ f₁', Steps P host ⟨s, f', [.label n [] (expression (localDce e))]⟩
      ⟨s₁, f₁', vals vs ++ [.plain .return_]⟩ := by
  obtain ⟨⟨ds, df, dc⟩, hd, hr⟩ := localDce_steps he hf h
  have hc : dc = vals vs ++ [.plain .return_] := hr.code.returning
  have hs : ds = s₁ := hr.store
  exact ⟨df, hc ▸ hs ▸ hd⟩

/-- an earlier step preserves divergence. -/
theorem localDce_diverges {s : Store H} {f f' : Frame} {n : Nat} {e : Expr}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Diverges P host ⟨s, f, [.label n [] (expression e)]⟩) :
    Diverges P host ⟨s, f', [.label n [] (expression (localDce e))]⟩ :=
  (localDceSim P host [] ⊥).diverges h (localDce_rel_entry he hf)

end Silmaril.Wasm.Dataflow
