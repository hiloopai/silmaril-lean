module

public import Silmaril.Proofs.Wasm.Dataflow.LocalDce.Basic

/-!
# an earlier step of the two-pass DCE: the simulation from clean target code

`localDce_step_sim_clean`: a source step from code `c` is matched from the target
`localDceAdminSeq env out c` (the `LCode.clean` case). Every rule of `Step` that fragment
code can take has its own lemma below; the main theorem is one line per rule.

The source proof (an earlier development `LocalDce.localDce_step_sim_clean`) was one
249-line induction; the rule lemmas are its arms, and the shared lock-step,
context and label cases are `LMatched.lock`, `LMatched.ctx` and `LMatched.label`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {env : List LiveSet}
  {out : LiveSet} {s : Store H} {f df : Frame}

/-! ## Rule lemmas -/

/-- A step that the transform fixes on both sides and that does not touch the frame. -/
theorem clean_fixed {is is' : List Admin}
    (hstep : Step P host ⟨s, df, is⟩ ⟨s, df, is'⟩)
    (hT : localDceAdminSeq env out is = is) (hT' : localDceAdminSeq env out is' = is')
    (hle : liveAdminSeq env out is' ≤ liveAdminSeq env out is)
    (hf : FrameRel (liveAdminSeq env out is) f df) (hfrag₂ : fragAdminSeq is' = true) :
    LMatched P host env out ⟨s, f, is⟩ ⟨s, f, is'⟩ ⟨s, df, localDceAdminSeq env out is⟩ :=
  LMatched.lock (by rw [hT, hT']; exact hstep) (hf.mono hle) hfrag₂

theorem parametric_fixed {is is' : List Admin} (hp : ParametricStep is is') :
    localDceAdminSeq env out is = is ∧ localDceAdminSeq env out is' = is' := by
  cases hp <;> simp [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, constI32]

theorem parametric_live {is is' : List Admin} (hp : ParametricStep is is') :
    liveAdminSeq env out is' ≤ liveAdminSeq env out is := by
  cases hp <;>
    simp [liveAdmin, liveAdmin_toAdmin, constI32, Backward.instr, liveness, liveTransfer]

theorem numeric_fixed {is is' : List Admin} (hp : NumericStep P is is') :
    localDceAdminSeq env out is = is ∧ localDceAdminSeq env out is' = is' := by
  cases hp <;> simp [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, constI32]

theorem numeric_live {is is' : List Admin} (hp : NumericStep P is is') :
    liveAdminSeq env out is' ≤ liveAdminSeq env out is := by
  cases hp <;>
    simp [liveAdmin, liveAdmin_toAdmin, constI32, Backward.instr, liveness, liveTransfer]

/-- The live set of `v; local.set x` kills `x`. -/
theorem liveAdminSeq_localSet (v : Val) (x : LocalIdx) :
    liveAdminSeq env out [v.toAdmin, .plain (.localSet x)] = LiveSet.kill x.toNat out := by
  simp [liveAdmin, liveAdmin_toAdmin, Backward.instr, liveness, liveTransfer]

theorem clean_localGet {x : LocalIdx} {v : Val} (hl : f.local? x = some (some v))
    (hf : FrameRel (liveAdminSeq env out [.plain (.localGet x)]) f df)
    (hfrag₂ : fragAdminSeq [v.toAdmin] = true) :
    LMatched P host env out ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [v.toAdmin]⟩
      ⟨s, df, localDceAdminSeq env out [.plain (.localGet x)]⟩ := by
  have hx : LiveSet.single x.toNat ≤ liveAdminSeq env out [.plain (.localGet x)] := by
    simp [liveAdmin, Backward.instr, liveness, liveTransfer]
  have hl' : df.local? x = some (some v) := (hf.local?_eq hx).symm.trans hl
  refine clean_fixed (.variable (.localGet hl')) (by simp [localDceAdmin, localDceInstr])
    (by simp [localDceAdmin_toAdmin]) ?_ hf hfrag₂
  simp [liveAdmin, liveAdmin_toAdmin, Backward.instr, liveness, liveTransfer]

theorem clean_localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (hf : FrameRel (liveAdminSeq env out [v.toAdmin, .plain (.localSet x)]) f df)
    (hfrag₂ : fragAdminSeq [] = true) :
    LMatched P host env out ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩
      ⟨s, df, localDceAdminSeq env out [v.toAdmin, .plain (.localSet x)]⟩ := by
  have hk : FrameRel (LiveSet.kill x.toNat out) f df := by
    rwa [liveAdminSeq_localSet] at hf
  cases hm : out.mem x.toNat
  · have hd : FrameRel out f df := by rwa [LiveSet.kill_eq_of_mem_false hm] at hk
    refine LMatched.lock (fd' := df) ?_ (by simpa using FrameRel.setLocal_dead v hm hd) hfrag₂
    simpa [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, hm] using
      (Step.parametric (P := P) (host := host) (s := s) (f := df) (.drop v))
  · refine LMatched.lock (fd' := df.setLocal x v) ?_ (by simpa using FrameRel.setLocal v hk)
      hfrag₂
    simpa [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, hm] using
      (Step.variable (P := P) (host := host) (.localSet (s := s) (hf.length ▸ hx)))

theorem clean_localTee {x : LocalIdx} {v : Val}
    (hf : FrameRel (liveAdminSeq env out [v.toAdmin, .plain (.localTee x)]) f df)
    (hfrag₂ : fragAdminSeq [v.toAdmin, v.toAdmin, .plain (.localSet x)] = true) :
    LMatched P host env out ⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩
      ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩
      ⟨s, df, localDceAdminSeq env out [v.toAdmin, .plain (.localTee x)]⟩ := by
  have hf' : FrameRel (liveAdminSeq env out [v.toAdmin, v.toAdmin, .plain (.localSet x)]) f df := by
    simpa [liveAdmin, liveAdmin_toAdmin, Backward.instr, liveness, liveTransfer] using hf
  cases hm : out.mem x.toNat
  · have hc := LCode.pend (env := env) (out := out) [v] v x [] (by simpa using hm)
    refine LMatched.stutter ⟨rfl, hf', hfrag₂, ?_⟩ ?_
    · simpa [vals, localDceAdmin, localDceInstr, localDceAdmin_toAdmin, hm] using hc
    · simp [codeSize, adminSize]
  · refine LMatched.lock (fd' := df) ?_ hf' hfrag₂
    simpa [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, hm] using
      (Step.variable (P := P) (host := host) (.localTee (s := s) (f := df) (x := x) (v := v)))

theorem clean_globalGet {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hg : s.global? f x = some (a, g))
    (hf : FrameRel (liveAdminSeq env out [.plain (.globalGet x)]) f df)
    (hfrag₂ : fragAdminSeq [g.value.toAdmin] = true) :
    LMatched P host env out ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩
      ⟨s, df, localDceAdminSeq env out [.plain (.globalGet x)]⟩ := by
  refine clean_fixed (.variable (.globalGet ((Store.global?_congr hf.module x).symm.trans hg)))
    (by simp [localDceAdmin, localDceInstr]) (by simp [localDceAdmin_toAdmin]) ?_ hf hfrag₂
  simp [liveAdmin, liveAdmin_toAdmin, Backward.instr, liveness, liveTransfer]

theorem clean_globalSet {x : GlobalIdx} {a : Nat} {g : GlobalInst} {v : Val}
    (hg : s.global? f x = some (a, g))
    (hf : FrameRel (liveAdminSeq env out [v.toAdmin, .plain (.globalSet x)]) f df)
    (hfrag₂ : fragAdminSeq [] = true) :
    LMatched P host env out ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩
      ⟨s, df, localDceAdminSeq env out [v.toAdmin, .plain (.globalSet x)]⟩ := by
  have hT : localDceAdminSeq env out [v.toAdmin, .plain (.globalSet x)] =
      [v.toAdmin, .plain (.globalSet x)] := by
    simp [localDceAdmin, localDceInstr, localDceAdmin_toAdmin]
  refine LMatched.lock (fd' := df) ?_ (hf.mono ?_) hfrag₂
  · rw [hT]
    exact .variable (.globalSet ((Store.global?_congr hf.module x).symm.trans hg))
  · simp [liveAdmin, liveAdmin_toAdmin, Backward.instr, liveness, liveTransfer]

theorem clean_block {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ [.plain (.block bt body)])) f df)
    (hfrag₂ : fragAdminSeq [.label t₂.length [] (vals vs ++ expression body)] = true) :
    LMatched P host env out ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩
      ⟨s, df, localDceAdminSeq env out (vals vs ++ [.plain (.block bt body)])⟩ := by
  refine LMatched.lock (fd' := df) ?_ ?_ hfrag₂
  · simp only [localDceAdminSeq_append, localDceAdminSeq_vals, localDceAdminSeq_cons,
      localDceAdminSeq_nil, localDceAdmin, localDceInstr, List.map_cons, List.map_nil,
      List.append_nil, liveAdminSeq_nil, Backward.seq_nil, localDceAdminSeq_expression]
    exact .block (hf.module ▸ hbt) hm
  · simpa [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin, liveAdminSeq_expression,
      Backward.instr_block] using hf

theorem clean_loop {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ [.plain (.loop bt body)])) f df)
    (hfrag₂ : fragAdminSeq [.label t₁.length [.loop bt body] (vals vs ++ expression body)] =
      true) :
    LMatched P host env out ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩
      ⟨s, df, localDceAdminSeq env out (vals vs ++ [.plain (.loop bt body)])⟩ := by
  refine LMatched.lock (fd' := df) ?_ (hf.mono ?_) hfrag₂
  · simp only [localDceAdminSeq_append, localDceAdminSeq_vals, localDceAdminSeq_cons,
      localDceAdminSeq_nil, localDceAdmin, localDceInstr, List.map_cons, List.map_nil,
      List.append_nil, liveAdminSeq_nil, Backward.seq_nil, Backward.seq_cons,
      localDceAdminSeq_expression, localDceSeq_cons, localDceSeq_nil]
    exact .loop (hf.module ▸ hbt) hm
  · simpa [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin, liveAdminSeq_expression] using
      liveSeq_loop_safe env out bt body

/-- `if` and the conditional branches: the transform keeps the instruction and maps the
taken body or branch to its transform. -/
theorem clean_if {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} {b : List Instr}
    (hb : b = b₁ ∨ b = b₂)
    (hstep : Step P host ⟨s, df, [constI32 c, .plain (.if_ bt (localDceSeq (out :: env) out b₁)
      (localDceSeq (out :: env) out b₂))]⟩
      ⟨s, df, [.plain (.block bt (localDceSeq (out :: env) out b))]⟩)
    (hf : FrameRel (liveAdminSeq env out [constI32 c, .plain (.if_ bt b₁ b₂)]) f df)
    (hfrag₂ : fragAdminSeq [.plain (.block bt b)] = true) :
    LMatched P host env out ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.plain (.block bt b)]⟩
      ⟨s, df, localDceAdminSeq env out [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ := by
  refine LMatched.lock (fd' := df) ?_ (hf.mono ?_) hfrag₂
  · simpa [localDceAdmin, localDceInstr, localDceAdmin_toAdmin, constI32] using hstep
  · rcases hb with rfl | rfl <;> simp [liveAdmin, liveAdmin_toAdmin, constI32, Backward.instr]

theorem clean_brIf {c : BitVec 32} {l : LabelIdx} {is' : List Admin}
    (his : is' = [.plain (.br l)] ∨ is' = [])
    (hstep : Step P host ⟨s, df, [constI32 c, .plain (.brIf l)]⟩ ⟨s, df, is'⟩)
    (hf : FrameRel (liveAdminSeq env out [constI32 c, .plain (.brIf l)]) f df)
    (hfrag₂ : fragAdminSeq is' = true) :
    LMatched P host env out ⟨s, f, [constI32 c, .plain (.brIf l)]⟩ ⟨s, f, is'⟩
      ⟨s, df, localDceAdminSeq env out [constI32 c, .plain (.brIf l)]⟩ := by
  refine clean_fixed hstep (by simp [localDceAdmin, localDceInstr, localDceAdmin_toAdmin,
    constI32]) ?_ ?_ hf hfrag₂
  · rcases his with rfl | rfl <;> simp [localDceAdmin, localDceInstr]
  · rcases his with rfl | rfl <;> simp [liveAdmin, liveAdmin_toAdmin, constI32, Backward.instr]

theorem clean_brTable {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
    (hl : l ∈ ls ∨ l = l')
    (hstep : Step P host ⟨s, df, [constI32 i, .plain (.brTable ls l')]⟩
      ⟨s, df, [.plain (.br l)]⟩)
    (hf : FrameRel (liveAdminSeq env out [constI32 i, .plain (.brTable ls l')]) f df)
    (hfrag₂ : fragAdminSeq [.plain (.br l)] = true) :
    LMatched P host env out ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩
      ⟨s, f, [.plain (.br l)]⟩
      ⟨s, df, localDceAdminSeq env out [constI32 i, .plain (.brTable ls l')]⟩ := by
  refine clean_fixed hstep (by simp [localDceAdmin, localDceInstr, localDceAdmin_toAdmin,
    constI32]) (by simp [localDceAdmin, localDceInstr]) ?_ hf hfrag₂
  simp only [liveAdminSeq_cons, liveAdminSeq_nil, liveAdmin, liveAdmin_toAdmin, constI32]
  exact liveness.labelVal_le_brTable env out hl

theorem clean_labelVals {n : Nat} {cont : List Instr} {vs : List Val}
    (hf : FrameRel (liveAdminSeq env out [.label n cont (vals vs)]) f df)
    (hfrag₂ : fragAdminSeq (vals vs) = true) :
    LMatched P host env out ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩
      ⟨s, df, localDceAdminSeq env out [.label n cont (vals vs)]⟩ := by
  refine LMatched.lock (fd' := df) ?_ (by simpa [liveAdmin, liveAdminSeq_vals] using hf) hfrag₂
  simp only [localDceAdminSeq_cons, localDceAdminSeq_nil, localDceAdmin, localDceAdminSeq_vals,
    List.append_nil]
  exact .labelVals

theorem clean_brLabelZero {n : Nat} {cont : List Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n)
    (hf : FrameRel (liveAdminSeq env out
      [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]) f df)
    (hfrag₂ : fragAdminSeq (vals vs ++ expression cont) = true) :
    LMatched P host env out
      ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩
      ⟨s, df, localDceAdminSeq env out
        [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩ := by
  refine LMatched.lock (fd' := df) ?_ ?_ hfrag₂
  · have := Step.brLabelZero (P := P) (host := host) (s := s) (f := df) (n := n)
      (cont := localDceSeq env out cont) (vs' := vs') (vs := vs)
      (rest := localDceAdminSeq (liveSeq env out cont :: env) out rest) hl hn
    simpa [localDceAdmin, localDceAdminSeq_append, localDceAdminSeq_vals, localDceInstr,
      localDceAdminSeq_expression] using this
  · simpa [liveAdmin, liveAdminSeq_append, liveAdminSeq_vals, liveAdminSeq_expression,
      Backward.instr, labelVal, hl] using hf

theorem clean_brLabelSucc {n : Nat} {cont : List Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : 0 < l.toNat)
    (hf : FrameRel (liveAdminSeq env out [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)])
      f df)
    (hfrag₂ : fragAdminSeq (vals vs ++ [.plain (.br (labelPred l))]) = true) :
    LMatched P host env out ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩
      ⟨s, df, localDceAdminSeq env out [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩ := by
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
  have hp : (labelPred l).toNat = k := by
    simp only [labelPred, Idx.toNat] at hk ⊢
    omega
  refine LMatched.lock (fd' := df) ?_ ?_ hfrag₂
  · have := Step.brLabelSucc (P := P) (host := host) (s := s) (f := df) (n := n)
      (cont := localDceSeq env out cont) (vs := vs)
      (rest := localDceAdminSeq (liveSeq env out cont :: env) out rest) hl
    simpa [localDceAdmin, localDceAdminSeq_append, localDceAdminSeq_vals, localDceInstr] using this
  · simpa [liveAdmin, liveAdminSeq_append, liveAdminSeq_vals, Backward.instr, labelVal, hk, hp]
      using hf

theorem clean_returnLabel {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin}
    (hf : FrameRel (liveAdminSeq env out [.label n cont (vals vs ++ [.plain .return_] ++ rest)])
      f df)
    (hfrag₂ : fragAdminSeq (vals vs ++ [.plain .return_]) = true) :
    LMatched P host env out ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩
      ⟨s, df, localDceAdminSeq env out [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩ := by
  refine LMatched.lock (fd' := df) ?_ (hf.mono ?_) hfrag₂
  · have := Step.returnLabel (P := P) (host := host) (s := s) (f := df) (n := n)
      (cont := localDceSeq env out cont) (vs := vs)
      (rest := localDceAdminSeq (liveSeq env out cont :: env) out rest)
    simpa [localDceAdmin, localDceAdminSeq_append, localDceAdminSeq_vals, localDceInstr] using this
  · simp [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin, Backward.instr]

theorem clean_trapLabel {n : Nat} {cont : List Instr}
    (hf : FrameRel (liveAdminSeq env out [.label n cont [.trap]]) f df)
    (hfrag₂ : fragAdminSeq [.trap] = true) :
    LMatched P host env out ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
      ⟨s, df, localDceAdminSeq env out [.label n cont [.trap]]⟩ := by
  refine LMatched.lock (fd' := df) ?_ (hf.mono (by simp [liveAdmin])) hfrag₂
  simp only [localDceAdminSeq_cons, localDceAdminSeq_nil, localDceAdmin, List.append_nil]
  exact .trapLabel

/-- `Step/trap-instrs`: a lock step, unless the target has already absorbed everything
around the trap (then the target stutters). -/
theorem clean_trapInstrs {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ [.trap] ++ rest)) f df)
    (hfrag₂ : fragAdminSeq [.trap] = true) :
    LMatched P host env out ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩
      ⟨s, df, localDceAdminSeq env out (vals vs ++ [.trap] ++ rest)⟩ := by
  have hT : localDceAdminSeq env out (vals vs ++ [.trap] ++ rest) =
      vals vs ++ [.trap] ++ localDceAdminSeq env out rest := by
    simpa [localDceAdmin] using localDceAdminSeq_ctx env out vs [.trap] rest
  have hf' : FrameRel (liveAdminSeq env out [.trap]) f df := by
    simpa [liveAdmin] using hf.mono bot_le
  by_cases hne' : vs ≠ [] ∨ localDceAdminSeq env out rest ≠ []
  · refine LMatched.lock (fd' := df) ?_ hf' hfrag₂
    rw [hT]
    simpa [localDceAdmin] using (Step.trapInstrs (P := P) (host := host) (s := s) (f := df) hne')
  · obtain ⟨hvs, hr⟩ : vs = [] ∧ localDceAdminSeq env out rest = [] := by simpa using hne'
    have hrest : rest ≠ [] := by simpa [hvs] using hne
    have hc : LCode env out [Admin.trap]
        (localDceAdminSeq env out (vals vs ++ [.trap] ++ rest)) := by
      rw [hT, hr, hvs]
      simpa [localDceAdmin, vals] using LCode.clean (env := env) (out := out) [Admin.trap]
    refine LMatched.stutter ⟨rfl, hf', hfrag₂, hc⟩ ?_
    have := codeSize_pos hrest
    simp [hvs, vals, codeSize_cons, adminSize]
    omega

/-- `Step/ctxt-instrs`, from the induction hypothesis for the inner step. -/
theorem clean_ctxtInstrs {s' : Store H} {f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : ∀ {env : List LiveSet} {out : LiveSet} {df : Frame}, fragAdminSeq is = true →
      fragAdminSeq is' = true → FrameRel (liveAdminSeq env out is) f df →
      LMatched P host env out ⟨s, f, is⟩ ⟨s', f', is'⟩ ⟨s, df, localDceAdminSeq env out is⟩)
    (hfrag : fragAdminSeq (vals vs ++ is ++ rest) = true)
    (hfrag₂ : fragAdminSeq (vals vs ++ is' ++ rest) = true)
    (hf : FrameRel (liveAdminSeq env out (vals vs ++ is ++ rest)) f df) :
    LMatched P host env out ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
      ⟨s, df, localDceAdminSeq env out (vals vs ++ is ++ rest)⟩ := by
  have h₁ : fragAdminSeq is = true := by simp_all
  have h₂ : fragAdminSeq is' = true := by simp_all
  have hf' : FrameRel (liveAdminSeq env (liveAdminSeq env out rest) is) f df := by
    simpa [liveAdminSeq_append, liveAdminSeq_vals] using hf
  rw [localDceAdminSeq_ctx]
  exact LMatched.ctx vs rest (ih h₁ h₂ hf') hfrag₂

/-- `Step/ctxt-label`, from the induction hypothesis for the body step. -/
theorem clean_ctxtLabel {s' : Store H} {f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin}
    (ih : ∀ {env : List LiveSet} {out : LiveSet} {df : Frame}, fragAdminSeq is = true →
      fragAdminSeq is' = true → FrameRel (liveAdminSeq env out is) f df →
      LMatched P host env out ⟨s, f, is⟩ ⟨s', f', is'⟩ ⟨s, df, localDceAdminSeq env out is⟩)
    (hfrag : fragAdminSeq [.label n cont is] = true)
    (hfrag₂ : fragAdminSeq [.label n cont is'] = true)
    (hf : FrameRel (liveAdminSeq env out [.label n cont is]) f df) :
    LMatched P host env out ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
      ⟨s, df, localDceAdminSeq env out [.label n cont is]⟩ := by
  have h₁ : fragAdminSeq is = true := by simp_all
  have h₂ : fragAdminSeq is' = true := by simp_all
  have hf' : FrameRel (liveAdminSeq (liveSeq env out cont :: env) out is) f df := by
    simpa [liveAdmin] using hf
  have hm : LMatched P host env out ⟨s, f, vals [] ++ .label n cont is :: []⟩
      ⟨s', f', vals [] ++ .label n cont is' :: []⟩
      ⟨s, df, vals [] ++ .label n (localDceSeq env (liveAdminSeq env out []) cont)
        (localDceAdminSeq (liveSeq env out cont :: env) out is) :: localDceAdminSeq env out []⟩ :=
    LMatched.label [] [] (by simpa using ih h₁ h₂ hf') (by simpa using hfrag₂)
  simpa [localDceAdmin] using hm

/-! ## The simulation -/

/-- **Pass-1 simulation from clean target code**, by induction on the step. -/
theorem localDce_step_sim_clean {c₁ c₂ : Config H} (h : Step P host c₁ c₂)
    (hfrag : fragAdminSeq c₁.code = true) (hfrag₂ : fragAdminSeq c₂.code = true)
    (hf : FrameRel (liveAdminSeq env out c₁.code) c₁.frame df) :
    LMatched P host env out c₁ c₂ ⟨c₁.store, df, localDceAdminSeq env out c₁.code⟩ := by
  induction h generalizing env out df with
  | parametric hp =>
    exact clean_fixed (.parametric hp) (parametric_fixed hp).1 (parametric_fixed hp).2
      (parametric_live hp) hf hfrag₂
  | numeric hp =>
    exact clean_fixed (.numeric hp) (numeric_fixed hp).1 (numeric_fixed hp).2
      (numeric_live hp) hf hfrag₂
  | «variable» hv =>
    cases hv with
    | localGet hl => exact clean_localGet hl hf hfrag₂
    | localSet hx => exact clean_localSet hx hf hfrag₂
    | localTee => exact clean_localTee hf hfrag₂
    | globalGet hg => exact clean_globalGet hg hf hfrag₂
    | globalSet hg => exact clean_globalSet hg hf hfrag₂
  | ctxtInstrs _ _ ih => exact clean_ctxtInstrs ih hfrag hfrag₂ hf
  | ctxtLabel _ ih => exact clean_ctxtLabel ih hfrag hfrag₂ hf
  | block hbt hm => exact clean_block hbt hm hf hfrag₂
  | loop hbt hm => exact clean_loop hbt hm hf hfrag₂
  | ifTrue hc => exact clean_if (.inl rfl) (.ifTrue hc) hf hfrag₂
  | ifFalse => exact clean_if (.inr rfl) .ifFalse hf hfrag₂
  | labelVals => exact clean_labelVals hf hfrag₂
  | brLabelZero hl hn => exact clean_brLabelZero hl hn hf hfrag₂
  | brLabelSucc hl => exact clean_brLabelSucc hl hf hfrag₂
  | brIfTrue hc => exact clean_brIf (.inl rfl) (.brIfTrue hc) hf hfrag₂
  | brIfFalse => exact clean_brIf (.inr rfl) .brIfFalse hf hfrag₂
  | brTableLt hi =>
    exact clean_brTable (.inl (List.mem_of_getElem? hi)) (.brTableLt hi) hf hfrag₂
  | brTableGe hi => exact clean_brTable (.inr rfl) (.brTableGe hi) hf hfrag₂
  | returnLabel => exact clean_returnLabel hf hfrag₂
  | trapInstrs hne => exact clean_trapInstrs hne hf hfrag₂
  | trapLabel => exact clean_trapLabel hf hfrag₂
  | callRefNull hc' => exact absurd hfrag (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefFunc hc' => exact absurd hfrag (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefHost hc' => exact absurd hfrag (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefHostDiv hc' => exact absurd hfrag (by simp [IsCallRef.fragAdmin_eq hc'])
  | returnCallRefLabel hc' => exact absurd hfrag (by simp [IsReturnCallRef.fragAdmin_eq hc'])
  | vector hv => cases hv <;> simp_all [fragInstr]
  | table hv => cases hv <;> simp_all [fragInstr]
  | memory hv => cases hv <;> simp_all [fragInstr]
  | reference hv => cases hv <;> simp_all [fragInstr]
  | aggregate hv => cases hv <;> simp_all [fragInstr]
  | _ => simp_all [fragInstr, throwing]

end Silmaril.Wasm.Dataflow
