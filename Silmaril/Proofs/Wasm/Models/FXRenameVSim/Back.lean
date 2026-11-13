module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.Inv

/-!
# Exception renaming for `StepFX'`: the backward simulation, one step

`Bwd P n d₀ d` says that the step `d₀ → d` (of a target configuration) is, whenever `d₀` is a
renamed configuration of some `⟨s, K, f, code⟩` (an `ExnRen n` store, a `KRn n` continuation
store, the renamed frame and code), the renamed image of a step of `⟨s, K, f, code⟩`.
**`stepV_rn_back`**: every host-free `StepFX'` step without FX functions has this property.
Each rule is one lemma (`bwd_*`): the target code, written as the rule's shape, is read back
(`Silmaril.Proofs.Wasm.Models.FXRenameVSim.Inv`), the side conditions are pulled back to the
source store (`resolve_rn`, `tag?_rn`, `kRn_some_back`, …), and the source takes the same rule.
The `core` rule is the Core backward renaming `step_rn_back`; the context rules use the
induction hypothesis.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV Silmaril.Wasm.Models.FXRenameVSim
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {n : Nat}

/-- **A target step is the renamed image of a source step.** -/
def Bwd (P : Profile) (n : Nat) (d₀ d : ConfigFX H) : Prop :=
  ∀ {s : Store H} {K : List (Option ContFX)} {f : Frame} {code : List AdminFX},
    ExnRen n s d₀.store → KRn n K d₀.conts → d₀.frame = rnFrame n f → d₀.code = rnL n code →
    ∃ (c' : ConfigFX H) (t' : Store H) (K₂' : List (Option ContFX)),
      StepFX' P noHost noFX ⟨s, K, f, code⟩ c' ∧ d = rnCfgV n c' t' K₂' ∧
      ExnRen n c'.store t' ∧ KRn n c'.conts K₂'

variable {t t' : Store H} {K₂ K₂' : List (Option ContFX)} {f₀ f₀' fi fi' : Frame}
  {vs vs' : List FVal} {es es' rest : List AdminFX} {m : Nat} {k : List InstrFX}

/-- A step that keeps both stores and the frame, read back with both stores kept. -/
theorem bwd_pure {code₀ code₀' : List AdminFX}
    (hinv : ∀ {s : Store H} {K : List (Option ContFX)} {f : Frame} {code : List AdminFX},
      ExnRen n s t → KRn n K K₂ → f₀ = rnFrame n f → code₀ = rnL n code →
      ∃ code', StepFX' P noHost noFX ⟨s, K, f, code⟩ ⟨s, K, f, code'⟩ ∧ code₀' = rnL n code') :
    Bwd P n ⟨t, K₂, f₀, code₀⟩ ⟨t, K₂, f₀, code₀'⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨code', hst, hc'⟩ := hinv h hK hf hc
  have hf' : f₀ = rnFrame n f := hf
  exact ⟨⟨s, K, f, code'⟩, t, K₂, hst, by rw [hf', hc'], h, hK⟩

theorem bwd_core {cs cs' : List Admin}
    (hs : Step P (blockFX noHost noFX) ⟨t, f₀, cs⟩ ⟨t', f₀', cs'⟩) :
    Bwd P n ⟨t, K₂, f₀, cs.map .core⟩ ⟨t', K₂, f₀', cs'.map .core⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨cs₀, rfl, hcs⟩ := rnL_eq_map_core_iff.mp hc.symm
  have h₀ : Step P noHost ⟨t, rnFrame n f, rnAdmins n cs₀⟩ ⟨t', f₀', cs'⟩ := by
    rw [← hf, hcs, ← blockFX_noHost']; exact hs
  obtain ⟨c', t'', hst, hd, ht''⟩ :=
    Silmaril.Wasm.Models.FXRenameSim.step_rn_back (c := ⟨s, f, cs₀⟩) h h₀
  have hst' : Step P (blockFX noHost noFX) ⟨s, f, cs₀⟩ c' := by rw [blockFX_noHost']; exact hst
  refine ⟨⟨c'.store, K, c'.frame, c'.code.map .core⟩, t'', K₂, .core hst', ?_, ht'', hK⟩
  have hd' : t' = t'' ∧ f₀' = rnFrame n c'.frame ∧ cs' = rnAdmins n c'.code := by
    simpa only [Config.mk.injEq] using hd
  rw [hd'.1, hd'.2.1, hd'.2.2]
  simp only [rnCfgV, rnL_map_core']

theorem bwd_seq (ih : Bwd P n ⟨t, K₂, f₀, es⟩ ⟨t', K₂', f₀', es'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ es ++ rest⟩ ⟨t', K₂', f₀', fvals vs ++ es' ++ rest⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨L₁, R₀, rfl, h₁, hR⟩ := inv_app hc
  obtain ⟨vs₀, E₀, rfl, rfl, hE⟩ := inv_fv_app h₁
  obtain ⟨⟨s', K', f', es₀'⟩, t'', K₂'', hst, hd, ht'', hK''⟩ := ih h hK hf hE
  have hne' : vs₀ ≠ [] ∨ R₀ ≠ [] := by
    simpa only [map_rnFV_ne_nil, hR, ne_eq, rnL_eq_nil_iff] using hne
  refine ⟨⟨s', K', f', fvals vs₀ ++ es₀' ++ R₀⟩, t'', K₂'', .seq hst hne', ?_, ht'', hK''⟩
  have hd' : t' = t'' ∧ K₂' = K₂'' ∧ f₀' = rnFrame n f' ∧ es' = rnL n es₀' := by
    simpa only [rnCfgV, ConfigFX.mk.injEq] using hd
  rw [hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2, hR]
  simp only [rnCfgV, rnL_append, rnL_fvals]

theorem bwd_ctxLabel (ih : Bwd P n ⟨t, K₂, f₀, es⟩ ⟨t', K₂', f₀', es'⟩) :
    Bwd P n ⟨t, K₂, f₀, [.label m k es]⟩ ⟨t', K₂', f₀', [.label m k es']⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨B₀, rfl, hB⟩ := inv_label hc
  obtain ⟨⟨s', K', f', es₀'⟩, t'', K₂'', hst, hd, ht'', hK''⟩ := ih h hK hf hB
  refine ⟨⟨s', K', f', [.label m k es₀']⟩, t'', K₂'', .ctxLabel hst, ?_, ht'', hK''⟩
  have hd' : t' = t'' ∧ K₂' = K₂'' ∧ f₀' = rnFrame n f' ∧ es' = rnL n es₀' := by
    simpa only [rnCfgV, ConfigFX.mk.injEq] using hd
  rw [hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2]
  simp only [rnCfgV, rnL_cons, rnL_nil, rnA_label]

theorem bwd_ctxFrame (ih : Bwd P n ⟨t, K₂, fi, es⟩ ⟨t', K₂', fi', es'⟩) :
    Bwd P n ⟨t, K₂, f₀, [.frame m fi es]⟩ ⟨t', K₂', f₀, [.frame m fi' es']⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨fi₀, B₀, rfl, hfi, hB⟩ := inv_frame hc
  obtain ⟨⟨s', K', f', es₀'⟩, t'', K₂'', hst, hd, ht'', hK''⟩ := ih h hK hfi hB
  refine ⟨⟨s', K', f, [.frame m f' es₀']⟩, t'', K₂'', .ctxFrame hst, ?_, ht'', hK''⟩
  have hd' : t' = t'' ∧ K₂' = K₂'' ∧ fi' = rnFrame n f' ∧ es' = rnL n es₀' := by
    simpa only [rnCfgV, ConfigFX.mk.injEq] using hd
  rw [hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2, show f₀ = rnFrame n f from hf]
  simp only [rnCfgV, rnL_cons, rnL_nil, rnA_frame]

theorem bwd_ctxHandler {hs : List HClause} (ih : Bwd P n ⟨t, K₂, f₀, es⟩ ⟨t', K₂', f₀', es'⟩) :
    Bwd P n ⟨t, K₂, f₀, [.handler hs es]⟩ ⟨t', K₂', f₀', [.handler hs es']⟩ := by
  intro s K f code h hK hf hc
  obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
  obtain ⟨⟨s', K', f', es₀'⟩, t'', K₂'', hst, hd, ht'', hK''⟩ := ih h hK hf hB
  refine ⟨⟨s', K', f', [.handler hs es₀']⟩, t'', K₂'', .ctxHandler hst, ?_, ht'', hK''⟩
  have hd' : t' = t'' ∧ K₂' = K₂'' ∧ f₀' = rnFrame n f' ∧ es' = rnL n es₀' := by
    simpa only [rnCfgV, ConfigFX.mk.injEq] using hd
  rw [hd'.1, hd'.2.1, hd'.2.2.1, hd'.2.2.2]
  simp only [rnCfgV, rnL_cons, rnL_nil, rnA_handler]

/-! ## Rules that keep both stores -/

theorem bwd_block {bt : BlockType} {body : List InstrFX} {t₁ t₂ : List CValType}
    (hbt : f₀.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.block bt body]⟩
      ⟨t, K₂, f₀, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩ :=
  bwd_pure fun _ _ hf hc => by
    obtain ⟨vs₀, a₀, rfl, rfl, ha⟩ := inv_fv_one hc
    obtain rfl := inv_block ha
    subst hf
    exact ⟨_, .block hbt (by simpa using hm), by simp⟩

theorem bwd_loop {bt : BlockType} {body : List InstrFX} {t₁ t₂ : List CValType}
    (hbt : f₀.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.loop bt body]⟩
      ⟨t, K₂, f₀, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩ :=
  bwd_pure fun _ _ hf hc => by
    obtain ⟨vs₀, a₀, rfl, rfl, ha⟩ := inv_fv_one hc
    obtain rfl := inv_loop ha
    subst hf
    exact ⟨_, .loop hbt (by simpa using hm), by simp⟩

theorem bwd_ifTrue {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List InstrFX} (hc0 : c ≠ 0) :
    Bwd P n ⟨t, K₂, f₀, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨t, K₂, f₀, [.block bt b₁]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two hc
    obtain rfl := inv_const ha
    obtain rfl := inv_if hc'
    exact ⟨_, .ifTrue hc0, by simp⟩

theorem bwd_ifFalse {bt : BlockType} {b₁ b₂ : List InstrFX} :
    Bwd P n ⟨t, K₂, f₀, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨t, K₂, f₀, [.block bt b₂]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two hc
    obtain rfl := inv_const ha
    obtain rfl := inv_if hc'
    exact ⟨_, .ifFalse, by simp⟩

theorem bwd_labelVals : Bwd P n ⟨t, K₂, f₀, [.label m k (fvals vs)]⟩ ⟨t, K₂, f₀, fvals vs⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨vs₀, rfl, rfl⟩ := inv_fv hB
    exact ⟨_, .labelVals, by simp⟩

theorem bwd_brLabelZero {l : LabelIdx} (hl : l.toNat = 0) (hn : vs.length = m) :
    Bwd P n ⟨t, K₂, f₀, [.label m k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs ++ k.map InstrFX.toAdmin⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨L₁, R₀, rfl, h₁, -⟩ := inv_app hB
    obtain ⟨L₂, L₃, rfl, h₂, h₃⟩ := inv_app h₁
    obtain ⟨L₄, L₅, rfl, h₄, h₅⟩ := inv_app h₂
    obtain ⟨vs'₀, rfl, rfl⟩ := inv_fv h₄
    obtain ⟨vs₀, rfl, rfl⟩ := inv_fv h₅
    obtain ⟨a₀, rfl, ha⟩ := inv_one h₃
    obtain rfl := inv_plain ha
    exact ⟨_, .brLabelZero hl (by simpa using hn), by simp⟩

theorem bwd_brLabelSucc {l : LabelIdx} (hl : 0 < l.toNat) :
    Bwd P n ⟨t, K₂, f₀, [.label m k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, ha, -⟩ := inv_fv_one_app hB
    obtain rfl := inv_plain ha
    exact ⟨_, .brLabelSucc hl, by simp⟩

theorem bwd_brHandler {hs : List HClause} {l : LabelIdx} :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs ++ [.core (.plain (.br l))]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, ha, -⟩ := inv_fv_one_app hB
    obtain rfl := inv_plain ha
    exact ⟨_, .brHandler, by simp⟩

theorem bwd_returnLabel :
    Bwd P n ⟨t, K₂, f₀, [.label m k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs ++ [.core (.plain .return_)]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, ha, -⟩ := inv_fv_one_app hB
    obtain rfl := inv_plain ha
    exact ⟨_, .returnLabel, by simp⟩

theorem bwd_returnHandler {hs : List HClause} :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs ++ [.core (.plain .return_)]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, ha, -⟩ := inv_fv_one_app hB
    obtain rfl := inv_plain ha
    exact ⟨_, .returnHandler, by simp⟩

theorem bwd_frameVals (hn : vs.length = m) :
    Bwd P n ⟨t, K₂, f₀, [.frame m fi (fvals vs)]⟩ ⟨t, K₂, f₀, fvals vs⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨fi₀, B₀, rfl, -, hB⟩ := inv_frame hc
    obtain ⟨vs₀, rfl, rfl⟩ := inv_fv hB
    exact ⟨_, .frameVals (by simpa using hn), by simp⟩

theorem bwd_returnFrame (hn : vs.length = m) :
    Bwd P n ⟨t, K₂, f₀,
        [.frame m fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
      ⟨t, K₂, f₀, fvals vs⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨fi₀, B₀, rfl, -, hB⟩ := inv_frame hc
    obtain ⟨L₁, R₀, rfl, h₁, -⟩ := inv_app hB
    obtain ⟨L₂, L₃, rfl, h₂, h₃⟩ := inv_app h₁
    obtain ⟨L₄, L₅, rfl, h₄, h₅⟩ := inv_app h₂
    obtain ⟨vs'₀, rfl, rfl⟩ := inv_fv h₄
    obtain ⟨vs₀, rfl, rfl⟩ := inv_fv h₅
    obtain ⟨a₀, rfl, ha⟩ := inv_one h₃
    obtain rfl := inv_plain ha
    exact ⟨_, .returnFrame (by simpa using hn), by simp⟩

theorem bwd_handlerVals {hs : List HClause} :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (fvals vs)]⟩ ⟨t, K₂, f₀, fvals vs⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
    obtain ⟨vs₀, rfl, rfl⟩ := inv_fv hB
    exact ⟨_, .handlerVals, by simp⟩

theorem bwd_dropCont {kk : Nat} :
    Bwd P n ⟨t, K₂, f₀, [.contRef kk, .core (.plain .drop)]⟩ ⟨t, K₂, f₀, []⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two hc
    obtain rfl := inv_contRef ha
    obtain rfl := inv_plain hc'
    exact ⟨_, .dropCont, by simp⟩

theorem bwd_trapSeq (hne : vs ≠ [] ∨ rest ≠ []) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.core .trap] ++ rest⟩ ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, ha, rfl⟩ := inv_fv_one_app hc
    obtain rfl := inv_trap ha
    exact ⟨_, .trapSeq (by simpa using hne), by simp⟩

theorem bwd_trapLabel :
    Bwd P n ⟨t, K₂, f₀, [.label m k [.core .trap]]⟩ ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨a₀, rfl, ha⟩ := inv_one hB
    obtain rfl := inv_trap ha
    exact ⟨_, .trapLabel, by simp⟩

theorem bwd_trapFrame :
    Bwd P n ⟨t, K₂, f₀, [.frame m fi [.core .trap]]⟩ ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨fi₀, B₀, rfl, -, hB⟩ := inv_frame hc
    obtain ⟨a₀, rfl, ha⟩ := inv_one hB
    obtain rfl := inv_trap ha
    exact ⟨_, .trapFrame, by simp⟩

theorem bwd_trapHandler {hs : List HClause} :
    Bwd P n ⟨t, K₂, f₀, [.handler hs [.core .trap]]⟩ ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
    obtain ⟨a₀, rfl, ha⟩ := inv_one hB
    obtain rfl := inv_trap ha
    exact ⟨_, .trapHandler, by simp⟩

theorem bwd_throwSeq {b : Nat} (hne : vs ≠ [] ∨ rest ≠ []) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ cthrowing b ++ rest⟩ ⟨t, K₂, f₀, cthrowing b⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨vs₀, a₀, R₀, rfl, rfl, rfl, rfl⟩ := inv_fv_throw_app hc
    exact ⟨_, .throwSeq (by simpa using hne), by simp⟩

theorem bwd_throwLabel {b : Nat} :
    Bwd P n ⟨t, K₂, f₀, [.label m k (cthrowing b)]⟩ ⟨t, K₂, f₀, cthrowing b⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_label hc
    obtain ⟨a₀, rfl, rfl⟩ := inv_cthrowing hB
    exact ⟨_, .throwLabel, by simp⟩

theorem bwd_throwFrame {b : Nat} :
    Bwd P n ⟨t, K₂, f₀, [.frame m fi (cthrowing b)]⟩ ⟨t, K₂, f₀, cthrowing b⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨fi₀, B₀, rfl, -, hB⟩ := inv_frame hc
    obtain ⟨a₀, rfl, rfl⟩ := inv_cthrowing hB
    exact ⟨_, .throwFrame, by simp⟩

theorem bwd_throwHandler {hs : List HClause} {b : Nat} :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (cthrowing b)]⟩ ⟨t, K₂, f₀, cthrowing b⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨B₀, rfl, hB⟩ := inv_handler hc
    obtain ⟨a₀, rfl, rfl⟩ := inv_cthrowing hB
    exact ⟨_, .throwHandler, by simp⟩

theorem bwd_contNewNull {ct : TypeIdx} :
    Bwd P n ⟨t, K₂, f₀, [.core (.ref .null), .fx (.contNew ct)]⟩ ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two hc
    obtain rfl := inv_refNull ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .contNewNull, by simp⟩

theorem bwd_contBindNull {ct ct' : TypeIdx} :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
      ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
    obtain rfl := inv_refNull ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .contBindNull, by simp⟩

theorem bwd_contBindUsed {kk : Nat} {ct ct' : TypeIdx} (hk : K₂[kk]? = some none) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.contRef kk, .fx (.contBind ct ct')]⟩
      ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ hK _ hc => by
    obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
    obtain rfl := inv_contRef ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .contBindUsed (kRn_none_back hK hk), by simp⟩

theorem bwd_resumeNull {ct : TypeIdx} {hs : List OnClause} :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
      ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
    obtain rfl := inv_refNull ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .resumeNull, by simp⟩

theorem bwd_resumeUsed {kk : Nat} {ct : TypeIdx} {hs : List OnClause} (hk : K₂[kk]? = some none) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.contRef kk, .fx (.resume ct hs)]⟩
      ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ hK _ hc => by
    obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
    obtain rfl := inv_contRef ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .resumeUsed (kRn_none_back hK hk), by simp⟩

theorem bwd_resumeThrowNull {ws : List Val} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
    Bwd P n ⟨t, K₂, f₀, cvals ws ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
      ⟨t, K₂, f₀, [.core .trap]⟩ :=
  bwd_pure fun _ _ _ hc => by
    obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := inv_app hc
    obtain ⟨ws₀, rfl, rfl⟩ := inv_cv h₁
    obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two h₂
    obtain rfl := inv_refNull ha
    obtain rfl := inv_fx hc'
    exact ⟨_, .resumeThrowNull, by simp⟩

end Silmaril.Proofs.Wasm.Models.FXRenameVSim
