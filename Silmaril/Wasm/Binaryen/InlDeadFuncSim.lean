module

public import Silmaril.Wasm.Binaryen.InlDeadFuncFam
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

@[expose] public section

/-! # Appending a dead function: the lockstep simulation

A host-free step of a configuration whose references name existing functions is matched by
the same step of every related configuration (`sim`): related code is equal up to extended
frames, related stores differ only in their function lists, and extended instances resolve
every existing index to the same address.
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile}

/-! ## Helpers -/

theorem blockType?_mext (a : ModuleInst) (l : List Nat) (bt : BlockType) :
    (mext a l).blockType? bt = a.blockType? bt := by
  cases bt <;> rfl

theorem instRef_mext (a : ModuleInst) (l : List Nat) (rt : RefType) :
    (mext a l).instRef rt = a.instRef rt := rfl

theorem retToCallIn_mext (a : ModuleInst) (l : List Nat) (c : Admin) :
    c.retToCallIn (mext a l) = c.retToCallIn a := rfl

theorem catchMatches_ext (s : Store H) (X : List (FuncInst H)) (f : Frame) (l : List Nat)
    (a : Nat) (c : Catch) : CatchMatches (withFuncs s X) (fext f l) a c ↔ CatchMatches s f a c := by
  cases c <;> exact Iff.rfl

theorem rel_inv {s : Store H} {f : Frame} {is : List Admin} {c' : Config H}
    (h : Rel ⟨s, f, is⟩ c') :
    ∃ X l code', c' = ⟨withFuncs s X, fext f l, code'⟩ ∧ FL s.funcs X ∧ CRel is code' := by
  obtain ⟨⟨X, hX, hfl⟩, ⟨l, hl⟩, hc⟩ := h
  obtain ⟨t, g, code'⟩ := c'
  simp only at hX hl hc
  subst hX hl
  exact ⟨X, l, code', rfl, hfl, hc⟩

theorem rel_mk {s : Store H} {f : Frame} {is is' : List Admin} {X : List (FuncInst H)}
    {l : List Nat} (hX : FL s.funcs X) (hc : CRel is is') :
    Rel ⟨s, f, is⟩ ⟨withFuncs s X, fext f l, is'⟩ :=
  ⟨⟨X, rfl, hX⟩, ⟨l, rfl⟩, hc⟩

theorem CRel.nil_right : ∀ {xs : List Admin}, CRel xs [] → xs = []
  | _, .nil => rfl

theorem ne_nil_of_crel {xs ys : List Admin} (h : CRel xs ys) (hne : xs ≠ []) : ys ≠ [] := by
  rintro rfl
  exact hne (CRel.nil_right h)

theorem isFlat_of_fam {e : Admin} (h : Det.famOf e ≠ .control) : isFlat e = true := by
  cases e with
  | plain i => rfl
  | _ => exact absurd rfl h

theorem flat_shape {k : Det.Fam} {l : List Admin} (h : Det.FamShape k l) (hk : k ≠ .control) :
    ∀ x ∈ l, isFlat x = true := by
  obtain ⟨args, e, rfl, -, he⟩ := h
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact flat_vals args x hx
  · rw [List.mem_singleton] at hx
    subst hx
    exact isFlat_of_fam (by rw [he]; exact hk)

theorem flat_step {s : Store H} {f : Frame} {is is' code' : List Admin} (X : List (FuncInst H))
    (l : List Nat) (hX : FL s.funcs X) (hc : CRel is code') (hflat : ∀ x ∈ is, isFlat x = true)
    (hst : Step P Det.noHost ⟨withFuncs s X, fext f l, is⟩ ⟨withFuncs s X, fext f l, is'⟩) :
    ∃ d', Step P Det.noHost ⟨withFuncs s X, fext f l, code'⟩ d' ∧ Rel ⟨s, f, is'⟩ d' := by
  rw [CRel.eq_of_flat hc hflat]
  exact ⟨_, hst, rel_mk hX (CRel.refl _)⟩

macro "flat_tac" : tactic =>
  `(tactic| (refine allFlat_iff.1 ?_; simp))

/-! ## One step -/

set_option maxHeartbeats 800000 in
/-- **One host-free step**, matched by the same step. -/
theorem sim {c d : Config H} (h : Step P Det.noHost c d) :
    ∀ {c' : Config H}, RefsIn c.store.funcs.length c.code → Rel c c' →
      ∃ d', Step P Det.noHost c' d' ∧ Rel d d' := by
  induction h with
  | parametric h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (flat_shape (Det.ParametricStep.shape h) (by decide)) (.parametric h)
  | numeric h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (flat_shape (Det.NumericStep.shape h) (by decide)) (.numeric h)
  | vector h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (flat_shape (Det.VectorStep.shape h) (by decide)) (.vector h)
  | @«variable» c₁ c₂ h =>
    obtain ⟨s, f, is⟩ := c₁
    obtain ⟨s₂, f₂, is₂⟩ := c₂
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (flat_shape (Det.VariableStep.shape h) (by decide))]
    obtain ⟨hfs, -, hst⟩ := variableStep_ext h X l
    exact ⟨_, .variable hst, ⟨X, rfl, by rw [hfs]; exact hX⟩, ⟨l, rfl⟩, CRel.refl _⟩
  | @table c₁ c₂ h =>
    obtain ⟨s, f, is⟩ := c₁
    obtain ⟨s₂, f₂, is₂⟩ := c₂
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (flat_shape (Det.TableStep.shape h) (by decide))]
    obtain ⟨hfs, rfl, hst⟩ := tableStep_ext h X l
    exact ⟨_, .table hst, ⟨X, rfl, by rw [hfs]; exact hX⟩, ⟨l, rfl⟩, CRel.refl _⟩
  | @memory c₁ c₂ h =>
    obtain ⟨s, f, is⟩ := c₁
    obtain ⟨s₂, f₂, is₂⟩ := c₂
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (flat_shape (Det.MemoryStep.shape h) (by decide))]
    obtain ⟨hfs, rfl, hst⟩ := memoryStep_ext h X l
    exact ⟨_, .memory hst, ⟨X, rfl, by rw [hfs]; exact hX⟩, ⟨l, rfl⟩, CRel.refl _⟩
  | @reference c₁ c₂ h =>
    obtain ⟨s, f, is⟩ := c₁
    obtain ⟨s₂, f₂, is₂⟩ := c₂
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (flat_shape (Det.RefStep.shape h) (by decide))]
    obtain ⟨rfl, rfl, hst⟩ := refStep_ext h hX hin l
    exact ⟨_, .reference hst, rel_mk hX (CRel.refl _)⟩
  | @aggregate c₁ c₂ h =>
    obtain ⟨s, f, is⟩ := c₁
    obtain ⟨s₂, f₂, is₂⟩ := c₂
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (flat_shape (Det.AggregateStep.shape h) (by decide))]
    obtain ⟨hfs, rfl, hst⟩ := aggregateStep_ext h X l
    exact ⟨_, .aggregate hst, ⟨X, rfl, by rw [hfs]; exact hX⟩, ⟨l, rfl⟩, CRel.refl _⟩
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨y₁, y₃, rfl, h₁, h₃⟩ := CRel.split hc
    obtain ⟨y₂, rfl, h₂⟩ := CRel.flat_append h₁ (flat_vals vs)
    obtain ⟨⟨t', g', z⟩, hst, hrel⟩ :=
      ih (hin.mono fun a ha => by simp [ha]) (rel_mk (l := l) hX h₂)
    refine ⟨⟨t', g', vals vs ++ z ++ y₃⟩, .ctxtInstrs hst ?_, hrel.1, hrel.2.1,
      CRel.append (CRel.append (CRel.refl _) hrel.2.2) h₃⟩
    rcases hne with hne | hne
    · exact .inl hne
    · exact .inr (ne_nil_of_crel h₃ hne)
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    obtain ⟨⟨t', g', z⟩, hst, hrel⟩ := ih hin.label (rel_mk (l := l) hX hb)
    exact ⟨_, .ctxtLabel hst, hrel.1, hrel.2.1, .cons (.label hrel.2.2) .nil⟩
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    obtain ⟨⟨t', g', z⟩, hst, hrel⟩ := ih hin.handler (rel_mk (l := l) hX hb)
    exact ⟨_, .ctxtHandler hst, hrel.1, hrel.2.1, .cons (.handler hrel.2.2) .nil⟩
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, ⟨l₁, rfl⟩, hb⟩ := CRel.frame_inv hc
    obtain ⟨⟨t', g', z⟩, hst, hrel⟩ := ih hin.frame (rel_mk (l := l₁) hX hb)
    exact ⟨_, .ctxtFrame hst, hrel.1, ⟨l, rfl⟩, .cons (.frame hrel.2.1 hrel.2.2) .nil⟩
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have hbt' : (fext f l).module.blockType? bt = some (t₁, t₂) := by
      rw [fext_module, blockType?_mext]; exact hbt
    exact flat_step X l hX hc (by flat_tac) (.block hbt' hm)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have hbt' : (fext f l).module.blockType? bt = some (t₁, t₂) := by
      rw [fext_module, blockType?_mext]; exact hbt
    exact flat_step X l hX hc (by flat_tac) (.loop hbt' hm)
  | ifTrue hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.ifTrue hc0)
  | ifFalse =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .ifFalse
  | labelVals =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    rw [CRel.vals_inv hb]
    exact ⟨_, .labelVals, rel_mk hX (CRel.refl _)⟩
  | brLabelZero hl hn =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .brLabelZero hl hn, rel_mk hX (CRel.refl _)⟩
  | brLabelSucc hl =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .brLabelSucc hl, rel_mk hX (CRel.refl _)⟩
  | brHandler =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .brHandler, rel_mk hX (CRel.refl _)⟩
  | brIfTrue hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.brIfTrue hc0)
  | brIfFalse =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .brIfFalse
  | brTableLt hi =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.brTableLt hi)
  | brTableGe hi =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.brTableGe hi)
  | brOnNullNull =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .brOnNullNull
  | brOnNullAddr hv =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.brOnNullAddr hv)
  | brOnNonNullNull =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .brOnNonNullNull
  | brOnNonNullAddr hv =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) (.brOnNonNullAddr hv)
  | @brOnCastSucceed s f r l₀ rt₁ rt₂ h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have h' : RefOk (withFuncs s X) r ((fext f l).module.instRef rt₂) := refOk_fl hX h
    exact flat_step X l hX hc (by flat_tac) (.brOnCastSucceed h')
  | @brOnCastFail s f r l₀ rt₁ rt₂ h =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have h' : ¬ RefOk (withFuncs s X) r ((fext f l).module.instRef rt₂) := fun h' =>
      h ((refOk_fl_iff hX (hin.ref (by simp))).1 h')
    exact flat_step X l hX hc (by flat_tac) (.brOnCastFail h')
  | @brOnCastFailSucceed s f r l₀ rt₁ rt₂ h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have h' : RefOk (withFuncs s X) r ((fext f l).module.instRef rt₂) := refOk_fl hX h
    exact flat_step X l hX hc (by flat_tac) (.brOnCastFailSucceed h')
  | @brOnCastFailFail s f r l₀ rt₁ rt₂ h =>
    intro c' hin hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have h' : ¬ RefOk (withFuncs s X) r ((fext f l).module.instRef rt₂) := fun h' =>
      h ((refOk_fl_iff hX (hin.ref (by simp))).1 h')
    exact flat_step X l hX hc (by flat_tac) (.brOnCastFailFail h')
  | @call s f x a fi hx hf =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (by flat_tac)]
    obtain ⟨fi', h1, h2⟩ := hX.get hf
    refine ⟨_, .call (mext_funcs_get hx) h1, rel_mk hX ?_⟩
    rw [h2.type]
    exact CRel.refl _
  | callRefNull hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (allFlat_iff.1 (by simp [isFlat_of_isCallRef hc0])) (.callRefNull hc0)
  | @callRefFunc s f c vs a fi ps rs code hc0 hf he hn hcode =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (allFlat_iff.1 (by simp [isFlat_of_isCallRef hc0]))]
    obtain ⟨fi', h1, h2⟩ := hX.get hf
    obtain ⟨l', hl'⟩ := h2.module
    refine ⟨_, .callRefFunc hc0 h1 (by rw [h2.type]; exact he) hn (by rw [h2.code]; exact hcode),
      rel_mk hX ?_⟩
    rw [hl']
    exact .cons (.frame ⟨l', rfl⟩ (CRel.refl _)) .nil
  | callRefHost _ _ _ _ _ hhost => exact (hhost : False).elim
  | callRefHostDiv _ _ _ _ _ hhost => exact (hhost : False).elim
  | @returnCall s f x a fi hx hf =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (by flat_tac)]
    obtain ⟨fi', h1, h2⟩ := hX.get hf
    refine ⟨_, .returnCall (mext_funcs_get hx) h1, rel_mk hX ?_⟩
    rw [h2.type]
    exact CRel.refl _
  | returnCallRefLabel hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    obtain ⟨rest', rfl, -⟩ :=
      CRel.flat_append hb (allFlat_iff.1 (by simp [isFlat_of_isReturnCallRef hc0]))
    exact ⟨_, .returnCallRefLabel hc0, rel_mk hX (CRel.refl _)⟩
  | returnCallRefHandler hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    obtain ⟨rest', rfl, -⟩ :=
      CRel.flat_append hb (allFlat_iff.1 (by simp [isFlat_of_isReturnCallRef hc0]))
    exact ⟨_, .returnCallRefHandler hc0, rel_mk hX (CRel.refl _)⟩
  | returnCallRefFrameNull hc0 =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, -, hb⟩ := CRel.frame_inv hc
    obtain ⟨rest', rfl, -⟩ :=
      CRel.flat_append hb (allFlat_iff.1 (by simp [isFlat_of_isReturnCallRef hc0]))
    exact ⟨_, .returnCallRefFrameNull hc0, rel_mk hX (CRel.refl _)⟩
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hc0 hf he hn =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, ⟨l₁, rfl⟩, hb⟩ := CRel.frame_inv hc
    obtain ⟨rest', rfl, -⟩ :=
      CRel.flat_append hb (allFlat_iff.1 (by simp [isFlat_of_isReturnCallRef hc0]))
    obtain ⟨fn', h1, h2⟩ := hX.get hf
    refine ⟨_, .returnCallRefFrameAddr hc0 h1 (by rw [h2.type]; exact he) hn, rel_mk hX ?_⟩
    rw [fext_module, retToCallIn_mext]
    exact CRel.refl _
  | callIndirect =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .callIndirect
  | returnCallIndirect =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .returnCallIndirect
  | frameVals hn =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, -, hb⟩ := CRel.frame_inv hc
    rw [CRel.vals_inv hb]
    exact ⟨_, .frameVals hn, rel_mk hX (CRel.refl _)⟩
  | returnFrame hn =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, -, hb⟩ := CRel.frame_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .returnFrame hn, rel_mk hX (CRel.refl _)⟩
  | returnLabel =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .returnLabel, rel_mk hX (CRel.refl _)⟩
  | returnHandler =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    obtain ⟨rest', rfl, -⟩ := CRel.flat_append hb (by flat_tac)
    exact ⟨_, .returnHandler, rel_mk hX (CRel.refl _)⟩
  | throw ht he hn =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    rw [CRel.eq_of_flat hc (by flat_tac)]
    exact ⟨_, .throw ht he hn, ⟨X, rfl, hX⟩, ⟨l, rfl⟩, CRel.refl _⟩
  | throwRefNull =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    exact flat_step X l hX hc (by flat_tac) .throwRefNull
  | throwRefInstrs hne =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨rest', rfl, hr⟩ := CRel.flat_append hc (by flat_tac)
    refine ⟨_, .throwRefInstrs ?_, rel_mk hX (CRel.refl _)⟩
    rcases hne with hne | hne
    · exact .inl hne
    · exact .inr (ne_nil_of_crel hr hne)
  | throwRefLabel =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefLabel, rel_mk hX (CRel.refl _)⟩
  | throwRefFrame =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, -, hb⟩ := CRel.frame_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefFrame, rel_mk hX (CRel.refl _)⟩
  | throwRefHandlerEmpty =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerEmpty, rel_mk hX (CRel.refl _)⟩
  | throwRefHandlerCatch he ht =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerCatch he ht, rel_mk hX (CRel.refl _)⟩
  | throwRefHandlerCatchRef he ht =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerCatchRef he ht, rel_mk hX (CRel.refl _)⟩
  | throwRefHandlerCatchAll =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerCatchAll, rel_mk hX (CRel.refl _)⟩
  | throwRefHandlerCatchAllRef =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerCatchAllRef, rel_mk hX (CRel.refl _)⟩
  | @throwRefHandlerNext s f n c cs a h =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .throwRefHandlerNext fun h' => h ((catchMatches_ext s X f l a c).1 h'),
      rel_mk hX (CRel.refl _)⟩
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    have hbt' : (fext f l).module.blockType? bt = some (t₁, t₂) := by
      rw [fext_module, blockType?_mext]; exact hbt
    exact flat_step X l hX hc (by flat_tac) (.tryTable hbt' hm)
  | handlerVals =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.vals_inv hb]
    exact ⟨_, .handlerVals, rel_mk hX (CRel.refl _)⟩
  | trapInstrs hne =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨rest', rfl, hr⟩ := CRel.flat_append hc (by flat_tac)
    refine ⟨_, .trapInstrs ?_, rel_mk hX (CRel.refl _)⟩
    rcases hne with hne | hne
    · exact .inl hne
    · exact .inr (ne_nil_of_crel hr hne)
  | trapLabel =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.label_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .trapLabel, rel_mk hX (CRel.refl _)⟩
  | trapHandler =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨b', rfl, hb⟩ := CRel.handler_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .trapHandler, rel_mk hX (CRel.refl _)⟩
  | trapFrame =>
    intro c' _ hR
    obtain ⟨X, l, code', rfl, hX, hc⟩ := rel_inv hR
    obtain ⟨fi₁, b', rfl, -, hb⟩ := CRel.frame_inv hc
    rw [CRel.eq_of_flat hb (by flat_tac)]
    exact ⟨_, .trapFrame, rel_mk hX (CRel.refl _)⟩

/-! ## Results -/

/-- Related results are equal. -/
theorem Rel.result {c c' : Config H} {r : Result} (h : Rel c c') (hr : c.code = r.toAdmin) :
    c'.code = r.toAdmin := by
  have hc := h.2.2
  rw [hr] at hc
  refine CRel.eq_of_flat hc ?_
  cases r <;> exact allFlat_iff.1 (by simp [Result.toAdmin])

theorem Rel.result' {c c' : Config H} {r : Result} (h : Rel c c') (hr : c'.code = r.toAdmin) :
    c.code = r.toAdmin := by
  have hc := h.2.2
  rw [hr] at hc
  cases r with
  | values vs => exact (CRel.eq_of_flat' hc (flat_vals vs)).symm
  | trap => exact (CRel.eq_of_flat' hc (allFlat_iff.1 (by simp [Result.toAdmin]))).symm
  | throw a => exact (CRel.eq_of_flat' hc (allFlat_iff.1 (by simp [Result.toAdmin]))).symm

end Silmaril.Wasm.Binaryen.InlDF
