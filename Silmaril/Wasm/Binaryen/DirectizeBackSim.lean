module

public import Silmaril.Wasm.Binaryen.DirectizeStable

@[expose] public section

/-! # Directize: matching a chosen target step

Numerical results are transported from the actual chosen step. No uniqueness or
deterministic-profile theorem is used.
-/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile}

def Res (ok : SiteOk) (mi : ModuleInst) (P : Numerics.Profile) (c d' : Config H) : Prop :=
  ∃ c', Relation.TransGen (Step P Det.noHost) c c' ∧ MR ok mi c' d' ∧ SR ok mi c'.store d'.store

def SimIH (ok : SiteOk) (mi : ModuleInst) (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (d d' c : Config H), sizeOf d.code < k → Step P Det.noHost d d' → MR ok mi c d →
    SR ok mi c.store d.store → DInv ok mi c.store → Res ok mi P c d'

theorem SimIH.mono {k k' : Nat} (h : SimIH ok mi P H k) (hk : k' ≤ k) : SimIH ok mi P H k' :=
  fun d d' c hsz => h d d' c (by omega)

def HRes (ok : SiteOk) (mi : ModuleInst) (P : Numerics.Profile) (s : Store H) (f : Frame) (args : List Val)
    (e : Admin) (d₀ : Config H) : Prop :=
  ∃ c₀ : Config H,
    Relation.TransGen (Step P Det.noHost) ⟨s, f, vals args ++ [e]⟩ c₀ ∧
      SR ok mi c₀.store d₀.store ∧ c₀.frame = d₀.frame ∧
      GL ok mi f.module c₀.code d₀.code

theorem SR.restore {s t t' : Store H} (hSR : SR ok mi s t) (hf : t'.funcs = t.funcs) :
    SR ok mi (withFuncs t' s.funcs) t' := by
  refine ⟨?_, ?_⟩
  · simpa only [withFuncs_funcs, hf] using hSR.funcs
  · cases t'; rfl

theorem source_store {s t : Store H} (hSR : SR ok mi s t) : withFuncs t s.funcs = s := by
  rw [hSR.eq]
  rfl

theorem call_rel {s t : Store H} (hSR : SR ok mi s t) {a : Nat}
    {fi' : FuncInst H} {code' : Func} (hf : t.funcs[a]? = some fi')
    (hcode : fi'.code = .wasm code') :
    ∃ (fi : FuncInst H) (code : Func), s.funcs[a]? = some fi ∧ fi.type = fi'.type ∧
      fi.module = fi'.module ∧ fi.code = .wasm code ∧ code'.locals = code.locals ∧
      GIL ok mi fi.module code.body code'.body := by
  obtain ⟨fi, hf, ht, hm, hc⟩ := hSR.get' hf
  cases hfc : fi.code with
  | wasm code =>
    rw [hfc, hcode] at hc
    exact ⟨fi, code, hf, ht, hm, hfc, hc.2.1.symm, hc.2.2⟩
  | host h => rw [hfc, hcode] at hc; exact hc.elim

theorem head_callData {s t : Store H} {f : Frame} {args : List Val}
    {e e' : Admin} {d₀ : Config H} (hSR : SR ok mi s t) (he : e.IsCallRef)
    (hcd : CallData t f args e' d₀) : HRes ok mi P s f args e d₀ := by
  obtain ⟨vs, a, fi', ps, rs, code', rfl, hc, hf, hex, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi, code, hf, ht, hm, hcode, hl, hb⟩ := call_rel hSR hf hcode
  refine ⟨_, tg_head (.callRefFunc rfl he hf (ht.symm ▸ hex) hn hcode), hSR, rfl, ?_⟩
  rw [← hm, hl]
  exact .cons (.frame (.cons (.label .nil (GL.of_GIL hb)) (.nil _))) (.nil _)

/-- Match an atomic instruction using the exact choice made by the target step. -/
theorem head_flat {s t : Store H} {f : Frame} {args : List Val}
    {e : Admin} {d₀ : Config H} (hh : Det.Head P t f args e d₀) (hSR : SR ok mi s t)
    (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : HRes ok mi P s f args e d₀ := by
  have htypes : SameTypes s.funcs t.funcs := by rw [hSR.eq]; exact hSR.sameTypes.symm
  by_cases hS : SimpleE e
  · rcases head_simple hh hS htypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · have hc : e.IsCallRef := by obtain ⟨_, _, _, _, _, _, -, hc, -⟩ := hcd; exact hc
      exact head_callData hSR hc hcd
    · rw [source_store hSR] at hN
      exact ⟨⟨withFuncs d₀.store s.funcs, f, d₀.code⟩, tg_head hN,
        SR.restore hSR hfs, hfr.symm, GL.refl _⟩
  · obtain ⟨s₀, f₀, is₀⟩ := d₀
    have hloc : ∃ x, e = .plain (.localGet x) ∨ e = .plain (.localSet x) ∨
        e = .plain (.localTee x) := by
      refine Classical.byContradiction fun hne => hS ⟨hL, hH, hF, ?_, ?_, ?_⟩
      · intro x hx; exact hne ⟨x, .inl hx⟩
      · intro x hx; exact hne ⟨x, .inr (.inl hx)⟩
      · intro x hx; exact hne ⟨x, .inr (.inr hx)⟩
    obtain ⟨x, hx⟩ := hloc
    have hfam : Det.famOf e = .variable := by rcases hx with rfl | rfl | rfl <;> rfl
    cases hh with
    | «variable» h =>
      obtain ⟨hfs, h'⟩ := variableStep_withFuncs h s.funcs
      rw [source_store hSR] at h'
      exact ⟨⟨withFuncs s₀ s.funcs, f₀, is₀⟩, tg_head (.variable h'),
        SR.restore hSR hfs, rfl, GL.refl _⟩
    | parametric h =>
      exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape h)).2.symm.trans hfam) (by decide)
    | numeric h =>
      exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape h)).2.symm.trans hfam) (by decide)
    | vector h =>
      exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape h)).2.symm.trans hfam) (by decide)
    | table h =>
      exact absurd ((Det.famOf_of_shape (Det.TableStep.shape h)).2.symm.trans hfam) (by decide)
    | memory h =>
      exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape h)).2.symm.trans hfam) (by decide)
    | reference h =>
      exact absurd ((Det.famOf_of_shape (Det.RefStep.shape h)).2.symm.trans hfam) (by decide)
    | aggregate h =>
      exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape h)).2.symm.trans hfam) (by decide)
    | _ => rcases hx with h | h | h <;> (try cases h) <;> simp_all [Admin.IsCallRef]

/-- Two call forms with different annotations: the same call. -/
theorem head_ann {P : Numerics.Profile} {s t : Store H} {f : Frame}
    {args : List Val} {e e' : Admin} {c₀ : Config H} (hh : Det.Head P t f args e' c₀)
    (hSR : SR ok mi s t) (he : e.IsCallRef) (he' : e'.IsCallRef) :
    HRes ok mi P s f args e c₀ := by
  have hc := he'
  unfold Admin.IsCallRef at hc
  split at hc
  all_goals first
    | exact hc.elim
    | (cases hh with
      | callRefNull =>
        exact ⟨_, tg_head (.callRefNull he), hSR, rfl, GL.refl _⟩
      | callRefFunc ha _ hf he₁ hn hcode =>
        exact head_callData hSR he ⟨_, _, _, _, _, _, ha, he', hf, he₁, hn, hcode, rfl⟩
      | _ => fam_dismiss)


end Silmaril.Wasm.Binaryen.DirSim.Back
