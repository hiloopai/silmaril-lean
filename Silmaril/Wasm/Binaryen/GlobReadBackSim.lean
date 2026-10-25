module

public import Silmaril.Wasm.Binaryen.GlobReadBackValues

@[expose] public section

/-! # Immutable-global substitution: matching a step of the literal side

Numerical results are transported from the actual chosen step. No uniqueness or
deterministic-profile theorem is used.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

def Res (p : Prm) (P : Numerics.Profile) (c d' : Config H) : Prop :=
  ∃ c', Relation.TransGen (Step P Det.noHost) c c' ∧ MR p c' d' ∧ SR p c'.store d'.store

def SimIH (p : Prm) (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (d d' c : Config H), sizeOf d.code < k → Step P Det.noHost d d' → MR p c d →
    SR p c.store d.store → GInv p.lk p.mi c.store → Res p P c d'

theorem SimIH.mono {k k' : Nat} (h : SimIH p P H k) (hk : k' ≤ k) : SimIH p P H k' :=
  fun d d' c hsz => h d d' c (by omega)

def HRes (p : Prm) (P : Numerics.Profile) (s : Store H) (f : Frame) (args : List Val)
    (e : Admin) (d₀ : Config H) : Prop :=
  ∃ c₀ : Config H,
    Relation.TransGen (Step P Det.noHost) ⟨s, f, vals args ++ [e]⟩ c₀ ∧
      SR p c₀.store d₀.store ∧ c₀.frame = d₀.frame ∧
      GL p.lk p.mi f.module c₀.code d₀.code

theorem SR.restore {s t t' : Store H} (hSR : SR p s t) (hf : t'.funcs = t.funcs) :
    SR p (withFuncs t' s.funcs) t' := by
  refine ⟨hSR.hg, ?_⟩
  have htf : t'.funcs = s.funcs.set p.ag (gR p) := by rw [hf, hSR.ht]; rfl
  cases t'
  simp only [withFuncs] at htf ⊢
  congr 1

theorem source_store {s t : Store H} (hSR : SR p s t) : withFuncs t s.funcs = s := by
  rw [hSR.ht]
  rfl

theorem call_rel (hok : PrmOk p) {s t : Store H} (hSR : SR p s t) {a : Nat}
    {fi' : FuncInst H} {code' : Func} (hf : t.funcs[a]? = some fi')
    (hcode : fi'.code = .wasm code') :
    ∃ (fi : FuncInst H) (code : Func), s.funcs[a]? = some fi ∧ fi.type = fi'.type ∧
      fi.module = fi'.module ∧ fi.code = .wasm code ∧ code'.locals = code.locals ∧
      GIL p.lk p.mi fi.module code.body code'.body := by
  rw [hSR.get a] at hf
  by_cases hag : a = p.ag
  · subst hag
    simp only [↓reduceIte, Option.some.injEq] at hf
    subst hf
    simp only [gR, FuncCode.wasm.injEq] at hcode
    subst hcode
    exact ⟨gL p, p.cL, hSR.hg, rfl, rfl, rfl, hok.locals, hok.body⟩
  · simp only [hag, ↓reduceIte] at hf
    exact ⟨fi', code', hf, rfl, rfl, hcode, rfl, GIL.refl _⟩

theorem head_callData (hok : PrmOk p) {s t : Store H} {f : Frame} {args : List Val}
    {e : Admin} {d₀ : Config H} (hSR : SR p s t) (hcd : CallData t f args e d₀) :
    HRes p P s f args e d₀ := by
  obtain ⟨vs, a, fi', ps, rs, code', rfl, hc, hf, he, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi, code, hf, ht, hm, hcode, hl, hb⟩ := call_rel hok hSR hf hcode
  refine ⟨_, tg_head (.callRefFunc rfl hc hf (ht.symm ▸ he) hn hcode), hSR, rfl, ?_⟩
  rw [← hm, hl]
  exact .cons (.frame (.cons (.label .nil (GL.of_GIL hb)) (.nil _))) (.nil _)

/-- Match an atomic instruction using the exact choice made by the literal-side step. -/
theorem head_flat (hok : PrmOk p) {s t : Store H} {f : Frame} {args : List Val}
    {e : Admin} {d₀ : Config H} (hh : Det.Head P t f args e d₀) (hSR : SR p s t)
    (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : HRes p P s f args e d₀ := by
  have htypes : SameTypes s.funcs t.funcs := by rw [hSR.ht]; exact hSR.sameTypes.symm
  by_cases hS : SimpleE e
  · rcases head_simple hh hS htypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · exact head_callData hok hSR hcd
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

end Silmaril.Wasm.Binaryen.GlobRead.Back
