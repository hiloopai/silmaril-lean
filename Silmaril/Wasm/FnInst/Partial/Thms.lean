module

public import Silmaril.Wasm.FnInst.Partial.Defs
public import Silmaril.Wasm.FnInst.Frag.Thms
public import Silmaril.Logic.Inst.Core.Thms

/-!
# Monotonicity in information, and how distinction behaves

For any handler presentation `P` (in particular the hole, one-, several- and all-function
institutions):

* **equivalence (any sentence) is monotone**: true in every completion of `M` implies true in
  every completion of a more informative `N` (`HPres.partial_sat_mono`); so a rewrite proved
  with less known about the other bodies stays valid when more is known;
* `DistAll` (distinguished in every completion) is monotone too (`HPres.distAll_mono`);
* `DistSome` (distinguished in some completion) is **antitone** (`HPres.distSome_anti`), and
  is exactly the failure of satisfaction (`HPres.partial_sat_iff_not_distSome`); it is *not*
  monotone: `Frag.distSome_not_mono` specifies a body and loses the distinction;
* `DistAll` implies failure of satisfaction only when the model has a completion
  (`HPres.not_sat_of_distAll`): an inconsistent model satisfies everything;
* validity over partial models is validity over handlers (`HPres.valid_partial_iff`): the
  least informative models (`PModel.free`) contain every handler, and `PModel.exact` pins one.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory Silmaril.Inst

variable {L : Lang} {W : Type}

namespace PModel

variable {C : Ctx}

theorem infoLe_refl (M : PModel L W C) : M.InfoLe M := fun _ h => h

theorem InfoLe.trans {M N O : PModel L W C} (h₁ : M.InfoLe N) (h₂ : N.InfoLe O) :
    M.InfoLe O :=
  fun _ h => h₁ (h₂ h)

theorem BodySpec.le_base {s t : BodySpec L C} (h : s.Le t) (hs : s = .base) : t = .base := by
  rcases h with h | h
  · rw [hs] at h
    cases h
  · rw [← h, hs]

theorem BodySpec.le_code {s t : BodySpec L C} {b : L.Code C} (h : s.Le t) (hs : s = .code b) :
    t = .code b := by
  rcases h with h | h
  · rw [hs] at h
    cases h
  · rw [← h, hs]

/-- Specifying more bodies goes up in the information order. -/
theorem infoLe_withBody (M : PModel L W C) (body : M.C'.Idx .func → BodySpec L M.C')
    (hb : ∀ f, (M.body f).Le (body f)) : M.InfoLe (M.withBody body) := by
  rintro _ ⟨h', ⟨hbase, hcode⟩, rfl⟩
  refine ⟨h', ⟨fun e he => hbase e fun f a hfa => ?_, fun f b hfb => ?_⟩, rfl⟩
  · exact BodySpec.le_base (hb f) (he f a hfa)
  · exact hcode f b (BodySpec.le_code (hb f) hfb)

theorem self_mem_den_free (h₀ : Handler L W C) : h₀ ∈ (free h₀).den :=
  ⟨h₀, ⟨fun _ _ => rfl, fun _ _ hb => by cases hb⟩, Handler.reduct_id h₀⟩

theorem den_exact (h₀ : Handler L W C) : (exact h₀).den = {h₀} := by
  ext h
  constructor
  · rintro ⟨h', ⟨hbase, _⟩, rfl⟩
    have hh' : h' = h₀ := funext fun e => hbase e fun _ _ _ => rfl
    rw [hh']
    exact Handler.reduct_id h₀
  · rintro rfl
    exact ⟨h, ⟨fun _ _ => rfl, fun _ _ hb => by cases hb⟩, Handler.reduct_id h⟩

end PModel

namespace HPres

variable {Sign : Type} [Category.{0} Sign] (P : HPres L W Sign)

theorem partial_sat_iff {S : Sign} (M : PModel L W (P.ctx.obj S)) (φ : P.Sen S) :
    M ⊨[P.partialInst] φ ↔ ∀ h ∈ M.den, P.Sat h φ :=
  Iff.rfl

/-- **Monotonicity**: what holds with less information holds with more. -/
theorem partial_sat_mono {S : Sign} {M N : PModel L W (P.ctx.obj S)} (hMN : M.InfoLe N)
    {φ : P.Sen S} (hM : M ⊨[P.partialInst] φ) : N ⊨[P.partialInst] φ :=
  fun h hN => hM h (hMN hN)

theorem distAll_mono {S : Sign} {M N : PModel L W (P.ctx.obj S)} (hMN : M.InfoLe N)
    {φ : P.Sen S} (hM : P.DistAll M φ) : P.DistAll N φ :=
  fun h hN => hM h (hMN hN)

theorem distSome_anti {S : Sign} {M N : PModel L W (P.ctx.obj S)} (hMN : M.InfoLe N)
    {φ : P.Sen S} (hN : P.DistSome N φ) : P.DistSome M φ := by
  obtain ⟨h, hNh, hn⟩ := hN
  exact ⟨h, hMN hNh, hn⟩

theorem partial_sat_iff_not_distSome {S : Sign} (M : PModel L W (P.ctx.obj S)) (φ : P.Sen S) :
    M ⊨[P.partialInst] φ ↔ ¬ P.DistSome M φ := by
  constructor
  · rintro hM ⟨h, hh, hn⟩
    exact hn (hM h hh)
  · intro hn h hh
    by_contra hs
    exact hn ⟨h, hh, hs⟩

theorem not_sat_of_distAll {S : Sign} {M : PModel L W (P.ctx.obj S)} {φ : P.Sen S}
    (hne : M.den.Nonempty) (hd : P.DistAll M φ) : ¬ M ⊨[P.partialInst] φ := by
  obtain ⟨h, hh⟩ := hne
  exact fun hM => hd h hh (hM h hh)

/-- A handler's exact partial model satisfies exactly what the handler does. -/
theorem sat_exact_iff {S : Sign} (h : Handler L W (P.ctx.obj S)) (φ : P.Sen S) :
    PModel.exact h ⊨[P.partialInst] φ ↔ P.Sat h φ := by
  show (∀ h' ∈ (PModel.exact h).den, P.Sat h' φ) ↔ P.Sat h φ
  rw [PModel.den_exact]
  exact ⟨fun H => H h rfl, fun H h' hh' => by rw [hh']; exact H⟩

/-- Validity over partial models is validity over handlers. -/
theorem valid_partial_iff {S : Sign} (φ : P.Sen S) :
    P.partialInst.Valid φ ↔ P.inst.Valid φ := by
  constructor
  · intro hv h
    exact (sat_exact_iff P h φ).1 (hv (PModel.exact h))
  · intro hv M h _
    exact hv h

end HPres

/-! ### Distinction in some completion is not monotone -/

namespace Frag

/-- One defined function of type `[] → [i32]`, nothing else. -/
def oneFnCtx : Ctx where
  n
    | .func => 1
    | _ => 0
  decl
    | .func, _ => ⟨⟨[], [.i32]⟩, false⟩
    | .type, i => i.elim0
    | .table, i => i.elim0
    | .mem, i => i.elim0
    | .global, i => i.elim0
    | .tag, i => i.elim0
    | .data, i => i.elim0
    | .elem, i => i.elim0

/-- The function. -/
def f0 : oneFnCtx.Idx .func := ⟨0, Nat.zero_lt_one⟩

/-- `call f0` against `i32.const 7`, at the free hole of `oneFnCtx`. -/
def callSen : (holePres frag W).Sen ⟨oneFnCtx, freeTy⟩ := Formula.atom (.call f0, .const 7)

/-- Nothing known about `f0`; its calls trap in the base. -/
def knowNothing : PModel frag W oneFnCtx := PModel.free fun _ w => (none, w)

/-- `f0`'s body is `i32.const 7`. -/
def knowBody : PModel frag W oneFnCtx := knowNothing.withBody fun _ => .code (.const 7)

theorem knowNothing_le : (knowNothing (W := W)).InfoLe knowBody :=
  PModel.infoLe_withBody _ _ fun _ => Or.inl rfl

/-- With `f0` unknown, some completion tells `call f0` from `i32.const 7`. -/
theorem distSome_knowNothing [Inhabited W] :
    (holePres frag W).DistSome (S := ⟨oneFnCtx, freeTy⟩) knowNothing callSen := by
  refine ⟨_, PModel.self_mem_den_free _, fun hs => ?_⟩
  have h : Out.trap (default : W) = Out.normal [7] [] default :=
    hs ([], []) default (freeTy_free _)
  cases h

/-- Once `f0`'s body is known to be `i32.const 7`, no completion does. -/
theorem not_distSome_knowBody :
    ¬ (holePres frag W).DistSome (S := ⟨oneFnCtx, freeTy⟩) knowBody callSen := by
  rintro ⟨_, ⟨h', ⟨_, hcode⟩, rfl⟩, hn⟩
  apply hn
  rintro ⟨s, l⟩ w _
  have hcall : h' (.call f0 []) w = (some [7], w) := hcode f0 (.const 7) rfl [] w
  show exec (fun e => h' (e.map (𝟙 oneFnCtx))) (.call f0) s l w = Out.normal (7 :: s) l w
  have h0 : (oneFnCtx.fty f0).params.length = 0 := rfl
  simp only [exec, answer, h0, List.take_zero, List.drop_zero, List.reverse_nil]
  rw [ite_eq_left (Nat.zero_le _)]
  show answer (h' (.call f0 []) w) s l = _
  rw [hcall]
  rfl

/-- **Distinction in some completion is not monotone in information.** -/
theorem distSome_not_mono [Inhabited W] :
    ∃ (M N : PModel frag W oneFnCtx), M.InfoLe N ∧
      (holePres frag W).DistSome (S := ⟨oneFnCtx, freeTy⟩) M callSen ∧
      ¬ (holePres frag W).DistSome (S := ⟨oneFnCtx, freeTy⟩) N callSen :=
  ⟨knowNothing, knowBody, knowNothing_le, distSome_knowNothing, not_distSome_knowBody⟩

end Frag

end Silmaril.Wasm.FnInst
