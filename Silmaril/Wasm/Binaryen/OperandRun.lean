module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.InstrUtil
public import Silmaril.Wasm.Binaryen.LocalsSim
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Runs of an operand: divergence or one value

An operand of an inlined call (`inlineN_resolves`) is a profile expression typed
`[] → [t]` that neither calls, traps, branches out of itself nor returns. Every run
of it from a typed configuration either diverges or reaches exactly one value,
and the configuration stays typed (`operand_classify`), so the next operand can be
classified in turn.

The typing is carried by `TypedAt C₀`: code typed in a context `Ct` that sits under
the frame's context (`CtxUnder`, the generalised preservation of
`Soundness/Preservation.lean`) and extends `C₀` by setting locals (`CtxLe`). The code
may sit under labels of the enclosing function (`Ct.labels`); branches to them are
excluded by the effect analysis (`effects_control_br`). Returns are excluded by typing
in the frame's context (`InstrsOk.closed`), which has neither labels nor a return type.
-/

namespace Silmaril.Wasm.Binaryen.OpRun

open Silmaril.Wasm Execution.Core Validation Numerics SingleThreaded

variable {H : Type}

/-! ## Closed code types in the frame context

`closedI d i`: every branch target of `i` is below `d` (relative to `i`'s own
context), and there is no `return` or tail call. Such code types in any context that
agrees with the original on the labels below `d`, with any return type
(`InstrOk.closed`); with `d = 0`, in the frame's context. -/

mutual
/-- Branch targets below `d`, no `return` or tail call. -/
def closedI (d : Nat) : Instr → Bool
  | .br l => decide (l.toNat < d)
  | .brIf l => decide (l.toNat < d)
  | .brOnNull l => decide (l.toNat < d)
  | .brOnNonNull l => decide (l.toNat < d)
  | .brOnCast l _ _ => decide (l.toNat < d)
  | .brOnCastFail l _ _ => decide (l.toNat < d)
  | .brTable ls l => decide (l.toNat < d) && ls.all (fun l => decide (l.toNat < d))
  | .return_ => false
  | .returnCall _ => false
  | .returnCallRef _ => false
  | .returnCallIndirect _ _ => false
  | .block _ b => closedIs (d + 1) b
  | .loop _ b => closedIs (d + 1) b
  | .if_ _ b₁ b₂ => closedIs (d + 1) b₁ && closedIs (d + 1) b₂
  | .tryTable _ cs b => cs.all (fun c => decide (Catch.label c < d)) && closedIs (d + 1) b
  | _ => true
/-- `closedI` on a list. -/
def closedIs (d : Nat) : List Instr → Bool
  | [] => true
  | i :: is => closedI d i && closedIs d is
end

theorem closedIs_append (d : Nat) : ∀ a b : List Instr,
    closedIs d (a ++ b) = (closedIs d a && closedIs d b)
  | [], b => by simp [closedIs]
  | i :: a, b => by simp [closedIs, closedIs_append d a b, Bool.and_assoc]

theorem initLocals_lr (C : Context) (L : List (List CValType)) (r : Option (List CValType))
    (xs : List Nat) :
    ({ C with labels := L, return_ := r } : Context).initLocals xs =
      { C.initLocals xs with labels := L, return_ := r } := by
  obtain ⟨L₁, h₁, hy₁⟩ :=
    Context.initLocals_spec ({ C with labels := L, return_ := r } : Context) xs
  obtain ⟨L₂, h₂, hy₂⟩ := Context.initLocals_spec C xs
  rw [h₁, h₂]
  have : L₁ = L₂ := List.ext_getElem? fun y => by rw [hy₁, hy₂]
  subst this
  rfl

theorem labels_cons_agree {d : Nat} {L M : List (List CValType)}
    (hL : ∀ l < d, L[l]? = M[l]?) (ts : List CValType) :
    ∀ l < d + 1, (ts :: L)[l]? = (ts :: M)[l]? := by
  intro l hl
  cases l with
  | zero => rfl
  | succ l => simpa using hL l (by omega)

theorem catchOk_closed {C : Context} {c : Catch} (h : CatchOk C c) {d : Nat} (hd : Catch.label c < d)
    (L : List (List CValType)) (r : Option (List CValType))
    (hL : ∀ l < d, L[l]? = C.labels[l]?) :
    CatchOk { C with labels := L, return_ := r } c := by
  cases h with
  | @catch_ x l d' ts lt hx he hl hs =>
    exact .catch_ hx he (by show L[l.toNat]? = some lt; rw [hL l.toNat hd]; exact hl) hs
  | @catchRef x l d' ts lt hx he hl hs =>
    exact .catchRef hx he (by show L[l.toNat]? = some lt; rw [hL l.toNat hd]; exact hl) hs
  | @catchAll l lt hl hs =>
    exact .catchAll (by show L[l.toNat]? = some lt; rw [hL l.toNat hd]; exact hl) hs
  | @catchAllRef l lt hl hs =>
    exact .catchAllRef (by show L[l.toNat]? = some lt; rw [hL l.toNat hd]; exact hl) hs

mutual

/-- Closed instructions type under any labels agreeing below `d` and any return type. -/
theorem InstrOk.closed {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    {d : Nat} (hc : closedI d i = true) (L : List (List CValType))
    (r : Option (List CValType)) (hL : ∀ l < d, L[l]? = C.labels[l]?) :
    InstrOk { C with labels := L, return_ := r } i it :=
  match h with
  | .parametric h => .parametric (by
      cases h with
      | unreachable h => exact .unreachable h
      | _ => (constructor; all_goals assumption))
  | .numeric h => .numeric (by cases h <;> (constructor; all_goals assumption))
  | .vector h => .vector (by cases h <;> constructor <;> assumption)
  | .variable h => .variable (by cases h <;> constructor <;> assumption)
  | .memory h => .memory (by cases h <;> constructor <;> assumption)
  | .table h => .table (by cases h <;> constructor <;> assumption)
  | .reference h => .reference (by cases h <;> constructor <;> assumption)
  | .block hbt hb =>
    .block (by cases hbt <;> constructor <;> assumption)
      (InstrsOk.closed hb hc _ r (labels_cons_agree hL _))
  | .loop hbt hb =>
    .loop (by cases hbt <;> constructor <;> assumption)
      (InstrsOk.closed hb hc _ r (labels_cons_agree hL _))
  | .if_ hbt h₁ h₂ =>
    .if_ (by cases hbt <;> constructor <;> assumption)
      (InstrsOk.closed h₁ ((Bool.and_eq_true _ _).mp hc).1 _ r (labels_cons_agree hL _))
      (InstrsOk.closed h₂ ((Bool.and_eq_true _ _).mp hc).2 _ r (labels_cons_agree hL _))
  | .br hl hok => .br (by rw [hL _ (of_decide_eq_true hc)]; exact hl) hok
  | .brIf hl => .brIf (by rw [hL _ (of_decide_eq_true hc)]; exact hl)
  | .brTable hls hl' hok => by
    simp only [closedI, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    refine .brTable (fun l hl => ?_) ?_ hok
    · obtain ⟨lt, h₁, h₂⟩ := hls l hl
      exact ⟨lt, by rw [hL _ (hc.2 l hl)]; exact h₁, h₂⟩
    · obtain ⟨lt, h₁, h₂⟩ := hl'
      exact ⟨lt, by rw [hL _ hc.1]; exact h₁, h₂⟩
  | .brOnNull hl hh => .brOnNull (by rw [hL _ (of_decide_eq_true hc)]; exact hl) hh
  | .brOnNonNull hl => .brOnNonNull (by rw [hL _ (of_decide_eq_true hc)]; exact hl)
  | .brOnCast hl h₁ h₂ h₂₁ h₂l =>
    .brOnCast (by rw [hL _ (of_decide_eq_true hc)]; exact hl) h₁ h₂ h₂₁ h₂l
  | .brOnCastFail hl h₁ h₂ h₂₁ hdl =>
    .brOnCastFail (by rw [hL _ (of_decide_eq_true hc)]; exact hl) h₁ h₂ h₂₁ hdl
  | .call hf he => .call hf he
  | .callRef hd he => .callRef hd he
  | .callIndirect ht hs hd he => .callIndirect ht hs hd he
  | .return_ .. => absurd hc (by simp [closedI])
  | .returnCall .. => absurd hc (by simp [closedI])
  | .returnCallRef .. => absurd hc (by simp [closedI])
  | .returnCallIndirect .. => absurd hc (by simp [closedI])
  | .throw hx he hok => .throw hx he hok
  | .throwRef hok => .throwRef hok
  | .tryTable hbt hb hcs => by
    simp only [closedI, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    exact .tryTable (by cases hbt <;> constructor <;> assumption)
      (InstrsOk.closed hb hc.2 _ r (labels_cons_agree hL _))
      (fun c hc' => catchOk_closed (hcs c hc') (hc.1 c hc') L r hL)

/-- Closed sequences type under any labels agreeing below `d` and any return type. -/
theorem InstrsOk.closed {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {d : Nat} (hc : closedIs d is = true) (L : List (List CValType))
    (r : Option (List CValType)) (hL : ∀ l < d, L[l]? = C.labels[l]?) :
    InstrsOk { C with labels := L, return_ := r } is it :=
  match h with
  | .nil => .nil
  | .instr h => .instr (InstrOk.closed h (by simpa [closedIs] using hc) L r hL)
  | .seq (xs₁ := xs₁) h₁ hx h₂ => by
    rw [closedIs_append, Bool.and_eq_true] at hc
    have h₂' := InstrsOk.closed h₂ hc.2 L r (by simpa using hL)
    rw [← initLocals_lr] at h₂'
    exact .seq (InstrsOk.closed h₁ hc.1 L r hL) hx h₂'
  | .cons (xs₁ := xs₁) hi hx hs => by
    simp only [closedIs, Bool.and_eq_true] at hc
    have hs' := InstrsOk.closed hs hc.2 L r (by simpa using hL)
    rw [← initLocals_lr] at hs'
    exact .cons (InstrOk.closed hi hc.1 L r hL) hx hs'
  | .sub h hs hok => .sub (InstrsOk.closed h hc L r hL) hs hok
  | .frame h hok => .frame (InstrsOk.closed h hc L r hL) hok

end

/-! ## From the effect analysis to the code -/

theorem lowIs_append (n : Nat) : ∀ a b : List Instr,
    LocSim.lowIs n (a ++ b) = (LocSim.lowIs n a && LocSim.lowIs n b)
  | [], b => by simp [LocSim.lowIs]
  | i :: a, b => by simp [LocSim.lowIs, lowIs_append n a b, Bool.and_assoc]

theorem lt_succ_of_unbind {ns : List Nat} {d : Nat} (h : ∀ l ∈ unbind ns, l < d) :
    ∀ l ∈ ns, l < d + 1 := by
  intro l hl
  cases l with
  | zero => omega
  | succ k =>
    have hk : k ∈ unbind ns := by
      simp only [unbind, List.mem_filterMap]
      exact ⟨k + 1, hl, by simp⟩
    have := h k hk
    omega

theorem closedI_of_instrEffects (i : Instr) (d : Nat) (ha : (instrEffects i).any = false)
    (hb : (instrEffects i).branchesOut = false)
    (hl : ∀ l ∈ (instrEffects i).breakTargets, l < d) : closedI d i = true := by
  cases i <;> simp_all [instrEffects, closedI, Effects.top]

theorem lowI_of_instrEffects (i : Instr) (n : Nat) (ha : (instrEffects i).any = false)
    (hc : (instrEffects i).calls = false)
    (hx : ∀ x ∈ (instrEffects i).localsRead ++ (instrEffects i).localsWritten, x < n) :
    LocSim.lowI n i = true := by
  cases i <;> simp_all [instrEffects, LocSim.lowI, Effects.top]

mutual

theorem closed_of_effects : ∀ (e : BExpr) (d : Nat), (effects e).any = false →
    (effects e).branchesOut = false → (∀ l ∈ (effects e).breakTargets, l < d) →
    closedIs d e.lower = true
  | .op i args, d, ha, hb, hl => by
    simp only [effects, Effects.merge, Bool.or_eq_false_iff, List.mem_append] at ha hb hl
    simp only [BExpr.lower, closedIs_append, closedIs, Bool.and_true, Bool.and_eq_true]
    exact ⟨closed_of_effectsList args d ha.1 hb.1 (fun l h => hl l (.inl h)),
      closedI_of_instrEffects i d ha.2 hb.2 (fun l h => hl l (.inr h))⟩
  | .block bt b, d, ha, hb, hl => by
    simp only [effects, Effects.unbindLabel] at ha hb hl
    simp only [BExpr.lower, closedIs, closedI, Bool.and_true]
    exact closed_of_effectsList b (d + 1) ha hb (lt_succ_of_unbind hl)
  | .loop bt b, d, ha, hb, hl => by
    simp only [effects, Effects.unbindLabel] at ha hb hl
    simp only [BExpr.lower, closedIs, closedI, Bool.and_true]
    exact closed_of_effectsList b (d + 1) ha hb (lt_succ_of_unbind hl)
  | .if_ bt c t e, d, ha, hb, hl => by
    simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff,
      List.mem_append] at ha hb hl
    simp only [BExpr.lower, closedIs_append, closedIs, closedI, Bool.and_true, Bool.and_eq_true]
    have hl' := lt_succ_of_unbind (fun l h => hl l (.inr h))
    simp only [List.mem_append] at hl'
    exact ⟨closed_of_effectsList c d ha.1 hb.1 (fun l h => hl l (.inl h)),
      closed_of_effectsList t (d + 1) ha.2.1 hb.2.1 (fun l h => hl' l (.inl h)),
      closed_of_effectsList e (d + 1) ha.2.2 hb.2.2 (fun l h => hl' l (.inr h))⟩
  | .tryTable _ _ _, _, ha, _, _ => by simp [effects, Effects.top] at ha

theorem closed_of_effectsList : ∀ (es : List BExpr) (d : Nat), (effectsList es).any = false →
    (effectsList es).branchesOut = false → (∀ l ∈ (effectsList es).breakTargets, l < d) →
    closedIs d (BExpr.lowerList es) = true
  | [], _, _, _, _ => rfl
  | e :: es, d, ha, hb, hl => by
    simp only [effectsList, Effects.merge, Bool.or_eq_false_iff, List.mem_append] at ha hb hl
    simp only [BExpr.lowerList, closedIs_append, Bool.and_eq_true]
    exact ⟨closed_of_effects e d ha.1 hb.1 (fun l h => hl l (.inl h)),
      closed_of_effectsList es d ha.2 hb.2 (fun l h => hl l (.inr h))⟩

end

mutual

theorem low_of_effects : ∀ (e : BExpr) (n : Nat), (effects e).any = false →
    (effects e).calls = false →
    (∀ x ∈ (effects e).localsRead ++ (effects e).localsWritten, x < n) →
    LocSim.lowIs n e.lower = true
  | .op i args, n, ha, hc, hx => by
    simp only [effects, Effects.merge, Bool.or_eq_false_iff, List.mem_append] at ha hc hx
    simp only [BExpr.lower, lowIs_append, LocSim.lowIs, Bool.and_true, Bool.and_eq_true]
    refine ⟨low_of_effectsList args n ha.1 hc.1 ?_, lowI_of_instrEffects i n ha.2 hc.2 ?_⟩
    · intro x h
      simp only [List.mem_append] at h
      rcases h with h | h
      · exact hx x (.inl (.inl h))
      · exact hx x (.inr (.inl h))
    · intro x h
      simp only [List.mem_append] at h
      rcases h with h | h
      · exact hx x (.inl (.inr h))
      · exact hx x (.inr (.inr h))
  | .block bt b, n, ha, hc, hx => by
    simp only [effects, Effects.unbindLabel] at ha hc hx
    simp only [BExpr.lower, LocSim.lowIs, LocSim.lowI, Bool.and_true]
    exact low_of_effectsList b n ha hc hx
  | .loop bt b, n, ha, hc, hx => by
    simp only [effects, Effects.unbindLabel] at ha hc hx
    simp only [BExpr.lower, LocSim.lowIs, LocSim.lowI, Bool.and_true]
    exact low_of_effectsList b n ha hc hx
  | .if_ bt c t e, n, ha, hc, hx => by
    simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff] at ha hc hx
    simp only [BExpr.lower, lowIs_append, LocSim.lowIs, LocSim.lowI, Bool.and_true,
      Bool.and_eq_true]
    refine ⟨low_of_effectsList c n ha.1 hc.1 ?_, low_of_effectsList t n ha.2.1 hc.2.1 ?_,
      low_of_effectsList e n ha.2.2 hc.2.2 ?_⟩ <;>
    · intro x h
      apply hx x
      simp only [List.mem_append] at h ⊢
      tauto
  | .tryTable _ _ _, _, ha, _, _ => by simp [effects, Effects.top] at ha

theorem low_of_effectsList : ∀ (es : List BExpr) (n : Nat), (effectsList es).any = false →
    (effectsList es).calls = false →
    (∀ x ∈ (effectsList es).localsRead ++ (effectsList es).localsWritten, x < n) →
    LocSim.lowIs n (BExpr.lowerList es) = true
  | [], _, _, _, _ => rfl
  | e :: es, n, ha, hc, hx => by
    simp only [effectsList, Effects.merge, Bool.or_eq_false_iff] at ha hc hx
    simp only [BExpr.lowerList, lowIs_append, Bool.and_eq_true]
    refine ⟨low_of_effects e n ha.1 hc.1 ?_, low_of_effectsList es n ha.2 hc.2 ?_⟩ <;>
    · intro x h
      apply hx x
      simp only [List.mem_append] at h ⊢
      tauto

end

/-! ## Typed configurations under the frame -/

/-- `c` is typed at `it` in a context under `c`'s frame that extends `C₀`. -/
def TypedAt (C₀ : Context) (c : Config H) (it : InstrType) : Prop :=
  StoreOk c.store ∧ ∃ Cf Ct, FrameOk c.store c.frame Cf ∧ CtxUnder Ct Cf ∧ CtxLe C₀ Ct ∧
    Ct.Wf ∧ AdminsOk c.store Ct c.code it

theorem storeTypesOk_of {s : Store H} (hs : StoreOk s) : StoreTypesOk s :=
  ⟨hs.structsClosed, hs.arraysClosed⟩

theorem LocalsLe.length_le {L L' : List LocalType} (h : LocalsLe L L') :
    L.length ≤ L'.length := by
  rcases Nat.lt_or_ge 0 L.length with h0 | h0
  · obtain ⟨i, hi, -⟩ := h (L.length - 1) L[L.length - 1] (List.getElem?_eq_getElem (by omega))
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  · omega

theorem wf_of_under {C₀ : Context} {s : Store H} {f : Frame} {Cf Ct : Context} (hs : StoreOk s)
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf) (hle : CtxLe C₀ Ct) (hC₀ : C₀.Wf) : Ct.Wf := by
  have hwf : Cf.Wf := FrameOk.ctxWf hs (storeTypesOk_of hs) hf
  refine CtxLe.wf hle hC₀ ?_
  intro lt hlt
  obtain ⟨y, hy⟩ := List.mem_iff_getElem?.mp hlt
  obtain ⟨i, hi, -⟩ := hu.le y lt hy
  rw [CtxUnder.toTypeCtx hu]
  exact hwf.locals ⟨i, lt.type⟩ (List.mem_of_getElem? hi)

theorem TypedAt.step {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {C₀ : Context} (hC₀ : C₀.Wf) {c c' : Config H} {it : InstrType} (h : TypedAt C₀ c it)
    (hs : Step P host c c') : TypedAt C₀ c' it ∧ Extend c.store c'.store := by
  obtain ⟨hS, Cf, Ct, hf, hu, hle, hwf, hty⟩ := h
  obtain ⟨Cf', Ct', hS', hext, hf', -, hu', hle', hty'⟩ :=
    Step.preservation_gen hhost hs hS hf hu hwf (storeTypesOk_of hS) hty
  have hle'' := hle.trans hle'
  exact ⟨⟨hS', Cf', Ct', hf', hu', hle'', wf_of_under hS' hf' hu' hle'' hC₀, hty'⟩, hext⟩

theorem TypedAt.steps {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {C₀ : Context} (hC₀ : C₀.Wf) {c c' : Config H} {it : InstrType} (h : TypedAt C₀ c it)
    (hs : Steps P host c c') : TypedAt C₀ c' it ∧ Extend c.store c'.store := by
  induction hs with
  | refl => exact ⟨h, Extend.refl h.1⟩
  | tail _ hst ih =>
    obtain ⟨h₁, he₁⟩ := ih
    obtain ⟨h₂, he₂⟩ := TypedAt.step hhost hC₀ h₁ hst
    exact ⟨h₂, he₁.trans he₂⟩

/-- The progress context of a typed configuration whose context has the frame's locals. -/
theorem ctxOk_of {s : Store H} {f : Frame} {Cf Ct : Context} (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hlen : Ct.locals.length = f.locals.length) : CtxOk s f Ct := by
  have hfl := (FrameOk.ctx_fields hf).2.2
  refine ⟨⟨Cf, hf, ?_, by omega⟩, hlen, ?_⟩
  · have e := hu.eq
    rw [e]
    rfl
  · intro x t hx
    obtain ⟨i, hi, hs⟩ := hu.le x _ hx
    obtain rfl := hs rfl
    exact FrameOk.set hf x t hi

/-! ## Low code has no host-call redex -/

theorem lowAs_fill {n : Nat} : ∀ (E : Ctx) (xs : List Admin),
    LocSim.lowAs n (E.fill xs) = true → LocSim.lowAs n xs = true
  | .top pre rest, xs, h => by
    simp only [Ctx.fill, LocSim.lowAs_append, Bool.and_eq_true] at h
    exact h.1.2
  | .label pre k cont E rest, xs, h => by
    simp only [Ctx.fill, LocSim.lowAs_append, LocSim.lowAs_cons, LocSim.lowAs_nil,
      Bool.and_eq_true, LocSim.lowA, Bool.and_true] at h
    exact lowAs_fill E xs h.1.2.2
  | .handler pre k cs E rest, xs, h => by
    simp [Ctx.fill, LocSim.lowAs_append, LocSim.lowA] at h
  | .frame pre k f E rest, xs, h => by
    simp [Ctx.fill, LocSim.lowAs_append, LocSim.lowA] at h

theorem decompose?_none_of_low {n : Nat} {s : Store H} {code : List Admin}
    (h : LocSim.lowAs n code = true) : decompose? s code = none := by
  cases hd : decompose? s code with
  | none => rfl
  | some x =>
    obtain ⟨E, a, hh, args⟩ := x
    obtain ⟨fi, yy, ps, rs, -, -, hyy, -, -, hcode⟩ := decompose?_sound hd
    rw [hcode] at h
    have h' := lowAs_fill E _ h
    simp [LocSim.lowAs_append, LocSim.lowAs_vals, LocSim.lowA_callRef (n := n) hyy] at h'

/-! ## Steps keep the number of locals -/

theorem step_locals_length {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : c'.frame.locals.length = c.frame.locals.length := by
  induction h with
  | «variable» h => cases h <;> simp [Frame.setLocal]
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

theorem steps_locals_length {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') : c'.frame.locals.length = c.frame.locals.length := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [step_locals_length hst, ih]

/-! ## Non-divergence gives a normal form -/

theorem exists_nf_of_not_diverges {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : ¬ Diverges P host c) : ∃ c', Steps P host c c' ∧ ∀ x, ¬ Step P host c' x := by
  by_contra hne
  simp only [not_exists, not_and, not_forall, not_not] at hne
  exact h (InfiniteTrace.coinduct (fun d => Steps P host c d)
    (fun d hd => let ⟨x, hx⟩ := hne d hd; ⟨x, hx, hd.tail hx⟩) .refl)

/-! ## The classification -/

/-- The effect hypotheses on an operand. -/
structure OpEff (n : Nat) (bs : List BExpr) : Prop where
  any : (effectsList bs).any = false
  calls : (effectsList bs).calls = false
  trap : (effectsList bs).trap = false
  implicitTrap : (effectsList bs).implicitTrap = false
  breakTargets : (effectsList bs).breakTargets = []
  low : LocSim.lowIs n (BExpr.lowerList bs) = true

theorem steps_closed_divHost {P : Profile} {c c' : Config H}
    (h : Steps P closedHost c c') : Steps P (divHost (H := H)) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (Step.of_noHost _ hst)

/-- **An operand diverges or reaches one value**, staying typed. -/
theorem operand_classify {P : Profile} {C₀ : Context} (hC₀ : C₀.Wf) (hR : C₀.return_ = none)
    {n : Nat} {bs : List BExpr} {xs : List Nat} {t : CValType} (heff : OpEff n bs)
    {s : Store H} {f : Frame} (hT : TypedAt C₀ (codeConfig s f [] bs) ⟨[], xs, [t]⟩)
    (hlen : C₀.locals.length = f.locals.length) :
    Diverges P closedHost (codeConfig s f [] bs) ∨
      ∃ c' v, Steps P closedHost (codeConfig s f [] bs) c' ∧ c'.code = vals [v] ∧
        TypedAt C₀ c' ⟨[], xs, [t]⟩ ∧ Extend s c'.store := by
  by_cases hd : Diverges P closedHost (codeConfig s f [] bs)
  · exact Or.inl hd
  right
  obtain ⟨c', hrun, hnf⟩ := exists_nf_of_not_diverges hd
  obtain ⟨hT', hext⟩ := TypedAt.steps divHost_ok hC₀ hT (steps_closed_divHost hrun)
  -- the code stays low
  have hlow0 : LocSim.lowAs n (codeConfig s f [] bs).code = true := by
    show LocSim.lowAs n (vals [] ++ expression (BExpr.lowerList bs)) = true
    rw [LocSim.lowAs_append, LocSim.lowAs_vals, LocSim.lowAs_expression, heff.low]
    rfl
  obtain ⟨-, -, -, hlow⟩ := LocSim.steps_low hrun hlow0 (LocSim.Agree.refl n f.locals)
  obtain ⟨hS, Cf, Ct, hf, hu, hle, -, hty⟩ := hT'
  -- the frame's locals keep their number
  have hlen' : Ct.locals.length = c'.frame.locals.length := by
    have h1 := LocalsLe.length_le hle.le
    have h2 := LocalsLe.length_le hu.le
    have h3 := (FrameOk.ctx_fields hf).2.2
    have h4 : c'.frame.locals.length = f.locals.length := steps_locals_length hrun
    omega
  have hR' : Ct.return_ = none := by rw [hle.eq]; exact hR
  have hout := progress_aux (P := P) divHost_ok hS hty c'.frame [] (ctxOk_of hf hu hlen') .nil
  simp only [vals, List.map_nil, List.nil_append, hR'] at hout
  -- no step at all (a host step would need a call redex)
  have hnostep : ∀ x, ¬ Step P (divHost (H := H)) c' x := by
    intro x hx
    rcases Step.split_host hx with hn | ⟨E, a, hh, args, hdc, -⟩
    · exact hnf x (Step.of_noHost _ hn)
    · rw [decompose?_none_of_low hlow] at hdc
      cases hdc
  rcases hout with ⟨vs, hvs, hvt⟩ | ⟨x, hx⟩ | ⟨vs, rest, hc⟩ | ⟨vs, a, rest, hc⟩ |
    ⟨vs, l, rest, tl, hc, -, -⟩ | ⟨vs, rest, rt, -, h1, -⟩ | ⟨vs, r, c, rest, rt, -, -, h1, -⟩
  · obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
      have := hvt.length_eq
      match vs, this with
      | [v], _ => exact ⟨v, rfl⟩
    exact ⟨c', v, hrun, hvs, ⟨hS, Cf, Ct, hf, hu, hle, wf_of_under hS hf hu hle hC₀, hty⟩, hext⟩
  · exact absurd hx (hnostep _)
  · -- a trap: the effects say there is none
    rcases trap_or_step (P := P) (host := divHost (H := H)) (s := c'.store) (f := c'.frame) vs rest
      with ⟨rfl, rfl⟩ | ⟨x, hx⟩
    · have := effects_control_trap heff.any heff.calls hrun (junk := []) (by simpa using hc)
      rw [heff.trap, heff.implicitTrap] at this
      simp at this
    · exact absurd (by rw [← hc] at hx; exact hx) (hnostep _)
  · -- a throw: low code has none
    rw [hc] at hlow
    simp [LocSim.lowAs_append, LocSim.lowAs_vals, throwing, LocSim.lowA, LocSim.lowI] at hlow
  · -- a branch: the effects say there is none
    have := effects_control_br (ws := vs) (l := l) heff.any hrun (junk := rest) (by rw [hc]; simp)
    rw [heff.breakTargets] at this
    cases this
  · cases h1
  · cases h1

end Silmaril.Wasm.Binaryen.OpRun
