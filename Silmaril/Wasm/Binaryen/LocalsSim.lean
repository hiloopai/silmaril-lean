module

public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Profile code ignores the locals it does not mention

`lowAs n code` says that the administrative code `code` consists of profile
instructions (constants, integer operators, locals, globals, `select`, `drop`,
`nop`, `unreachable`, branches, `return`, `block`/`loop`/`if`), values, labels
and traps, and that every local it reads or writes has index below `n`. No
calls, frames, handlers or exceptions.

Such code runs the same in every frame that agrees with the current one on the
locals below `n` (`step_low`, `steps_low`, `diverges_low`): the run in the other
frame visits the same stores and code, and the frames keep agreeing below `n`.
This is the frame-independence half of Binaryen's inlined block
(`inlineN_resolves`): the operands, stored one by one into the callee's locals
`base ..`, never look at them.
-/

namespace Silmaril.Wasm.Binaryen.LocSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

mutual
/-- A profile instruction whose local accesses are below `n`. -/
def lowI (n : Nat) : Instr → Bool
  | .nop => true
  | .unreachable => true
  | .drop => true
  | .select _ => true
  | .block _ b => lowIs n b
  | .loop _ b => lowIs n b
  | .if_ _ b₁ b₂ => lowIs n b₁ && lowIs n b₂
  | .br _ => true
  | .brIf _ => true
  | .brTable _ _ => true
  | .return_ => true
  | .localGet x => decide (x.toNat < n)
  | .localSet x => decide (x.toNat < n)
  | .localTee x => decide (x.toNat < n)
  | .globalGet _ => true
  | .globalSet _ => true
  | .intConst _ _ => true
  | .floatConst _ _ => true
  | .vecConst _ => true
  | .intUnOp _ _ => true
  | .intBinOp _ _ => true
  | .intTestOp _ _ => true
  | .intRelOp _ _ => true
  | _ => false
/-- `lowI` on a list. -/
def lowIs (n : Nat) : List Instr → Bool
  | [] => true
  | i :: is => lowI n i && lowIs n is
end

mutual
/-- Administrative code of the profile whose local accesses are below `n`. -/
def lowA (n : Nat) : Admin → Bool
  | .plain i => lowI n i
  | .ref _ => true
  | .label _ cont b => lowIs n cont && lowAs n b
  | .trap => true
  | _ => false
/-- `lowA` on a list. -/
def lowAs (n : Nat) : List Admin → Bool
  | [] => true
  | a :: as => lowA n a && lowAs n as
end

@[simp] theorem lowAs_nil (n : Nat) : lowAs n [] = true := rfl

@[simp] theorem lowAs_cons (n : Nat) (a : Admin) (as : List Admin) :
    lowAs n (a :: as) = (lowA n a && lowAs n as) := rfl

theorem lowAs_append (n : Nat) : ∀ a b : List Admin, lowAs n (a ++ b) = (lowAs n a && lowAs n b)
  | [], b => by simp
  | x :: a, b => by simp [lowAs_append n a b, Bool.and_assoc]

@[simp] theorem lowA_val (n : Nat) (v : Val) : lowA n v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem lowA_constI32 (n : Nat) (c : BitVec 32) : lowA n (constI32 c) = true :=
  lowA_val n _

theorem lowAs_vals (n : Nat) : ∀ vs : List Val, lowAs n (vals vs) = true
  | [] => rfl
  | v :: vs => by
    show lowAs n (v.toAdmin :: vals vs) = true
    rw [lowAs_cons, lowA_val, lowAs_vals n vs]
    rfl

theorem lowAs_expression (n : Nat) : ∀ is : List Instr, lowAs n (expression is) = lowIs n is
  | [] => rfl
  | i :: is => by
    show lowAs n (.plain i :: expression is) = _
    rw [lowAs_cons, lowAs_expression n is]
    rfl

theorem lowA_callRef {n : Nat} {c : Admin} (hc : c.IsCallRef) : lowA n c = false := by
  cases c with
  | plain i => cases i <;> first | rfl | exact hc.elim
  | _ => first | rfl | exact hc.elim

theorem lowA_returnCallRef {n : Nat} {c : Admin} (hc : c.IsReturnCallRef) : lowA n c = false := by
  cases c with
  | plain i => cases i <;> first | rfl | exact hc.elim
  | _ => first | rfl | exact hc.elim

/-! ## Agreement below `n` -/

/-- Two local vectors of the same length agreeing below `n`. -/
def Agree (n : Nat) (l l' : List (Option Val)) : Prop :=
  l.length = l'.length ∧ ∀ i < n, l[i]? = l'[i]?

theorem Agree.refl (n : Nat) (l : List (Option Val)) : Agree n l l := ⟨rfl, fun _ _ => rfl⟩

theorem Agree.set {n : Nat} {l l' : List (Option Val)} (h : Agree n l l') (j : Nat)
    (a : Option Val) : Agree n (l.set j a) (l'.set j a) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  simp only [List.getElem?_set, h.1, h.2 i hi]

/-! ## Outputs of the pure families -/

theorem parametric_low {n : Nat} {is is' : List Admin} (h : ParametricStep is is') :
    lowAs n is' = true := by
  cases h <;> simp [lowA]

theorem numeric_low {n : Nat} {is is' : List Admin} (h : NumericStep P is is') :
    lowAs n is' = true := by
  cases h <;> simp [lowA, lowI]

/-! ## The simulation -/

/-- **One step in another frame.** Low code takes the same step in a frame that
agrees below `n` (same module), and stays low; the frames keep agreeing. -/
theorem step_low {c c' : Config H} (h : Step P host c c') {n : Nat} {gl : List (Option Val)}
    (hlow : lowAs n c.code = true) (hg : Agree n c.frame.locals gl) :
    ∃ gl', Step P host ⟨c.store, ⟨gl, c.frame.module⟩, c.code⟩
        ⟨c'.store, ⟨gl', c'.frame.module⟩, c'.code⟩ ∧
      Agree n c'.frame.locals gl' ∧ lowAs n c'.code = true := by
  induction h generalizing gl
  all_goals first
    | (exfalso
       simp only [lowAs_append, lowAs_vals, lowAs_cons, lowAs_nil, lowA, lowI, throwing,
         lowA_val, lowA_constI32, Bool.and_true, Bool.true_and, Bool.and_false,
         Bool.false_and, Bool.false_eq_true] at hlow
       done)
    | skip
  case parametric s f is is' hp => exact ⟨gl, .parametric hp, hg, parametric_low hp⟩
  case numeric s f is is' hp => exact ⟨gl, .numeric hp, hg, numeric_low hp⟩
  case vector s f is is' hv =>
    exfalso
    cases hv <;> simp [lowA, lowI, vconst] at hlow
  case «variable» c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    cases hv with
    | @localGet _ _ x v hx =>
      have hxn : x.toNat < n := by simpa [lowA, lowI] using hlow
      refine ⟨gl, .variable (.localGet ?_), hg, by simp⟩
      show gl[x.toNat]? = some (some v)
      rw [← hg.2 _ hxn]
      exact hx
    | @localSet _ _ x v hx =>
      have hxn : x.toNat < n := by simpa [lowA, lowI] using hlow
      exact ⟨gl.set x.toNat (some v), .variable (.localSet (by rw [← hg.1]; exact hx)),
        hg.set x.toNat (some v), rfl⟩
    | @localTee _ _ x v =>
      have hxn : x.toNat < n := by simpa [lowA, lowI] using hlow
      exact ⟨gl, .variable .localTee, hg, by simp [lowA, lowI, hxn]⟩
    | globalGet hx => exact ⟨gl, .variable (.globalGet hx), hg, by simp⟩
    | globalSet hx => exact ⟨gl, .variable (.globalSet hx), hg, rfl⟩
  case table c c' ht =>
    exfalso
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    cases ht <;> simp [lowA, lowI] at hlow
  case memory c c' hm =>
    exfalso
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    cases hm <;> simp [lowA, lowI] at hlow
  case reference c c' hr =>
    exfalso
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    cases hr <;> simp [lowA, lowI] at hlow
  case aggregate c c' ha =>
    exfalso
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    cases ha <;> simp [lowAs_append, lowAs_vals, lowA, lowI] at hlow
  case ctxtInstrs s s' f f' vs is is' rest hs hne ih =>
    have hl : lowAs n is = true ∧ lowAs n rest = true := by
      simpa [lowAs_append, lowAs_vals] using hlow
    obtain ⟨gl', hs', hg', hl'⟩ := ih hl.1 hg
    refine ⟨gl', .ctxtInstrs hs' hne, hg', ?_⟩
    show lowAs n (vals vs ++ is' ++ rest) = true
    simp only [lowAs_append, lowAs_vals, hl', hl.2, Bool.and_self]
  case ctxtLabel s s' f f' k cont is is' hs ih =>
    have hl : lowIs n cont = true ∧ lowAs n is = true := by
      simpa [lowA] using hlow
    obtain ⟨gl', hs', hg', hl'⟩ := ih hl.2 hg
    refine ⟨gl', .ctxtLabel hs', hg', ?_⟩
    show lowAs n [.label k cont is'] = true
    simp [lowA, hl.1, hl']
  case block s f bt body vs t₁ t₂ hbt hm =>
    refine ⟨gl, .block hbt hm, hg, ?_⟩
    have hb : lowIs n body = true := by simpa [lowAs_append, lowAs_vals, lowA, lowI] using hlow
    show lowAs n [.label t₂.length [] (vals vs ++ expression body)] = true
    simp [lowA, lowIs, lowAs_append, lowAs_vals, lowAs_expression, hb]
  case loop s f bt body vs t₁ t₂ hbt hm =>
    refine ⟨gl, .loop hbt hm, hg, ?_⟩
    have hb : lowIs n body = true := by simpa [lowAs_append, lowAs_vals, lowA, lowI] using hlow
    show lowAs n [.label t₁.length [.loop bt body] (vals vs ++ expression body)] = true
    simp [lowA, lowIs, lowI, lowAs_append, lowAs_vals, lowAs_expression, hb]
  case ifTrue s f c bt b₁ b₂ hc =>
    refine ⟨gl, .ifTrue hc, hg, ?_⟩
    have hb : lowIs n b₁ = true ∧ lowIs n b₂ = true := by simpa [lowA, lowI] using hlow
    show lowAs n [.plain (.block bt b₁)] = true
    simp [lowA, lowI, hb.1]
  case ifFalse s f bt b₁ b₂ =>
    refine ⟨gl, .ifFalse, hg, ?_⟩
    have hb : lowIs n b₁ = true ∧ lowIs n b₂ = true := by simpa [lowA, lowI] using hlow
    show lowAs n [.plain (.block bt b₂)] = true
    simp [lowA, lowI, hb.2]
  case labelVals s f k cont vs =>
    exact ⟨gl, .labelVals, hg, lowAs_vals n vs⟩
  case brLabelZero s f k cont vs' vs l rest hl hn =>
    refine ⟨gl, .brLabelZero hl hn, hg, ?_⟩
    have hc : lowIs n cont = true := by
      have h' := hlow
      simp [lowA, lowAs_append, lowAs_vals] at h'
      exact h'.1
    show lowAs n (vals vs ++ expression cont) = true
    simp [lowAs_append, lowAs_vals, lowAs_expression, hc]
  case brLabelSucc s f k cont vs l rest hl =>
    refine ⟨gl, .brLabelSucc hl, hg, ?_⟩
    show lowAs n (vals vs ++ [.plain (.br (labelPred l))]) = true
    simp [lowAs_append, lowAs_vals, lowA, lowI]
  case brIfTrue s f c l hc =>
    exact ⟨gl, .brIfTrue hc, hg, rfl⟩
  case brIfFalse s f l =>
    exact ⟨gl, .brIfFalse, hg, rfl⟩
  case brTableLt s f i ls l' l hi =>
    exact ⟨gl, .brTableLt hi, hg, rfl⟩
  case brTableGe s f i ls l' hi =>
    exact ⟨gl, .brTableGe hi, hg, rfl⟩
  case callRefNull s f c hc =>
    exfalso
    have := lowA_callRef (n := n) hc
    simp_all
  case callRefFunc s f c vs a fi ps rs code hc hf he hn hcode =>
    exfalso
    have := lowA_callRef (n := n) hc
    simp_all [lowAs_append, lowAs_vals]
  case callRefHost s s' f c vs a fi ps rs h r hc hf he hn hcode hhost =>
    exfalso
    have := lowA_callRef (n := n) hc
    simp_all [lowAs_append, lowAs_vals]
  case callRefHostDiv s f c vs a fi ps rs h hc hf he hn hcode hhost =>
    exfalso
    have := lowA_callRef (n := n) hc
    simp_all [lowAs_append, lowAs_vals]
  case returnCallRefLabel s f k cont vs c rest hc =>
    exfalso
    have := lowA_returnCallRef (n := n) hc
    simp_all [lowA, lowAs_append, lowAs_vals]
  case returnLabel s f k cont vs rest =>
    refine ⟨gl, .returnLabel, hg, ?_⟩
    show lowAs n (vals vs ++ [.plain .return_]) = true
    simp [lowAs_append, lowAs_vals, lowA, lowI]
  case trapInstrs s f vs rest hne =>
    exact ⟨gl, .trapInstrs hne, hg, rfl⟩
  case trapLabel s f k cont =>
    exact ⟨gl, .trapLabel, hg, rfl⟩

/-- **Runs in another frame.** -/
theorem steps_low {c c' : Config H} (h : Steps P host c c') {n : Nat} {gl : List (Option Val)}
    (hlow : lowAs n c.code = true) (hg : Agree n c.frame.locals gl) :
    ∃ gl', Steps P host ⟨c.store, ⟨gl, c.frame.module⟩, c.code⟩
        ⟨c'.store, ⟨gl', c'.frame.module⟩, c'.code⟩ ∧
      Agree n c'.frame.locals gl' ∧ lowAs n c'.code = true := by
  induction h with
  | refl => exact ⟨gl, .refl, hg, hlow⟩
  | tail _ hs ih =>
    obtain ⟨gl₁, h₁, hg₁, hl₁⟩ := ih
    obtain ⟨gl₂, h₂, hg₂, hl₂⟩ := step_low hs hl₁ hg₁
    exact ⟨gl₂, h₁.tail h₂, hg₂, hl₂⟩

/-- **Divergence in another frame.** -/
theorem diverges_low {c : Config H} (h : Diverges P host c) {n : Nat} {gl : List (Option Val)}
    (hlow : lowAs n c.code = true) (hg : Agree n c.frame.locals gl) :
    Diverges P host ⟨c.store, ⟨gl, c.frame.module⟩, c.code⟩ := by
  refine InfiniteTrace.coinduct
    (fun d => ∃ (c : Config H) (gl : List (Option Val)), Diverges P host c ∧
      lowAs n c.code = true ∧ Agree n c.frame.locals gl ∧
      d = ⟨c.store, ⟨gl, c.frame.module⟩, c.code⟩) ?_ ⟨c, gl, h, hlow, hg, rfl⟩
  rintro d ⟨c, gl, hc, hl, hg, rfl⟩
  obtain ⟨c₁, hs, hc₁⟩ := InfiniteTrace.unfold hc
  obtain ⟨gl₁, hs', hg₁, hl₁⟩ := step_low hs hl hg
  exact ⟨_, hs', c₁, gl₁, hc₁, hl₁, hg₁, rfl⟩

/-! ## Context lifting of divergence -/

/-- Divergence under a value prefix and a suffix. -/
theorem diverges_ctxtInstrs {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (h : Diverges P host ⟨s, f, is⟩) : Diverges P host ⟨s, f, vals vs ++ is ++ rest⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · refine InfiniteTrace.coinduct
      (fun d => ∃ (c : Config H), Diverges P host c ∧
        d = ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩) ?_ ⟨_, h, rfl⟩
    rintro d ⟨⟨s, f, is⟩, hc, rfl⟩
    obtain ⟨⟨s₁, f₁, is₁⟩, hs, hc₁⟩ := InfiniteTrace.unfold hc
    exact ⟨_, .ctxtInstrs hs hne, ⟨s₁, f₁, is₁⟩, hc₁, rfl⟩
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using h

end Silmaril.Wasm.Binaryen.LocSim
