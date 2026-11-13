module

public import Silmaril.Machine.LambdaRTLLir.Sim.Defs

/-!
# λRTL to the C-backend `Lir` machine: simulation proofs

Restated in `Silmaril.Machine.LambdaRTLLir.Sim.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.LambdaRTLLir.Sim

open Silmaril.Machine.Lir
open Silmaril.Machine.LambdaRTLLir (LVal)
open Silmaril.Machine.LambdaRTLLir.Sim
open Silmaril.SSA.LambdaRTL (Region Model Val upd obs)

set_option linter.unusedSectionVars false

variable {R L : Type} [DecidableEq R] [DecidableEq L]

/-! ## Agreement -/

theorem agreeOn_mono {S T : Finset R} {σ : R → LVal} {fr : Frame R} (h : AgreeOn S σ fr)
    (hT : T ⊆ S) : AgreeOn T σ fr :=
  fun x hx => h x (hT hx)

theorem agreeOn_let1 {x : R} {o : Silmaril.SSA.LambdaRTL.Op R COp} {k : Region R L COp}
    {σ : R → LVal} {fr : Frame R} (w : Word) (h : AgreeOn (Region.let1 x o k).fv σ fr) :
    AgreeOn k.fv (upd σ x (.word w)) (fr.set x w) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    simp [upd, wordOf]
  · have hm : y ∈ (Region.let1 x o k).fv := by simp [Region.fv, hy, hyx]
    simp [upd, hyx, h y hm]

/-! ## One binding -/

theorem opLower_exec {x : R} {o : Silmaril.SSA.LambdaRTL.Op R COp} {i : Op R}
    (h : opLower x o = some i) {σ : R → LVal} {fr : Frame R} (hag : AgreeOn o.fv σ fr)
    (m : Memory) :
    (o.eval cmodel σ = none ∧ i.exec fr m = none) ∨
      ∃ w, o.eval cmodel σ = some (.word w) ∧ i.exec fr m = some (fr.set x w, m) := by
  rcases o with a | ⟨f, a⟩ | a | a | a
  · cases h
  · rcases f with w | u | b | _
    · cases h
      exact .inr ⟨w, rfl, rfl⟩
    · rcases a with y | _ | ⟨a₁, a₂⟩ <;> cases h
      have hy : fr.get y = wordOf (σ y) := hag y (by simp [Silmaril.SSA.LambdaRTL.Op.fv, Val.fv])
      have hev : (Silmaril.SSA.LambdaRTL.Op.app (COp.unary u) (Val.var y)).eval cmodel σ =
          capp (.unary u) (σ y) := rfl
      have hex : (Op.unary u x y).exec fr m =
          (wordOf (σ y)).map fun v => (fr.set x (u.eval v), m) := by
        show (fr.get y).map _ = _
        rw [hy]
      rw [hev, hex]
      cases σ y with
      | word v => exact .inr ⟨u.eval v, rfl, rfl⟩
      | unit => exact .inl ⟨rfl, rfl⟩
      | pair _ _ => exact .inl ⟨rfl, rfl⟩
      | inl _ => exact .inl ⟨rfl, rfl⟩
      | inr _ => exact .inl ⟨rfl, rfl⟩
    · rcases a with _ | _ | ⟨a₁, a₂⟩ <;> try cases h
      rcases a₁ with y | _ | _ <;> rcases a₂ with z | _ | _ <;> cases h
      have hy : fr.get y = wordOf (σ y) := hag y (by simp [Silmaril.SSA.LambdaRTL.Op.fv, Val.fv])
      have hz : fr.get z = wordOf (σ z) := hag z (by simp [Silmaril.SSA.LambdaRTL.Op.fv, Val.fv])
      have hev : (Silmaril.SSA.LambdaRTL.Op.app (COp.binary b) (Val.pair (.var y) (.var z))).eval
          cmodel σ = capp (.binary b) (.pair (σ y) (σ z)) := rfl
      have hex : (Op.binary b x y z).exec fr m =
          (wordOf (σ y)).bind fun v => (wordOf (σ z)).bind fun v' =>
            (b.eval v v').map fun r => (fr.set x r, m) := by
        show (fr.get y).bind _ = _
        rw [hy, hz]
      rw [hev, hex]
      cases σ y with
      | word v =>
        cases σ z with
        | word v' =>
          show ((b.eval v v').map LVal.word = none ∧
              (b.eval v v').map (fun r => (fr.set x r, m)) = none) ∨
            ∃ w, (b.eval v v').map LVal.word = some (.word w) ∧
              (b.eval v v').map (fun r => (fr.set x r, m)) = some (fr.set x w, m)
          cases b.eval v v' with
          | none => exact .inl ⟨rfl, rfl⟩
          | some r => exact .inr ⟨r, rfl, rfl⟩
        | unit => exact .inl ⟨rfl, rfl⟩
        | pair _ _ => exact .inl ⟨rfl, rfl⟩
        | inl _ => exact .inl ⟨rfl, rfl⟩
        | inr _ => exact .inl ⟨rfl, rfl⟩
      | unit => exact .inl ⟨rfl, rfl⟩
      | pair _ _ => exact .inl ⟨rfl, rfl⟩
      | inl _ => exact .inl ⟨rfl, rfl⟩
      | inr _ => exact .inl ⟨rfl, rfl⟩
    · cases h
  · cases h
  · cases h
  · cases h

/-! ## The lowerable prefix -/

theorem evalObs_let1 (x : R) (o : Silmaril.SSA.LambdaRTL.Op R COp) (k : Region R L COp)
    (σ : R → LVal) :
    (Region.let1 x o k).evalObs cmodel σ =
      o.eval cmodel σ >>= fun a => k.evalObs cmodel (upd σ x a) := by
  simp only [Region.evalObs, Region.evalRTL]
  cases o.eval cmodel σ <;> rfl

theorem lowerPre_let1_some {x : R} {o : Silmaril.SSA.LambdaRTL.Op R COp} {k : Region R L COp}
    {i : Op R} (hi : opLower x o = some i) :
    lower (.let1 x o k) = i :: lower k ∧ tail (.let1 x o k) = tail k := by
  simp [lower, tail, lowerPre, hi]

theorem lowerPre_let1_none {x : R} {o : Silmaril.SSA.LambdaRTL.Op R COp} {k : Region R L COp}
    (hi : opLower x o = none) :
    lower (.let1 x o k) = [] ∧ tail (.let1 x o k) = .let1 x o k := by
  simp [lower, tail, lowerPre, hi]

/-- The lowered prefix runs as the λRTL prefix: both fail, or both succeed (memory unchanged)
with agreeing store and frame, and the region's outcome is the tail's outcome. -/
theorem prefix_sim (k : Region R L COp) (σ : R → LVal) (fr : Frame R) (m : Memory)
    (hag : AgreeOn k.fv σ fr) :
    (execOps (lower k) fr m = none ∧ k.evalObs cmodel σ = none) ∨
      ∃ σ' fr', execOps (lower k) fr m = some (fr', m) ∧
        k.evalObs cmodel σ = (tail k).evalObs cmodel σ' ∧ AgreeOn (tail k).fv σ' fr' := by
  induction k generalizing σ fr with
  | br ℓ a => exact .inr ⟨σ, fr, rfl, rfl, hag⟩
  | let2 x y o k _ => exact .inr ⟨σ, fr, rfl, rfl, hag⟩
  | case o x k₁ y k₂ _ _ => exact .inr ⟨σ, fr, rfl, rfl, hag⟩
  | join k₁ ℓ x k₂ _ _ => exact .inr ⟨σ, fr, rfl, rfl, hag⟩
  | let1 x o k ih =>
    cases hi : opLower x o with
    | none =>
      obtain ⟨e₁, e₂⟩ := lowerPre_let1_none (k := k) hi
      rw [e₁, e₂]
      exact .inr ⟨σ, fr, rfl, rfl, hag⟩
    | some i =>
      obtain ⟨e₁, e₂⟩ := lowerPre_let1_some (k := k) hi
      rw [e₁, e₂, execOps_cons, evalObs_let1]
      have hop := opLower_exec hi (agreeOn_mono hag (by simp [Region.fv])) m
      rcases hop with ⟨h₁, h₂⟩ | ⟨w, h₁, h₂⟩
      · rw [h₁, h₂]
        exact .inl ⟨rfl, rfl⟩
      · rw [h₁, h₂]
        exact ih (upd σ x (.word w)) (fr.set x w) (agreeOn_let1 w hag)

/-! ## `Lir` executions of blocks -/

theorem behaves_of_steps {p : Prog R} {s t : State R} {b : Behavior} (hb : b ≠ .diverges)
    (h : Steps p s t) (h' : Behaves p t b) : Behaves p s b := by
  cases b with
  | returned vs m =>
    obtain ⟨u, hu, hst⟩ := h'
    exact show ∃ u, Steps p s u ∧ _ from ⟨u, h.trans hu, hst⟩
  | trapped m =>
    obtain ⟨u, hu, hst⟩ := h'
    exact show ∃ u, Steps p s u ∧ _ from ⟨u, h.trans hu, hst⟩
  | stuck =>
    obtain ⟨u, hu, hst⟩ := h'
    exact show ∃ u, Steps p s u ∧ _ from ⟨u, h.trans hu, hst⟩
  | diverges => exact absurd rfl hb

theorem expect_ne_diverges (o : Option (L × LVal)) (m : Memory) : expect o m ≠ .diverges := by
  unfold expect
  split <;> simp

/-- A failing operation in a block makes the run stuck. -/
theorem stuck_of_execOps_none {p : Prog R} {b : Block R} :
    ∀ {os : List (Op R)} {s : State R} {rest : List (Instr R)},
    p.block? s.point.func s.point.label = some b →
    b.instrs.drop s.point.index = os.map .op ++ rest →
    execOps os s.frame s.mem = none → Behaves p s .stuck
  | [], _, _, _, _, hx => by simp at hx
  | o :: os, s, rest, hb, hcode, hx => by
    rw [execOps_cons] at hx
    cases h₁ : o.exec s.frame s.mem with
    | none =>
      have hi : b.instrs[s.point.index]? = some (.op o) := by
        have := congrArg (fun l => l[0]?) hcode
        simpa [List.getElem?_drop] using this
      have hf := Prog.fetch_eq_instr hb hi
      exact show ∃ u, Steps p s u ∧ _ from ⟨s, .refl, by simp [step, hf, h₁]⟩
    | some r =>
      obtain ⟨fr₁, m₁⟩ := r
      simp only [h₁, Option.bind_some] at hx
      have st := step_op_at hb (by simpa using hcode) h₁
      have tl := stuck_of_execOps_none (os := os)
        (s := ⟨⟨s.point.func, s.point.label, s.point.index + 1⟩, fr₁, s.stack, m₁⟩)
        (rest := rest) hb (drop_succ_of_cons (by simpa using hcode)) hx
      exact behaves_of_steps (by simp) (Relation.ReflTransGen.single st) tl

/-- The `ret [reg r]` step of a top-level activation. -/
theorem step_ret {p : Prog R} {s : State R} {r : R}
    (hf : p.fetch s.point = some (.term (.ret [.reg r]))) (hs : s.stack = []) :
    step p s = match s.frame.get r with
      | some w => .returned [w] s.mem
      | none => .stuck := by
  cases hg : s.frame.get r with
  | none =>
    have hg' : s.frame.regs r = none := hg
    simp [step, hf, Frame.readAll, Frame.read, hg']
  | some w =>
    have hg' : s.frame.regs r = some w := hg
    simp [step, hf, hs, Frame.readAll, Frame.read, hg']

/-! ## Straight-line simulation -/

theorem evalObs_br (ℓ : L) (r : R) (σ : R → LVal) :
    (Region.br ℓ (.var r) : Region R L COp).evalObs cmodel σ = some (ℓ, σ r) := rfl

/-- Running the block of a straight-line region from its first instruction, in a frame that
agrees with the store on the region's free registers, has the behaviour `expect` predicts. -/
theorem behaves_straight {p : Prog R} {s : State R} {k : Region R L COp} {ℓ : L} {r : R}
    {σ : R → LVal} (htail : tail k = .br ℓ (.var r))
    (hb : p.block? s.point.func s.point.label = some (retBlock k r))
    (hi : s.point.index = 0) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame) :
    Behaves p s (expect (k.evalObs cmodel σ) s.mem) := by
  have hcode : (retBlock k r).instrs.drop s.point.index = (lower k).map .op ++ [] := by
    simp [hi, retBlock]
  rcases prefix_sim k σ s.frame s.mem hag with ⟨h₁, h₂⟩ | ⟨σ', fr', h₁, h₂, h₃⟩
  · rw [h₂]
    exact stuck_of_execOps_none hb hcode h₁
  · have steps := steps_execOps hb hcode h₁
    have hf := Prog.fetch_eq_term (p := p)
      (pt := ⟨s.point.func, s.point.label, s.point.index + (lower k).length⟩) hb
      (by simp [hi, retBlock])
    have hst := step_ret (s := ⟨⟨s.point.func, s.point.label, s.point.index + (lower k).length⟩,
      fr', s.stack, s.mem⟩) hf hs
    have hfr : fr'.get r = wordOf (σ' r) := h₃ r (by rw [htail]; simp [Region.fv, Val.fv])
    rw [h₂, htail, evalObs_br]
    simp only [expect, Option.bind_some]
    simp only [hfr] at hst
    cases hw : wordOf (σ' r) with
    | none =>
      rw [hw] at hst
      exact show ∃ u, Steps p s u ∧ _ from ⟨_, steps, hst⟩
    | some w =>
      rw [hw] at hst
      exact show ∃ u, Steps p s u ∧ _ from ⟨_, steps, hst⟩

theorem behaves_iff_of {p : Prog R} {s : State R} {e : Behavior} (h : Behaves p s e)
    (b : Behavior) : Behaves p s b ↔ b = e :=
  ⟨fun hb => Behaves.unique hb h, fun hb => hb ▸ h⟩

/-- The start state of a function: entry point, fresh frame from the parameters, empty stack. -/
theorem start_eq {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory} {s : State R}
    (h : p.start f args mem = some s) :
    ∃ fn fr, p.func? f = some fn ∧ Frame.empty.writeAll fn.params args = some fr ∧
      s = ⟨⟨f, fn.entry, 0⟩, fr, [], mem⟩ := by
  unfold Prog.start Prog.enter at h
  cases hf : p.func? f with
  | none => simp [hf] at h
  | some fn =>
    cases hw : (Frame.empty : Frame R).writeAll fn.params args with
    | none => simp [hf, hw] at h
    | some fr =>
      simp only [hf, hw, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨fn, fr, rfl, hw, h.symm⟩

/-! ## One conditional -/

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by
  simp [h]

theorem evalObs_case_test (c x y : R) (r₁ r₂ : Region R L COp) (σ : R → LVal) :
    (Region.case (.app .test (.var c)) x r₁ y r₂).evalObs cmodel σ =
      match wordOf (σ c) with
      | none => none
      | some v => if v = 0 then r₂.evalObs cmodel (upd σ y .unit)
          else r₁.evalObs cmodel (upd σ x .unit) := by
  simp only [Region.evalObs, Region.evalRTL, Silmaril.SSA.LambdaRTL.Op.eval, Val.eval]
  cases hσ : σ c with
  | word v =>
    by_cases hv : v = 0
    · have e : cmodel.app COp.test (LVal.word v) = some (.inr .unit) := by
        show (some (if v ≠ 0 then LVal.inl .unit else .inr .unit) : Option LVal) = _
        rw [ite_neg' (not_not.mpr hv)]
      rw [e]
      simp only [wordOf]
      rw [ite_pos' hv]
      rfl
    · have e : cmodel.app COp.test (LVal.word v) = some (.inl .unit) := by
        show (some (if v ≠ 0 then LVal.inl .unit else .inr .unit) : Option LVal) = _
        rw [ite_pos' hv]
      rw [e]
      simp only [wordOf]
      rw [ite_neg' hv]
      rfl
  | unit => rfl
  | pair _ _ => rfl
  | inl _ => rfl
  | inr _ => rfl

theorem agreeOn_branch {S T : Finset R} {σ : R → LVal} {fr : Frame R} {x : R} (a : LVal)
    (h : AgreeOn S σ fr) (hx : x ∉ T) (hT : T.erase x ⊆ S) : AgreeOn T (upd σ x a) fr := by
  intro z hz
  have hzx : z ≠ x := fun e => hx (e ▸ hz)
  rw [show upd σ x a z = σ z from ite_neg' hzx _ _]
  exact h z (hT (Finset.mem_erase.mpr ⟨hzx, hz⟩))

/-- Running the lowered conditional program from its entry has the predicted behaviour. -/
theorem behaves_cond {params : List (Loc R)} {k r₁ r₂ : Region R L COp} {c x y a b : R}
    {ℓ₁ ℓ₂ : L} {s : State R} {σ : R → LVal}
    (htail : tail k = .case (.app .test (.var c)) x r₁ y r₂)
    (h₁ : tail r₁ = .br ℓ₁ (.var a)) (h₂ : tail r₂ = .br ℓ₂ (.var b))
    (hx : x ∉ r₁.fv) (hy : y ∉ r₂.fv)
    (hpt : s.point = ⟨0, 0, 0⟩) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame) :
    Behaves (condProg params k c r₁ a r₂ b) s (expect (k.evalObs cmodel σ) s.mem) := by
  obtain ⟨⟨f, l, i⟩, fr, st, mem⟩ := s
  simp only [Point.mk.injEq] at hpt
  obtain ⟨rfl, rfl, rfl⟩ := hpt
  simp only at hs
  subst hs
  simp only at hag ⊢
  have hb : (condProg params k c r₁ a r₂ b).block? 0 0 =
      some ⟨(lower k).map .op, .branch c 1 2⟩ := rfl
  have hcode : (Block.mk ((lower k).map Instr.op) (.branch c 1 2)).instrs.drop 0 =
      (lower k).map .op ++ [] := by
    simp
  rcases prefix_sim k σ fr mem hag with ⟨e₁, e₂⟩ | ⟨σ', fr', e₁, e₂, e₃⟩
  · rw [e₂]
    exact stuck_of_execOps_none (s := ⟨⟨0, 0, 0⟩, fr, [], mem⟩) hb hcode e₁
  · have steps := steps_execOps (s := ⟨⟨0, 0, 0⟩, fr, [], mem⟩) hb hcode e₁
    have hf := Prog.fetch_eq_term (p := condProg params k c r₁ a r₂ b)
      (pt := ⟨0, 0, 0 + (lower k).length⟩) hb (by simp)
    rw [htail] at e₃
    have hc : fr'.get c = wordOf (σ' c) :=
      e₃ c (by simp [Region.fv, Silmaril.SSA.LambdaRTL.Op.fv, Val.fv])
    rw [e₂, htail, evalObs_case_test]
    cases hw : wordOf (σ' c) with
    | none =>
      have hst : step (condProg params k c r₁ a r₂ b)
          ⟨⟨0, 0, 0 + (lower k).length⟩, fr', [], mem⟩ = .stuck := by
        have hc' : fr'.get c = none := hc.trans hw
        unfold step
        rw [hf]
        simp only [hc']
      exact show ∃ u, Steps _ _ u ∧ _ from ⟨_, steps, hst⟩
    | some v =>
      have hst := (Transition.branch (p := condProg params k c r₁ a r₂ b)
        (s := ⟨⟨0, 0, 0 + (lower k).length⟩, fr', [], mem⟩) hf (hc.trans hw)).step_eq
      have steps' := steps.tail hst
      simp only at steps' ⊢
      refine behaves_of_steps (expect_ne_diverges _ _) steps' ?_
      by_cases hv : v = 0
      · rw [ite_pos' hv 2 1, ite_pos' hv (r₂.evalObs cmodel (upd σ' y .unit)) _]
        have hag₂ : AgreeOn r₂.fv (upd σ' y .unit) fr' :=
          agreeOn_branch _ e₃ hy (by
            intro z hz; simp only [Region.fv, Finset.mem_union]; exact .inr hz)
        exact behaves_straight (p := condProg params k c r₁ a r₂ b)
          (s := ⟨⟨0, 2, 0⟩, fr', [], mem⟩) h₂ rfl rfl rfl hag₂
      · rw [ite_neg' hv 2 1, ite_neg' hv _ (r₁.evalObs cmodel (upd σ' x .unit))]
        have hag₁ : AgreeOn r₁.fv (upd σ' x .unit) fr' :=
          agreeOn_branch _ e₃ hx (by
            intro z hz; simp only [Region.fv, Finset.mem_union]; exact .inl (.inr hz))
        exact behaves_straight (p := condProg params k c r₁ a r₂ b)
          (s := ⟨⟨0, 1, 0⟩, fr', [], mem⟩) h₁ rfl rfl rfl hag₁

end Silmaril.Proofs.Machine.LambdaRTLLir.Sim
