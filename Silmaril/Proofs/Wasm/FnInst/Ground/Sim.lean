module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Inv

@[expose] public section

/-! # The bridge: equal runs give silmaril's `BaseSim`

`gBaseSim`: `BaseSim P closedHost F GBI GB gCodeRank` at every numerical profile `P` and
every function relation `F`. How the right side (any code of the fragment) follows the left:

* a step of a stack-only left instruction is matched by **stuttering** (the right does not
  move, `gCodeRank` decreases), and the runtime pair keeps equal runs from every frame and
  every stack below (`pairRef_step`): a stack-only step neither reads nor writes the frame;
* when the left side becomes values, or at its `local.get` (pairs of the `read` kind), the
  right side **commits**: it runs its whole code at once (`run_steps`), to the values the left
  will have (`advance`), so the pairs never depend on the frame they were created in.

Also `g_noRedex` (no host call at the head of a left side), the rank laws
(`LawfulCodeRank gCodeRank`), and the exit and value laws (a left side always has a
non-value head that is not an exit).
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-! ## The rank -/

@[simp] theorem gCodeRank_nil : gCodeRank [] = 0 := rfl

@[simp] theorem gCodeRank_cons (a : Admin) (l : List Admin) :
    gCodeRank (a :: l) = gAdminRank a + gCodeRank l := rfl

@[simp] theorem gCodeRank_append (a b : List Admin) :
    gCodeRank (a ++ b) = gCodeRank a + gCodeRank b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Nat.add_assoc]

theorem gAdminRank_pos (a : Admin) : 0 < gAdminRank a := by
  unfold gAdminRank
  split <;> omega

theorem gCodeRank_pos {a : List Admin} (ha : a ≠ []) : 0 < gCodeRank a := by
  cases a with
  | nil => simp at ha
  | cons x a => have := gAdminRank_pos x; simp; omega

@[simp] theorem gAdminRank_val (v : Val) : gAdminRank v.toAdmin = 1 := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem gCodeRank_vals (vs : List Val) : gCodeRank (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change gAdminRank v.toAdmin + gCodeRank (vals vs) = vs.length + 1
    rw [gAdminRank_val, ih]
    omega

theorem gAdminRank_lower {i : GInstr} (hc : i.isConst = false) :
    gAdminRank (.plain i.lower) = 2 := by
  cases i <;> first | rfl | exact absurd hc (by simp [GInstr.isConst])

instance : LawfulCodeRank gCodeRank where
  context_lt := by intros; simp only [gCodeRank_append]; omega
  infix_lt := by
    intro p m q hm
    have := gCodeRank_pos hm
    simp only [gCodeRank_append]
    omega
  label_body_lt := by intros; simp [gAdminRank]; omega
  label_lt := by intros; simp_all [gAdminRank]
  handler_body_lt := by intros; simp [gAdminRank]; omega
  handler_lt := by intros; simp_all [gAdminRank]
  frame_body_lt := by intros; simp [gAdminRank]; omega
  frame_lt := by intros; simp_all [gAdminRank]

/-- An inverted step pushes at most one value. -/
theorem step1_length {i : GInstr} (hi : Inv i) {f f' : Frame} {X Y : List Val}
    (h : step1 i f X = some (f', Y)) : Y.length ≤ X.length + 1 := by
  rcases hi with ⟨hs | ⟨x, rfl⟩, hc⟩
  · obtain ⟨-, h'⟩ := step1_stk_inv hs h
    cases i with
    | const _ => cases hc
    | localGet _ | localSet _ | localTee _ => cases hs
    | bin _ => obtain ⟨_, _, _, rfl, rfl⟩ := stepS_bin_inv h'; simp
    | eqz => obtain ⟨_, _, rfl, rfl⟩ := stepS_eqz_inv h'; simp
    | drop => obtain ⟨_, rfl⟩ := stepS_drop_inv h'; simp only [List.length_cons]; omega
    | nop => obtain rfl := Option.some.inj h'; simp
  · obtain ⟨_, _, -, rfl⟩ := step1_get_inv h
    simp

theorem rank_step {i : GInstr} (hc : i.isConst = false) {W Y : List Val}
    (hY : Y.length ≤ W.length + 1) (R : List Admin) :
    gCodeRank (vals Y.reverse ++ R) < gCodeRank (vals W ++ .plain i.lower :: R) := by
  have h2 := gAdminRank_lower hc
  simp only [gCodeRank_append, gCodeRank_vals, gCodeRank_cons, List.length_reverse, h2]
  omega

/-! ## Shapes of the runtime pairs -/

theorem code_split (vs q : List Val) (ks : List (BitVec 32)) (i : GInstr) (a₁ : List GInstr)
    (rest : List Admin) :
    vals vs ++ (vals q ++ expression (lower (ks.map GInstr.const ++ i :: a₁))) ++ rest =
      vals (vs ++ q ++ kvals ks) ++ .plain i.lower :: (expression (lower a₁) ++ rest) := by
  have hk : expression (lower (ks.map GInstr.const)) = vals (kvals ks) := expression_consts ks
  have e : expression (lower (ks.map GInstr.const ++ i :: a₁)) =
      vals (kvals ks) ++ .plain i.lower :: expression (lower a₁) := by
    rw [← hk]
    simp [lower, expression]
  rw [e]
  simp [List.append_assoc]

/-- Every left side has a non-value head that the bridge can invert. -/
theorem gb_head {x y : List Admin} (h : GB x y) (vs : List Val) :
    ∃ W i R, Inv i ∧ vals vs ++ x = vals W ++ .plain i.lower :: R := by
  rcases h with ⟨q, a, r, b, rfl, -, ha, -⟩ | ⟨a, b, rfl, -, ⟨ha, -⟩ | ⟨⟨x₀, L, rfl, -⟩, -⟩⟩
  · obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
    refine ⟨vs ++ q ++ kvals ks, i, expression (lower a₁), ⟨Or.inl (ha.1 i (by simp)), hi⟩, ?_⟩
    simpa using code_split vs q ks i a₁ []
  · obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
    refine ⟨vs ++ [] ++ kvals ks, i, expression (lower a₁), ⟨Or.inl (ha.1 i (by simp)), hi⟩, ?_⟩
    simpa using code_split vs [] ks i a₁ []
  · exact ⟨vs, .localGet x₀, expression (lower L), ⟨Or.inr ⟨x₀, rfl⟩, rfl⟩,
      by simp [lower, expression]⟩

/-! ## The step law -/

/-- The conclusion of `BaseSim.step`, with the bridge's relations and rank. -/
def StepGoal (P : Profile) (F : FuncInst H → FuncInst H → Prop) (t s' : Store H)
    (f f' : Frame) (vs : List Val) (x y rest rest' es' : List Admin) : Prop :=
  ∃ (t' : Store H) (es'' : List Admin),
    (Relation.TransGen (Step P closedHost) ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t', f', es''⟩ ∨
      (t' = t ∧ f' = f ∧ es'' = vals vs ++ y ++ rest' ∧
        gCodeRank es' < gCodeRank (vals vs ++ x ++ rest))) ∧
    StoreRel F s' t' ∧ AdminsRel GBI GB es' es''

/-- **The right side moves (or stays) to code related to the left's.** -/
theorem advance {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs : List Val} {x y rest rest' X Z : List Admin} (hst : StoreRel F s t)
    (hXZ : AdminsRel GBI GB X Z)
    (hrun : Steps P closedHost ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t, f, Z ++ rest'⟩)
    (hrank : gCodeRank (X ++ rest) < gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel GBI GB rest rest') :
    StepGoal P F t s f f vs x y rest rest' (X ++ rest) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrun with he | ht
  · have hz : Z ++ rest' = vals vs ++ y ++ rest' := (Config.mk.inj he).2.2
    exact ⟨t, vals vs ++ y ++ rest', Or.inr ⟨rfl, rfl, rfl, hrank⟩, hst, hz ▸ hXZ.append hrest⟩
  · exact ⟨t, Z ++ rest', Or.inl ht, hst, hXZ.append hrest⟩

/-- A stack-only step keeps equal runs from every frame and every stack below. -/
theorem pairRef_step {q r Y : List Val} {vs : List Val} {ks : List (BitVec 32)} {i : GInstr}
    {a₁ b : List GInstr} {f : Frame} (hi : i.stk = true)
    (hp : PairRef q (ks.map GInstr.const ++ i :: a₁) r b)
    (hY : step1 i f (vs ++ q ++ kvals ks).reverse = some (f, Y)) :
    PairRef Y.reverse a₁ (vs ++ r) b := by
  intro f₀ S res h
  have hs : step1 i f₀ ((vs ++ q ++ kvals ks).reverse ++ S) = some (f₀, Y ++ S) :=
    (step1_stk hi hY).2 f₀ S
  have hrun : run (ks.map GInstr.const ++ i :: a₁) f₀ (q.reverse ++ (vs.reverse ++ S)) =
      some res := by
    rw [run_consts, run_cons]
    have e : (kvals ks).reverse ++ (q.reverse ++ (vs.reverse ++ S)) =
        (vs ++ q ++ kvals ks).reverse ++ S := by simp
    rw [e, hs]
    simpa using h
  simpa using hp f₀ (vs.reverse ++ S) res hrun

/-- The value of constant code. -/
theorem run_consts_only (ks : List (BitVec 32)) (f : Frame) (st : List Val) :
    run (ks.map GInstr.const) f st = some (f, (kvals ks).reverse ++ st) := by
  rw [← List.append_nil (ks.map GInstr.const), run_consts]
  rfl

/-- The rank of a stack-only step decreases. -/
theorem stk_rank {vs q Y : List Val} {ks : List (BitVec 32)} {i : GInstr} {a₁ : List GInstr}
    {rest : List Admin} {f : Frame} (hiS : i.stk = true) (hi : i.isConst = false)
    (hY : step1 i f (vs ++ q ++ kvals ks).reverse = some (f, Y)) :
    gCodeRank (vals Y.reverse ++ (expression (lower a₁) ++ rest)) <
      gCodeRank (vals vs ++ (vals q ++ expression (lower (ks.map GInstr.const ++ i :: a₁))) ++
        rest) := by
  have hlen : Y.length ≤ (vs ++ q ++ kvals ks).length + 1 := by
    have h₁ := step1_length ⟨Or.inl hiS, hi⟩ hY
    simp only [List.length_reverse] at h₁
    exact h₁
  have hrank := rank_step hi hlen (expression (lower a₁) ++ rest)
  rw [← code_split] at hrank
  exact hrank

/-- **The step law for a stack-only left side.** -/
theorem stk_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {a b : List GInstr} {rest rest' es' : List Admin}
    (hst : StoreRel F s t) (ha : StkOp a) (hp : PairRef q a r b)
    (hrest : AdminsRel GBI GB rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ (vals q ++ expression (lower a)) ++ rest⟩
      ⟨s', f', es'⟩) :
    StepGoal P F t s' f f' vs (vals q ++ expression (lower a))
      (vals r ++ expression (lower b)) rest rest' es' := by
  obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
  have hiS : i.stk = true := ha.1 i (by simp)
  rw [code_split] at hstep
  obtain ⟨Y, hY, hc⟩ := step_inv ⟨Or.inl hiS, hi⟩ hstep
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  have hp' : PairRef Y.reverse a₁ (vs ++ r) b := pairRef_step hiS hp hY
  have hrank := stk_rank (a₁ := a₁) (rest := rest) hiS hi hY
  have e : vals Y.reverse ++ (expression (lower a₁) ++ rest) =
      vals Y.reverse ++ expression (lower a₁) ++ rest := (List.append_assoc _ _ _).symm
  rw [e]
  by_cases hop : ∃ j ∈ a₁, j.isConst = false
  · have hB : GB (vals Y.reverse ++ expression (lower a₁)) (vals vs ++ (vals r ++
        expression (lower b))) :=
      Or.inl ⟨Y.reverse, a₁, vs ++ r, b, rfl, by simp,
        ⟨fun j hj => ha.1 j (by simp [hj]), hop⟩, hp'⟩
    exact advance hst (.base hB) .refl (by simpa using hrank) hrest
  · exact stk_finish hst hp' hop hrank hrest
where
  /-- The left side becomes values: the right side runs to them. -/
  stk_finish {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
      {vs r Y : List Val} {a₁ b : List GInstr} {x rest rest' : List Admin}
      (hst : StoreRel F s t) (hp' : PairRef Y.reverse a₁ (vs ++ r) b)
      (hop : ¬ ∃ j ∈ a₁, j.isConst = false)
      (hrank : gCodeRank (vals Y.reverse ++ (expression (lower a₁) ++ rest)) <
        gCodeRank (vals vs ++ x ++ rest))
      (hrest : AdminsRel GBI GB rest rest') :
      StepGoal P F t s f f vs x (vals r ++ expression (lower b)) rest rest'
        (vals Y.reverse ++ expression (lower a₁) ++ rest) := by
    obtain ⟨ks₂, rfl⟩ := all_consts hop
    have hb : run b f ((vs ++ r).reverse) = some (f, (kvals ks₂).reverse ++ Y) := by
      simpa using hp' f [] _ (by simpa using run_consts_only ks₂ f Y)
    have hrun := run_steps (P := P) (host := closedHost) (s := t) hb rest'
    have e : vals Y.reverse ++ expression (lower (ks₂.map GInstr.const)) =
        vals ((kvals ks₂).reverse ++ Y).reverse := by
      simp [expression_consts]
    rw [e]
    refine advance hst (.refl _) (by simpa using hrun) ?_ hrest
    rw [← e]
    simpa [List.append_assoc] using hrank

/-- After the read, the rest of the left side runs to the right side's values. -/
theorem read_pairRef {vs F₀ : List Val} {v : Val} {L : List GInstr}
    (hF' : ∀ f₀ S, run L f₀ ((v :: vs.reverse) ++ S) = some (f₀, F₀ ++ S)) :
    PairRef (vs ++ [v]) L F₀.reverse [] := by
  intro f₀ S res h
  have h₁ : run L f₀ (v :: (vs.reverse ++ S)) = some res := by simpa using h
  have h₂ : run L f₀ (v :: (vs.reverse ++ S)) = some (f₀, F₀ ++ S) := hF' f₀ S
  rw [h₂] at h₁
  rw [List.reverse_reverse]
  exact h₁

/-- After the read: the right side has run to the left side's final values. -/
theorem read_finish {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs F₀ : List Val} {v : Val} {L : List GInstr} {x y rest rest' : List Admin}
    (hst : StoreRel F s t) (hL : ∀ i ∈ L, i.stk = true)
    (hF : run L f (v :: vs.reverse) = some (f, F₀))
    (hF' : ∀ f₀ S, run L f₀ ((v :: vs.reverse) ++ S) = some (f₀, F₀ ++ S))
    (hrun : Steps P closedHost ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t, f, vals F₀.reverse ++ rest'⟩)
    (hrank : gCodeRank (vals (vs ++ [v]) ++ expression (lower L) ++ rest) <
      gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel GBI GB rest rest') :
    StepGoal P F t s f f vs x y rest rest' (vals (vs ++ [v]) ++ expression (lower L) ++ rest) := by
  by_cases hop : ∃ j ∈ L, j.isConst = false
  · show StepGoal P F t s f f vs x y rest rest' (vals (vs ++ [v]) ++ expression (lower L) ++ rest)
    have hp : PairRef (vs ++ [v]) L F₀.reverse [] := read_pairRef hF'
    have hB : GB (vals (vs ++ [v]) ++ expression (lower L)) (vals F₀.reverse) :=
      Or.inl ⟨vs ++ [v], L, F₀.reverse, [], rfl, by simp [lower, expression], ⟨hL, hop⟩, hp⟩
    exact advance hst (.base hB) hrun hrank hrest
  · show StepGoal P F t s f f vs x y rest rest' (vals (vs ++ [v]) ++ expression (lower L) ++ rest)
    obtain ⟨ks, rfl⟩ := all_consts hop
    have hF₀ : F₀ = (kvals ks).reverse ++ v :: vs.reverse := by
      have h₁ := run_consts_only ks f (v :: vs.reverse)
      rw [hF] at h₁
      exact (Prod.mk.inj (Option.some.inj h₁)).2
    subst hF₀
    have e₃ : vals (vs ++ [v]) ++ expression (lower (ks.map GInstr.const)) =
        vals ((kvals ks).reverse ++ v :: vs.reverse).reverse := by
      simp [expression_consts]
    rw [e₃]
    rw [e₃] at hrank
    exact advance hst (.refl _) hrun hrank hrest

theorem read_code (vs : List Val) (x₀ : LocalIdx) (L : List GInstr) (rest : List Admin) :
    vals vs ++ expression (lower (.localGet x₀ :: L)) ++ rest =
      vals vs ++ .plain (GInstr.localGet x₀).lower :: (expression (lower L) ++ rest) := by
  simp [lower, expression]

theorem read_rank (vs : List Val) (v : Val) (x₀ : LocalIdx) (L : List GInstr)
    (rest : List Admin) :
    gCodeRank (vals (vs ++ [v]) ++ expression (lower L) ++ rest) <
      gCodeRank (vals vs ++ expression (lower (.localGet x₀ :: L)) ++ rest) := by
  have hrank := rank_step (i := .localGet x₀) rfl (W := vs) (Y := v :: vs.reverse) (by simp)
    (expression (lower L) ++ rest)
  rw [← read_code] at hrank
  simpa using hrank

/-- **The step law for a left side of the `read` kind**: its `local.get` is matched by the
whole run of the right side. -/
theorem read_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs : List Val} {x₀ : LocalIdx} {L b : List GInstr} {rest rest' es' : List Admin}
    (hst : StoreRel F s t) (hL : ∀ i ∈ L, i.stk = true)
    (htot : ∀ f v X, (run L f (v :: X)).isSome) (href : RunRef (.localGet x₀ :: L) b)
    (hrest : AdminsRel GBI GB rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ expression (lower (.localGet x₀ :: L)) ++ rest⟩
      ⟨s', f', es'⟩) :
    StepGoal P F t s' f f' vs (expression (lower (.localGet x₀ :: L))) (expression (lower b))
      rest rest' es' := by
  have e := read_code vs x₀ L rest
  rw [e] at hstep
  obtain ⟨Y, hY, hc⟩ := step_inv ⟨Or.inr ⟨x₀, rfl⟩, rfl⟩ hstep
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  obtain ⟨v, -, -, rfl⟩ := step1_get_inv hY
  obtain ⟨⟨f₁, F₀⟩, hF⟩ := Option.isSome_iff_exists.mp (htot f' v vs.reverse)
  obtain ⟨rfl, hF'⟩ := run_stk hL hF
  have hb : run b f₁ vs.reverse = some (f₁, F₀) :=
    href f₁ vs.reverse _ (by rw [run_cons, hY]; exact hF)
  have hrun := run_steps (P := P) (host := closedHost) (s := t) hb rest'
  have e₂ : vals (v :: vs.reverse).reverse ++ (expression (lower L) ++ rest) =
      vals (vs ++ [v]) ++ expression (lower L) ++ rest := by simp
  rw [e₂]
  exact read_finish hst hL hF hF' (by simpa using hrun) (read_rank vs v x₀ L rest) hrest

/-- Grounded instructions are not exits. -/
theorem not_exit_lower {i : GInstr} (hc : i.isConst = false) {W us : List Val}
    {R k j : List Admin} (hk : Exit k) (h : vals W ++ .plain i.lower :: R = vals us ++ k ++ j) :
    False :=
  GuardSim.not_exit (lower_val hc) (by cases i <;> simp [GInstr.lower])
    (by cases i <;> simp [GInstr.lower]) (by cases i <;> simp [GInstr.lower, Admin.IsReturnCallRef])
    (by simp) (by cases i <;> simp [GInstr.lower]) hk h

/-- The step law for every runtime pair. -/
theorem g_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs : List Val} {x y rest rest' es' : List Admin} (hst : StoreRel F s t) (hxy : GB x y)
    (hrest : AdminsRel GBI GB rest rest')
    (hstep : Step P closedHost ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩) :
    StepGoal P F t s' f f' vs x y rest rest' es' := by
  rcases hxy with ⟨q, a, r, b, rfl, rfl, ha, hp⟩ |
    ⟨a, b, rfl, rfl, ⟨ha, href⟩ | ⟨⟨x₀, L, rfl, hL, htot⟩, href⟩⟩
  · exact stk_step hst ha hp hrest hstep
  · exact stk_step (q := []) (r := []) hst ha (fun f S res h => href f S res h) hrest hstep
  · exact read_step hst hL htot href hrest hstep

/-- **The bridge**: good pairs satisfy silmaril's base obligations, at every numerical profile,
for every function relation. -/
theorem gBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F GBI GB gCodeRank where
  src := by
    rintro x y ⟨a, b, hg, rfl, rfl⟩
    exact Or.inr ⟨a, b, rfl, rfl, hg⟩
  step := fun hst hxy hrest hstep => g_step hst hxy hrest hstep
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    obtain ⟨W, i, R, hi, hW⟩ := gb_head hxy vs
    exact absurd (hW.symm.trans he) (fun h => not_exit_lower hi.2 hk h)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨W, i, R, hi, hW⟩ := gb_head hxy vs
    have hm : Admin.plain i.lower ∈ vals (vs ++ us) := by
      rw [vals_append, ← hx, hW]
      simp
    exact SingleThreaded.Det.mem_vals hm (lower_val hi.2)

/-- **No host call** at the head of a left side. -/
theorem g_noRedex : CodeSimClosed.NoRedexB H GB := by
  intro x y hxy s vs rest
  obtain ⟨W, i, R, hi, hW⟩ := gb_head hxy vs
  rw [hW, List.append_assoc, List.cons_append]
  exact SingleThreaded.decompose?_vals_cons_none (lower_val hi.2)
    (fun _ _ => SingleThreaded.decompHead_plain (by cases i <;> rfl))

end Silmaril.Wasm.FnInst.Ground
