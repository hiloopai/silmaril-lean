module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Iteration

/-! # Direct monadic denotation of the flat two-loop CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs

open Isotope.LambdaSSA (Region)
open Isotope.SSA (At)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open LinearChain (Site localSite externalSite)
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B K M C J E D X Y : τ} {L Γ : List τ}

private def siteValue (target : Site L X) : TyDen X → LabelDen L :=
  LabelValue.inject target.index target.typing

omit [Iterate m] [LawfulElgotMonad m] in
private theorem instruction_denotes_at (op : TwoBlock.Instruction Φ X Y) {i : Nat}
    (h : Γ[i]? = some X) :
    Denotes (m := m) ε (op.typingAt h) (fun env => TwoBlock.call (ε := ε) op (Env.get env i h)) := by
  obtain ⟨op, source, target⟩ := op
  subst X
  subst Y
  have d := Denotes.op (m := m) (ε := ε) (Denotes.var (Φ := Φ) h)
  simpa [TwoBlock.call, bind_pure] using d

omit [Iterate m] [LawfulElgotMonad m] in
private theorem call_denotes (op : TwoBlock.Instruction Φ X Y) :
    Denotes (m := m) ε (op.typing Γ) (fun env => TwoBlock.call (ε := ε) op env.2) := by
  exact instruction_denotes_at (ε := ε) (Γ := X :: Γ) (i := 0) op rfl

omit [LawfulElgotMonad m] in
private theorem branch_denotes (target : Site L X) :
    RegionDenotes (m := m) ε (.br target.typing (.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl))
      (fun env => pure (siteValue target env.2)) := by
  simpa only [siteValue, Env.get, pure_bind, labelInject_eq_recursive] using
    RegionDenotes.br (m := m) (ε := ε) (h := target.typing)
      (Denotes.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl)

/-- The denotation of a generated block only uses its current payload.
The routing function determines the result of its actual branch. -/
private def blockAction {O : Type u} (route : ∀ {Z}, Site L Z → TyDen Z → O) :
    Block Φ L X → TyDen X → m O
  | .jump op site, x => TwoBlock.call (ε := ε) op x >>= fun y => pure (route site y)
  | .branch op left right, x => callCase (ε := ε) op x >>= fun y =>
      pure (Sum.elim (route left) (route right) y)

omit [LawfulElgotMonad m] in
private theorem block_denotes (block : Block Φ L X) :
    RegionDenotes (m := m) ε (block.typing Γ) (fun env =>
      blockAction (ε := ε) siteValue block env.2) := by
  cases block with
  | jump op site =>
    simpa only [Block.typing, blockAction, labelInject_eq_recursive, siteValue] using
      RegionDenotes.br (m := m) (ε := ε) (h := site.typing) (call_denotes op)
  | branch op l r =>
    have den := RegionDenotes.case (call_denotes (Γ := Γ) op)
      (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := X :: Γ) l)
      (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := X :: Γ) r)
    change RegionDenotes (m := m) ε
      (.case (op.typing Γ) (.br l.typing (.var (i := 0) rfl)) (.br r.typing (.var (i := 0) rfl))) _
    convert den using 1
    funext env
    simp only [blockAction, callCase, bind_assoc, pure_bind]
    congr 1
    funext out
    cases TypeModel.coprodEquiv _ _ out <;> rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem block_map {I O : Type u} {R : List τ}
    (block : Block Φ L X) (x : TyDen X) (rename : ∀ {Z}, Site L Z → Site R Z)
    (src : ∀ {Z}, Site L Z → TyDen Z → I) (dest : ∀ {Z}, Site R Z → TyDen Z → O)
    (map : I → O) (commute : ∀ {Z} (site : Site L Z) (p : TyDen Z),
      dest (rename site) p = map (src site p)) :
    blockAction (ε := ε) (m := m) dest (block.rename rename) x =
      blockAction (ε := ε) src block x >>= fun r => pure (map r) := by
  cases block with
  | jump op site =>
    simp only [Block.rename, blockAction, bind_assoc, pure_bind, commute]
  | branch op left right =>
    simp only [Block.rename, blockAction, bind_assoc, pure_bind]
    congr 1
    funext out
    cases out <;> simp only [Sum.elim_inl, Sum.elim_inr, commute]

private theorem split_local (external : List τ) :
    (locals : List τ) → (i : Nat) → {Z : τ} →
    (outside : At (locals ++ external) i Z) → (inside : At locals i Z) → (x : TyDen Z) →
    LabelValue.appendSplit locals external (LabelValue.inject i outside x) =
      .inr (LabelValue.inject i inside x)
  | [], _, _, _, inside, _ => by simp [At] at inside
  | _ :: _, 0, _, _, _, _ => rfl
  | _ :: rest, i + 1, _, outside, inside, x => by
    rw [LabelValue.inject_succ i outside (show At (rest ++ external) i _ from outside),
      LabelValue.inject_succ i inside (show At rest i _ from inside),
      LabelValue.appendSplit, split_local]

theorem split_external (external : List τ) :
    (locals : List τ) → (i : Nat) → {Z : τ} →
    (outside : At (locals ++ external) (i + locals.length) Z) →
    (inside : At external i Z) → (x : TyDen Z) →
    LabelValue.appendSplit locals external (LabelValue.inject (i + locals.length) outside x) =
      .inl (LabelValue.inject i inside x)
  | [], _, _, _, _, _ => rfl
  | _ :: rest, i, _, outside, inside, x => by
    simp only [List.length_cons, Nat.add_succ]
    rw [LabelValue.inject_succ (i + rest.length) outside (show At (rest ++ external) (i + rest.length) _ from outside),
      LabelValue.appendSplit, split_external]

private noncomputable def route {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) {Z : τ} (target : Site (List.ofFn R ++ L) Z) (x : TyDen Z) :
    LabelDen L ⊕ I :=
  Sum.map id (encode ∘ labelDenToFinite R) (LabelValue.appendSplit (List.ofFn R) L (siteValue target x))

private theorem route_local {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (i : Fin n) (x : TyDen (R i)) :
    route R L encode (localSite R L i) x = .inr (encode ⟨i,x⟩) := by
  unfold route siteValue
  simp only [localSite]
  rw [split_local L (List.ofFn R) i.val _ (by simp [At]) x]
  rw [Sum.map_inr, Function.comp_apply, labelDenToFinite_recursiveInject]
  rfl

private theorem route_external {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (i : Fin L.length) (x : TyDen (L.get i)) :
    route R L encode (externalSite R L i) x = .inl (LabelValue.inject i.val
      (List.getElem?_eq_getElem i.isLt) x) := by
  unfold route siteValue
  simp only [externalSite]
  rw [split_external L (List.ofFn R) i.val _ (List.getElem?_eq_getElem i.isLt) x]
  rfl

private theorem cfg_denotes {n : Nat} (R : Fin (n+1) → τ) (L : List τ) {I : Type u}
    (blocks : ∀ i, Block Φ (List.ofFn R ++ L) (R i))
    (start : Site (List.ofFn R ++ L) X) (encode : FiniteLabelDen R → I)
    (step : I → m (LabelDen L ⊕ I)) (initial : TyDen X → I)
    (enter : ∀ x, route R L encode start x = .inr (initial x))
    (dispatch : ∀ i x, blockAction (ε := ε) (m := m) (route R L encode) (blocks i) x =
      step (encode ⟨i,x⟩)) :
    RegionDenotes (m := m) ε
      (.cfg R (.br start.typing (.var (Φ := Φ) (Γ := [X]) (i := 0) rfl))
        (fun i => (blocks i).typing [X]))
      (fun env => iter step (initial env.2)) := by
  let entry : Env [X] → m (LabelDen (List.ofFn R ++ L)) := fun e => pure (siteValue start e.2)
  let actions i (e : Env (R i :: [X])) := blockAction (ε := ε) (m := m) siteValue (blocks i) e.2
  let collect (p : Env [X] × FiniteLabelDen R) := actions p.2.1 (p.1,p.2.2)
  have agrees : CollectiveDenotes [X] R L actions collect := ⟨fun _ _ _ => rfl⟩
  have den := RegionDenotes.cfg _ _ (branch_denotes (m := m) (ε := ε) (Γ := []) start)
    (fun i => block_denotes (m := m) (ε := ε) (Γ := [X]) (blocks i)) agrees
  suffices eq : cfgDenotation (R := R) entry collect = fun env => iter step (initial env.2) by
    rwa [← eq]
  funext env
  let raw : LabelDen (List.ofFn R) → m (LabelDen L ⊕ LabelDen (List.ofFn R)) :=
    fun l => collect (env, labelDenToFinite R l) >>= fun r => pure (LabelValue.appendSplit _ _ r)
  let loc := encode ∘ labelDenToFinite R
  have square : (raw >=> liftPure (Sum.map id loc)) = (liftPure loc >=> step) := by
    funext l
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, raw, bind_assoc]
    change _ = step (encode (labelDenToFinite R l))
    obtain ⟨i, x⟩ := labelDenToFinite R l
    change (blockAction (ε := ε) (m := m) siteValue (blocks i) x >>= fun r =>
      pure (Sum.map id (encode ∘ labelDenToFinite R) (LabelValue.appendSplit (List.ofFn R) L r))) =
        step (encode ⟨i,x⟩)
    rw [← dispatch i x]
    have identity : (blocks i).rename (fun s => s) = blocks i := by
      cases blocks i <;> rfl
    simpa only [identity] using (block_map (ε := ε) (m := m) (blocks i) x (fun s => s)
      siteValue (route R L encode)
      (fun l => Sum.map id loc (LabelValue.appendSplit (List.ofFn R) L l)) (fun _ _ => rfl)).symm
  let split := LabelValue.appendSplit (List.ofFn R) L (siteValue start env.2)
  have startCase : Sum.map id loc split = .inr (initial env.2) := enter env.2
  simp only [cfgDenotation, entry, pure_bind, binaryCoproductIso_hom_labelAppendSplit]
  rw [show LabelValue.appendSplit (List.ofFn R) L (siteValue start env.2) = split from rfl]
  cases eq : split with
  | inl l => simp [eq] at startCase
  | inr x =>
    have hx : loc x = initial env.2 := by simpa [eq] using startCase
    exact (congrFun (LawfulElgotMonad.uniformity raw step loc square) x).trans
      (by simp [Bind.kleisliRight, liftPure, hx])

private noncomputable def step (s : Loop Φ A B K E D)
    (p : FiniteLabelDen (Theta.localTypes s)) : m (LabelDen [E,D] ⊕ FiniteLabelDen (Theta.localTypes s)) :=
  blockAction (ε := ε) (route (Theta.localTypes s) [E,D] id) (Theta.blockAt s p.1) p.2

private theorem single_denotes (s : Loop Φ A B K E D) :
    RegionDenotes (m := m) ε (Theta.regionTyping s) (fun env => iter (step (ε := ε) s) ⟨0, env.2⟩) :=
  cfg_denotes _ _ (Theta.blockAt s) (localSite (Theta.localTypes s) [E,D] 0)
    id (step (ε := ε) s) (fun x => ⟨0,x⟩) (route_local _ _ id 0) (fun _ _ => rfl)

variable (s : Loops Φ A B K M C J E D)

private abbrev Local1 := FiniteLabelDen (Theta.localTypes s.first)
private abbrev Local2 := FiniteLabelDen (Theta.localTypes s.second)

private def phaseAt : (i : Fin (firstCount s + secondCount s)) →
    TyDen (localTypes s i) → Local1 s ⊕ Local2 s :=
  Fin.addCases (motive := fun i => TyDen (localTypes s i) → Local1 s ⊕ Local2 s)
    (fun i x => .inl ⟨i, first_type s i ▸ x⟩)
    (fun i x => .inr ⟨i, second_type s i ▸ x⟩)

private def encode (p : FiniteLabelDen (localTypes s)) : Local1 s ⊕ Local2 s := phaseAt s p.1 p.2

private theorem route_cast {n : Nat} (R : Fin n → τ) (L : List τ) {I : Type u}
    (encode : FiniteLabelDen R → I) (h : X = Y) (target : Site (List.ofFn R ++ L) X) (x : TyDen Y) :
    route R L encode (h ▸ target) x = route R L encode target (h.symm ▸ x) := by
  cases h
  rfl

private theorem payload_cast_cancel (h : X = Y) (y : TyDen Y) :
    h ▸ (h.symm ▸ y : TyDen X) = y := by
  cases h
  rfl

private theorem first_route (i : Fin (firstCount s)) (x : TyDen (Theta.localTypes s.first i)) :
    route (localTypes s) [E,D] (encode s) (firstLocal s i) x = .inr (.inl ⟨i,x⟩) := by
  rw [firstLocal, route_cast, route_local]
  simp only [encode, phaseAt, Fin.addCases_left, payload_cast_cancel]

private theorem second_route (i : Fin (secondCount s)) (x : TyDen (Theta.localTypes s.second i)) :
    route (localTypes s) [E,D] (encode s) (secondLocal s i) x = .inr (.inr ⟨i,x⟩) := by
  rw [secondLocal, route_cast, route_local]
  simp only [encode, phaseAt, Fin.addCases_right, payload_cast_cancel]

private def leftTarget (r : LabelDen [M,M] ⊕ Local1 s) : LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s) :=
  .inr (Sum.elim (Sum.inr ∘ fun label => ⟨0, merge label⟩) Sum.inl r)

private def rightTarget : LabelDen [E,D] ⊕ Local2 s → LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s) :=
  Sum.map id Sum.inr

private theorem left_route (target : Site (Theta.Labels s.first) X) (x : TyDen X) :
    route (localTypes s) [E,D] (encode s) (leftSite s target) x =
      leftTarget s (route (Theta.localTypes s.first) [M,M] id target x) := by
  unfold leftSite redirect
  generalize eq : splitSite (Theta.localTypes s.first) [M,M] target = split
  obtain ⟨whereTo, eqSite⟩ := split
  subst target
  cases whereTo with
  | «local» i =>
    change route (localTypes s) [E,D] (encode s) (firstLocal s i) x =
      leftTarget s (route (Theta.localTypes s.first) [M,M] id (localSite _ _ i) x)
    rw [route_local, first_route]
    rfl
  | external i =>
    change _ = leftTarget s (route (Theta.localTypes s.first) [M,M] id (externalSite _ _ i) x)
    rw [route_external]
    revert x
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> intro x
    · exact second_route s 0 x
    · exact second_route s 0 x

private theorem right_route (target : Site (Theta.Labels s.second) X) (x : TyDen X) :
    route (localTypes s) [E,D] (encode s) (rightSite s target) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id target x) := by
  unfold rightSite redirect
  generalize eq : splitSite (Theta.localTypes s.second) [E,D] target = split
  obtain ⟨whereTo, eqSite⟩ := split
  subst target
  cases whereTo with
  | «local» i =>
    change route (localTypes s) [E,D] (encode s) (secondLocal s i) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id (localSite _ _ i) x)
    rw [route_local, second_route]
    rfl
  | external i =>
    change route (localTypes s) [E,D] (encode s) (externalSite _ _ i) x =
      rightTarget s (route (Theta.localTypes s.second) [E,D] id (externalSite _ _ i) x)
    rw [route_external, route_external]
    rfl

private noncomputable def flatStep : Local1 s ⊕ Local2 s → m (LabelDen [E,D] ⊕ (Local1 s ⊕ Local2 s))
  | .inl p => step (ε := ε) s.first p >>= fun r => pure (leftTarget s r)
  | .inr p => step (ε := ε) s.second p >>= fun r => pure (rightTarget s r)

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
private theorem action_cast {R : List τ} {I : Type u}
    (dest : ∀ {Z}, Site R Z → TyDen Z → I) (h : X = Y) (b : Block Φ R X) (y : TyDen Y) :
    blockAction (ε := ε) (m := m) dest (h ▸ b) y = blockAction (ε := ε) dest b (h.symm ▸ y) := by
  cases h
  rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem dispatch (i : Fin (firstCount s + secondCount s)) (x : TyDen (localTypes s i)) :
    blockAction (ε := ε) (m := m) (route (localTypes s) [E,D] (encode s)) (blockAt s i) x =
      flatStep (ε := ε) s (encode s ⟨i,x⟩) := by
  revert x
  refine Fin.addCases ?_ ?_ i
  · intro i x
    simp only [blockAt, encode, phaseAt, Fin.addCases_left, action_cast, flatStep, step]
    exact block_map (Theta.blockAt s.first i) _ (leftSite s) _ _ _ (left_route s)
  · intro i x
    simp only [blockAt, encode, phaseAt, Fin.addCases_right, action_cast, flatStep, step]
    exact block_map (Theta.blockAt s.second i) _ (rightSite s) _ _ _ (right_route s)

private theorem flat_denotes :
    RegionDenotes (m := m) ε (regionTyping s) (fun env =>
      iter (flatStep (ε := ε) s) (.inl ⟨0,env.2⟩)) := by
  apply cfg_denotes _ _ (blockAt s) (firstEntry s) (encode s) (flatStep (ε := ε) s)
    (fun x => .inl ⟨0,x⟩)
  · exact first_route s 0
  · exact dispatch s

open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

theorem region_entry (s : Loop Φ A B K E D) {Γ : List τ} {gate : Isotope.LambdaSSA.Region Φ}
    (typing : Isotope.LambdaSSA.Region.HasType Γ gate (Theta.Labels s))
    {action : Env Γ → m (LabelDen (Theta.Labels s))}
    (entryDenotes : RegionDenotes (m := m) ε typing action)
    (choose : Env Γ → m (LabelDen [E,D] ⊕ TyDen A))
    (entrySplit : ∀ env, (action env >>= fun x => pure (LabelValue.appendSplit _ _ x)) =
      (choose env >>= fun branch => pure (splitEntry s branch)))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env Γ) :
    Region.denote (ε := ε) (m := m) (.cfg (Theta.localTypes s) typing
      (fun i => (Theta.blockAt s i).typing Γ)) env =
      choose env >>= fun
        | .inl external => pure external
        | .inr header => Region.denote (ε := ε) (m := m) (Theta.regionTyping s) (PUnit.unit, header) := by
  let collect {Δ : List τ} (p : Env Δ × FiniteLabelDen (Theta.localTypes s)) :=
    blockAction (ε := ε) (m := m) siteValue (Theta.blockAt s p.2.1) p.2.2
  have blocks (Δ : List τ) :
      ∀ i, RegionDenotes (m := m) ε ((Theta.blockAt s i).typing Δ)
        (fun env => blockAction (ε := ε) siteValue (Theta.blockAt s i) env.2) :=
    fun i => block_denotes (Theta.blockAt s i)
  have collective (Δ : List τ) : CollectiveDenotes Δ (Theta.localTypes s) [E,D]
      (fun i env => blockAction (ε := ε) siteValue (Theta.blockAt s i) env.2) collect :=
    ⟨fun _ _ _ => rfl⟩
  let start := localSite (Theta.localTypes s) [E,D] 0
  let step : LabelDen (List.ofFn (Theta.localTypes s)) →
      m (LabelDen [E,D] ⊕ LabelDen (List.ofFn (Theta.localTypes s))) :=
    fun current => collect (env, labelDenToFinite _ current) >>= fun next =>
      pure (LabelValue.appendSplit _ _ next)
  let run : LabelDen [E,D] ⊕ LabelDen (List.ofFn (Theta.localTypes s)) → m (LabelDen [E,D]) :=
    Sum.elim pure (iter step)
  have plain (x : TyDen A) : Region.denote (ε := ε) (m := m) (Theta.regionTyping s) (PUnit.unit, x) =
      run (splitEntry s (.inr x)) := by
    rw [TwoBlock.regionDenote_eq_of coherent (RegionDenotes.cfg _ _
      (branch_denotes (m := m) (ε := ε) (Γ := []) start) (blocks [A]) (collective [A]))]
    simp only [cfgDenotation, pure_bind, binaryCoproductIso_hom_labelAppendSplit]
    change _ = run (LabelValue.appendSplit (List.ofFn (Theta.localTypes s)) [E,D] (siteValue start x))
    cases LabelValue.appendSplit (List.ofFn (Theta.localTypes s)) [E,D] (siteValue start x) <;> rfl
  have selected := RegionDenotes.cfg (Γ := Γ) (R := Theta.localTypes s) (L := [E,D])
    typing (fun i => (Theta.blockAt s i).typing Γ) entryDenotes (blocks Γ) (collective Γ)
  rw [TwoBlock.regionDenote_eq_of coherent selected]
  simp only [cfgDenotation, binaryCoproductIso_hom_labelAppendSplit]
  calc
    _ = (action env >>= fun x => run (LabelValue.appendSplit _ _ x)) := by
      congr 1
      funext target
      cases LabelValue.appendSplit (List.ofFn (Theta.localTypes s)) [E,D] target <;> rfl
    _ = ((action env >>= fun x => pure (LabelValue.appendSplit _ _ x)) >>= run) := by
      simp only [bind_assoc, pure_bind]
    _ = _ := by
      rw [entrySplit env]
      simp only [bind_assoc, pure_bind]
      congr 1
      funext result
      cases result with
      | inl => rfl
      | inr x => exact (plain x).symm

theorem region_sequential
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s.first) env >>= fun mid =>
        Region.denote (ε := ε) (m := m) (Theta.regionTyping s.second) (PUnit.unit, merge mid) := by
  rw [TwoBlock.regionDenote_eq_of coherent (flat_denotes s),
    TwoBlock.regionDenote_eq_of coherent (single_denotes s.first),
    TwoBlock.regionDenote_eq_of coherent (single_denotes s.second)]
  exact iter_sequential (step (ε := ε) s.first) (step (ε := ε) s.second) (fun label => ⟨0, merge label⟩)
    (flatStep (ε := ε) s) (fun _ => rfl) (fun _ => rfl) _


section FlatLink

open Flat

private def runBlock {L : List τ} {O : Type u} (dest : ∀ {Z}, Site L Z → TyDen Z → O) :
    {Z : τ} → Flat.Block Φ L Z → TyDen Z → m O
  | _, .jump site, x => pure (dest site x)
  | _, .call op site, x => TwoBlock.call (ε := ε) op x >>= fun y => pure (dest site y)
  | _, .split l r, x => Sum.elim (runBlock dest l) (runBlock dest r) (TypeModel.coprodEquiv _ _ x)
  | _, .choose op l r, x => callCase (ε := ε) op x >>= Sum.elim (runBlock dest l) (runBlock dest r)
  | _, .bindChoose value test l r, x => TwoBlock.call (ε := ε) value x >>= fun y =>
    callCase (ε := ε) test x >>= fun tag => pure (dest (tag.elim (fun _ => l) (fun _ => r)) y)

omit [Isotope.Subtyping τ] [TypeModel τ] in
private theorem flat_rename_id {Z : τ} (b : Flat.Block Φ L Z) : b.rename (fun s => s) = b := by
  induction b <;> simp only [Flat.Block.rename, *]

omit [Iterate m] [LawfulElgotMonad m] in
private theorem runBlock_map {L R : List τ} {I O : Type u} {Z : τ}
    (block : Flat.Block Φ L Z) (x : TyDen Z) (rename : ∀ {W}, Site L W → Site R W)
    (src : ∀ {W}, Site L W → TyDen W → I) (dest : ∀ {W}, Site R W → TyDen W → O)
    (f : I → O) (commute : ∀ {W} (site : Site L W) (p : TyDen W), dest (rename site) p = f (src site p)) :
    runBlock (ε := ε) (m := m) dest (block.rename rename) x =
      runBlock (ε := ε) src block x >>= fun a => pure (f a) := by
  induction block with
  | jump => simp only [Flat.Block.rename, runBlock, pure_bind, commute]
  | call => simp only [Flat.Block.rename, runBlock, bind_assoc, pure_bind, commute]
  | split l r hl hr =>
    simp only [Flat.Block.rename, runBlock]
    cases TypeModel.coprodEquiv _ _ x with
    | inl y => exact hl y
    | inr y => exact hr y
  | choose op l r hl hr =>
    simp only [Flat.Block.rename, runBlock, bind_assoc]
    congr 1
    funext result
    cases result with
    | inl y => exact hl y
    | inr y => exact hr y
  | bindChoose value test l r =>
    simp only [Flat.Block.rename, runBlock, bind_assoc, pure_bind]
    congr 1
    funext payload
    congr 1
    funext tag
    cases tag <;> simp only [Sum.elim_inl, Sum.elim_inr, commute]

omit [LawfulElgotMonad m] in
private theorem flatBlock_denotes {L : List τ} {Z : τ} (b : Flat.Block Φ L Z) (Δ : List τ) :
    RegionDenotes (m := m) ε (b.typing Δ)
      (fun env => runBlock (ε := ε) siteValue b env.2) := by
  induction b generalizing Δ with
  | jump site => exact branch_denotes site
  | call op site =>
    simpa only [Flat.Block.typing, runBlock, labelInject_eq_recursive, siteValue] using
      RegionDenotes.br (m := m) (ε := ε) (h := site.typing) (call_denotes op)
  | split l r hl hr =>
    have den := RegionDenotes.case (Denotes.var (m := m) (ε := ε) (Φ := Φ) (i := 0) rfl)
      (hl (_ :: Δ)) (hr (_ :: Δ))
    convert den using 1 <;> try rfl
    funext env
    simp only [runBlock, Env.get, pure_bind]
    cases TypeModel.coprodEquiv _ _ env.2 <;> rfl
  | choose op l r hl hr =>
    have den := RegionDenotes.case (call_denotes (m := m) (Γ := Δ) op)
      (hl (_ :: Δ)) (hr (_ :: Δ))
    convert den using 1 <;> try rfl
    funext env
    simp only [runBlock, callCase, bind_assoc, pure_bind]
    congr 1
    funext output
    cases TypeModel.coprodEquiv _ _ output <;> rfl
  | @bindChoose U V B C value test l r =>
    have valueDen := call_denotes (m := m) (ε := ε) (Γ := Δ) value
    have testDen := instruction_denotes_at (m := m) (ε := ε) test (i := 1) (Γ := V :: U :: Δ) rfl
    have leftDen := RegionDenotes.br (m := m) (ε := ε) (h := l.typing)
      (Denotes.var (m := m) (ε := ε) (Φ := Φ) (Γ := B :: V :: U :: Δ) (i := 1) rfl)
    have rightDen := RegionDenotes.br (m := m) (ε := ε) (h := r.typing)
      (Denotes.var (m := m) (ε := ε) (Φ := Φ) (Γ := C :: V :: U :: Δ) (i := 1) rfl)
    have den := RegionDenotes.let₁ valueDen (RegionDenotes.case testDen leftDen rightDen)
    convert den using 1 <;> try rfl
    funext env
    simp only [runBlock, callCase, bind_assoc, pure_bind, Env.get, labelInject_eq_recursive, siteValue]
    congr 1
    funext y
    congr 1
    funext tag
    cases TypeModel.coprodEquiv _ _ tag <;> rfl

private noncomputable def fragStep (p : Fragment Φ A E D) (i : FiniteLabelDen p.localTypes) :
    m (LabelDen [E,D] ⊕ FiniteLabelDen p.localTypes) :=
  runBlock (ε := ε) (route p.localTypes [E,D] id) (p.blocks i.1) i.2

private theorem fragment_run (p : Fragment Φ A E D) {I : Type u}
    (encode : FiniteLabelDen p.localTypes → I) (step : I → m (LabelDen [E,D] ⊕ I))
    (dispatch : ∀ i x, runBlock (ε := ε) (m := m) (route p.localTypes [E,D] encode) (p.blocks i) x =
      step (encode ⟨i,x⟩))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) p.typing env =
      runBlock (ε := ε) (route p.localTypes [E,D] encode) p.entry env.2 >>= Sum.elim pure (iter step) := by
  let actions i (e : Env (p.localTypes i :: [A])) := runBlock (ε := ε) (m := m) siteValue (p.blocks i) e.2
  let collect (x : Env [A] × FiniteLabelDen p.localTypes) := actions x.2.1 (x.1,x.2.2)
  have agrees : CollectiveDenotes [A] p.localTypes [E,D] actions collect := ⟨fun _ _ _ => rfl⟩
  rw [TwoBlock.regionDenote_eq_of coherent
    (RegionDenotes.cfg (R := p.localTypes) _ _ (flatBlock_denotes p.entry []) (fun i => flatBlock_denotes (p.blocks i) [A]) agrees)]
  let raw : LabelDen (List.ofFn p.localTypes) → m (LabelDen [E,D] ⊕ LabelDen (List.ofFn p.localTypes)) :=
    fun l => collect (env, labelDenToFinite p.localTypes l) >>= fun r => pure (LabelValue.appendSplit _ _ r)
  let loc := encode ∘ labelDenToFinite p.localTypes
  have mapBlock {Z : τ} (b : Flat.Block Φ p.Labels Z) (x : TyDen Z) :
      runBlock (ε := ε) (m := m) (route p.localTypes [E,D] encode) b x =
        runBlock (ε := ε) siteValue b x >>= fun l =>
          pure (Sum.map id loc (LabelValue.appendSplit (List.ofFn p.localTypes) [E,D] l)) := by
    simpa only [flat_rename_id] using runBlock_map (ε := ε) b x (fun s => s) siteValue
      (route p.localTypes [E,D] encode) (fun l => Sum.map id loc (LabelValue.appendSplit _ _ l))
      (fun _ _ => rfl)
  have square : (raw >=> liftPure (Sum.map id loc)) = (liftPure loc >=> step) := by
    funext l
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, raw, bind_assoc]
    change _ = step (encode (labelDenToFinite p.localTypes l))
    obtain ⟨i, x⟩ := labelDenToFinite p.localTypes l
    rw [← dispatch i x]
    exact (mapBlock (p.blocks i) x).symm
  have loop := LawfulElgotMonad.uniformity raw step loc square
  simp only [cfgDenotation, binaryCoproductIso_hom_labelAppendSplit, mapBlock, bind_assoc, pure_bind]
  congr 1
  funext l
  cases LabelValue.appendSplit (List.ofFn p.localTypes) [E,D] l with
  | inl => rfl
  | inr i =>
    simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, raw, loc, Sum.elim_inr, Sum.map_inr] using
      congrFun loop i

theorem flat_classify_denote (op : TwoBlock.Instruction Φ A (Silmaril.coprod E D))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (Fragment.classify op).typing env =
      callCase (ε := ε) op env.2 >>= fun result => pure (TwoBlock.TwoExit.exitLabel result) := by
  let p := Fragment.classify op
  rw [fragment_run p id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent]
  simp only [p, Fragment.classify, runBlock, bind_assoc]
  congr 1
  funext result
  cases result
  · simp only [Sum.elim_inl, pure_bind]
    rw [route_external]
    rfl
  · simp only [Sum.elim_inr, pure_bind]
    rw [route_external]
    rfl

section Feedback

variable (p : Fragment Φ A E A)

private abbrev BodyState := FiniteLabelDen p.localTypes
private abbrev FeedbackState := TyDen A ⊕ BodyState p

private def feedbackState (i : Fin (p.count + 1)) : TyDen (p.feedbackTypes i) → FeedbackState p :=
  Fin.cases (motive := fun i => TyDen (p.feedbackTypes i) → FeedbackState p)
    Sum.inl (fun j x => .inr ⟨j, x⟩) i

private def feedbackEncode (i : FiniteLabelDen p.feedbackTypes) : FeedbackState p :=
  feedbackState p i.1 i.2

private def feedbackExit : LabelDen [E,A] → LabelDen [E,D] ⊕ TyDen A :=
  (⟨.first, .consumer⟩ : ExitRouting E A A E D).select

/-- Local branches stay in the inner iterator. A body exit completes the
inner iterator and either returns or restarts at the outer header. -/
private def feedbackGroup : LabelDen [E,A] ⊕ BodyState p →
    (LabelDen [E,D] ⊕ FeedbackState p) ⊕ FeedbackState p :=
  Sum.elim (Sum.inl ∘ Sum.map id Sum.inl ∘ feedbackExit) (Sum.inr ∘ Sum.inr)

private noncomputable def bodyEntry (x : TyDen A) : m (LabelDen [E,A] ⊕ BodyState p) :=
  runBlock (ε := ε) (route p.localTypes [E,A] id) p.entry x

private noncomputable def groupedFeedback : FeedbackState p →
    m ((LabelDen [E,D] ⊕ FeedbackState p) ⊕ FeedbackState p) :=
  fun x => Sum.elim (bodyEntry (ε := ε) p) (fragStep (ε := ε) p) x >>= pure ∘ feedbackGroup p

private theorem feedback_route (site : Site p.Labels X) (x : TyDen X) :
    route p.feedbackTypes [E,D] (feedbackEncode p) (p.feedbackSite site) x =
      flatten (feedbackGroup p (route p.localTypes [E,A] id site x)) := by
  unfold Fragment.feedbackSite redirect
  generalize h : splitSite p.localTypes [E,A] site = dest
  obtain ⟨dest, eq⟩ := dest
  subst site
  cases dest with
  | «local» i =>
    change route _ _ _ (localSite p.feedbackTypes [E,D] i.succ) x =
      flatten (feedbackGroup p (route _ _ id (localSite _ _ i) x))
    rw [route_local, route_local]
    rfl
  | external i =>
    change route _ _ _ (Fin.cases (motive := fun i => Site _ ([E,A].get i))
      (externalSite p.feedbackTypes [E,D] 0)
      (Fin.cases (localSite p.feedbackTypes [E,D] 0) (fun j => j.elim0)) i) x =
        flatten (feedbackGroup p (route _ _ id (externalSite _ _ i) x))
    rw [route_external]
    revert x
    refine Fin.cases (fun x => ?_) (Fin.cases (fun x => ?_) (fun j => j.elim0)) i
    · rw [Fin.cases_zero, route_external]
      rfl
    · rw [Fin.cases_succ, Fin.cases_zero, route_local]
      rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem feedback_map {Z : τ} (b : Flat.Block Φ p.Labels Z) (x : TyDen Z) :
    runBlock (ε := ε) (m := m) (route p.feedbackTypes [E,D] (feedbackEncode p))
        (b.rename p.feedbackSite) x =
      runBlock (ε := ε) (route p.localTypes [E,A] id) b x >>=
        fun r => pure (flatten (feedbackGroup p r)) :=
  runBlock_map (ε := ε) b x p.feedbackSite _ _ _ (feedback_route p)

private theorem feedback_fold
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (a : TyDen A) :
    iter (flattenBody (groupedFeedback (ε := ε) (m := m) (D := D) p)) (.inl a) =
      iter (fun x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit, x) >>=
        pure ∘ feedbackExit (D := D)) a := by
  let routeExit : LabelDen [E,A] → LabelDen [E,D] ⊕ FeedbackState p :=
    Sum.map id Sum.inl ∘ feedbackExit
  have square : (mapReturn (fragStep (ε := ε) (m := m) p) (liftPure routeExit) >=>
        liftPure (Sum.map id Sum.inr)) =
      (liftPure Sum.inr >=> groupedFeedback (ε := ε) p) := by
    funext i
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, groupedFeedback,
      Sum.elim_inr, mapReturn, bind_assoc]
    congr 1
    funext r
    cases r <;> simp [feedbackGroup, routeExit, pure_bind]
  have localIteration (i : BodyState p) :
      iter (groupedFeedback (ε := ε) (m := m) p) (.inr i) =
        iter (fragStep (ε := ε) (m := m) p) i >>= liftPure routeExit := by
    have h := congrFun (LawfulElgotMonad.uniformity _ _ _ square) i
    rw [← LawfulElgotMonad.naturality] at h
    simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using h.symm
  have headerIteration (x : TyDen A) :
      iter (groupedFeedback (ε := ε) (m := m) p) (.inl x) =
        Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) >>= liftPure routeExit := by
    rw [congrFun (LawfulElgotMonad.fixpoint (groupedFeedback (ε := ε) p)) (.inl x),
      fragment_run p id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent]
    simp only [groupedFeedback, Sum.elim_inl, bodyEntry, bind_assoc, Function.comp_apply, pure_bind]
    congr 1
    funext r
    cases r <;> simp [feedbackGroup, routeExit, liftPure, localIteration]
  have outerSquare :
      ((fun x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) >>= pure ∘ feedbackExit (D := D)) >=>
        liftPure (Sum.map id Sum.inl)) =
      (liftPure Sum.inl >=> iter (groupedFeedback (ε := ε) (m := m) p)) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, bind_assoc, headerIteration]
    rfl
  rw [← LawfulElgotMonad.codiagonal]
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using
    (congrFun (LawfulElgotMonad.uniformity _ _ _ outerSquare) a).symm

theorem flat_feedback_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (p.feedback (D := D)).typing env =
      iter (fun x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) >>=
        fun r => pure ((⟨.first, .consumer⟩ : ExitRouting E A A E D).select r)) env.2 := by
  let step := flattenBody (groupedFeedback (ε := ε) (m := m) (D := D) p)
  rw [fragment_run p.feedback (feedbackEncode p) step ?_ coherent]
  · change (pure (route p.feedbackTypes [E,D] (feedbackEncode p)
      (localSite p.feedbackTypes [E,D] 0) env.2) >>= _) = _
    rw [route_local, pure_bind, Sum.elim_inr]
    exact feedback_fold p coherent env.2
  · intro i
    refine Fin.cases (fun x => ?_) (fun j x => ?_) i
    · simpa only [Fragment.feedback, feedbackEncode, feedbackState, Fin.cases_zero, step,
        flattenBody, Bind.kleisliRight, liftPure, groupedFeedback, Sum.elim_inl, bodyEntry,
        bind_assoc, Function.comp_apply, pure_bind] using feedback_map (ε := ε) (m := m) p p.entry x
    · simpa only [Fragment.feedback, feedbackEncode, feedbackState, Fin.cases_succ, step,
        flattenBody, Bind.kleisliRight, liftPure, groupedFeedback, Sum.elim_inr, fragStep,
        bind_assoc, Function.comp_apply, pure_bind] using feedback_map (ε := ε) (m := m) p (p.blocks j) x

end Feedback

theorem flat_splitReturn_denote (p : Fragment Φ A E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    (env : Env [Silmaril.coprod A E]) :
    Region.denote (ε := ε) (m := m) p.splitReturn.typing env =
      match TypeModel.coprodEquiv A E env.2 with
      | .inl x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x)
      | .inr e => pure (.inl e) := by
  rw [fragment_run p.splitReturn id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent]
  change (Sum.elim _ _ (TypeModel.coprodEquiv A E env.2) >>= _) = _
  cases TypeModel.coprodEquiv A E env.2 with
  | inl x => exact (fragment_run p id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent (PUnit.unit,x)).symm
  | inr e =>
    simp only [Sum.elim_inr, runBlock, pure_bind]
    change Sum.elim pure (iter (fragStep (ε := ε) p))
      (route p.localTypes [E,D] id (externalSite p.localTypes [E,D] 0) e) = _
    rw [route_external]
    rfl

theorem flat_gateCarrier_denote (p : Fragment Φ M E D)
    (gate : TwoBlock.Instruction Φ A (TwoBlock.TwoExit.Carrier M E D))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (p.gateCarrier gate).typing env =
      callCase (ε := ε) gate env.2 >>= fun
        | .inl e => pure (TwoBlock.TwoExit.exitLabel (TypeModel.coprodEquiv E D e))
        | .inr x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) := by
  rw [fragment_run (p.gateCarrier gate) id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent]
  simp only [Fragment.gateCarrier, runBlock, bind_assoc]
  congr 1
  funext result
  cases result with
  | inl e =>
    simp only [Sum.elim_inl]
    cases TypeModel.coprodEquiv E D e <;>
      simp only [Sum.elim_inl, Sum.elim_inr, route_external, pure_bind] <;> rfl
  | inr x => exact (fragment_run p id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent (PUnit.unit,x)).symm

theorem flat_bindChooseLoop_denote {V W : τ} (value : TwoBlock.Instruction Φ A A)
    (test : TwoBlock.Instruction Φ A (Silmaril.coprod V W))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m)
        (Fragment.bindChooseLoop (D := D) value test).typing env =
      iter (fun x => TwoBlock.call (ε := ε) value x >>= fun y =>
        callCase (ε := ε) test x >>= fun tag =>
          pure (tag.elim (fun _ => Sum.inl y) (fun _ => Sum.inr y))) env.2 >>= fun y =>
        pure (.inl y) := by
  let loop := Fragment.bindChooseLoop (D := D) value test
  let encode : FiniteLabelDen loop.localTypes → TyDen A := fun p => p.2
  let step (x : TyDen A) : m (TyDen A ⊕ TyDen A) :=
    TwoBlock.call (ε := ε) value x >>= fun y =>
      callCase (ε := ε) test x >>= fun tag =>
        pure (tag.elim (fun _ => Sum.inl y) (fun _ => Sum.inr y))
  let ret : TyDen A → m (LabelDen [A,D]) := fun y => pure (.inl y)
  have dispatch i x :
      runBlock (ε := ε) (m := m) (route loop.localTypes [A,D] encode) (loop.blocks i) x =
        mapReturn step ret (encode ⟨i,x⟩) := by
    change runBlock (ε := ε) (m := m) _ (.bindChoose value test _ _) x = _
    simp only [runBlock, mapReturn, step, bind_assoc, pure_bind]
    congr 1
    funext y
    congr 1
    funext tag
    cases tag with
    | inl =>
      simp only [Sum.elim_inl]
      change pure (route loop.localTypes [A,D] encode (externalSite loop.localTypes [A,D] 0) y) = _
      rw [route_external]
      simp [ret, LabelValue.inject]
    | inr =>
      simp only [Sum.elim_inr]
      change pure (route loop.localTypes [A,D] encode (localSite loop.localTypes [A,D] 0) y) = _
      rw [route_local]
      rfl
  rw [fragment_run loop encode _ dispatch coherent]
  change (pure (route loop.localTypes [A,D] encode (localSite _ _ 0) env.2) >>= _) = _
  rw [route_local, pure_bind, Sum.elim_inr]
  exact (congrFun (LawfulElgotMonad.naturality step ret) env.2).symm

variable {P Q : τ}
variable (p : Fragment Φ A P Q) (q : Fragment Φ M E D) (routing : ExitRouting P Q M E D)

private abbrev Left := FiniteLabelDen p.localTypes
private abbrev Right := FiniteLabelDen (rightTypes q)

private def intoRight (i : FiniteLabelDen q.localTypes) : Right q := ⟨i.1.succ, i.2⟩

private def startRight (x : TyDen M) : Right q := ⟨0, x⟩

private def phaseAtFlat (i : Fin (p.count + (q.count + 1))) :
    TyDen (linkedTypes p q i) → Left p ⊕ Right q :=
  Fin.addCases (motive := fun j => TyDen (linkedTypes p q j) → Left p ⊕ Right q)
    (fun j x => .inl ⟨j, Flat.left_type p q j ▸ x⟩)
    (fun j x => .inr ⟨j, Flat.right_type p q j ▸ x⟩) i

private def encodeFlat (x : FiniteLabelDen (linkedTypes p q)) : Left p ⊕ Right q :=
  phaseAtFlat p q x.1 x.2

private def producerTarget (exit : LabelDen [P,Q]) : LabelDen [E,D] ⊕ Right q :=
  Sum.map id (startRight q) (routing.select exit)

private def leftOut : LabelDen [P,Q] ⊕ Left p → LabelDen [E,D] ⊕ (Left p ⊕ Right q) :=
  Sum.elim (Sum.map id Sum.inr ∘ producerTarget q routing) (Sum.inr ∘ Sum.inl)

private def rightOut (r : LabelDen [E,D] ⊕ Right q) : LabelDen [E,D] ⊕ (Left p ⊕ Right q) :=
  Sum.map id Sum.inr r

private theorem flat_target (target : ExitTarget M E D X) (x : TyDen X) :
    route (linkedTypes p q) [E,D] (encodeFlat p q) (targetSite p q target) x =
      Sum.map id Sum.inr (Sum.map id (startRight q) (target.select x)) := by
  cases target with
  | consumer =>
    rw [targetSite, Flat.handoff, Flat.rightLocal, route_cast, route_local]
    simp only [encodeFlat, phaseAtFlat, Fin.addCases_right, payload_cast_cancel]
    rfl
  | first => rw [targetSite, route_external]; rfl
  | second => rw [targetSite, route_external]; rfl

private theorem select_injected (i : Fin [P,Q].length) (x : TyDen ([P,Q].get i)) :
    routing.select (LabelValue.inject i.val (List.getElem?_eq_getElem i.isLt) x) =
      (routing.target i).select x := by
  revert x
  exact Fin.cases (fun _ => rfl) (Fin.cases (fun _ => rfl) (fun j => j.elim0)) i

private theorem flat_left_route (target : Site p.Labels X) (x : TyDen X) :
    route (linkedTypes p q) [E,D] (encodeFlat p q) (Flat.leftSiteBy p q routing target) x =
      leftOut p q routing (route p.localTypes [P,Q] id target x) := by
  unfold Flat.leftSiteBy redirect
  generalize h : splitSite p.localTypes [P,Q] target = dest
  obtain ⟨dest, eq⟩ := dest
  subst target
  cases dest with
  | «local» i =>
    change route (linkedTypes p q) [E,D] (encodeFlat p q) (Flat.leftLocal p q i) x =
      leftOut p q routing (route p.localTypes [P,Q] id (localSite _ _ i) x)
    rw [Flat.leftLocal, route_cast, route_local, route_local]
    simp only [encodeFlat, phaseAtFlat, Fin.addCases_left, payload_cast_cancel]
    rfl
  | external i =>
    change route _ _ _ (targetSite p q (routing.target i)) x =
      leftOut p q routing (route p.localTypes [P,Q] id (externalSite _ _ i) x)
    rw [route_external]
    simp only [leftOut, Sum.elim_inl, Function.comp_apply, producerTarget, select_injected]
    exact flat_target p q (routing.target i) x

private theorem flat_right_route (target : Site q.Labels X) (x : TyDen X) :
    route (linkedTypes p q) [E,D] (encodeFlat p q) (Flat.rightSite p q target) x =
      rightOut p q (route q.localTypes [E,D] (intoRight q) target x) := by
  unfold Flat.rightSite redirect
  generalize h : splitSite q.localTypes [E,D] target = dest
  obtain ⟨dest, eq⟩ := dest
  subst target
  cases dest with
  | «local» i =>
    change route (linkedTypes p q) [E,D] (encodeFlat p q) (Flat.rightLocal p q i.succ) x =
      rightOut p q (route q.localTypes [E,D] (intoRight q) (localSite _ _ i) x)
    rw [Flat.rightLocal, route_cast, route_local, route_local]
    simp only [encodeFlat, phaseAtFlat, Fin.addCases_right, payload_cast_cancel]
    rfl
  | external i =>
    change route (linkedTypes p q) [E,D] (encodeFlat p q) (externalSite _ _ i) x =
      rightOut p q (route q.localTypes [E,D] (intoRight q) (externalSite _ _ i) x)
    rw [route_external, route_external]
    rfl

private noncomputable def rightStep (i : Right q) : m (LabelDen [E,D] ⊕ Right q) :=
  Fin.cases (motive := fun j => TyDen (rightTypes q j) → m (LabelDen [E,D] ⊕ Right q))
    (runBlock (ε := ε) (route q.localTypes [E,D] (intoRight q)) q.entry)
    (fun j => runBlock (ε := ε) (route q.localTypes [E,D] (intoRight q)) (q.blocks j)) i.1 i.2

private noncomputable def linkedStep : Left p ⊕ Right q → m (LabelDen [E,D] ⊕ (Left p ⊕ Right q))
  | .inl i => fragStep (ε := ε) p i >>= fun r => pure (leftOut p q routing r)
  | .inr i => rightStep (ε := ε) q i >>= fun r => pure (rightOut p q r)

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
private theorem flat_action_cast {R : List τ} {I : Type u}
    (dest : ∀ {Z}, Site R Z → TyDen Z → I) (h : X = Y) (b : Flat.Block Φ R X) (y : TyDen Y) :
    runBlock (ε := ε) (m := m) dest (h ▸ b) y = runBlock (ε := ε) dest b (h.symm ▸ y) := by
  cases h
  rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem linked_dispatch (i : Fin ((linkBy p q routing).count)) (x : TyDen ((linkBy p q routing).localTypes i)) :
    runBlock (ε := ε) (m := m) (route (linkedTypes p q) [E,D] (encodeFlat p q)) ((linkBy p q routing).blocks i) x =
      linkedStep (ε := ε) p q routing (encodeFlat p q ⟨i,x⟩) := by
  revert x
  refine Fin.addCases (m := p.count) (n := q.count + 1) ?_ ?_ i
  · intro j x
    simp only [linkBy, encodeFlat, phaseAtFlat, Fin.addCases_left, flat_action_cast, linkedStep, fragStep]
    exact runBlock_map (ε := ε) (m := m) (p.blocks j) _ (Flat.leftSiteBy p q routing) _ _ _ (flat_left_route p q routing)
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    all_goals
      intro x
      simp only [linkBy, encodeFlat, phaseAtFlat, Fin.addCases_right, flat_action_cast, linkedStep,
        rightBlock, rightStep, Fin.cases_zero, Fin.cases_succ]
      first
      | exact runBlock_map (ε := ε) (m := m) q.entry _ (Flat.rightSite p q) _ _ _ (flat_right_route p q)
      | exact runBlock_map (ε := ε) (m := m) (q.blocks k) _ (Flat.rightSite p q) _ _ _ (flat_right_route p q)

private theorem right_start
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (x : TyDen M) :
    iter (rightStep (ε := ε) (m := m) q) (startRight q x) =
      Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,x) := by
  rw [fragment_run q id (fragStep (ε := ε) q) (fun _ _ => rfl) coherent]
  rw [congrFun (LawfulElgotMonad.fixpoint (rightStep (ε := ε) q)) (startRight q x)]
  let f : LabelDen [E,D] ⊕ FiniteLabelDen q.localTypes → LabelDen [E,D] ⊕ Right q := Sum.map id (intoRight q)
  have mapRuns {Z : τ} (b : Flat.Block Φ q.Labels Z) (v : TyDen Z) :
      runBlock (ε := ε) (m := m) (route q.localTypes [E,D] (intoRight q)) b v =
        runBlock (ε := ε) (route q.localTypes [E,D] id) b v >>= fun k => pure (f k) := by
    have maps : ∀ {W} (site : Site q.Labels W) (a : TyDen W),
        route q.localTypes [E,D] (intoRight q) site a = f (route q.localTypes [E,D] id site a) := by
      intro W site a
      unfold route f
      cases LabelValue.appendSplit (List.ofFn q.localTypes) [E,D] (siteValue site a) <;> rfl
    simpa only [flat_rename_id] using runBlock_map (ε := ε) b v (fun s => s) _ _ f maps
  have square : (fragStep (ε := ε) (m := m) q >=> liftPure f) =
      (liftPure (intoRight q) >=> rightStep (ε := ε) q) := by
    funext i
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, fragStep, rightStep, intoRight, Fin.cases_succ]
    exact (mapRuns (q.blocks i.1) i.2).symm
  simp only [rightStep, startRight, Fin.cases_zero, mapRuns, bind_assoc, pure_bind]
  congr 1
  funext r
  cases r with
  | inl => rfl
  | inr i =>
    simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, f, Sum.map_inr, Sum.elim_inr] using
      (congrFun (LawfulElgotMonad.uniformity _ _ _ square) i).symm

private theorem linked_right_start
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (x : TyDen M) :
    iter (linkedStep (ε := ε) (m := m) p q routing) (.inr (startRight q x)) =
      Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,x) := by
  rw [← right_start q coherent]
  let inj : Right q → Left p ⊕ Right q := Sum.inr
  have sq : (rightStep (ε := ε) (m := m) q >=> liftPure (Sum.map id inj)) =
      (liftPure inj >=> linkedStep (ε := ε) p q routing) := by
    funext i
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, inj, linkedStep, rightOut]
    rfl
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, inj] using
    (congrFun (LawfulElgotMonad.uniformity _ _ _ sq) (startRight q x)).symm

theorem flat_linkBy_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (linkBy p q routing).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Sum.elim pure (fun input => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,input))
          (routing.select y) := by
  rw [fragment_run (linkBy p q routing) (encodeFlat p q) (linkedStep (ε := ε) p q routing)
      (linked_dispatch p q routing) coherent,
    fragment_run p id (fragStep (ε := ε) p) (fun _ _ => rfl) coherent]
  change (runBlock (ε := ε) (m := m) (route (linkedTypes p q) [E,D] (encodeFlat p q))
    (p.entry.rename (Flat.leftSiteBy p q routing)) env.2 >>= _) = _
  rw [runBlock_map (ε := ε) (m := m) p.entry _ (Flat.leftSiteBy p q routing) _ _ _
    (flat_left_route p q routing)]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext k
  cases k with
  | inl e =>
    simp only [leftOut, Sum.elim_inl, pure_bind, Function.comp_apply, producerTarget]
    cases selected : routing.select e with
    | inl label => simp
    | inr input => simpa [selected] using linked_right_start p q routing coherent input
  | inr i =>
    change iter (linkedStep (ε := ε) p q routing) (.inl i) = _
    rw [iter_sequential_select (fragStep (ε := ε) p) (rightStep (ε := ε) q)
      (producerTarget q routing) (linkedStep (ε := ε) p q routing) (fun _ => rfl) (fun _ => rfl)]
    congr 1
    funext e
    cases selected : routing.select e with
    | inl label => simp [producerTarget, selected]
    | inr input => simpa [producerTarget, selected] using right_start q coherent input

theorem flat_link_denote (p : Fragment Φ A M M) (q : Fragment Φ M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (link p q).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Region.denote (ε := ε) (m := m) q.typing (PUnit.unit, merge y) := by
  rw [Flat.link, flat_linkBy_denote _ _ _ coherent]
  congr 1
  funext y
  rcases y with x | x | impossible
  · rfl
  · rfl
  · exact impossible.elim

end FlatLink

section FlatFork

open Flat
open TwoBlock.TwoExit (Carrier)

variable (p : Fragment Φ M E D) (q : Fragment Φ Y E D)

private abbrev ForkState := FiniteLabelDen p.localTypes ⊕ FiniteLabelDen q.localTypes

private def forkAt (i : Fin (p.count + q.count)) : TyDen (forkTypes p q i) → ForkState p q :=
  Fin.addCases (motive := fun j => TyDen (forkTypes p q j) → ForkState p q)
    (fun j x => .inl ⟨j, forkLeft_type p q j ▸ x⟩)
    (fun j x => .inr ⟨j, forkRight_type p q j ▸ x⟩) i

private def forkEncode (x : FiniteLabelDen (forkTypes p q)) := forkAt p q x.1 x.2

private theorem fork_route {n : Nat} (R : Fin n → τ) (inj : FiniteLabelDen R → ForkState p q)
    (localDest : ∀ i, Site (ForkLabels p q) (R i))
    (localEq : ∀ i x, route (forkTypes p q) [E,D] (forkEncode p q) (localDest i) x = .inr (inj ⟨i,x⟩))
    (site : Site (List.ofFn R ++ [E,D]) X) (x : TyDen X) :
    route (forkTypes p q) [E,D] (forkEncode p q)
      (redirect localDest (externalSite (forkTypes p q) [E,D]) site) x =
        Sum.map id inj (route R [E,D] id site x) := by
  unfold redirect
  generalize h : splitSite R [E,D] site = dest
  obtain ⟨dest, eq⟩ := dest
  subst site
  cases dest with
  | «local» i =>
    change route _ _ _ (localDest i) x = Sum.map id inj (route R [E,D] id (localSite _ _ i) x)
    rw [route_local]
    exact localEq i x
  | external i =>
    change route _ _ _ (externalSite _ _ i) x = Sum.map id inj (route R [E,D] id (externalSite _ _ i) x)
    rw [route_external, route_external]
    rfl

private theorem fork_left_route (site : Site p.Labels X) (x : TyDen X) :
    route (forkTypes p q) [E,D] (forkEncode p q) (forkLeft p q site) x =
      Sum.map id Sum.inl (route p.localTypes [E,D] id site x) :=
  fork_route p q p.localTypes Sum.inl _ (by
    intro i x
    rw [route_cast, route_local]
    simp only [forkEncode, forkAt, Fin.addCases_left, payload_cast_cancel]) site x

private theorem fork_right_route (site : Site q.Labels X) (x : TyDen X) :
    route (forkTypes p q) [E,D] (forkEncode p q) (forkRight p q site) x =
      Sum.map id Sum.inr (route q.localTypes [E,D] id site x) :=
  fork_route p q q.localTypes Sum.inr _ (by
    intro i x
    rw [route_cast, route_local]
    simp only [forkEncode, forkAt, Fin.addCases_right, payload_cast_cancel]) site x

private noncomputable def forkStep : ForkState p q → m (LabelDen [E,D] ⊕ ForkState p q)
  | .inl i => fragStep (ε := ε) p i >>= fun r => pure (Sum.map id Sum.inl r)
  | .inr i => fragStep (ε := ε) q i >>= fun r => pure (Sum.map id Sum.inr r)

variable (gate : TwoBlock.Instruction Φ A (Carrier Y M M))

omit [Iterate m] [LawfulElgotMonad m] in
private theorem forkDispatch (entry : Flat.Block Φ (ForkLabels p q) A)
    (i : Fin ((forkWith p q entry).count)) (x : TyDen ((forkWith p q entry).localTypes i)) :
    runBlock (ε := ε) (m := m) (route (forkTypes p q) [E,D] (forkEncode p q)) ((forkWith p q entry).blocks i) x =
      forkStep (ε := ε) p q (forkEncode p q ⟨i,x⟩) := by
  revert x
  refine Fin.addCases (m := p.count) (n := q.count) ?_ ?_ i
  · intro j x
    simp only [forkWith, forkEncode, forkAt, Fin.addCases_left, flat_action_cast, forkStep, fragStep]
    exact runBlock_map (ε := ε) (p.blocks j) _ (forkLeft p q) _ _ _ (fork_left_route p q)
  · intro j x
    simp only [forkWith, forkEncode, forkAt, Fin.addCases_right, flat_action_cast, forkStep, fragStep]
    exact runBlock_map (ε := ε) (q.blocks j) _ (forkRight p q) _ _ _ (fork_right_route p q)

private theorem forkArm {Z : τ} (arm : Fragment Φ Z E D)
    (rename : ∀ {W}, Site arm.Labels W → Site (ForkLabels p q) W)
    (inj : FiniteLabelDen arm.localTypes → ForkState p q)
    (commute : ∀ {W} (site : Site arm.Labels W) (x : TyDen W),
      route (forkTypes p q) [E,D] (forkEncode p q) (rename site) x =
        Sum.map id inj (route arm.localTypes [E,D] id site x))
    (stepEq : ∀ i, forkStep (ε := ε) (m := m) p q (inj i) =
      fragStep (ε := ε) arm i >>= fun r => pure (Sum.map id inj r))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (x : TyDen Z) :
    (runBlock (ε := ε) (route (forkTypes p q) [E,D] (forkEncode p q)) (arm.entry.rename rename) x >>=
      Sum.elim pure (iter (forkStep (ε := ε) p q))) =
      Region.denote (ε := ε) (m := m) arm.typing (PUnit.unit, x) := by
  rw [fragment_run arm id (fragStep (ε := ε) arm) (fun _ _ => rfl) coherent,
    runBlock_map (ε := ε) arm.entry x rename _ _ _ commute]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext r
  cases r with
  | inl => rfl
  | inr i =>
    have square : (fragStep (ε := ε) (m := m) arm >=> liftPure (Sum.map id inj)) =
        (liftPure inj >=> forkStep (ε := ε) (m := m) p q) := by
      funext j
      simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
      exact (stepEq j).symm
    simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, Sum.map_inr, Sum.elim_inr] using
      (congrFun (LawfulElgotMonad.uniformity _ _ _ square) i).symm

theorem flat_fork_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (fork p q gate).typing env =
      callCase (ε := ε) gate env.2 >>= fun
        | .inl x => Region.denote (ε := ε) (m := m) p.typing
            (PUnit.unit, Sum.elim id id (TypeModel.coprodEquiv M M x))
        | .inr y => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit, y) := by
  rw [fragment_run (fork p q gate) (forkEncode p q) (forkStep (ε := ε) p q)
    (forkDispatch p q _) coherent]
  simp only [fork, forkWith, runBlock, bind_assoc]
  congr 1
  funext selected
  cases selected with
  | inl x =>
    simp only [Sum.elim_inl]
    cases TypeModel.coprodEquiv M M x <;>
      exact forkArm p q p (forkLeft p q) Sum.inl (fork_left_route p q) (fun _ => rfl) coherent _
  | inr y => exact forkArm p q q (forkRight p q) Sum.inr (fork_right_route p q) (fun _ => rfl) coherent y

theorem flat_forkCase_denote (gate : TwoBlock.Instruction Φ A (Silmaril.coprod M Y))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (forkCase p q gate).typing env =
      callCase (ε := ε) gate env.2 >>= fun
        | .inl x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x)
        | .inr y => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,y) := by
  rw [fragment_run (forkCase p q gate) (forkEncode p q) (forkStep (ε := ε) p q)
    (forkDispatch p q _) coherent]
  simp only [forkCase, forkWith, runBlock, bind_assoc]
  congr 1
  funext selected
  cases selected with
  | inl x => exact forkArm p q p (forkLeft p q) Sum.inl (fork_left_route p q) (fun _ => rfl) coherent x
  | inr y => exact forkArm p q q (forkRight p q) Sum.inr (fork_right_route p q) (fun _ => rfl) coherent y

end FlatFork

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs
