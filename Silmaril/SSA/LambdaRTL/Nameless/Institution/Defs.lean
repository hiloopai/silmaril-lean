module

public import Silmaril.SSA.LambdaRTL.Nameless.Thms
public import Silmaril.SSA.LambdaRTL.Institution.Defs

/-!
# Named and nameless λSSA institutions and the comorphisms between them

`dbInst R`: sentences are de Bruijn judgements `n ⊢ d ⋈ d'` with `d`, `d'` well-scoped in `n`
variables; a model satisfies one when `R (⟦d⟧η) (⟦d'⟧η)` for every environment `η : ℕ → α`.

* `toDBCoHom R : Inst.CoHom (ssa V L M α R) (dbInst L M α R)` — named → nameless, translating
  `Γ ⊢ r ⋈ r'` (with `Γ` a `Finset`) along the list `Γ.toList`.
* `ofDBCoHom S R : Inst.CoHom (dbInst L M α R) (ssa V L M α R)` — nameless → named, using a
  fresh-name supply `S : Supply V` (this is the only place infinitude is needed: a supply exists
  iff every finite set of names can be avoided, e.g. `Supply.ofInfinite` for `[Infinite V]`).

Both are identity on signatures and models. **Round trips (sentence level):**
`ofDB_toDB_sen`: nameless → named → nameless is the identity on sentences, exactly.
named → nameless → named is the identity only **up to α-equivalence and a renaming of the
context** (`Region.alphaEq_ofDB_toDB`, stated in the canonical context); we do not package this
as an equivalence of institutions here.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Institution

open CategoryTheory Silmaril.Logic.Institution

variable (V L : Type) [DecidableEq V] [DecidableEq L] (M : Type → Type) [Monad M] (α : Type)

/-- A de Bruijn judgement `n ⊢ d ⋈ d'`. -/
structure DBJudgement (F : Type) where
  n : ℕ
  lhs : DB.Region L F
  rhs : DB.Region L F
  lhs_ws : lhs.WS n
  rhs_ws : rhs.WS n

variable {L}

omit [DecidableEq L] in
theorem DBJudgement.ext' {F : Type} {j k : DBJudgement L F} (hn : j.n = k.n)
    (hl : j.lhs = k.lhs) (hr : j.rhs = k.rhs) : j = k := by
  cases j; cases k; cases hn; cases hl; cases hr; rfl

omit [DecidableEq L] in
theorem SSAJudgement.ext' {V : Type} [DecidableEq V] {F : Type} {j k : SSAJudgement V L F}
    (hc : j.ctx = k.ctx) (hl : j.lhs = k.lhs) (hr : j.rhs = k.rhs) : j = k := by
  rcases j with ⟨⟨_, _, _⟩, _, _⟩; rcases k with ⟨⟨_, _, _⟩, _, _⟩
  cases hc; cases hl; cases hr; rfl

/-- Renaming instructions in a de Bruijn judgement. -/
def DBJudgement.map {F F' : Type} (h : F → F') (j : DBJudgement L F) : DBJudgement L F' :=
  ⟨j.n, j.lhs.mapOp h, j.rhs.mapOp h, (DB.Region.ws_mapOp h _ _).2 j.lhs_ws,
    (DB.Region.ws_mapOp h _ _).2 j.rhs_ws⟩

variable (L)

/-- The room of de Bruijn judgements over `F`. -/
def dbRoom (R : M (L × α) → M (L × α) → Prop) (S : Sig) : Room.{0, 0, 0} where
  Sen := DBJudgement L S.ops
  Mod := Cat.of (Discrete (Model S.ops M α))
  Sat m j := ∀ η : ℕ → α, R (j.lhs.eval m.as η) (j.rhs.eval m.as η)

/-- The nameless λSSA equivalence/refinement-in-context institution. -/
def dbInst (R : M (L × α) → M (L × α) → Prop) : Inst.{1, 0, 0, 0, 0} where
  Sign := Sig
  I :=
    { obj := dbRoom L M α R
      map {S S'} h :=
        ⟨DBJudgement.map h, reductFunctor h, fun m j => by
          change (∀ η, R ((j.lhs.mapOp h).eval m.as η) ((j.rhs.mapOp h).eval m.as η)) ↔
            ∀ η, R (j.lhs.eval (m.as.reduct h) η) (j.rhs.eval (m.as.reduct h) η)
          simp only [DB.Region.eval_mapOp]⟩
      map_id S := by
        apply Room.hom_ext
        · funext j
          change DBJudgement.map id j = j
          cases j
          simp only [DBJudgement.map, DB.Region.mapOp_id]
        · exact reductFunctor_id S.ops
      map_comp {S S' S''} h k := by
        apply Room.hom_ext
        · funext j
          change DBJudgement.map (k ∘ h) j = DBJudgement.map k (DBJudgement.map h j)
          cases j
          simp only [DBJudgement.map, DB.Region.mapOp_comp]
        · exact reductFunctor_comp h k }

variable {V L M α}

/-- Satisfaction transfer along `toDB` for any pair of regions scoped in `Γ`. -/
theorem forall_evalSSA_iff_forall_eval {F : Type} (m : Model F M α) (P : M (L × α) → M (L × α) → Prop)
    {Γ : List V} {r r' : Region V L F} (hr : r.fv ⊆ Γ.toFinset) (hr' : r'.fv ⊆ Γ.toFinset) :
    (∀ ρ : V → α, P (r.evalSSA m ρ) (r'.evalSSA m ρ)) ↔
      ∀ η : ℕ → α, P ((r.toDB Γ).eval m η) ((r'.toDB Γ).eval m η) := by
  constructor
  · intro h η
    rw [Region.eval_toDB m r (agree_comp Γ η) hr, Region.eval_toDB m r' (agree_comp Γ η) hr']
    exact h _
  · intro h ρ
    rw [← Region.eval_toDB_env m r hr ρ m.unit, ← Region.eval_toDB_env m r' hr' ρ m.unit]
    exact h _

/-- Named SSA judgement to de Bruijn judgement. -/
noncomputable def toDBSen {F : Type} (j : SSAJudgement V L F) : DBJudgement L F :=
  ⟨j.ctx.toList.length, j.lhs.toDB j.ctx.toList, j.rhs.toDB j.ctx.toList,
    Region.ws_toDB _ (by simpa using Region.fv_subset_of_isSSA j.lhs_ssa),
    Region.ws_toDB _ (by simpa using Region.fv_subset_of_isSSA j.rhs_ssa)⟩

/-- de Bruijn judgement to named SSA judgement, along a fresh-name supply. -/
def ofDBSen {F : Type} (S : Supply V) (j : DBJudgement L F) : SSAJudgement V L F :=
  ⟨⟨(S.ctx j.n).toFinset, j.lhs.ofDB S (S.ctx j.n), j.rhs.ofDB S (S.ctx j.n)⟩,
    DB.Region.isSSA_ofDB S _ _ (by simpa [Supply.length_ctx] using j.lhs_ws),
    DB.Region.isSSA_ofDB S _ _ (by simpa [Supply.length_ctx] using j.rhs_ws)⟩

omit [DecidableEq L] in
/-- **Round trip** nameless → named → nameless is the identity on sentences. -/
theorem ofDB_toDB_sen {F : Type} (S : Supply V) (j : DBJudgement L F) :
    (ofDBSen S j).lhs.toDB (S.ctx j.n) = j.lhs ∧ (ofDBSen S j).rhs.toDB (S.ctx j.n) = j.rhs :=
  ⟨DB.Region.toDB_ofDB S (Supply.nodup_ctx S _) _ (by simpa [Supply.length_ctx] using j.lhs_ws),
    DB.Region.toDB_ofDB S (Supply.nodup_ctx S _) _ (by simpa [Supply.length_ctx] using j.rhs_ws)⟩

variable (V L M α)

/-- **Comorphism** named λSSA → nameless λSSA. -/
noncomputable def toDBCoHom (R : M (L × α) → M (L × α) → Prop) :
    Inst.CoHom (ssa V L M α R) (dbInst L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app S := ⟨toDBSen, 𝟭 _, fun m j => by
        change (∀ η, R ((j.lhs.toDB j.ctx.toList).eval m.as η)
            ((j.rhs.toDB j.ctx.toList).eval m.as η)) ↔
          ∀ ρ, R (j.lhs.evalSSA m.as ρ) (j.rhs.evalSSA m.as ρ)
        exact (forall_evalSSA_iff_forall_eval m.as R
          (by simpa using Region.fv_subset_of_isSSA j.lhs_ssa)
          (by simpa using Region.fv_subset_of_isSSA j.rhs_ssa)).symm⟩
      naturality := by
        intro S S' h
        apply Room.hom_ext
        · funext j
          change toDBSen (SSAJudgement.map h j) = DBJudgement.map h (toDBSen j)
          exact DBJudgement.ext' rfl (Region.toDB_mapOp h _ _) (Region.toDB_mapOp h _ _)
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

/-- **Comorphism** nameless λSSA → named λSSA, along a fresh-name supply. -/
def ofDBCoHom (S : Supply V) (R : M (L × α) → M (L × α) → Prop) :
    Inst.CoHom (dbInst L M α R) (ssa V L M α R) where
  Φ := 𝟭 Sig
  ρ :=
    { app _ := ⟨ofDBSen S, 𝟭 _, fun m j => by
        change (∀ ρ, R ((j.lhs.ofDB S (S.ctx j.n)).evalSSA m.as ρ)
            ((j.rhs.ofDB S (S.ctx j.n)).evalSSA m.as ρ)) ↔
          ∀ η, R (j.lhs.eval m.as η) (j.rhs.eval m.as η)
        have hl : j.lhs.WS (S.ctx j.n).length := by simpa [Supply.length_ctx] using j.lhs_ws
        have hr : j.rhs.WS (S.ctx j.n).length := by simpa [Supply.length_ctx] using j.rhs_ws
        rw [forall_evalSSA_iff_forall_eval m.as R (DB.Region.fv_ofDB S _ _ hl)
          (DB.Region.fv_ofDB S _ _ hr),
          DB.Region.toDB_ofDB S (Supply.nodup_ctx S _) _ hl,
          DB.Region.toDB_ofDB S (Supply.nodup_ctx S _) _ hr]⟩
      naturality := by
        intro S₁ S₂ h
        apply Room.hom_ext
        · funext j
          change ofDBSen S (DBJudgement.map h j) = SSAJudgement.map h (ofDBSen S j)
          exact SSAJudgement.ext' rfl (DB.Region.ofDB_mapOp h S _ _) (DB.Region.ofDB_mapOp h S _ _)
        · exact CategoryTheory.Functor.ext (fun m => by cases m; rfl) }

end Silmaril.SSA.LambdaRTL.Institution
