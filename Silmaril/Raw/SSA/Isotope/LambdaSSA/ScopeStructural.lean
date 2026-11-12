module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.RegionScope
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Sequence
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-!
# Stability of positional scope under renaming

Renaming value variables or exit labels keeps a term or region scoped, provided
the renaming maps every in-range index to an in-range index. Label renamings
must be respected underneath control-flow-graph binders, which shift the label
scope by the number of blocks they introduce.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u}

/-- An expression stays scoped under a renaming that respects the variable bound. -/
theorem Tm.Scoped.rename {a : Tm Φ} {n m : Nat} {ρ : Nat → Nat}
    (h : a.Scoped n) (hρ : ∀ i, i < n → ρ i < m) : (a.rename ρ).Scoped m := by
  induction a generalizing n m ρ with
  | var i => exact hρ i h
  | op _ a ih => exact ih h hρ
  | let₁ a b iha ihb =>
      exact ⟨iha h.1 hρ, ihb h.2 (fun i hi => by
        cases i with
        | zero => exact Nat.zero_lt_succ _
        | succ j => exact Nat.succ_lt_succ (hρ j (Nat.lt_of_succ_lt_succ hi)))⟩
  | pair a b iha ihb => exact ⟨iha h.1 hρ, ihb h.2 hρ⟩
  | unit => trivial
  | let₂ a b iha ihb =>
      refine ⟨iha h.1 hρ, ihb h.2 (fun i hi => ?_)⟩
      match i with
      | 0 => rw [Silmaril.DeBruijn.liftN_lt ρ (by omega)]; omega
      | 1 => rw [Silmaril.DeBruijn.liftN_lt ρ (by omega)]; omega
      | j + 2 =>
          have := hρ j (by omega)
          rw [Silmaril.DeBruijn.liftN_ge ρ (by omega), Nat.add_sub_cancel]
          omega
  | inl a ih => exact ih h hρ
  | inr a ih => exact ih h hρ
  | case e l r ihe ihl ihr =>
      refine ⟨ihe h.1 hρ, ihl h.2.1 ?_, ihr h.2.2 ?_⟩ <;>
        exact fun i hi => by
          cases i with
          | zero => exact Nat.zero_lt_succ _
          | succ j => exact Nat.succ_lt_succ (hρ j (Nat.lt_of_succ_lt_succ hi))
  | abort a ih => exact ih h hρ

/-- A region stays scoped under a value renaming that respects the variable bound. -/
theorem Region.Scoped.renameVars {r : Region Φ} {labels n m : Nat} {ρ : Nat → Nat}
    (h : r.Scoped labels n) (hρ : ∀ i, i < n → ρ i < m) :
    (r.renameVars ρ).Scoped labels m := by
  induction r generalizing labels n m ρ with
  | br ℓ a => exact ⟨h.1, Tm.Scoped.rename h.2 hρ⟩
  | case a l r ihl ihr =>
      have hlift : ∀ i, i < n + 1 → Silmaril.DeBruijn.lift ρ i < m + 1 := fun i hi => by
        cases i with
        | zero => exact Nat.zero_lt_succ _
        | succ j => exact Nat.succ_lt_succ (hρ j (Nat.lt_of_succ_lt_succ hi))
      exact ⟨Tm.Scoped.rename h.1 hρ, ihl h.2.1 hlift, ihr h.2.2 hlift⟩
  | let₁ a b ih =>
      refine ⟨Tm.Scoped.rename h.1 hρ, ih h.2 (fun i hi => ?_)⟩
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ j => exact Nat.succ_lt_succ (hρ j (Nat.lt_of_succ_lt_succ hi))
  | let₂ a b ih =>
      refine ⟨Tm.Scoped.rename h.1 hρ, ih h.2 (fun i hi => ?_)⟩
      match i with
      | 0 => rw [Silmaril.DeBruijn.liftN_lt ρ (by omega)]; omega
      | 1 => rw [Silmaril.DeBruijn.liftN_lt ρ (by omega)]; omega
      | j + 2 =>
          have := hρ j (by omega)
          rw [Silmaril.DeBruijn.liftN_ge ρ (by omega), Nat.add_sub_cancel]
          omega
  | cfg entry count blocks ihe ihb =>
      refine ⟨ihe h.1 hρ, fun i => ihb i (h.2 i) (fun j hj => ?_)⟩
      cases j with
      | zero => exact Nat.zero_lt_succ _
      | succ j => exact Nat.succ_lt_succ (hρ j (Nat.lt_of_succ_lt_succ hj))

/-- A region stays scoped under a label renaming that respects the label bound. -/
theorem Region.Scoped.renameLabels {r : Region Φ} {labels labels' n : Nat} {ρ : Nat → Nat}
    (h : r.Scoped labels n) (hρ : ∀ i, i < labels → ρ i < labels') :
    (r.renameLabels ρ).Scoped labels' n := by
  induction r generalizing labels labels' n ρ with
  | br ℓ a => exact ⟨hρ ℓ h.1, h.2⟩
  | case a l r ihl ihr => exact ⟨h.1, ihl h.2.1 hρ, ihr h.2.2 hρ⟩
  | let₁ a b ih => exact ⟨h.1, ih h.2 hρ⟩
  | let₂ a b ih => exact ⟨h.1, ih h.2 hρ⟩
  | cfg entry count blocks ihe ihb =>
      have hlift : ∀ i, i < count + labels → Silmaril.DeBruijn.liftN count ρ i < count + labels' := by
        intro i hi
        by_cases hlt : i < count
        · rw [Silmaril.DeBruijn.liftN_lt ρ hlt]; omega
        · rw [Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hlt)]
          have := hρ (i - count) (by omega)
          omega
      exact ⟨ihe h.1 hlift, fun i => ihb i (h.2 i) hlift⟩

/-- Widening the exit context preserves scope. -/
theorem Region.Scoped.mono {r : Region Φ} {labels labels' n : Nat}
    (h : r.Scoped labels n) (hle : labels ≤ labels') : r.Scoped labels' n := by
  induction r generalizing labels labels' n with
  | br ℓ a => exact ⟨Nat.lt_of_lt_of_le h.1 hle, h.2⟩
  | case a l r ihl ihr => exact ⟨h.1, ihl h.2.1 hle, ihr h.2.2 hle⟩
  | let₁ a b ih => exact ⟨h.1, ih h.2 hle⟩
  | let₂ a b ih => exact ⟨h.1, ih h.2 hle⟩
  | cfg entry count blocks ihe ihb =>
      exact ⟨ihe h.1 (by omega), fun i => ihb i (h.2 i) (by omega)⟩

variable {α : Type v} {σ : Type w} {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- Internal control transfers stay inside the graph, so a transfer that starts
inside a graph whose blocks only exit in range leaves it in range. -/
theorem Region.Follow.label_lt {count labels : Nat} {blocks : Fin count → Region Φ}
    {env : Semantics.Env α} {first : Nat} {current : Value α} {s : σ}
    {label : Nat} {value : Value α} {s' : σ}
    (hblocks : ∀ (i : Fin count) (cur : Value α) {s : σ} {next : Nat} {v : Value α} {s' : σ},
      Semantics.Region.Eval instr (Semantics.extend env cur) (blocks i) s next v s' →
      next < count + labels)
    (h : Semantics.Region.Follow instr env blocks first current s label value s') :
    first < count + labels → label < labels := by
  induction h using Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => intro hfirst; omega
  | step inside head _ _ ih => intro _; exact ih hblocks (hblocks _ _ head)
  | _ => trivial

/-- A scoped region can only exit at one of its own labels. -/
theorem Region.Scoped.eval_label_lt {r : Region Φ} {labels n : Nat}
    {env : Semantics.Env α} {s s' : σ} {label : Nat} {out : Value α}
    (h : r.Scoped labels n) (run : Semantics.Region.Eval instr env r s label out s') :
    label < labels := by
  induction r generalizing labels n env s s' label out with
  | br ℓ a => cases run with | br _ => exact h.1
  | case a l r ihl ihr =>
      cases run with
      | case_inl _ branch => exact ihl h.2.1 branch
      | case_inr _ branch => exact ihr h.2.2 branch
  | let₁ a b ih => cases run with | let₁ _ body => exact ih h.2 body
  | let₂ a b ih => cases run with | let₂ _ body => exact ih h.2 body
  | cfg entry count blocks ihe ihb =>
      cases run with
      | cfg entryRun follow =>
          exact Region.Follow.label_lt
            (fun i cur {_s _next _v _s'} run => ihb i (h.2 i) run) follow (ihe h.1 entryRun)

/-- Sequencing a single-exit region with a continuation keeps both scoped. -/
theorem Region.Scoped.sequence {first next : Region Φ} {labels n : Nat}
    (hf : first.Scoped 1 n) (hn : next.Scoped labels (n + 1)) :
    (Region.sequence first next).Scoped labels n := by
  refine ⟨hf.mono (by omega), fun _ => hn.renameLabels (fun i hi => by omega)⟩

end Silmaril.Isotope.LambdaSSA
