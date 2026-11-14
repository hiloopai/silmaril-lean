module

public import Silmaril.X86.Concurrency.Cir.Progress.Defs

/-!
# Proofs: the thread-local progress rules

`Inv w A s B` (every thread state reachable from `s` under `A` is `Good`, and `B` holds at the
end) is closed under `seq`, `ite`, bounded loops (with `A` a loop invariant) and consequence, and
holds of every leaf whose access fits the width map. `inv_of_rel` is the coinduction-style
principle behind the structural rules: a relation closed under thread steps whose states are all
`Good`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Progress

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Progress
open Silmaril.X86.Atomic9 (FenceKind)

/-! ## Reachability -/

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h1 : Star r a b)
    (h2 : Star r b c) : Star r a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem star_snoc {α : Type} {r : α → α → Prop} {a b c : α} (h1 : Star r a b) (h : r b c) :
    Star r a c := star_trans h1 (.step h .refl)

theorem treach_snoc {p q : Stmt × Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TReach p q) (st : TStep q.1 q.2 l s' rs') : TReach p (s', rs') :=
  star_snoc h ⟨l, st⟩

/-- **The relation principle**: a relation containing the start states, closed under thread
steps, whose states are `Good` and satisfy `B` when finished, gives `Inv`. -/
theorem inv_of_rel {w : Nat → Option Nat} {A B : Regs → Prop} {s : Stmt}
    (R : Stmt → Regs → Prop) (h0 : ∀ rs, A rs → R s rs)
    (hc : ∀ s rs, R s rs → Good w s rs ∧ (s = .skip → B rs) ∧
      ∀ l s' rs', TStep s rs l s' rs' → R s' rs') : Inv w A s B := by
  intro rs hA p hp
  have key : ∀ q p, TReach q p → R q.1 q.2 → R p.1 p.2 := by
    intro q p h
    induction h with
    | refl => exact id
    | step h _ ih =>
      intro hq
      obtain ⟨l, hl⟩ := h
      exact ih ((hc _ _ hq).2.2 _ _ _ hl)
  have := key _ _ hp (h0 rs hA)
  exact ⟨(hc _ _ this).1, (hc _ _ this).2.1⟩

/-! ## `Good` -/

theorem good_skip {w : Nat → Option Nat} {rs : Regs} : Good w .skip rs :=
  ⟨fun _ _ _ h => (by cases h), Or.inl rfl⟩

/-- A state with only silent steps, one of which exists. -/
theorem good_tau {w : Nat → Option Nat} {s s' : Stmt} {rs rs' : Regs}
    (hno : ∀ l s' rs', ¬ TStep s rs (some l) s' rs') (h : TStep s rs none s' rs') : Good w s rs :=
  ⟨fun l s' rs' st => absurd st (hno l s' rs'), Or.inr (Or.inr (Or.inl ⟨s', rs', h⟩))⟩

theorem good_seq {w : Nat → Option Nat} {s t : Stmt} {rs : Regs} (h : Good w s rs) :
    Good w (.seq s t) rs := by
  refine ⟨fun l s' rs' st => ?_, ?_⟩
  · cases st with
    | seq h' => exact h.1 _ _ _ h'
  · rcases h.2 with hs | ⟨c, b, h1, h2⟩ | ⟨s', rs', st⟩ | hH
    · subst hs
      exact Or.inr (Or.inr (Or.inl ⟨t, rs, .seqSkip⟩))
    · exact Or.inr (Or.inl ⟨c, b, h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, _, .seq st⟩))
    · refine Or.inr (Or.inr (Or.inr fun H hf hm => ?_))
      obtain ⟨l, s', rs', st, hok⟩ := hH H hf fun l s' rs' st a ha => hm l _ _ (.seq st) a ha
      exact ⟨l, _, _, .seq st, hok⟩

/-! ## Structural rules -/

theorem inv_conseq {w : Nat → Option Nat} {A A' B B' : Regs → Prop} {s : Stmt}
    (hA : ∀ rs, A' rs → A rs) (hB : ∀ rs, B rs → B' rs) (h : Inv w A s B) : Inv w A' s B' :=
  fun rs ha p hp => ⟨(h rs (hA rs ha) p hp).1, fun e => hB _ ((h rs (hA rs ha) p hp).2 e)⟩

theorem inv_skip {w : Nat → Option Nat} {A : Regs → Prop} : Inv w A .skip A := by
  refine inv_of_rel (fun x rs => x = .skip ∧ A rs) (fun rs h => ⟨rfl, h⟩) ?_
  rintro s rs ⟨rfl, h⟩
  exact ⟨good_skip, fun _ => h, fun _ _ _ st => by cases st⟩

theorem inv_seq {w : Nat → Option Nat} {A B C : Regs → Prop} {s t : Stmt} (h1 : Inv w A s B)
    (h2 : Inv w B t C) : Inv w A (.seq s t) C := by
  refine inv_of_rel (fun x rs => (∃ y rs0, A rs0 ∧ TReach (s, rs0) (y, rs) ∧ x = .seq y t) ∨
      ∃ rs1, B rs1 ∧ TReach (t, rs1) (x, rs)) (fun rs h => Or.inl ⟨s, rs, h, .refl, rfl⟩) ?_
  rintro x rs (⟨y, rs0, hA, hr, rfl⟩ | ⟨rs1, hB, hr⟩)
  · have G := h1 rs0 hA _ hr
    refine ⟨good_seq G.1, fun e => (by cases e), fun l s' rs' st => ?_⟩
    cases st with
    | seq h' => exact Or.inl ⟨_, rs0, hA, treach_snoc hr h', rfl⟩
    | seqSkip => exact Or.inr ⟨rs, G.2 rfl, .refl⟩
  · have G := h2 rs1 hB _ hr
    exact ⟨G.1, G.2, fun l s' rs' st => Or.inr ⟨rs1, hB, treach_snoc hr st⟩⟩

theorem inv_ite {w : Nat → Option Nat} {A B : Regs → Prop} {c : Expr} {s t : Stmt}
    (h1 : Inv w A s B) (h2 : Inv w A t B) : Inv w A (.ite c s t) B := by
  refine inv_of_rel (fun x rs => (x = .ite c s t ∧ A rs) ∨
      (∃ rs0, A rs0 ∧ TReach (s, rs0) (x, rs)) ∨ ∃ rs0, A rs0 ∧ TReach (t, rs0) (x, rs))
    (fun rs h => Or.inl ⟨rfl, h⟩) ?_
  rintro x rs (⟨rfl, hA⟩ | ⟨rs0, hA, hr⟩ | ⟨rs0, hA, hr⟩)
  · refine ⟨?_, fun e => (by cases e), fun l s' rs' st => ?_⟩
    · cases hc : truthy (c.eval rs)
      · exact good_tau (fun _ _ _ st => by cases st) (.iteF hc)
      · exact good_tau (fun _ _ _ st => by cases st) (.iteT hc)
    · cases st with
      | iteT _ => exact Or.inr (Or.inl ⟨rs, hA, .refl⟩)
      | iteF _ => exact Or.inr (Or.inr ⟨rs, hA, .refl⟩)
  · have G := h1 rs0 hA _ hr
    exact ⟨G.1, G.2, fun l s' rs' st => Or.inr (Or.inl ⟨rs0, hA, treach_snoc hr st⟩)⟩
  · have G := h2 rs0 hA _ hr
    exact ⟨G.1, G.2, fun l s' rs' st => Or.inr (Or.inr ⟨rs0, hA, treach_snoc hr st⟩)⟩

/-- **Bounded loops**, at every bound, with `A` a loop invariant of the body. -/
theorem inv_loop {w : Nat → Option Nat} {A : Regs → Prop} {n : Nat} {c : Expr} {b : Stmt}
    (hb : Inv w A b A) : Inv w A (.loop n c b) A := by
  refine inv_of_rel (fun x rs => (∃ m, x = .loop m c b ∧ A rs) ∨
      (∃ y rs0 m, A rs0 ∧ TReach (b, rs0) (y, rs) ∧ x = .seq y (.loop m c b)) ∨
      (x = .skip ∧ A rs))
    (fun rs h => Or.inl ⟨n, rfl, h⟩) ?_
  rintro x rs (⟨m, rfl, hA⟩ | ⟨y, rs0, m, hA, hr, rfl⟩ | ⟨rfl, hA⟩)
  · refine ⟨?_, fun e => (by cases e), fun l s' rs' st => ?_⟩
    · cases hc : truthy (c.eval rs)
      · exact good_tau (fun _ _ _ st => by cases st) (.loopF hc)
      · cases m with
        | zero => exact ⟨fun _ _ _ st => (by cases st), Or.inr (Or.inl ⟨c, b, rfl, hc⟩)⟩
        | succ m => exact good_tau (fun _ _ _ st => by cases st) (.loopT hc)
    · cases st with
      | loopT _ => exact Or.inr (Or.inl ⟨b, rs, _, hA, .refl, rfl⟩)
      | loopF _ => exact Or.inr (Or.inr ⟨rfl, hA⟩)
  · have G := hb rs0 hA _ hr
    refine ⟨good_seq G.1, fun e => (by cases e), fun l s' rs' st => ?_⟩
    cases st with
    | seq h' => exact Or.inr (Or.inl ⟨_, rs0, m, hA, treach_snoc hr h', rfl⟩)
    | seqSkip => exact Or.inl ⟨m, rfl, G.2 rfl⟩
  · exact ⟨good_skip, fun _ => hA, fun _ _ _ st => by cases st⟩

/-! ## Leaves -/

/-- A leaf: every step ends at `skip`, satisfying `B`. -/
theorem inv_leaf {w : Nat → Option Nat} {A B : Regs → Prop} {s : Stmt} (hs : s ≠ .skip)
    (hg : ∀ rs, A rs → Good w s rs)
    (hpost : ∀ rs, A rs → ∀ l s' rs', TStep s rs l s' rs' → s' = .skip ∧ B rs') :
    Inv w A s B := by
  refine inv_of_rel (fun x rs => (x = s ∧ A rs) ∨ (x = .skip ∧ B rs))
    (fun rs h => Or.inl ⟨rfl, h⟩) ?_
  rintro x rs (⟨rfl, hA⟩ | ⟨rfl, hB⟩)
  · refine ⟨hg rs hA, fun e => absurd e hs, fun l s' rs' st => ?_⟩
    obtain ⟨h1, h2⟩ := hpost rs hA l s' rs' st
    exact Or.inr ⟨h1, h2⟩
  · exact ⟨good_skip, fun _ => hB, fun _ _ _ st => by cases st⟩

theorem pow_mono {k sz : Nat} (h : k ≤ sz) : 2 ^ (8 * k) ≤ 2 ^ (8 * sz) :=
  Nat.pow_le_pow_right (by decide) (by omega)

theorem pow_pos' (k : Nat) : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _

theorem inv_assign {w : Nat → Option Nat} {A B : Regs → Prop} {d : Reg} {e : Expr}
    (hB : ∀ rs, A rs → B (rs.set d (e.eval rs))) : Inv w A (.assign d e) B :=
  inv_leaf (by intro h; cases h) (fun _ _ => good_tau (fun _ _ _ st => by cases st) .assign)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA⟩

theorem inv_load {w : Nat → Option Nat} {A B : Regs → Prop} {d : Reg} {m : Mode} {sz : Nat}
    {fl : Flav} {a : Expr}
    (hw : ∀ rs, A rs → ∃ k, w (a.eval rs).toNat = some k ∧ k ≤ sz)
    (hB : ∀ rs, A rs → ∀ v, B (rs.set d v)) : Inv w A (.load d m sz fl a) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA _⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st
    exact ⟨fun _ _ h => by simp [Lab.wval] at h, fun e he => by simp [Lab.ents] at he⟩
  · obtain ⟨k, hk, hks⟩ := hw rs hA
    have hT := hm _ _ _ (TStep.load (v := 0) (pow_pos' sz)) (a.eval rs).toNat
      (Or.inl ⟨0, by simp [Lab.reads]⟩)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
    have hlt : x < 2 ^ (8 * sz) := Nat.lt_of_lt_of_le (hf _ _ hx k hk) (pow_mono hks)
    exact ⟨_, _, _, TStep.load hlt, by simp [Lab.okH, Lab.reads, hx]⟩

theorem inv_store {w : Nat → Option Nat} {A B : Regs → Prop} {m : Mode} {sz : Nat} {fl : Flav}
    {a v : Expr} (hw : ∀ rs, A rs → ∀ k, w (a.eval rs).toNat = some k → sz ≤ k)
    (hB : ∀ rs, A rs → B rs) : Inv w A (.store m sz fl a v) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA⟩
  have hfit : fits w (a.eval rs).toNat ((v.eval rs).toNat % 2 ^ (8 * sz)) := fun k hk =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (pow_pos' sz)) (pow_mono (hw rs hA k hk))
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st
    refine ⟨fun x y h => ?_, fun e he x y b hb => ?_⟩
    · simp only [Lab.wval] at h
      split at h
      · cases h; subst_vars; exact hfit
      · cases h
    · simp only [Lab.ents, List.mem_singleton] at he
      subst he
      cases hb
      exact hfit
  · exact ⟨_, _, _, TStep.store, by simp [Lab.okH, Lab.reads]⟩

theorem rmw_result_lt {rs : Regs} {sz old : Nat} {arg : Word} (op : RmwOp)
    (h : old < 2 ^ (8 * sz)) : op.result rs sz old arg < 2 ^ (8 * sz) := by
  cases op with
  | xchg => exact Nat.mod_lt _ (pow_pos' sz)
  | fadd => exact Nat.mod_lt _ (pow_pos' sz)
  | cas e =>
    simp only [RmwOp.result]
    split
    · exact Nat.mod_lt _ (pow_pos' sz)
    · exact h
  | op o => exact Nat.mod_lt _ (pow_pos' sz)

theorem inv_rmw {w : Nat → Option Nat} {A B : Regs → Prop} {d : Reg} {m : Mode} {sz : Nat}
    {op : RmwOp} {a arg : Expr} (hw : ∀ rs, A rs → w (a.eval rs).toNat = some sz)
    (hB : ∀ rs, A rs → ∀ v, B (rs.set d v)) : Inv w A (.rmw d m sz op a arg) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA _⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st with
    | rmw hv =>
      refine ⟨fun x y h => ?_, fun e he => by simp [Lab.ents] at he⟩
      simp only [Lab.wval] at h
      split at h
      · cases h; subst_vars
        intro k hk
        rw [hw rs hA] at hk
        cases hk
        exact rmw_result_lt op hv
      · cases h
  · have hT := hm _ _ _ (TStep.rmw (op := op) (arg := arg) (old := 0) (pow_pos' sz))
      (a.eval rs).toNat (Or.inl ⟨0, by simp [Lab.reads]⟩)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
    have hlt : x < 2 ^ (8 * sz) := hf _ _ hx sz (hw rs hA)
    exact ⟨_, _, _, TStep.rmw hlt, by simp [Lab.okH, Lab.reads, hx]⟩

theorem inv_fence {w : Nat → Option Nat} {A B : Regs → Prop} {k : FenceKind}
    (hB : ∀ rs, A rs → B rs) : Inv w A (.fence k) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st
    refine ⟨fun _ _ h => by simp [Lab.wval] at h, fun e he x y b hb => ?_⟩
    subst hb
    cases k <;> simp [Lab.ents] at he
  · exact ⟨_, _, _, TStep.fence, by simp [Lab.okH, Lab.reads]⟩

theorem inv_fwait {w : Nat → Option Nat} {A B : Regs → Prop} {d : Reg} {a v : Expr}
    (hw : ∀ rs, A rs → ∃ k, w (a.eval rs).toNat = some k ∧ k ≤ 4)
    (hB : ∀ rs, A rs → ∀ x, B (rs.set d x)) : Inv w A (.futexWait d a v) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA _⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st
    exact ⟨fun _ _ h => by simp [Lab.wval] at h, fun e he => by simp [Lab.ents] at he⟩
  · obtain ⟨k, hk, hks⟩ := hw rs hA
    have hT := hm _ _ _ (TStep.fwait (v := v) (seen := 0) (r := 0) (by decide) (by decide))
      (a.eval rs).toNat (Or.inl ⟨0, by simp [Lab.reads]⟩)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
    have hlt : x < 2 ^ 32 :=
      Nat.lt_of_lt_of_le (hf _ _ hx k hk) (pow_mono (sz := 4) hks)
    exact ⟨_, _, _, TStep.fwait (r := 0) hlt (by decide), by simp [Lab.okH, Lab.reads, hx]⟩

theorem inv_fwake {w : Nat → Option Nat} {A B : Regs → Prop} {a n : Expr}
    (hB : ∀ rs, A rs → B rs) : Inv w A (.futexWake a n) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st
    exact ⟨fun _ _ h => by simp [Lab.wval] at h, fun e he => by simp [Lab.ents] at he⟩
  · exact ⟨_, _, _, TStep.fwake (q := 0) (by decide), by simp [Lab.okH, Lab.reads]⟩

/-! ## Blocks -/

theorem cellVals_fst : ∀ {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat},
    c ∈ cellVals cs vs → ∃ d ∈ cs, d.1 = c.1
  | [], _, _, h => by simp [cellVals] at h
  | _ :: _, [], _, h => by simp [cellVals] at h
  | d :: cs, v :: vs, c, h => by
    simp only [cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d, List.mem_cons_self .., rfl⟩
    · obtain ⟨d', hd', e⟩ := cellVals_fst h
      exact ⟨d', List.mem_cons_of_mem _ hd', e⟩

theorem cellLast_some : ∀ {l : List (Nat × Nat × Nat)} {a v : Nat}, cellLast l a = some v →
    ∃ c ∈ l, c.1 = a
  | [], _, _, h => by simp [cellLast] at h
  | c :: l, a, v, h => by
    simp only [cellLast] at h
    cases e : cellLast l a with
    | some _ =>
      obtain ⟨c', hc', e'⟩ := cellLast_some e
      exact ⟨c', List.mem_cons_of_mem _ hc', e'⟩
    | none =>
      rw [e] at h
      simp only [Option.none_or] at h
      split at h
      · exact ⟨c, List.mem_cons_self .., by assumption⟩
      · cases h

theorem cellVals_map : ∀ (cs : List (Nat × Nat)) (f : Nat × Nat → Nat),
    cellVals cs (cs.map f) = cs.map fun c => (c.1, c.2, f c)
  | [], _ => rfl
  | c :: cs, f => by simp [cellVals, cellVals_map cs f]

theorem inv_block {w : Nat → Option Nat} {A B : Regs → Prop} {b : Block}
    (htot : ∀ rs, A rs → ∀ ivs, ivs.length = b.ins.length → ∃ rvs ovs,
      rvs.length = b.rout.length ∧ ovs.length = b.outs.length ∧
      b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) (rvs ++ ovs))
    (hw : ∀ c ∈ b.outs, w c.1 = none)
    (hB : ∀ rs, A rs → ∀ rvs, B (rs.setMany b.rout rvs)) : Inv w A (.local b) B := by
  refine inv_leaf (by intro h; cases h) (fun rs hA => ?_)
    fun rs hA l s' rs' st => by cases st; exact ⟨rfl, hB rs hA _⟩
  refine ⟨fun l s' rs' st => ?_, Or.inr (Or.inr (Or.inr fun H hf hm => ?_))⟩
  · cases st with
    | blk hspec hi hr ho =>
      refine ⟨fun x y h => ?_, fun e he x y bb hb => ?_⟩
      · simp only [Lab.wval] at h
        obtain ⟨c, hc, rfl⟩ := cellLast_some h
        obtain ⟨d, hd, e⟩ := cellVals_fst hc
        intro k hk
        rw [← e, hw d hd] at hk
        cases hk
      · simp only [Lab.ents, List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        cases hb
        obtain ⟨d, hd, e⟩ := cellVals_fst hc
        intro k hk
        rw [← e, hw d hd] at hk
        cases hk
  · obtain ⟨rvs0, ovs0, hr0, ho0, hs0⟩ := htot rs hA (b.ins.map fun _ => 0) (by simp)
    have st0 := TStep.blk (rs := rs) hs0 (by simp) hr0 ho0
    have hmap : ∀ c ∈ b.ins, (H c.1).isSome := by
      intro c hc
      refine hm _ _ _ st0 c.1 (Or.inl ⟨0, ?_⟩)
      simp only [Lab.reads, List.mem_map]
      refine ⟨(c.1, c.2, 0), ?_, rfl⟩
      rw [show (b.ins.map fun _ => 0) = b.ins.map (fun (_ : Nat × Nat) => 0) from rfl,
        cellVals_map]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    let ivs := b.ins.map fun c => (H c.1).getD 0
    obtain ⟨rvs, ovs, hr, ho, hs⟩ := htot rs hA ivs (by simp [ivs])
    refine ⟨_, _, _, TStep.blk hs (by simp [ivs]) hr ho, ?_⟩
    intro p hp
    simp only [Lab.reads, ivs, cellVals_map, List.map_map, List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hmap c hc)
    simp [hx]

end Silmaril.Proofs.X86.Concurrency.Cir.Progress
