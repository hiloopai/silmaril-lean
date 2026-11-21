module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms

/-!
# Localisation: facts about runs

* `run_chain_append`: a run of `chain (l₁ ++ l₂)` is a run of `chain l₁` then one of `chain l₂`;
* `run_mono`: runs are monotone in the domain;
* `run_frame`: a run changes only the registers the statement writes;
* `run_frag`: the labels of an owned, thread-free, futex-free fragment access its cells
  (`FragLab`);
* `run_avoid`: the actions of a statement that avoids the cells (and every ghost byte, which is
  above `ctlAddr 0`) touch no byte of a cell (`ActAvoid`).

`mem_pick`, `pick_of`, `mem_seqL`, `seqL_of`, `mem_cellVals`, `mem_cellVals_pick` are
**copied** from `Silmaril/Proofs/X86/Concurrency/Cir/Seq/Lab.lean` and
`Silmaril/Proofs/X86/Concurrency/Cir/Domain/Run.lean`, whose headers do not export them.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (chain)
open Silmaril.X86.MemoryModel.Litmus (seqL XAct)

/-! ## Copied list lemmas -/

theorem mem_pick {dom : List Nat} {sz v : Nat} (h : v ∈ pick dom sz) : v < 2 ^ (8 * sz) := by
  simp only [pick, List.mem_filter, decide_eq_true_eq] at h; exact h.2

theorem mem_pick_dom {dom : List Nat} {sz v : Nat} (h : v ∈ pick dom sz) : v ∈ dom := by
  simp only [pick, List.mem_filter] at h; exact h.1

theorem pick_of {dom : List Nat} {sz v : Nat} (h : v ∈ dom) (hv : v < 2 ^ (8 * sz)) :
    v ∈ pick dom sz := by
  simp only [pick, List.mem_filter, decide_eq_true_eq]; exact ⟨h, hv⟩

theorem pick_mono {dom dom' : List Nat} (hd : ∀ v ∈ dom, v ∈ dom') {sz v : Nat}
    (h : v ∈ pick dom sz) : v ∈ pick dom' sz :=
  pick_of (hd _ (mem_pick_dom h)) (mem_pick h)

theorem qpick_mono {dom dom' : List Nat} (hd : ∀ v ∈ dom, v ∈ dom') {v : Nat}
    (h : v ∈ qpick dom) : v ∈ qpick dom' := by
  simp only [qpick, List.mem_filter] at h ⊢
  exact ⟨pick_mono hd h.1, h.2⟩

theorem mem_seqL {α β : Type} (g : β → List α) :
    ∀ (cs : List β) (vs : List α), vs ∈ seqL (cs.map g) → List.Forall₂ (fun c v => v ∈ g c) cs vs
  | [], vs, h => by simp [seqL] at h; subst h; exact .nil
  | c :: cs, vs, h => by
    simp only [List.map_cons, seqL, List.mem_flatMap, List.mem_map] at h
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    exact .cons hv (mem_seqL g cs ws hws)

theorem seqL_of {α β : Type} (g : β → List α) :
    ∀ (cs : List β) (vs : List α), List.Forall₂ (fun c v => v ∈ g c) cs vs → vs ∈ seqL (cs.map g)
  | [], _, .nil => by simp [seqL]
  | c :: cs, _ :: vs, .cons hv h => by
    simp only [List.map_cons, seqL, List.mem_flatMap, List.mem_map]
    exact ⟨_, hv, vs, seqL_of g cs vs h, rfl⟩

theorem seqL_mono {α β : Type} {g g' : β → List α} (hg : ∀ c v, v ∈ g c → v ∈ g' c)
    (cs : List β) (vs : List α) (h : vs ∈ seqL (cs.map g)) : vs ∈ seqL (cs.map g') :=
  seqL_of g' cs vs ((mem_seqL g cs vs h).imp fun {c v} hv => hg c v hv)

theorem mem_cellVals {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : (c.1, c.2.1) ∈ cs := by
  induction cs generalizing vs with
  | nil => simp [cellVals] at h
  | cons d cs ih =>
    cases vs with
    | nil => simp [cellVals] at h
    | cons v vs =>
      simp only [cellVals, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem mem_cellVals_pick {dom : List Nat} {cs : List (Nat × Nat)} {vs : List Nat}
    (hvs : List.Forall₂ (fun c v => v ∈ pick dom c.2) cs vs) {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : (c.1, c.2.1) ∈ cs ∧ c.2.2 < 2 ^ (8 * c.2.1) := by
  induction hvs with
  | nil => simp [cellVals] at h
  | cons hv _ ih =>
    simp only [cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, mem_pick hv⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-! ## Sequencing -/

theorem bind_iff {x : Res} {k : Regs → Res} {tr : List Lab} {rs' : Regs} :
    (tr, rs') ∈ Res.bind x k ↔ ∃ p ∈ x, ∃ q ∈ k p.2, tr = p.1 ++ q.1 ∧ rs' = q.2 := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map, Prod.ext_iff]
  constructor
  · rintro ⟨p, hp, q, hq, h1, h2⟩; exact ⟨p, hp, q, hq, h1.symm, h2.symm⟩
  · rintro ⟨p, hp, q, hq, h1, h2⟩; exact ⟨p, hp, q, hq, h1.symm, h2.symm⟩

theorem bind_mem {x : Res} {k : Regs → Res} {p : List Lab × Regs} (h : p ∈ Res.bind x k) :
    ∃ a ∈ x, ∃ b ∈ k a.2, p = (a.1 ++ b.1, b.2) := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_bind {x : Res} {k : Regs → Res} {a b : List Lab × Regs} (ha : a ∈ x)
    (hb : b ∈ k a.2) : (a.1 ++ b.1, b.2) ∈ Res.bind x k := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

/-- **Runs of a concatenation.** -/
theorem run_chain_append (dom : List Nat) : ∀ (l₁ l₂ : List Stmt) (rs : Regs) (tr : List Lab)
    (rs' : Regs), (tr, rs') ∈ run dom (chain (l₁ ++ l₂)) rs ↔
      ∃ tr₁ rs₁ tr₂, (tr₁, rs₁) ∈ run dom (chain l₁) rs ∧ (tr₂, rs') ∈ run dom (chain l₂) rs₁ ∧
        tr = tr₁ ++ tr₂
  | [], l₂, rs, tr, rs' => by
    simp only [List.nil_append, chain, run, List.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨[], rs, tr, ⟨rfl, rfl⟩, h, rfl⟩
    · rintro ⟨tr₁, rs₁, tr₂, ⟨rfl, rfl⟩, h, rfl⟩; exact h
  | s :: l₁, l₂, rs, tr, rs' => by
    simp only [List.cons_append, chain, run, bind_iff]
    constructor
    · rintro ⟨p, hp, q, hq, rfl, rfl⟩
      obtain ⟨tr₁, rs₁, tr₂, h1, h2, h3⟩ := (run_chain_append dom l₁ l₂ p.2 q.1 q.2).mp hq
      exact ⟨p.1 ++ tr₁, rs₁, tr₂, ⟨p, hp, (tr₁, rs₁), h1, rfl, rfl⟩, h2, by simp [h3]⟩
    · rintro ⟨tr₁, rs₁, tr₂, ⟨p, hp, q, hq, rfl, rfl⟩, h2, rfl⟩
      refine ⟨p, hp, (q.1 ++ tr₂, rs'), ?_, by simp, rfl⟩
      exact (run_chain_append dom l₁ l₂ p.2 _ rs').mpr ⟨q.1, q.2, tr₂, hq, h2, rfl⟩

/-! ## Monotonicity in the domain -/

theorem iter_mono {body body' : Regs → Res} {c : Expr} (hb : ∀ rs p, p ∈ body rs → p ∈ body' rs) :
    ∀ n rs p, p ∈ iter body c n rs → p ∈ iter body' c n rs
  | 0, rs, p, h => by simpa only [iter] using h
  | n + 1, rs, p, h => by
    simp only [iter] at h ⊢
    split at h
    · rename_i ht
      simp only [ht, ite_true]
      obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      exact mem_bind (hb rs a ha) (iter_mono hb n a.2 b hb')
    · rename_i ht
      simp only [ht]
      exact h

/-- **Runs are monotone in the domain.** -/
theorem run_mono {dom dom' : List Nat} (hd : ∀ v ∈ dom, v ∈ dom') :
    ∀ (s : Stmt) rs p, p ∈ run dom s rs → p ∈ run dom' s rs
  | .skip, _, _, h => h
  | .assign .., _, _, h => h
  | .load d md sz fl a, rs, p, h => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨v, pick_mono hd hv, rfl⟩
  | .store .., _, _, h => h
  | .rmw d md sz op a arg, rs, p, h => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨v, pick_mono hd hv, rfl⟩
  | .fence _, _, _, h => h
  | .futexWait d a v, rs, p, h => by
    simp only [run, List.mem_flatMap] at h ⊢
    obtain ⟨w, hw, h⟩ := h
    refine ⟨w, pick_mono hd hw, ?_⟩
    split at h
    · rename_i he
      simp only [he, ite_true, List.mem_map] at h ⊢
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨r, qpick_mono hd hr, rfl⟩
    · rename_i he
      simp only [he, ite_false]
      exact h
  | .futexWake a n, rs, p, h => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨q, hq, rfl⟩ := h
    exact ⟨q, qpick_mono hd hq, rfl⟩
  | .spawn _, _, _, h => h
  | .join _, _, _, h => h
  | .local b, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h ⊢
    obtain ⟨ivs, hivs, rvs, hrvs, ovs, hovs, h⟩ := h
    exact ⟨ivs, seqL_mono (fun _ _ hv => pick_mono hd hv) _ _ hivs, rvs,
      seqL_mono (fun _ _ hv => hd _ hv) _ _ hrvs, ovs,
      seqL_mono (fun _ _ hv => pick_mono hd hv) _ _ hovs, h⟩
  | .seq s t, rs, p, h => by
    simp only [run] at h ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    exact mem_bind (run_mono hd s rs a ha) (run_mono hd t a.2 b hb)
  | .ite c s t, rs, p, h => by
    simp only [run] at h ⊢
    split at h
    · rename_i ht; simp only [ht, ite_true]; exact run_mono hd s rs p h
    · rename_i ht; simp only [ht]; exact run_mono hd t rs p h
  | .loop n c body, rs, p, h => by
    simp only [run] at h ⊢
    exact iter_mono (fun rs p h => run_mono hd body rs p h) n rs p h

/-! ## Registers -/

theorem setMany_other (r : Reg) : ∀ (rs : Regs) (l : List Reg) (vs : List Nat), r ∉ l →
    rs.setMany l vs r = rs r
  | rs, [], vs, _ => by cases vs <;> rfl
  | rs, _ :: _, [], _ => rfl
  | rs, q :: l, v :: vs, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [Regs.setMany]
    rw [setMany_other r _ l vs h.2]
    simp [Regs.set, h.1]

theorem iter_frame {W : List Reg} {body : Regs → Res} {c : Expr}
    (hb : ∀ rs p, p ∈ body rs → ∀ r, r ∉ W → p.2 r = rs r) :
    ∀ n rs p, p ∈ iter body c n rs → ∀ r, r ∉ W → p.2 r = rs r
  | 0, rs, p, h => by
    simp only [iter] at h
    split at h
    · simp at h
    · simp only [List.mem_singleton] at h; subst h; simp
  | n + 1, rs, p, h => by
    simp only [iter] at h
    split at h
    · obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      intro r hr
      rw [iter_frame hb n a.2 b hb' r hr, hb rs a ha r hr]
    · simp only [List.mem_singleton] at h; subst h; simp

/-- **A run changes only the registers the statement writes.** -/
theorem run_frame (dom : List Nat) : ∀ (s : Stmt) rs p, p ∈ run dom s rs →
    ∀ r, r ∉ s.writes → p.2 r = rs r
  | .skip, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, rs, p, h => by
    simp [run] at h; subst h; intro r hr; simp [Stmt.writes] at hr; simp [Regs.set, hr]
  | .load d md sz fl a, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    intro r hr; simp [Stmt.writes] at hr; simp [Regs.set, hr]
  | .store .., rs, p, h => by simp [run] at h; subst h; simp
  | .rmw d md sz op a arg, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    intro r hr; simp [Stmt.writes] at hr; simp [Regs.set, hr]
  | .fence _, rs, p, h => by simp [run] at h; subst h; simp
  | .futexWait d a v, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, -, h⟩ := h
    intro r hr
    simp only [Stmt.writes, List.mem_singleton] at hr
    split at h
    · simp only [List.mem_map] at h
      obtain ⟨_, -, rfl⟩ := h
      simp [Regs.set, hr]
    · simp only [List.mem_singleton] at h; subst h; simp [Regs.set, hr]
  | .futexWake a n, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨_, -, rfl⟩ := h; simp
  | .spawn _, rs, p, h => by simp [run] at h; subst h; simp
  | .join _, rs, p, h => by simp [run] at h; subst h; simp
  | .local b, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, -, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h
      intro r hr
      exact setMany_other r rs b.rout rvs (by simpa [Stmt.writes] using hr)
    · cases h
  | .seq s t, rs, p, h => by
    simp only [run] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    intro r hr
    simp only [Stmt.writes, List.mem_append, not_or] at hr
    rw [run_frame dom t a.2 b hb r hr.2, run_frame dom s rs a ha r hr.1]
  | .ite c s t, rs, p, h => by
    simp only [run] at h
    intro r hr
    simp only [Stmt.writes, List.mem_append, not_or] at hr
    split at h
    · exact run_frame dom s rs p h r hr.1
    · exact run_frame dom t rs p h r hr.2
  | .loop n c body, rs, p, h => by
    simp only [run] at h
    exact iter_frame (fun rs p h => run_frame dom body rs p h) n rs p h

/-! ## Labels of the fragment -/

/-- A label of an owned fragment over the cells `cs` that writes only `outs`. -/
def FragLab (cs outs : List (Nat × Nat)) : Lab → Prop
  | .rd _ fl a sz v => fl = .wb ∧ (a, sz) ∈ cs ∧ v < 2 ^ (8 * sz)
  | .wr _ fl a sz _ => fl = .wb ∧ (a, sz) ∈ cs ∧ (a, sz) ∈ outs
  | .rmw _ a sz o _ => (a, sz) ∈ cs ∧ (a, sz) ∈ outs ∧ o < 2 ^ (8 * sz)
  | .fence _ => True
  | .blk _ ins os _ => (∀ c ∈ ins, (c.1, c.2.1) ∈ cs ∧ c.2.2 < 2 ^ (8 * c.2.1)) ∧
      ∀ c ∈ os, (c.1, c.2.1) ∈ cs ∧ (c.1, c.2.1) ∈ outs
  | _ => False

theorem iter_all {P : Lab → Prop} {body : Regs → Res} {c : Expr}
    (hb : ∀ rs p, p ∈ body rs → ∀ l ∈ p.1, P l) :
    ∀ n rs p, p ∈ iter body c n rs → ∀ l ∈ p.1, P l
  | 0, rs, p, h => by
    simp only [iter] at h
    split at h
    · simp at h
    · simp only [List.mem_singleton] at h; subst h; simp
  | n + 1, rs, p, h => by
    simp only [iter] at h
    split at h
    · obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hb rs a ha l hl
      · exact iter_all hb n a.2 b hb' l hl
    · simp only [List.mem_singleton] at h; subst h; simp

theorem lit_addr {cs : List (Nat × Nat)} {rs : Regs} (hcs : ∀ c ∈ cs, c.1 < 2 ^ 64) {a sz : Nat}
    (h : (a, sz) ∈ cs) : ((Expr.lit a).eval rs).toNat = a := by
  have := hcs _ h
  simp only [Expr.eval, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt this

/-- **Labels of an owned fragment.** -/
theorem run_frag (dom : List Nat) (cs outs : List (Nat × Nat)) (hcs : ∀ c ∈ cs, c.1 < 2 ^ 64) :
    ∀ (s : Stmt), s.onCells cs = true → s.storesWithin outs = true → s.threadFree = true →
      s.futexFree = true → ∀ rs p, p ∈ run dom s rs → ∀ l ∈ p.1, FragLab cs outs l
  | .skip, _, _, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, _, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, hc, _, _, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      simp only [List.mem_singleton, forall_eq, FragLab, lit_addr hcs hc.2]
      exact ⟨hc.1, hc.2, mem_pick hv⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .store md sz fl a v, hc, hw, _, _, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
      simp only [Stmt.storesWithin, List.contains_iff_mem] at hw
      simp only [List.mem_singleton, forall_eq, FragLab, lit_addr hcs hc.2]
      exact ⟨hc.1, hc.2, hw⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .rmw d md sz op a arg, hc, hw, _, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, List.contains_iff_mem] at hc
      simp only [Stmt.storesWithin, List.contains_iff_mem] at hw
      simp only [List.mem_singleton, forall_eq, FragLab, lit_addr hcs hc]
      exact ⟨hc, hw, mem_pick hv⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .fence k, _, _, _, _, rs, p, h => by simp [run] at h; subst h; simp [FragLab]
  | .futexWait .., _, _, _, hf, _, _, _ => by simp [Stmt.futexFree] at hf
  | .futexWake .., _, _, _, hf, _, _, _ => by simp [Stmt.futexFree] at hf
  | .spawn _, _, _, ht, _, _, _, _ => by simp [Stmt.threadFree] at ht
  | .join _, _, _, ht, _, _, _, _ => by simp [Stmt.threadFree] at ht
  | .local b, hc, hw, _, _, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, hivs, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h
      have hi := mem_seqL _ _ _ hivs
      simp only [Stmt.onCells, List.all_eq_true, List.contains_iff_mem, List.mem_append] at hc
      simp only [Stmt.storesWithin, List.all_eq_true, List.contains_iff_mem] at hw
      simp only [List.mem_singleton, forall_eq, FragLab]
      refine ⟨fun c hc' => ?_, fun c hc' => ?_⟩
      · obtain ⟨h1, h2⟩ := mem_cellVals_pick hi hc'
        exact ⟨hc _ (.inl h1), h2⟩
      · have := mem_cellVals hc'
        exact ⟨hc _ (.inr this), hw _ this⟩
    · cases h
  | .seq s t, hc, hw, ht, hf, rs, p, h => by
    simp only [Stmt.onCells, Stmt.storesWithin, Stmt.threadFree, Stmt.futexFree,
      Bool.and_eq_true] at hc hw ht hf
    simp only [run] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact run_frag dom cs outs hcs s hc.1 hw.1 ht.1 hf.1 rs a ha l hl
    · exact run_frag dom cs outs hcs t hc.2 hw.2 ht.2 hf.2 a.2 b hb l hl
  | .ite c s t, hc, hw, ht, hf, rs, p, h => by
    simp only [Stmt.onCells, Stmt.storesWithin, Stmt.threadFree, Stmt.futexFree,
      Bool.and_eq_true] at hc hw ht hf
    simp only [run] at h
    split at h
    · exact run_frag dom cs outs hcs s hc.1 hw.1 ht.1 hf.1 rs p h
    · exact run_frag dom cs outs hcs t hc.2 hw.2 ht.2 hf.2 rs p h
  | .loop n c body, hc, hw, ht, hf, rs, p, h => by
    simp only [Stmt.onCells, Stmt.storesWithin, Stmt.threadFree, Stmt.futexFree] at hc hw ht hf
    simp only [run] at h
    exact iter_all (fun rs p h => run_frag dom cs outs hcs body hc hw ht hf rs p h) n rs p h

/-! ## Actions that avoid the cells -/

/-- The bytes of an action are disjoint from every cell of `cs` (a fence touches no byte). -/
def ActAvoid (cs : List (Nat × Nat)) (a : XAct) : Prop :=
  ∀ c ∈ cs, a.ev.addr + a.ev.size ≤ c.1 ∨ c.1 + c.2 ≤ a.ev.addr

theorem avoid_fence (cs : List (Nat × Nat)) (k) : ActAvoid cs (fenceAct k) := by
  intro c _; left; simp [fenceAct]

theorem avoid_ghost {cs : List (Nat × Nat)} (hcs : ∀ c ∈ cs, c.1 + c.2 ≤ ctlAddr 0) {a : XAct}
    (h : ctlAddr 0 ≤ a.ev.addr) : ActAvoid cs a := fun c hc => .inr ((hcs c hc).trans h)

theorem ctl_le_q (a : Nat) : ctlAddr 0 ≤ qAddr a := by simp [ctlAddr, qAddr]; omega
theorem ctl_le_ctl (t : Nat) : ctlAddr 0 ≤ ctlAddr t := by simp [ctlAddr]
theorem ctl_le_end (t : Nat) : ctlAddr 0 ≤ endAddr t := by simp [endAddr, ctlAddr]; omega

/-- **Actions of a statement that avoids the cells.** -/
theorem run_avoid (dom : List Nat) (cs : List (Nat × Nat))
    (hcs : ∀ c ∈ cs, c.1 + c.2 ≤ ctlAddr 0) :
    ∀ (s : Stmt), s.avoids cs = true → ∀ rs p, p ∈ run dom s rs →
      ∀ l ∈ p.1, ∀ a ∈ l.acts, ActAvoid cs a
  | .skip, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, hc, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.avoids] at hc
      simp only [List.mem_singleton, forall_eq, Lab.acts, ldAct]
      intro c hc'
      have := List.all_eq_true.mp hc c hc'
      simpa [Tv.cellsDisjoint, Expr.eval] using this
    | reg _ => simp [Stmt.avoids] at hc
    | bin _ _ _ => simp [Stmt.avoids] at hc
  | .store md sz fl a v, hc, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    cases a with
    | lit a =>
      simp only [Stmt.avoids] at hc
      simp only [List.mem_singleton, forall_eq, Lab.acts, stAct]
      intro c hc'
      have := List.all_eq_true.mp hc c hc'
      simpa [Tv.cellsDisjoint, Expr.eval] using this
    | reg _ => simp [Stmt.avoids] at hc
    | bin _ _ _ => simp [Stmt.avoids] at hc
  | .rmw d md sz op a arg, hc, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, -, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.avoids] at hc
      simp only [List.mem_singleton, forall_eq, Lab.acts, rmwAct]
      intro c hc'
      have := List.all_eq_true.mp hc c hc'
      simpa [Tv.cellsDisjoint, Expr.eval] using this
    | reg _ => simp [Stmt.avoids] at hc
    | bin _ _ _ => simp [Stmt.avoids] at hc
  | .fence k, _, rs, p, h => by
    simp [run] at h; subst h
    simp only [List.mem_singleton, forall_eq, Lab.acts]
    exact avoid_fence cs k
  | .futexWait d a v, hc, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, -, h⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.avoids] at hc
      have hw : ActAvoid cs (ldAct .wb (a % 2 ^ 64) 4 w) := by
        intro c hc'
        have := List.all_eq_true.mp hc c hc'
        simpa [Tv.cellsDisjoint, ldAct] using this
      split at h
      · simp only [List.mem_map] at h
        obtain ⟨r, -, rfl⟩ := h
        simp only [List.mem_singleton, forall_eq, Lab.acts, Expr.eval, BitVec.toNat_ofNat]
        rename_i he
        simp only [he, ite_true, List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl)
        · exact avoid_fence cs _
        · exact avoid_ghost hcs (by simpa [stAct] using ctl_le_q _)
        · exact avoid_fence cs _
        · exact he ▸ hw
        · exact avoid_ghost hcs (by simpa [rmwAct] using ctl_le_q _)
      · simp only [List.mem_singleton] at h; subst h
        rename_i he
        simp only [forall_eq, Lab.acts, Expr.eval, BitVec.toNat_ofNat, he,
          ite_false, List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · exact avoid_fence cs _
        · exact hw
        · exact avoid_fence cs _
    | reg _ => simp [Stmt.avoids] at hc
    | bin _ _ _ => simp [Stmt.avoids] at hc
  | .futexWake a n, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨q, -, rfl⟩ := h
    simp only [forall_eq, Lab.acts, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · exact avoid_fence cs _
    · exact avoid_ghost hcs (by simpa [rmwAct] using ctl_le_q _)
    · exact avoid_fence cs _
  | .spawn t, _, rs, p, h => by
    simp [run] at h; subst h
    simp only [List.mem_singleton, forall_eq, Lab.acts]
    exact avoid_ghost hcs (by simpa [ctlAct, rmwAct] using ctl_le_ctl t)
  | .join t, _, rs, p, h => by
    simp [run] at h; subst h
    simp only [List.mem_singleton, forall_eq, Lab.acts]
    exact avoid_ghost hcs (by simpa [endAct, rmwAct] using ctl_le_end t)
  | .local b, hc, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, -, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h
      simp only [Stmt.avoids, List.all_eq_true, List.mem_append] at hc
      simp only [List.mem_singleton, forall_eq, Lab.acts, List.mem_append, List.mem_map]
      rintro x (⟨c, hc', rfl⟩ | ⟨c, hc', rfl⟩)
      · intro d hd
        have := hc _ (.inl (mem_cellVals hc')) d hd
        simpa [Tv.cellsDisjoint, ldAct] using this
      · intro d hd
        have := hc _ (.inr (mem_cellVals hc')) d hd
        simpa [Tv.cellsDisjoint, stAct] using this
    · cases h
  | .seq s t, hc, rs, p, h => by
    simp only [Stmt.avoids, Bool.and_eq_true] at hc
    simp only [run] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact run_avoid dom cs hcs s hc.1 rs a ha l hl
    · exact run_avoid dom cs hcs t hc.2 a.2 b hb l hl
  | .ite c s t, hc, rs, p, h => by
    simp only [Stmt.avoids, Bool.and_eq_true] at hc
    simp only [run] at h
    split at h
    · exact run_avoid dom cs hcs s hc.1 rs p h
    · exact run_avoid dom cs hcs t hc.2 rs p h
  | .loop n c body, hc, rs, p, h => by
    simp only [Stmt.avoids] at hc
    simp only [run] at h
    exact iter_all (P := fun l => ∀ a ∈ l.acts, ActAvoid cs a)
      (fun rs p h => run_avoid dom cs hcs body hc rs p h) n rs p h

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
