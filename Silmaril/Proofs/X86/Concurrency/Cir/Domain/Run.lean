module

public import Silmaril.X86.Concurrency.Cir.Defs

/-!
# Domain closure on CIR: runs over a smaller domain

Proofs for `Silmaril/X86/Concurrency/Cir/Domain/Thms.lean`.

* `labs_ok`: every label of a run of a statement whose accesses are cells of `cs` accesses a
  cell of `cs` with a value that fits, and a block label satisfies the contract of one of the
  statement's blocks;
* `labs_futex`: a futex-free statement has no futex label;
* `run_restrict`: a run over `D` whose chosen values (read values, futex queue values, block
  outputs) lie in `dom` is a run over `dom`;
* `pre_of_run`: a prefix of a run over `D` whose chosen values lie in `dom` is a partial run
  over `dom` (`preRuns`).

`mem_pick`, `mem_qpick`, `mem_seqL`, `mem_cellVals` are **copied** from
`Silmaril/Proofs/X86/Concurrency/Cir/Seq/Lab.lean`, whose header does not export
them.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Domain

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (seqL)

/-! ## Copied list lemmas -/

theorem mem_pick {dom : List Nat} {sz v : Nat} (h : v ∈ pick dom sz) : v < 2 ^ (8 * sz) := by
  simp only [pick, List.mem_filter, decide_eq_true_eq] at h; exact h.2

theorem mem_pick_dom {dom : List Nat} {sz v : Nat} (h : v ∈ pick dom sz) : v ∈ dom := by
  simp only [pick, List.mem_filter] at h; exact h.1

theorem pick_of {dom : List Nat} {sz v : Nat} (h : v ∈ dom) (hv : v < 2 ^ (8 * sz)) :
    v ∈ pick dom sz := by
  simp only [pick, List.mem_filter, decide_eq_true_eq]; exact ⟨h, hv⟩

theorem mem_qpick {dom : List Nat} {v : Nat} (h : v ∈ qpick dom) : v < 2 := by
  simp only [qpick, List.mem_filter, decide_eq_true_eq] at h; exact h.2

theorem mem_qpick_dom {dom : List Nat} {v : Nat} (h : v ∈ qpick dom) : v ∈ dom := by
  simp only [qpick, List.mem_filter] at h; exact mem_pick_dom h.1

theorem qpick_of {dom : List Nat} {v : Nat} (h : v ∈ dom) (hv : v < 2) : v ∈ qpick dom := by
  simp only [qpick, List.mem_filter, decide_eq_true_eq]
  exact ⟨pick_of h (by omega), hv⟩

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

theorem cellVals_vals : ∀ (cs : List (Nat × Nat)) (vs : List Nat), cs.length = vs.length →
    (cellVals cs vs).map (·.2.2) = vs
  | [], [], _ => rfl
  | _ :: cs, _ :: vs, h => by
    simp only [cellVals, List.map_cons, List.cons.injEq, true_and]
    exact cellVals_vals cs vs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem cellVals_cells : ∀ (cs : List (Nat × Nat)) (vs : List Nat), cs.length = vs.length →
    (cellVals cs vs).map (fun c => (c.1, c.2.1)) = cs
  | [], [], _ => rfl
  | _ :: cs, _ :: vs, h => by
    simp only [cellVals, List.map_cons, List.cons.injEq, true_and]
    exact cellVals_cells cs vs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

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

theorem forall2_length {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : l.length = l'.length := h.length_eq

theorem forall2_mono_right {α β : Type} {R S : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (hS : ∀ a b, R a b → b ∈ l' → S a b) : List.Forall₂ S l l' := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih =>
    exact .cons (hS _ _ hr List.mem_cons_self)
      (ih fun a b h hb => hS a b h (List.mem_cons_of_mem _ hb))

/-! ## Labels -/

/-- The values a label chose from its domain: read values, futex queue values, block inputs,
outputs and output registers. -/
def Chosen (dom : List Nat) : Lab → Prop
  | .rd _ _ _ _ v => v ∈ dom
  | .rmw _ _ _ o _ => o ∈ dom
  | .fwait _ e seen r => seen ∈ dom ∧ (seen = e → r ∈ dom)
  | .fwake _ _ q => q ∈ dom
  | .blk _ ins outs rvs =>
    (∀ c ∈ ins, c.2.2 ∈ dom) ∧ (∀ c ∈ outs, c.2.2 ∈ dom) ∧ ∀ v ∈ rvs, v ∈ dom
  | _ => True

/-- A label of a run whose accesses are cells of `cs`, with blocks among `bs`. -/
def LabOk (cs : List (Nat × Nat)) (bs : List Block) : Lab → Prop
  | .rd _ _ a sz v => (a, sz) ∈ cs ∧ v < 2 ^ (8 * sz)
  | .wr _ _ a sz v => (a, sz) ∈ cs ∧ v < 2 ^ (8 * sz)
  | .rmw _ a sz o n => (a, sz) ∈ cs ∧ o < 2 ^ (8 * sz) ∧ n < 2 ^ (8 * sz)
  | .fwait a e seen r => (a, 4) ∈ cs ∧ seen < 2 ^ (8 * 4) ∧ r < 2 ∧ (seen ≠ e → r = 0)
  | .fwake _ _ q => q < 2
  | .fblock _ _ => False
  | .blk _ ins outs rvs =>
    (∀ c ∈ ins ++ outs, (c.1, c.2.1) ∈ cs ∧ c.2.2 < 2 ^ (8 * c.2.1)) ∧
      ∃ b ∈ bs, ∃ rv : List Nat, rv.length = b.rin.length ∧
        b.spec (rv ++ ins.map (·.2.2)) (rvs ++ outs.map (·.2.2))
  | _ => True

theorem labOk_mono {cs : List (Nat × Nat)} {bs bs' : List Block} (h : ∀ b ∈ bs, b ∈ bs')
    {l : Lab} (hl : LabOk cs bs l) : LabOk cs bs' l := by
  cases l <;> simp only [LabOk] at hl ⊢ <;> try exact hl
  obtain ⟨h1, b, hb, rv, h2, h3⟩ := hl
  exact ⟨h1, b, h b hb, rv, h2, h3⟩

/-- A futex label. -/
def labFutex : Lab → Bool
  | .fwait .. | .fwake .. | .fblock .. => true
  | _ => false

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
    · simp only [Res.bind, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, b, hb', rfl⟩ := h
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

/-- **Labels of runs of uniform statements.** -/
theorem labs_ok (D : List Nat) (cs : List (Nat × Nat)) (hcs : ∀ c ∈ cs, c.1 < 2 ^ 64) :
    ∀ (s : Stmt), s.onCells cs = true → ∀ rs p, p ∈ run D s rs → ∀ l ∈ p.1, LabOk cs s.blocks l
  | .skip, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, hc, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, Bool.and_eq_true, List.contains_iff_mem] at hc
      simp only [List.mem_singleton, forall_eq, LabOk, lit_addr hcs hc.2]
      exact ⟨hc.2, mem_pick hv⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .store md sz fl a v, hc, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, Bool.and_eq_true, List.contains_iff_mem] at hc
      simp only [List.mem_singleton, forall_eq, LabOk, lit_addr hcs hc.2]
      exact ⟨hc.2, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .rmw d md sz op a arg, hc, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, List.contains_iff_mem] at hc
      simp only [List.mem_singleton, forall_eq, LabOk, lit_addr hcs hc]
      refine ⟨hc, mem_pick hv, ?_⟩
      cases op <;> simp only [RmwOp.result] <;> try exact Nat.mod_lt _ (Nat.two_pow_pos _)
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact mem_pick hv
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .fence k, _, rs, p, h => by simp [run] at h; subst h; simp [LabOk]
  | .futexWait d a v, hc, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, hw, h⟩ := h
    cases a with
    | lit a =>
      simp only [Stmt.onCells, List.contains_iff_mem] at hc
      split at h
      · simp only [List.mem_map] at h
        obtain ⟨r, hr, rfl⟩ := h
        simp only [List.mem_singleton, forall_eq, LabOk, lit_addr hcs hc]
        exact ⟨hc, mem_pick hw, mem_qpick hr, fun h' => absurd ‹_› h'⟩
      · simp only [List.mem_singleton] at h; subst h
        simp only [List.mem_singleton, forall_eq, LabOk, lit_addr hcs hc]
        exact ⟨hc, mem_pick hw, by omega, by simp⟩
    | reg _ => simp [Stmt.onCells] at hc
    | bin _ _ _ => simp [Stmt.onCells] at hc
  | .futexWake a n, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    simp only [List.mem_singleton, forall_eq, LabOk]
    exact mem_qpick hq
  | .spawn t, _, rs, p, h => by simp [run] at h; subst h; simp [LabOk]
  | .join t, _, rs, p, h => by simp [run] at h; subst h; simp [LabOk]
  | .local b, hc, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, hivs, rvs, -, ovs, hovs, h⟩ := h
    split at h
    · rename_i hspec
      cases h
      have hi := mem_seqL _ _ _ hivs
      have ho := mem_seqL _ _ _ hovs
      simp only [Stmt.onCells, List.all_eq_true, List.contains_iff_mem] at hc
      simp only [List.mem_singleton, forall_eq, LabOk, Stmt.blocks]
      refine ⟨fun c hcm => ?_, b, rfl, b.rin.map fun r => (rs r).toNat, List.length_map _, ?_⟩
      · rcases List.mem_append.mp hcm with hcm | hcm
        · obtain ⟨h1, h2⟩ := mem_cellVals_pick hi hcm
          exact ⟨hc _ (List.mem_append_left _ h1), h2⟩
        · obtain ⟨h1, h2⟩ := mem_cellVals_pick ho hcm
          exact ⟨hc _ (List.mem_append_right _ h1), h2⟩
      · rw [cellVals_vals _ _ (forall2_length hi), cellVals_vals _ _ (forall2_length ho)]
        exact @of_decide_eq_true _ (b.dec _ _) hspec
    · cases h
  | .seq s t, hc, rs, p, h => by
    simp only [Stmt.onCells, Bool.and_eq_true] at hc
    simp only [run, Res.bind, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact labOk_mono (fun _ h => List.mem_append_left _ h)
        (labs_ok D cs hcs s hc.1 rs a ha l hl)
    · exact labOk_mono (fun _ h => List.mem_append_right _ h)
        (labs_ok D cs hcs t hc.2 a.2 b hb l hl)
  | .ite c s t, hc, rs, p, h => by
    simp only [Stmt.onCells, Bool.and_eq_true] at hc
    simp only [run] at h
    split at h
    · exact fun l hl => labOk_mono (fun _ h => List.mem_append_left _ h)
        (labs_ok D cs hcs s hc.1 rs p h l hl)
    · exact fun l hl => labOk_mono (fun _ h => List.mem_append_right _ h)
        (labs_ok D cs hcs t hc.2 rs p h l hl)
  | .loop n c body, hc, rs, p, h => by
    simp only [Stmt.onCells] at hc
    exact iter_all (fun rs p h => labs_ok D cs hcs body hc rs p h) n rs p h

/-- **A futex-free statement has no futex label.** -/
theorem labs_futex (D : List Nat) : ∀ (s : Stmt), s.futexFree = true → ∀ rs p,
    p ∈ run D s rs → ∀ l ∈ p.1, labFutex l = false
  | .skip, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp [labFutex]
  | .store md sz fl a v, _, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h; simp [labFutex]
  | .rmw d md sz op a arg, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp [labFutex]
  | .fence k, _, rs, p, h => by simp [run] at h; subst h; simp [labFutex]
  | .futexWait d a v, hf, _, _, _ => by simp [Stmt.futexFree] at hf
  | .futexWake a n, hf, _, _, _ => by simp [Stmt.futexFree] at hf
  | .spawn t, _, rs, p, h => by simp [run] at h; subst h; simp [labFutex]
  | .join t, _, rs, p, h => by simp [run] at h; subst h; simp [labFutex]
  | .local b, _, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, -, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h; simp [labFutex]
    · cases h
  | .seq s t, hf, rs, p, h => by
    simp only [Stmt.futexFree, Bool.and_eq_true] at hf
    simp only [run, Res.bind, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact labs_futex D s hf.1 rs a ha l hl
    · exact labs_futex D t hf.2 a.2 b hb l hl
  | .ite c s t, hf, rs, p, h => by
    simp only [Stmt.futexFree, Bool.and_eq_true] at hf
    simp only [run] at h
    split at h
    · exact labs_futex D s hf.1 rs p h
    · exact labs_futex D t hf.2 rs p h
  | .loop n c body, hf, rs, p, h => by
    simp only [Stmt.futexFree] at hf
    exact iter_all (fun rs p h => labs_futex D body hf rs p h) n rs p h

/-! ## Restriction to a smaller domain -/

theorem bind_mem {x : Res} {k : Regs → Res} {p : List Lab × Regs} (h : p ∈ Res.bind x k) :
    ∃ a ∈ x, ∃ b ∈ k a.2, p = (a.1 ++ b.1, b.2) := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_bind {x : Res} {k : Regs → Res} {a b : List Lab × Regs} (ha : a ∈ x) (hb : b ∈ k a.2) :
    (a.1 ++ b.1, b.2) ∈ Res.bind x k := by
  simp only [Res.bind, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

theorem iter_restrict {dom : List Nat} {bodyD body : Regs → Res} {c : Expr}
    (hb : ∀ rs p, p ∈ bodyD rs → (∀ l ∈ p.1, Chosen dom l) → p ∈ body rs) :
    ∀ n rs p, p ∈ iter bodyD c n rs → (∀ l ∈ p.1, Chosen dom l) → p ∈ iter body c n rs
  | 0, rs, p, h, _ => by simpa only [iter] using h
  | n + 1, rs, p, h, hc => by
    simp only [iter] at h ⊢
    split at h
    · rename_i ht
      simp only [ht, ite_true]
      obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      exact mem_bind (hb rs a ha fun l hl => hc l (List.mem_append_left _ hl))
        (iter_restrict hb n a.2 b hb' fun l hl => hc l (List.mem_append_right _ hl))
    · rename_i ht
      simp only [ht]
      exact h

/-- **A run over `D` whose choices lie in `dom` is a run over `dom`.** -/
theorem run_restrict (D dom : List Nat) : ∀ (s : Stmt) rs p, p ∈ run D s rs →
    (∀ l ∈ p.1, Chosen dom l) → p ∈ run dom s rs
  | .skip, rs, p, h, _ => h
  | .assign d e, rs, p, h, _ => h
  | .load d md sz fl a, rs, p, h, hc => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    simp only [List.mem_singleton, forall_eq, Chosen] at hc
    exact ⟨v, pick_of hc (mem_pick hv), rfl⟩
  | .store md sz fl a v, rs, p, h, _ => h
  | .rmw d md sz op a arg, rs, p, h, hc => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    simp only [List.mem_singleton, forall_eq, Chosen] at hc
    exact ⟨v, pick_of hc (mem_pick hv), rfl⟩
  | .fence k, rs, p, h, _ => h
  | .futexWait d a v, rs, p, h, hc => by
    simp only [run, List.mem_flatMap] at h ⊢
    obtain ⟨w, hw, h⟩ := h
    split at h
    · rename_i he
      simp only [List.mem_map] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [List.mem_singleton, forall_eq, Chosen] at hc
      refine ⟨w, pick_of hc.1 (mem_pick hw), ?_⟩
      simp only [he, ite_true, List.mem_map]
      exact ⟨r, qpick_of (hc.2 he) (mem_qpick hr), rfl⟩
    · rename_i he
      simp only [List.mem_singleton] at h; subst h
      simp only [List.mem_singleton, forall_eq, Chosen] at hc
      refine ⟨w, pick_of hc.1 (mem_pick hw), ?_⟩
      split
      · rename_i h'; exact absurd h' (by simpa using he)
      · exact List.mem_singleton_self _
  | .futexWake a n, rs, p, h, hc => by
    simp only [run, List.mem_map] at h ⊢
    obtain ⟨q, hq, rfl⟩ := h
    simp only [List.mem_singleton, forall_eq, Chosen] at hc
    exact ⟨q, qpick_of hc (mem_qpick hq), rfl⟩
  | .spawn t, rs, p, h, _ => h
  | .join t, rs, p, h, _ => h
  | .local b, rs, p, h, hc => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h ⊢
    obtain ⟨ivs, hivs, rvs, hrvs, ovs, hovs, h⟩ := h
    split at h
    · rename_i hspec
      cases h
      have hi := mem_seqL _ _ _ hivs
      have ho := mem_seqL _ _ _ hovs
      have hr := mem_seqL _ _ _ hrvs
      simp only [List.mem_singleton, forall_eq, Chosen] at hc
      obtain ⟨hc1, hc2, hc3⟩ := hc
      have hc1' : ∀ v ∈ ivs, v ∈ dom := by
        intro v hv
        rw [← cellVals_vals _ _ (forall2_length hi)] at hv
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hv
        exact hc1 c hcm
      have hc2' : ∀ v ∈ ovs, v ∈ dom := by
        intro v hv
        rw [← cellVals_vals _ _ (forall2_length ho)] at hv
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hv
        exact hc2 c hcm
      refine ⟨ivs, seqL_of _ _ _ (forall2_mono_right hi fun c v h hv => pick_of (hc1' v hv)
          (mem_pick h)), rvs, seqL_of _ _ _ (forall2_mono_right hr fun _ v _ hv => hc3 v hv),
        ovs, seqL_of _ _ _ (forall2_mono_right ho fun c v h hv => pick_of (hc2' v hv)
          (mem_pick h)), ?_⟩
      simp [hspec]
    · cases h
  | .seq s t, rs, p, h, hc => by
    simp only [run] at h ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    exact mem_bind (run_restrict D dom s rs a ha fun l hl => hc l (List.mem_append_left _ hl))
      (run_restrict D dom t a.2 b hb fun l hl => hc l (List.mem_append_right _ hl))
  | .ite c s t, rs, p, h, hc => by
    simp only [run] at h ⊢
    split at h
    · rename_i ht; simp only [ht, ite_true]; exact run_restrict D dom s rs p h hc
    · rename_i ht; simp only [ht]; exact run_restrict D dom t rs p h hc
  | .loop n c body, rs, p, h, hc => by
    simp only [run] at h ⊢
    exact iter_restrict (fun rs p h hc => run_restrict D dom body rs p h hc) n rs p h hc

/-! ## Prefixes are partial runs -/

theorem take_append_of_le {α : Type} {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  rw [List.take_append_of_le_length h]

theorem take_append_of_gt {α : Type} {l₁ l₂ : List α} {n : Nat} (h : l₁.length < n) :
    (l₁ ++ l₂).take n = l₁ ++ l₂.take (n - l₁.length) := by
  rw [List.take_append, List.take_of_length_le (by omega)]

theorem chosen_of_take {dom : List Nat} {l₁ l₂ : List Lab} {n : Nat} (h : l₁.length < n)
    (hc : ∀ l ∈ (l₁ ++ l₂).take n, Chosen dom l) : ∀ l ∈ l₁, Chosen dom l := by
  rw [take_append_of_gt h] at hc
  exact fun l hl => hc l (List.mem_append_left _ hl)

theorem chosen_of_take' {dom : List Nat} {l₁ l₂ : List Lab} {n : Nat} (h : l₁.length < n)
    (hc : ∀ l ∈ (l₁ ++ l₂).take n, Chosen dom l) :
    ∀ l ∈ l₂.take (n - l₁.length), Chosen dom l := by
  rw [take_append_of_gt h] at hc
  exact fun l hl => hc l (List.mem_append_right _ hl)

/-- An atomic statement: its partial runs are the empty trace and its runs. -/
theorem pre_atomic {dom D : List Nat} {s : Stmt} {rs : Regs} {p : List Lab × Regs}
    (hpre : preRuns dom s rs = [] :: (run dom s rs).map Prod.fst) (h : p ∈ run D s rs)
    (hlen : p.1.length ≤ 1) (n : Nat) (hc : ∀ l ∈ p.1.take n, Chosen dom l) :
    p.1.take n ∈ preRuns dom s rs := by
  rw [hpre]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [List.take_of_length_le (by omega)] at hc ⊢
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, run_restrict D dom s rs p h hc, rfl⟩)

theorem len_le_one_of_map {α : Type} {f : α → List Lab × Regs} {l : List α} {p : List Lab × Regs}
    (hf : ∀ a, (f a).1.length ≤ 1) (h : p ∈ l.map f) : p.1.length ≤ 1 := by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp h; exact hf a

theorem pre_iter {dom : List Nat} {bodyD body : Regs → Res} {pbody : Regs → List (List Lab)}
    {c : Expr}
    (hb : ∀ rs p, p ∈ bodyD rs → (∀ l ∈ p.1, Chosen dom l) → p ∈ body rs)
    (hp : ∀ rs p, p ∈ bodyD rs → ∀ n, (∀ l ∈ p.1.take n, Chosen dom l) → p.1.take n ∈ pbody rs) :
    ∀ k rs p, p ∈ iter bodyD c k rs → ∀ n, (∀ l ∈ p.1.take n, Chosen dom l) →
      p.1.take n ∈ preIter body pbody c k rs
  | 0, rs, p, h, n, _ => by
    simp only [iter] at h
    split at h
    · simp at h
    · simp only [List.mem_singleton] at h; subst h; simp [preIter]
  | k + 1, rs, p, h, n, hc => by
    simp only [iter] at h
    simp only [preIter]
    split at h
    · rename_i ht
      simp only [ht, ite_true]
      obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      by_cases hn : n ≤ a.1.length
      · simp only at hc ⊢
        rw [take_append_of_le hn] at hc ⊢
        exact List.mem_append_left _ (hp rs a ha n hc)
      · have hn' : a.1.length < n := by omega
        simp only at hc ⊢
        rw [take_append_of_gt hn']
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, hb rs a ha
          (chosen_of_take hn' hc), List.mem_map.mpr ⟨_, pre_iter hb hp k a.2 b hb' _
            (chosen_of_take' hn' hc), rfl⟩⟩)
    · rename_i ht
      simp only [ht]
      simp only [List.mem_singleton] at h; subst h; simp

/-- **A prefix of a run over `D` whose choices lie in `dom` is a partial run over `dom`.** -/
theorem pre_of_run (D dom : List Nat) : ∀ (s : Stmt) rs p, p ∈ run D s rs → ∀ n,
    (∀ l ∈ p.1.take n, Chosen dom l) → p.1.take n ∈ preRuns dom s rs
  | .skip, rs, p, h, n, hc => pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .assign d e, rs, p, h, n, hc => pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .load d md sz fl a, rs, p, h, n, hc =>
    pre_atomic rfl h (len_le_one_of_map (fun _ => by simp) h) n hc
  | .store md sz fl a v, rs, p, h, n, hc =>
    pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .rmw d md sz op a arg, rs, p, h, n, hc =>
    pre_atomic rfl h (len_le_one_of_map (fun _ => by simp) h) n hc
  | .fence k, rs, p, h, n, hc => pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .futexWait d a v, rs, p, h, n, hc => by
    refine pre_atomic rfl h ?_ n hc
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, -, h⟩ := h
    split at h
    · exact len_le_one_of_map (fun _ => by simp) h
    · simp only [List.mem_singleton] at h; subst h; simp
  | .futexWake a k, rs, p, h, n, hc =>
    pre_atomic rfl h (len_le_one_of_map (fun _ => by simp) h) n hc
  | .spawn t, rs, p, h, n, hc => pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .join t, rs, p, h, n, hc => pre_atomic rfl h (by simp [run] at h; subst h; simp) n hc
  | .local b, rs, p, h, n, hc => by
    refine pre_atomic rfl h ?_ n hc
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, -, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h; simp
    · cases h
  | .seq s t, rs, p, h, n, hc => by
    simp only [run] at h
    simp only [preRuns]
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    by_cases hn : n ≤ a.1.length
    · simp only at hc ⊢
      rw [take_append_of_le hn] at hc ⊢
      exact List.mem_append_left _ (pre_of_run D dom s rs a ha n hc)
    · have hn' : a.1.length < n := by omega
      simp only at hc ⊢
      rw [take_append_of_gt hn']
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, run_restrict D dom s rs a ha
        (chosen_of_take hn' hc), List.mem_map.mpr ⟨_, pre_of_run D dom t a.2 b hb _
          (chosen_of_take' hn' hc), rfl⟩⟩)
  | .ite c s t, rs, p, h, n, hc => by
    simp only [run] at h
    simp only [preRuns]
    split at h
    · rename_i ht; simp only [ht, ite_true]; exact pre_of_run D dom s rs p h n hc
    · rename_i ht; simp only [ht]; exact pre_of_run D dom t rs p h n hc
  | .loop k c body, rs, p, h, n, hc => by
    simp only [run] at h
    simp only [preRuns]
    exact pre_iter (fun rs p h hc => run_restrict D dom body rs p h hc)
      (fun rs p h n hc => pre_of_run D dom body rs p h n hc) k rs p h n hc

end Silmaril.Proofs.X86.Concurrency.Cir.Domain
