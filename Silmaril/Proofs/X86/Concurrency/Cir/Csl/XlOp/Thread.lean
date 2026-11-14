module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Domain.Thms

/-!
# The XL bridge, thread side: runs as small-step paths

Proofs for `Csl.Task.cirXlOpAx`.

* `run_path`: a run of `Cir.run` is a path of `TStep`s emitting its trace and ending at `skip`;
* `path_split`: such a path, cut at its labels, as two state sequences (`S c` after `c` labels,
  `Pre c` just before the `c`-th label step, silent steps in between);
* `labs_shape`: the labels of a run of a uniform, thread-free statement are write-back loads
  and stores, read-modify-writes, fences, futex calls and blocks;
* `safe_taus`, `safe_touch`: CSL safety survives silent steps and gives the touch obligations of
  the next label step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (mem_pick mem_qpick mem_seqL forall2_length
  cellVals_vals bind_mem lit_addr)

/-! ## Paths -/

/-- Small-step paths of one thread emitting a trace. -/
inductive TPath : Stmt → Regs → List Lab → Stmt → Regs → Prop
  | nil {s rs} : TPath s rs [] s rs
  | tau {s rs s' rs' tr s'' rs''} (h : TStep s rs none s' rs') (p : TPath s' rs' tr s'' rs'') :
      TPath s rs tr s'' rs''
  | lab {s rs l s' rs' tr s'' rs''} (h : TStep s rs (some l) s' rs')
      (p : TPath s' rs' tr s'' rs'') : TPath s rs (l :: tr) s'' rs''

theorem TPath.append {s rs tr₁ s₁ rs₁ tr₂ s₂ rs₂} (h₁ : TPath s rs tr₁ s₁ rs₁)
    (h₂ : TPath s₁ rs₁ tr₂ s₂ rs₂) : TPath s rs (tr₁ ++ tr₂) s₂ rs₂ := by
  induction h₁ with
  | nil => exact h₂
  | tau h _ ih => exact .tau h (ih h₂)
  | lab h _ ih => exact .lab h (ih h₂)

theorem TPath.seq {s rs tr s' rs'} (t : Stmt) (h : TPath s rs tr s' rs') :
    TPath (.seq s t) rs tr (.seq s' t) rs' := by
  induction h with
  | nil => exact .nil
  | tau h _ ih => exact .tau (.seq h) ih
  | lab h _ ih => exact .lab (.seq h) ih

theorem TPath.seqSkip {s rs tr rs' t tr' s'' rs''} (h : TPath s rs tr .skip rs')
    (h' : TPath t rs' tr' s'' rs'') : TPath (.seq s t) rs (tr ++ tr') s'' rs'' :=
  (h.seq t).append (.tau .seqSkip h')

theorem iter_path {dom : List Nat} {body : Stmt}
    (hb : ∀ rs p, p ∈ run dom body rs → TPath body rs p.1 .skip p.2) {c : Expr} :
    ∀ n rs p, p ∈ iter (run dom body) c n rs → TPath (.loop n c body) rs p.1 .skip p.2
  | 0, rs, p, h => by
    simp only [iter] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [List.mem_singleton] at h; subst h
      exact .tau (.loopF (by simpa using hc)) .nil
  | n + 1, rs, p, h => by
    simp only [iter] at h
    split at h
    · rename_i hc
      obtain ⟨a, ha, b, hb', rfl⟩ := bind_mem h
      exact .tau (.loopT hc) ((hb rs a ha).seqSkip (iter_path hb n a.2 b hb'))
    · rename_i hc
      simp only [List.mem_singleton] at h; subst h
      exact .tau (.loopF (by simpa using hc)) .nil

theorem run_path (dom : List Nat) : ∀ (s : Stmt) rs p, p ∈ run dom s rs → TPath s rs p.1 .skip p.2
  | .skip, rs, p, h => by simp [run] at h; subst h; exact .nil
  | .assign d e, rs, p, h => by simp [run] at h; subst h; exact .tau .assign .nil
  | .load d md sz fl a, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact .lab (.load (mem_pick hv)) .nil
  | .store md sz fl a v, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h; exact .lab .store .nil
  | .rmw d md sz op a arg, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact .lab (.rmw (mem_pick hv)) .nil
  | .fence k, rs, p, h => by simp [run] at h; subst h; exact .lab .fence .nil
  | .futexWait d a v, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, hw, h⟩ := h
    split at h
    · rename_i he
      simp only [List.mem_map] at h
      obtain ⟨r, hr, rfl⟩ := h
      have hst := TStep.fwait (d := d) (a := a) (v := v) (rs := rs) (seen := w) (r := r)
        (by have := mem_pick hw; simpa using this) (by have := mem_qpick hr; omega)
      have e0 : (if w = (v.eval rs).toNat % 2 ^ 32 then 0 else eagain) = 0 := ite_eq_left he
      rw [e0] at hst
      exact .lab hst .nil
    · rename_i he
      simp only [List.mem_singleton] at h; subst h
      have hst := TStep.fwait (d := d) (a := a) (v := v) (rs := rs) (seen := w) (r := 0)
        (by have := mem_pick hw; simpa using this) (by omega)
      have e0 : (if w = (v.eval rs).toNat % 2 ^ 32 then 0 else eagain) = eagain := ite_eq_right he
      rw [e0] at hst
      exact .lab hst .nil
  | .futexWake a n, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact .lab (.fwake (by have := mem_qpick hq; omega)) .nil
  | .spawn t, rs, p, h => by simp [run] at h; subst h; exact .lab .spawn .nil
  | .join t, rs, p, h => by simp [run] at h; subst h; exact .lab .join .nil
  | .local b, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, hivs, rvs, hrvs, ovs, hovs, h⟩ := h
    split at h
    · rename_i hspec
      cases h
      have hi := forall2_length (mem_seqL _ _ _ hivs)
      have hr := forall2_length (mem_seqL _ _ _ hrvs)
      have ho := forall2_length (mem_seqL _ _ _ hovs)
      exact .lab (.blk (@of_decide_eq_true _ (b.dec _ _) hspec) hi.symm hr.symm ho.symm) .nil
    · cases h
  | .seq s t, rs, p, h => by
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    exact (run_path dom s rs a ha).seqSkip (run_path dom t a.2 b hb)
  | .ite c s t, rs, p, h => by
    simp only [run] at h
    split at h
    · rename_i hc; exact .tau (.iteT hc) (run_path dom s rs p h)
    · rename_i hc; exact .tau (.iteF (by simpa using hc)) (run_path dom t rs p h)
  | .loop n c body, rs, p, h => iter_path (fun rs p h => run_path dom body rs p h) n rs p h

/-! ## Cutting a path at its labels -/

/-- A silent step on thread states. -/
def TauR (a b : Stmt × Regs) : Prop := TStep a.1 a.2 none b.1 b.2

/-- A path, cut at its labels: `S c` is the state after `c` labels, `Pre c` the state right
before the `c`-th label step. -/
structure Cut (s : Stmt) (rs : Regs) (tr : List Lab) (fin : Stmt × Regs)
    (S Pre : Nat → Stmt × Regs) : Prop where
  start : S 0 = (s, rs)
  taus : ∀ c < tr.length, Star TauR (S c) (Pre c)
  step : ∀ c (h : c < tr.length), TStep (Pre c).1 (Pre c).2 (some tr[c]) (S (c + 1)).1 (S (c + 1)).2
  last : Star TauR (S tr.length) fin

theorem path_split {s rs tr s' rs'} (h : TPath s rs tr s' rs') :
    ∃ S Pre : Nat → Stmt × Regs, Cut s rs tr (s', rs') S Pre := by
  induction h with
  | @nil s rs => exact ⟨fun _ => (s, rs), fun _ => (s, rs), rfl, fun c h => by simp at h,
      fun c h => by simp at h, Star.refl⟩
  | @tau s rs s1 rs1 tr s2 rs2 hs _ ih =>
    obtain ⟨S, Pre, hc⟩ := ih
    refine ⟨fun c => if c = 0 then (s, rs) else S c, Pre, rfl, ?_, ?_, ?_⟩
    · intro c hc'
      rcases c with _ | c
      · simp only [↓reduceIte]; exact .step (by simpa [TauR, hc.start] using hs) (hc.taus 0 hc')
      · simpa using hc.taus (c + 1) hc'
    · intro c hc'
      have := hc.step c hc'
      simpa using this
    · rcases hl : tr.length with _ | n
      · simp only [↓reduceIte]
        have := hc.last; rw [hl, hc.start] at this
        exact .step (by simpa [TauR] using hs) this
      · simpa [hl] using hc.last
  | @lab s rs l s1 rs1 tr s2 rs2 hs _ ih =>
    obtain ⟨S, Pre, hc⟩ := ih
    refine ⟨fun c => if c = 0 then (s, rs) else S (c - 1),
      fun c => if c = 0 then (s, rs) else Pre (c - 1), rfl, ?_, ?_, ?_⟩
    · intro c hc'
      rcases c with _ | c
      · exact Star.refl
      · simpa using hc.taus c (by simpa using hc')
    · intro c hc'
      rcases c with _ | c
      · simpa [hc.start] using hs
      · simpa using hc.step c (by simpa using hc')
    · simpa using hc.last

/-- **The cut of a run.** -/
theorem run_cut (dom : List Nat) {s : Stmt} {rs : Regs} {p : List Lab × Regs}
    (h : p ∈ run dom s rs) : ∃ S Pre : Nat → Stmt × Regs, Cut s rs p.1 (.skip, p.2) S Pre :=
  path_split (run_path dom s rs p h)

/-! ## The shape of the labels -/

/-- A label of a uniform, thread-free run. -/
def LabG : Lab → Prop
  | .rd _ fl _ _ _ => fl = .wb
  | .wr _ fl _ _ _ => fl = .wb
  | .fblock _ _ | .spawn _ | .join _ => False
  | _ => True

theorem iter_allP {Pr : Lab → Prop} {body : Regs → Res} {c : Expr}
    (hb : ∀ rs p, p ∈ body rs → ∀ l ∈ p.1, Pr l) :
    ∀ n rs p, p ∈ iter body c n rs → ∀ l ∈ p.1, Pr l :=
  Silmaril.Proofs.X86.Concurrency.Cir.Domain.iter_all hb

theorem labs_shape (D : List Nat) (cs : List (Nat × Nat)) :
    ∀ (s : Stmt), s.onCells cs = true → s.threadFree = true → ∀ rs p, p ∈ run D s rs →
      ∀ l ∈ p.1, LabG l
  | .skip, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .assign d e, _, _, rs, p, h => by simp [run] at h; subst h; simp
  | .load d md sz fl a, hc, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    cases a <;> simp_all [Stmt.onCells, LabG]
  | .store md sz fl a v, hc, _, rs, p, h => by
    simp only [run, List.mem_singleton] at h; subst h
    cases a <;> simp_all [Stmt.onCells, LabG]
  | .rmw d md sz op a arg, _, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp [LabG]
  | .fence k, _, _, rs, p, h => by simp [run] at h; subst h; simp [LabG]
  | .futexWait d a v, _, _, rs, p, h => by
    simp only [run, List.mem_flatMap] at h
    obtain ⟨w, hw, h⟩ := h
    split at h
    · simp only [List.mem_map] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp [LabG]
    · simp only [List.mem_singleton] at h; subst h; simp [LabG]
  | .futexWake a n, _, _, rs, p, h => by
    simp only [run, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    simp [LabG]
  | .spawn t, _, ht, _, _, _ => by simp [Stmt.threadFree] at ht
  | .join t, _, ht, _, _, _ => by simp [Stmt.threadFree] at ht
  | .local b, _, _, rs, p, h => by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨ivs, -, rvs, -, ovs, -, h⟩ := h
    split at h
    · cases h; simp [LabG]
    · cases h
  | .seq s t, hc, ht, rs, p, h => by
    simp only [Stmt.onCells, Stmt.threadFree, Bool.and_eq_true] at hc ht
    obtain ⟨a, ha, b, hb, rfl⟩ := bind_mem h
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact labs_shape D cs s hc.1 ht.1 rs a ha l hl
    · exact labs_shape D cs t hc.2 ht.2 a.2 b hb l hl
  | .ite c s t, hc, ht, rs, p, h => by
    simp only [Stmt.onCells, Stmt.threadFree, Bool.and_eq_true] at hc ht
    simp only [run] at h
    split at h
    · exact labs_shape D cs s hc.1 ht.1 rs p h
    · exact labs_shape D cs t hc.2 ht.2 rs p h
  | .loop n c body, hc, ht, rs, p, h => by
    simp only [Stmt.onCells, Stmt.threadFree] at hc ht
    exact iter_allP (fun rs p h => labs_shape D cs body hc ht rs p h) n rs p h

/-! ## Safety along silent steps -/

variable {I : HProp} {Q : Regs → HProp}

theorem safe_tau {s : Stmt} {rs : Regs} {h : Heap} (H : Safe I Q s rs h) {s' : Stmt} {rs' : Regs}
    (st : TStep s rs none s' rs') : Safe I Q s' rs' h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact ⟨R, (hpost s rs h hR).2.1 s' rs' st, hpost⟩

theorem safe_taus {a b : Stmt × Regs} (hab : Star TauR a b) {h : Heap}
    (H : Safe I Q a.1 a.2 h) : Safe I Q b.1 b.2 h := by
  induction hab with
  | refl => exact H
  | step st _ ih => exact ih (safe_tau H st)

/-- The touch obligations of a label step of a safe thread. -/
theorem safe_touch {s : Stmt} {rs : Regs} {h : Heap} (H : Safe I Q s rs h) {l : Lab} {s' : Stmt}
    {rs' : Regs} (st : TStep s rs (some l) s' rs') :
    (l.na = true → ∀ a, l.Touches a → (h a).isSome) ∧
    (l.na = false → ∀ hI, I hI → Heap.Disjoint h hI → ∀ a, l.Touches a →
      (Heap.union h hI a).isSome) := by
  obtain ⟨R, hR, hpost⟩ := H
  obtain ⟨-, h1, h2⟩ := (hpost s rs h hR).2.2 l s' rs' st
  exact ⟨fun hn => (h1 hn).1, fun hn hI hi hd => (h2 hn hI hi hd).1⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
