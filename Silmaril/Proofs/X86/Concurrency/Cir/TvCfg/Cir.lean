module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# CFG translation validation: the CIR side

Facts about flat continuations, loop bounds and `Csl.TStep` runs:

* `flat_erase`, `flat_setB`, `erase_setB`, `bge_setB`: flat continuations commute with erasing
  and setting loop bounds;
* `sbeq_eq`, `lbeq_eq`: the Boolean equalities are equalities;
* `TRun.trans`, `TRun.seqL`: runs compose and lift into the left of a `seq`;
* `skip_of_flat_nil`: a statement with an empty flat continuation runs silently to `skip`;
* `head_step`: a step of the first leaf of the flat continuation is a run of the whole
  statement, whose flat continuation is the leaf's successor followed by the rest.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Csl (TStep)

/-! ## Flat continuations and bounds -/

theorem flat_leaf {s : Stmt} (h : leafB s = true) : flat s = [s] := by
  cases s <;> simp_all [leafB, flat]

theorem leafB_of_mem_flat : ∀ {s x : Stmt}, x ∈ flat s → leafB x = true
  | .skip, x, h => by simp [flat] at h
  | .seq s t, x, h => by
    simp only [flat, List.mem_append] at h
    rcases h with h | h
    · exact leafB_of_mem_flat h
    · exact leafB_of_mem_flat h
  | .assign .., x, h | .load .., x, h | .store .., x, h | .rmw .., x, h | .fence _, x, h
  | .futexWait .., x, h | .futexWake .., x, h | .spawn _, x, h | .join _, x, h | .local _, x, h
  | .ite .., x, h | .loop .., x, h => by
    simp only [flat, List.mem_singleton] at h; subst h; rfl

theorem flat_erase : ∀ s : Stmt, flat (erase s) = (flat s).map erase
  | .skip => rfl
  | .seq s t => by simp [flat, erase, flat_erase s, flat_erase t]
  | .assign .. | .load .. | .store .. | .rmw .. | .fence _ | .futexWait .. | .futexWake ..
  | .spawn _ | .join _ | .local _ | .ite .. | .loop .. => rfl

theorem flat_setB (L : Nat) : ∀ s : Stmt, flat (setB L s) = (flat s).map (setB L)
  | .skip => rfl
  | .seq s t => by simp [flat, setB, flat_setB L s, flat_setB L t]
  | .assign .. | .load .. | .store .. | .rmw .. | .fence _ | .futexWait .. | .futexWake ..
  | .spawn _ | .join _ | .local _ | .ite .. | .loop .. => rfl

theorem erase_setB (L : Nat) : ∀ s : Stmt, erase (setB L s) = erase s
  | .seq s t => by simp [erase, setB, erase_setB L s, erase_setB L t]
  | .ite c s t => by simp [erase, setB, erase_setB L s, erase_setB L t]
  | .loop _ _ b => by simp [erase, setB, erase_setB L b]
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence _ | .futexWait .. | .futexWake ..
  | .spawn _ | .join _ | .local _ => rfl

theorem bge_setB (L : Nat) : ∀ s : Stmt, bge L (setB L s)
  | .seq s t => ⟨bge_setB L s, bge_setB L t⟩
  | .ite _ s t => ⟨bge_setB L s, bge_setB L t⟩
  | .loop _ _ b => ⟨le_refl L, bge_setB L b⟩
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence _ | .futexWait .. | .futexWake ..
  | .spawn _ | .join _ | .local _ => trivial

theorem bge_mono {F G : Nat} (hFG : G ≤ F) : ∀ {s : Stmt}, bge F s → bge G s
  | .seq _ _, h => ⟨bge_mono hFG h.1, bge_mono hFG h.2⟩
  | .ite _ _ _, h => ⟨bge_mono hFG h.1, bge_mono hFG h.2⟩
  | .loop _ _ _, h => ⟨Nat.le_trans hFG h.1, bge_mono hFG h.2⟩
  | .skip, _ | .assign .., _ | .load .., _ | .store .., _ | .rmw .., _ | .fence _, _
  | .futexWait .., _ | .futexWake .., _ | .spawn _, _ | .join _, _ | .local _, _ => trivial

theorem bge_flat {F : Nat} : ∀ {s : Stmt}, bge F s → ∀ x ∈ flat s, bge F x
  | .skip, _, x, hx => by simp [flat] at hx
  | .seq s t, h, x, hx => by
    simp only [flat, List.mem_append] at hx
    rcases hx with hx | hx
    · exact bge_flat h.1 x hx
    · exact bge_flat h.2 x hx
  | .assign .., h, x, hx | .load .., h, x, hx | .store .., h, x, hx | .rmw .., h, x, hx
  | .fence _, h, x, hx | .futexWait .., h, x, hx | .futexWake .., h, x, hx | .spawn _, h, x, hx
  | .join _, h, x, hx | .local _, h, x, hx | .ite .., h, x, hx | .loop .., h, x, hx => by
    simp only [flat, List.mem_singleton] at hx; subst hx; exact h

/-! ## Boolean equality -/

theorem sbeq_eq : ∀ {s t : Stmt}, sbeq s t = true → s = t := by
  intro s
  induction s with
  | seq s t ihs iht =>
    intro u h
    cases u <;> simp only [sbeq, Bool.and_eq_true, Bool.false_eq_true] at h
    rw [ihs h.1, iht h.2]
  | ite c s t ihs iht =>
    intro u h
    cases u <;> simp only [sbeq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, h2⟩, h3⟩ := h
    rw [ihs h2, iht h3]
  | loop n c b ih =>
    intro u h
    cases u <;> simp only [sbeq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h3⟩ := h
    rw [ih h3]
  | «local» b => intro u h; cases u <;> simp [sbeq] at h
  | _ => intro u h; cases u <;> simp_all [sbeq]

theorem lbeq_eq : ∀ {l l' : List Stmt}, lbeq l l' = true → l = l'
  | [], [], _ => rfl
  | s :: l, s' :: l', h => by
    simp only [lbeq, Bool.and_eq_true] at h
    rw [sbeq_eq h.1, lbeq_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [lbeq] at h

/-! ## Runs -/

theorem TRun.trans {s rs l s₁ rs₁ l' s₂ rs₂} (h : TRun s rs l s₁ rs₁) (h' : TRun s₁ rs₁ l' s₂ rs₂) :
    TRun s rs (l ++ l') s₂ rs₂ := by
  induction h with
  | refl => exact h'
  | tau hs _ ih => exact .tau hs (ih h')
  | lab hs _ ih => exact .lab hs (ih h')

/-- A run lifts into the left of a `seq`. -/
theorem TRun.seqL {s rs l s' rs'} (t : Stmt) (h : TRun s rs l s' rs') :
    TRun (.seq s t) rs l (.seq s' t) rs' := by
  induction h with
  | refl => exact .refl
  | tau hs _ ih => exact .tau (.seq hs) ih
  | lab hs _ ih => exact .lab (.seq hs) ih

/-- One step as a run. -/
theorem TRun.one {s rs s' rs'} : ∀ {o : Option Lab}, TStep s rs o s' rs' → TRun s rs o.toList s' rs'
  | none, h => .tau h .refl
  | some _, h => .lab h .refl

/-- A statement with no leaves runs silently to `skip`. -/
theorem skip_of_flat_nil {s : Stmt} (rs : Regs) (h : flat s = []) : TRun s rs [] .skip rs := by
  induction s with
  | skip => exact .refl
  | seq s t ihs iht =>
    simp only [flat, List.append_eq_nil_iff] at h
    exact TRun.trans (TRun.seqL t (ihs h.1)) (.tau .seqSkip (iht h.2))
  | _ => simp [flat] at h

/-- **A step of the first leaf** of the flat continuation is a run of the statement, ending
with the leaf's successor followed by the rest of the continuation. -/
theorem head_step {σ a : Stmt} {rest : List Stmt} (h : flat σ = a :: rest) {rs : Regs}
    {o : Option Lab} {a' : Stmt} {rs' : Regs} (hs : TStep a rs o a' rs') :
    ∃ σ', TRun σ rs o.toList σ' rs' ∧ flat σ' = flat a' ++ rest := by
  induction σ generalizing rest with
  | skip => simp [flat] at h
  | seq x y ihx ihy =>
    simp only [flat] at h
    cases hx : flat x with
    | nil =>
      rw [hx, List.nil_append] at h
      obtain ⟨σ', hr, hf⟩ := ihy h
      exact ⟨σ', TRun.trans (TRun.seqL y (skip_of_flat_nil rs hx)) (.tau .seqSkip hr), hf⟩
    | cons b r1 =>
      rw [hx, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x', hr, hf⟩ := ihx hx
      exact ⟨.seq x' y, TRun.seqL y hr, by simp [flat, hf]⟩
  | _ =>
    simp only [flat, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨a', TRun.one hs, by simp⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvCfg
