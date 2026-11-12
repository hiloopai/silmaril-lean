module

public import Silmaril.Wasm.Dataflow.Fused.Defs
public import Silmaril.Wasm.Dataflow.Liveness.Thms
public import Silmaril.Wasm.Dataflow.Fragment.Thms

/-!
# The fused one-pass DCE (retired): theorems

* `dceAdminSeq_expression`: on source code the administrative transform is the source
  transform;
* `fragSeq_dceSeq`: the transform keeps fragment code in the fragment;
* `Step.labelsOk`: reduction keeps label continuations admissible, for any code (the source
  also stated a version with an unused fragment hypothesis; it is not ported);
* `rel_entry`: `Rel` holds at the entry of a function body.

The step simulation for `Rel` is false (`Silmaril.Wasm.Dataflow.Litmus`).
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

theorem expression_cons (i : Instr) (e : List Instr) :
    expression (i :: e) = .plain i :: expression e := rfl

/-- On source code the administrative transform is the source transform. -/
theorem dceAdminSeq_expression (env : List LiveSet) (out : LiveSet) :
    ∀ e : List Instr, dceAdminSeq env out (expression e) = expression (dceSeq env out e)
  | [] => by simp [expression, dceAdminSeq, dceSeq]
  | [i] => by simp [expression, dceAdminSeq, dceSeq, dceAdmin]
  | i :: j :: is => by
      have ih1 := dceAdminSeq_expression env out is
      have ih2 := dceAdminSeq_expression env out (j :: is)
      have hl := liveAdminSeq_expression env out (j :: is)
      have hl' := liveAdminSeq_expression env out is
      rw [expression_cons] at ih2 hl
      rw [expression_cons, expression_cons]
      simp only [dceAdminSeq, dceSeq, adminPureArity?, adminDeadConsumer, dceAdmin, hl, hl',
        ih1, ih2]
      cases pureArity? i with
      | none => simp [expression]
      | some n =>
        by_cases hd : deadConsumer (liveSeq env out is) j = true <;> simp [expression, hd]

theorem fragSeq_replicate_drop (n : Nat) : fragSeq (List.replicate n .drop) = true := by
  rw [fragSeq_iff]
  intro i hi
  rw [List.eq_of_mem_replicate hi]
  rfl

mutual
/-- The transform of one fragment instruction is fragment code. -/
theorem fragSeq_dceInstr (env : List LiveSet) (out : LiveSet) (i : Instr)
    (h : fragInstr i = true) : fragSeq (dceInstr env out i) = true := by
  cases i with
  | block bt body =>
    simpa [dceInstr, fragInstr] using fragSeq_dceSeq _ _ body (by simpa [fragInstr] using h)
  | loop bt body =>
    simpa [dceInstr, fragInstr] using fragSeq_dceSeq _ _ body (by simpa [fragInstr] using h)
  | if_ bt b₁ b₂ =>
    have h' : fragSeq b₁ = true ∧ fragSeq b₂ = true := by simpa [fragInstr] using h
    simpa [dceInstr, fragInstr] using
      And.intro (fragSeq_dceSeq (out :: env) out b₁ h'.1) (fragSeq_dceSeq (out :: env) out b₂ h'.2)
  | localSet x => simp only [dceInstr]; split <;> rfl
  | localTee x => simp only [dceInstr]; split <;> rfl
  | _ => simpa [dceInstr] using h
termination_by sizeOf i

/-- The transform keeps fragment code in the fragment. -/
theorem fragSeq_dceSeq (env : List LiveSet) (out : LiveSet) (is : List Instr)
    (h : fragSeq is = true) : fragSeq (dceSeq env out is) = true := by
  match is with
  | [] => simp [dceSeq]
  | [i] => simpa [dceSeq] using fragSeq_dceInstr env out i (by simpa using h)
  | i :: j :: is =>
    have h' : fragInstr i = true ∧ fragInstr j = true ∧ fragSeq is = true := by simpa using h
    have hI := fragSeq_dceInstr env (liveSeq env out (j :: is)) i h'.1
    have hJ := fragSeq_dceSeq env out (j :: is) (by simp [h'.2.1, h'.2.2])
    have hK := fragSeq_dceSeq env out is h'.2.2
    simp only [dceSeq]
    split
    · split
      · simp [fragSeq_replicate_drop, hK]
      · simp only [fragSeq_append, Bool.and_eq_true]; exact ⟨hI, hJ⟩
    · simp only [fragSeq_append, Bool.and_eq_true]; exact ⟨hI, hJ⟩
termination_by sizeOf is
end

/-! ## Label continuations -/

/-- Source code has no labels. -/
@[simp] theorem labelsOkSeq_expression (e : List Instr) : labelsOkSeq (expression e) = true := by
  induction e with
  | nil => rfl
  | cons i e ih =>
      show (labelsOkAdmin (.plain i) && labelsOkSeq (expression e)) = true
      rw [ih]
      rfl

@[simp] theorem labelsOkSeq_nil : labelsOkSeq [] = true := rfl

@[simp] theorem labelsOkSeq_cons (a : Admin) (as : List Admin) :
    labelsOkSeq (a :: as) = (labelsOkAdmin a && labelsOkSeq as) := rfl

@[simp] theorem labelsOkSeq_append (as bs : List Admin) :
    labelsOkSeq (as ++ bs) = (labelsOkSeq as && labelsOkSeq bs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih, Bool.and_assoc]

@[simp] theorem labelsOkAdmin_plain (i : Instr) : labelsOkAdmin (.plain i) = true := rfl
@[simp] theorem labelsOkAdmin_ref (r : Ref) : labelsOkAdmin (.ref r) = true := rfl
@[simp] theorem labelsOkAdmin_trap : labelsOkAdmin .trap = true := rfl
@[simp] theorem labelsOkAdmin_frame (n : Nat) (f : Frame) (b : List Admin) :
    labelsOkAdmin (.frame n f b) = true := rfl
@[simp] theorem labelsOkAdmin_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    labelsOkAdmin (.handler n cs b) = true := rfl
@[simp] theorem labelsOkAdmin_callRefType (d : Validation.DefType) :
    labelsOkAdmin (.callRefType d) = true := rfl
@[simp] theorem labelsOkAdmin_returnCallRefType (d : Validation.DefType) :
    labelsOkAdmin (.returnCallRefType d) = true := rfl
@[simp] theorem labelsOkAdmin_label (n : Nat) (cont : List Instr) (b : List Admin) :
    labelsOkAdmin (.label n cont b) = (contOk cont && labelsOkSeq b) := rfl

@[simp] theorem labelsOkAdmin_val (v : Val) : labelsOkAdmin v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem labelsOkAdmin_constI32 (b : BitVec 32) : labelsOkAdmin (constI32 b) = true :=
  labelsOkAdmin_val _

@[simp] theorem labelsOkAdmin_store8 (x : MemIdx) : labelsOkAdmin (store8 x) = true := rfl
@[simp] theorem labelsOkAdmin_load8u (x : MemIdx) : labelsOkAdmin (load8u x) = true := rfl

@[simp] theorem labelsOkSeq_vals (vs : List Val) : labelsOkSeq (vals vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem labelsOkSeq_result (r : Result) : labelsOkSeq r.toAdmin = true := by
  cases r <;> simp [Result.toAdmin]

theorem labelsOkSeq_iff (as : List Admin) :
    labelsOkSeq as = true ↔ ∀ a ∈ as, labelsOkAdmin a = true := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

@[simp] theorem labelsOkSeq_map_ref (rs : List Ref) : labelsOkSeq (rs.map .ref) = true := by
  rw [labelsOkSeq_iff]; simp

@[simp] theorem labelsOkSeq_take {as : List Admin} (h : labelsOkSeq as = true) (n : Nat) :
    labelsOkSeq (as.take n) = true := by
  rw [labelsOkSeq_iff] at h ⊢
  exact fun a ha => h a (List.mem_of_mem_take ha)

@[simp] theorem labelsOkSeq_drop {as : List Admin} (h : labelsOkSeq as = true) (n : Nat) :
    labelsOkSeq (as.drop n) = true := by
  rw [labelsOkSeq_iff] at h ⊢
  exact fun a ha => h a (List.mem_of_mem_drop ha)

theorem labelsOkAdmin_retToCallIn (m : ModuleInst) (c : Admin) :
    labelsOkAdmin (c.retToCallIn m) = labelsOkAdmin c := by
  unfold Admin.retToCallIn
  split <;> (try split) <;> rfl

/-- Reduction keeps label continuations admissible, for any code: `block` and `loop`
create `[]` and `[loop bt body]`, and a `br` splices a continuation into the outer code as
plain instructions. -/
theorem Step.labelsOk {P : Numerics.Profile} {H : Type} {host : HostSemantics H}
    {c c' : Config H} (h : Step P host c c') (hl : labelsOkSeq c.code = true) :
    labelsOkSeq c'.code = true := by
  induction h with
  | parametric h => cases h <;> simp_all
  | numeric h => cases h <;> simp_all
  | vector h => cases h <;> simp_all
  | «variable» h => cases h <;> simp_all
  | table h => cases h <;> simp_all
  | memory h => cases h <;> simp_all
  | reference h => cases h <;> simp_all
  | aggregate h => cases h <;> simp_all
  | @ctxtInstrs _ _ _ _ vs is is' rest _ _ ih =>
    have hl' : labelsOkSeq is = true ∧ labelsOkSeq rest = true := by
      simpa only [labelsOkSeq_append, labelsOkSeq_vals, Bool.true_and, Bool.and_eq_true] using hl
    show labelsOkSeq (vals vs ++ is' ++ rest) = true
    simp only [labelsOkSeq_append, labelsOkSeq_vals, ih hl'.1, hl'.2, Bool.and_self]
  | @ctxtLabel _ _ _ _ n cont is is' _ ih =>
    have hl' : contOk cont = true ∧ labelsOkSeq is = true := by
      simpa only [labelsOkSeq_cons, labelsOkAdmin_label, Bool.and_eq_true, labelsOkSeq_nil,
        Bool.and_true] using hl
    show labelsOkSeq [.label n cont is'] = true
    simp only [labelsOkSeq_cons, labelsOkAdmin_label, hl'.1, ih hl'.2, labelsOkSeq_nil,
      Bool.and_self]
  | ctxtHandler => simp
  | ctxtFrame => simp
  | @returnCallRefLabel _ _ _ _ _ c _ hc => cases c <;> simp_all [Admin.IsReturnCallRef]
  | @returnCallRefHandler _ _ _ _ _ c _ hc => cases c <;> simp_all [Admin.IsReturnCallRef]
  | @returnCallRefFrameAddr _ _ _ _ _ _ _ c _ _ _ _ hc =>
    cases c <;> simp_all [labelsOkAdmin_retToCallIn, Admin.IsReturnCallRef]
  | _ => simp_all [contOk]

/-! ## The relation -/

variable {H : Type}

/-- Forget the label condition. -/
theorem Rel.toBase {env : List LiveSet} {out : LiveSet} {c d : Config H} (h : Rel env out c d) :
    RelBase env out c d :=
  ⟨h.store, h.frame, h.frag, h.code⟩

/-- The initial relation for a function body under its outer label. -/
theorem rel_entry {s : Store H} {f f' : Frame} {n : Nat} {e : Expr} (he : fragSeq e = true)
    (hf : FrameRel (liveEntry e) f f') :
    Rel [] ⊥ ⟨s, f, [.label n [] (expression e)]⟩ ⟨s, f', [.label n [] (expression (dce e))]⟩ := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show FrameRel (liveAdminSeq [] ⊥ [.label n [] (expression e)]) f f'
    rw [liveAdminSeq_cons, liveAdminSeq_nil]
    simp only [liveAdmin]
    rw [liveAdminSeq_expression]
    simpa [liveEntry] using hf
  · simp [he]
  · simp [contOk]
  · simp [dceAdminSeq, dceAdmin, dceSeq, dceAdminSeq_expression, dce]

end Silmaril.Wasm.Dataflow
