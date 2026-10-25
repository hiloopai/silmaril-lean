module

public import Silmaril.Logic.Metamath.Derivation

@[expose] public section

/-!
# The Metamath proof stack machine

A proof is checked by a stack machine (Megill and Wheeler, *Metamath*,
§4.1.4 and §4.3). Pushing a hypothesis pushes its expression. Applying an
assertion `B` pops one entry per mandatory hypothesis of `B`, reads the
substitution off the floating hypotheses, checks that every substituted
hypothesis matches its entry, checks `B`'s disjoint-variable conditions, and
pushes the substituted conclusion. Compressed proofs add two instructions:
`save` copies the top of the stack into a table of saved steps, and `load`
pushes a saved step again.

The machine is generic over constants and variables. Its only link to the
proof frame is the disjointness test `disj`. Soundness (`verify_sound`): if
every instruction is valid for a frame `F` and the axiom set `Γ` (hypotheses
of `F`, assertions of `Γ`) and `disj` implies `F.Disjoint`, then an accepted
proof yields a `Derivation Γ F` of the conclusion. Every stack and table entry
is derivable, which is the invariant of the proof.
-/

namespace Silmaril.Logic.Metamath.Verify

universe u

/-- Why a proof was rejected. -/
inductive ProofError where
  /-- The proof contains `?`. -/
  | incomplete
  /-- A label is not an active hypothesis or an earlier assertion. -/
  | unknownLabel (label : String)
  /-- A compressed proof lists a mandatory hypothesis in its label list. -/
  | mandatoryInList (label : String)
  /-- A character that is not a compressed proof letter. -/
  | badLetter (c : Char)
  /-- `Z` that does not directly follow a proof step. -/
  | badSave
  /-- A compressed number with leading digits `U`-`Y` but no final digit. -/
  | unfinishedNumber
  /-- A reference to a saved step that does not exist (yet). -/
  | badReference (n : Nat)
  /-- Too few stack entries for the hypotheses of an assertion. -/
  | underflow (label : String)
  /-- A stack entry does not match a hypothesis of an assertion. -/
  | mismatch (label : String)
  /-- A substitution violates a disjoint-variable condition. -/
  | dvViolation (label : String)
  /-- `save` with an empty stack. -/
  | emptySave
  /-- The final stack does not have exactly one entry. -/
  | finalStack (size : Nat)
  /-- The final entry is not the statement being proved. -/
  | wrongConclusion
  deriving DecidableEq, Repr, Inhabited

instance : ToString ProofError where
  toString
    | .incomplete => "incomplete proof (`?`)"
    | .unknownLabel l => s!"{l} is not an active hypothesis or an earlier assertion"
    | .mandatoryInList l => s!"mandatory hypothesis {l} in the compressed label list"
    | .badLetter c => s!"invalid character {repr c} in compressed proof"
    | .badSave => "`Z` does not follow a proof step"
    | .unfinishedNumber => "compressed proof ends inside a number"
    | .badReference n => s!"reference to saved step {n} before it is saved"
    | .underflow l => s!"too few stack entries for {l}"
    | .mismatch l => s!"hypotheses of {l} do not match the stack"
    | .dvViolation l => s!"disjoint variable violation applying {l}"
    | .emptySave => "`Z` with an empty stack"
    | .finalStack n => s!"final stack has {n} entries"
    | .wrongConclusion => "proof does not prove the statement"

/-- One instruction of the proof machine. -/
inductive Instr (C V : Type u) where
  /-- Push a hypothesis. -/
  | hyp (e : Expr C V)
  /-- Apply the assertion `B`, named `label`. -/
  | app (label : String) (B : Assertion C V)
  /-- Save the top of the stack. -/
  | save
  /-- Push the saved step with this index. -/
  | load (i : Nat)
  deriving Inhabited

/-- The machine state: the proof stack and the saved steps. -/
structure State (C V : Type u) where
  stack : Array (Expr C V) := #[]
  saved : Array (Expr C V) := #[]

variable {C V : Type u}

/-- The substitution determined by the floating hypotheses, as bindings. -/
def floatBinding : List (Hyp C V) → List (Expr C V) → List (V × Str C V)
  | .float _ v :: hs, a :: as => (v, a.body) :: floatBinding hs as
  | .ess _ :: hs, _ :: as => floatBinding hs as
  | _, _ => []

/-- Bindings as a substitution; unbound variables stay unchanged. -/
def substOf [DecidableEq V] (b : List (V × Str C V)) : Subst C V :=
  fun v => (b.lookup v).getD [.var v]

/-- The hypotheses under `σ` match the stack entries, one for one. -/
def hypsMatch [DecidableEq C] [DecidableEq V] (σ : Subst C V) :
    List (Hyp C V) → List (Expr C V) → Bool
  | [], [] => true
  | .float tc v :: hs, a :: as => (tc == a.tc && σ v == a.body) && hypsMatch σ hs as
  | .ess e :: hs, a :: as => (e.subst σ == a) && hypsMatch σ hs as
  | _, _ => false

/-- The disjoint-variable check of `dv` under `σ` against the test `disj`. -/
def dvOk [DecidableEq V] (disj : V → V → Bool) (σ : Subst C V) (dv : List (V × V)) : Bool :=
  dv.all fun p =>
    (Str.vars (σ p.1)).all fun a => (Str.vars (σ p.2)).all fun b => a != b && disj a b

/-- Drop the top `n` entries of an array. -/
def popN {α : Type u} (a : Array α) : Nat → Array α
  | 0 => a
  | n + 1 => popN a.pop n

variable [DecidableEq C] [DecidableEq V]

/-- Apply the assertion `B` to the top of the stack. -/
def apply (disj : V → V → Bool) (label : String) (B : Assertion C V) (s : State C V) :
    Except ProofError (State C V) :=
  let n := B.hyps.length
  if n ≤ s.stack.size then
    let args := (s.stack.extract (s.stack.size - n) s.stack.size).toList
    let σ := substOf (floatBinding B.hyps args)
    if hypsMatch σ B.hyps args then
      if dvOk disj σ B.dv then
        .ok { s with stack := (popN s.stack n).push (B.concl.subst σ) }
      else .error (.dvViolation label)
    else .error (.mismatch label)
  else .error (.underflow label)

/-- Execute one instruction. -/
def step (disj : V → V → Bool) (s : State C V) : Instr C V → Except ProofError (State C V)
  | .hyp e => .ok { s with stack := s.stack.push e }
  | .app label B => apply disj label B s
  | .save =>
    match s.stack.back? with
    | some e => .ok { s with saved := s.saved.push e }
    | none => .error .emptySave
  | .load i =>
    match s.saved[i]? with
    | some e => .ok { s with stack := s.stack.push e }
    | none => .error (.badReference i)

/-- Execute a list of instructions. -/
def run (disj : V → V → Bool) : State C V → List (Instr C V) → Except ProofError (State C V)
  | s, [] => .ok s
  | s, i :: is =>
    match step disj s i with
    | .ok s' => run disj s' is
    | .error e => .error e

/-- The final stack must consist of the conclusion alone. -/
def finish (s : State C V) (concl : Expr C V) : Except ProofError Unit :=
  match s.stack.toList with
  | [e] => if e = concl then .ok () else .error .wrongConclusion
  | _ => .error (.finalStack s.stack.size)

/-- Run a proof from the empty state and check its conclusion. -/
def verify (disj : V → V → Bool) (instrs : List (Instr C V)) (concl : Expr C V) :
    Except ProofError Unit :=
  match run disj {} instrs with
  | .ok s => finish s concl
  | .error e => .error e

/-! ## Soundness -/

/-- An instruction is valid for the frame `F` and the axiom set `Γ` when it
pushes a hypothesis of `F` or applies an assertion of `Γ`. -/
def Instr.Valid (Γ : Set (Assertion C V)) (F : Assertion C V) : Instr C V → Prop
  | .hyp e => e ∈ F.hypExprs
  | .app _ B => B ∈ Γ
  | .save => True
  | .load _ => True

instance (Γ : Set (Assertion C V)) [DecidablePred (· ∈ Γ)] (F : Assertion C V) (i : Instr C V) :
    Decidable (i.Valid Γ F) := by
  cases i <;> unfold Instr.Valid <;> infer_instance

/-- Every stack entry and every saved step is derivable in `F` from `Γ`. -/
structure State.Sound (Γ : Set (Assertion C V)) (F : Assertion C V) (s : State C V) : Prop where
  stack : ∀ e ∈ s.stack.toList, Nonempty (Derivation Γ F e)
  saved : ∀ e ∈ s.saved.toList, Nonempty (Derivation Γ F e)

omit [DecidableEq C] [DecidableEq V] in
theorem mem_popN {α : Type u} {a : Array α} {n : Nat} {x : α} (h : x ∈ (popN a n).toList) :
    x ∈ a.toList := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    have := ih h
    rw [Array.toList_pop] at this
    exact List.dropLast_subset _ this

theorem hypsMatch_sound {σ : Subst C V} :
    ∀ {hs : List (Hyp C V)} {as : List (Expr C V)}, hypsMatch σ hs as = true →
      ∀ h ∈ hs, ∃ a ∈ as, h.expr.subst σ = a
  | [], [], _ => by simp
  | .float tc v :: hs, a :: as, hm => by
    simp only [hypsMatch, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨htc, hv⟩, hm⟩ := hm
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · refine ⟨a, List.mem_cons_self, ?_⟩
      cases a
      simp_all [Expr.subst]
    · obtain ⟨b, hb, e⟩ := hypsMatch_sound hm h hh
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩
  | .ess e :: hs, a :: as, hm => by
    simp only [hypsMatch, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨he, hm⟩ := hm
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact ⟨a, List.mem_cons_self, he⟩
    · obtain ⟨b, hb, e⟩ := hypsMatch_sound hm h hh
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩
  | [], _ :: _, hm => by simp [hypsMatch] at hm
  | _ :: _, [], hm => by cases ‹Hyp C V› <;> simp [hypsMatch] at hm

omit [DecidableEq C] in
theorem dvOk_sound {disj : V → V → Bool} {σ : Subst C V} {B F : Assertion C V}
    (hdisj : ∀ a b, disj a b = true → F.Disjoint a b) (h : dvOk disj σ B.dv = true) :
    B.DVSafe σ F.Disjoint := by
  intro x y hxy a ha b hb
  simp only [dvOk, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hne, hd⟩ := h (x, y) hxy a ha b hb
  exact ⟨hne, hdisj a b hd⟩

theorem apply_sound {Γ : Set (Assertion C V)} {F : Assertion C V} {disj : V → V → Bool}
    (hdisj : ∀ a b, disj a b = true → F.Disjoint a b) {label : String} {B : Assertion C V}
    (hB : B ∈ Γ) {s s' : State C V} (hs : s.Sound Γ F) (h : apply disj label B s = .ok s') :
    s'.Sound Γ F := by
  unfold apply at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hm
      split at h
      · rename_i hdv
        cases h
        set args := (s.stack.extract (s.stack.size - B.hyps.length) s.stack.size).toList
        set σ := substOf (floatBinding B.hyps args)
        have hargs : ∀ a ∈ args, Nonempty (Derivation Γ F a) := by
          intro a ha
          simp only [args, Array.toList_extract, List.extract_eq_take_drop] at ha
          exact hs.stack a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
        have hprem : ∀ e ∈ B.hypExprs, Nonempty (Derivation Γ F (e.subst σ)) := by
          intro e he
          simp only [Assertion.hypExprs, List.mem_map] at he
          obtain ⟨h, hh, rfl⟩ := he
          obtain ⟨a, ha, hsub⟩ := hypsMatch_sound hm h hh
          rw [hsub]
          exact hargs a ha
        refine ⟨?_, hs.saved⟩
        intro e he
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hs.stack e (mem_popN he)
        · exact ⟨Derivation.app B hB σ (fun e he => Classical.choice (hprem e he))
            (dvOk_sound hdisj hdv)⟩
      · cases h
    · cases h
  · cases h

theorem step_sound {Γ : Set (Assertion C V)} {F : Assertion C V} {disj : V → V → Bool}
    (hdisj : ∀ a b, disj a b = true → F.Disjoint a b) {s s' : State C V} {i : Instr C V}
    (hi : i.Valid Γ F) (hs : s.Sound Γ F) (h : step disj s i = .ok s') : s'.Sound Γ F := by
  cases i with
  | hyp e =>
    cases h
    refine ⟨?_, hs.saved⟩
    intro a ha
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hs.stack a ha
    · exact ⟨Derivation.hyp hi⟩
  | app label B => exact apply_sound hdisj hi hs h
  | save =>
    simp only [step] at h
    split at h
    · rename_i e he
      cases h
      refine ⟨hs.stack, ?_⟩
      intro a ha
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hs.saved a ha
      · exact hs.stack a (Array.mem_toList_iff.2 (Array.mem_of_back? he))
    · cases h
  | load n =>
    simp only [step] at h
    split at h
    · rename_i e he
      cases h
      refine ⟨?_, hs.saved⟩
      intro a ha
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hs.stack a ha
      · exact hs.saved a (Array.mem_toList_iff.2 (Array.mem_of_getElem? he))
    · cases h

theorem run_sound {Γ : Set (Assertion C V)} {F : Assertion C V} {disj : V → V → Bool}
    (hdisj : ∀ a b, disj a b = true → F.Disjoint a b) :
    ∀ {s s' : State C V} {is : List (Instr C V)}, (∀ i ∈ is, i.Valid Γ F) → s.Sound Γ F →
      run disj s is = .ok s' → s'.Sound Γ F
  | _, _, [], _, hs, h => by cases h; exact hs
  | s, s', i :: is, hv, hs, h => by
    simp only [run] at h
    split at h
    · rename_i s₁ h₁
      exact run_sound hdisj (fun j hj => hv j (List.mem_cons_of_mem _ hj))
        (step_sound hdisj (hv i List.mem_cons_self) hs h₁) h
    · cases h

/-- **Soundness of the proof machine.** -/
theorem verify_sound {Γ : Set (Assertion C V)} {F : Assertion C V} {disj : V → V → Bool}
    (hdisj : ∀ a b, disj a b = true → F.Disjoint a b) {is : List (Instr C V)}
    (hv : ∀ i ∈ is, i.Valid Γ F) {concl : Expr C V} (h : verify disj is concl = .ok ()) :
    Nonempty (Derivation Γ F concl) := by
  simp only [verify] at h
  split at h
  · rename_i s hs
    have sound := run_sound hdisj hv ⟨by simp, by simp⟩ hs
    simp only [finish] at h
    split at h
    · rename_i e he
      split at h
      · subst concl
        exact sound.stack e (by rw [he]; simp)
      · cases h
    · cases h
  · cases h

end Silmaril.Logic.Metamath.Verify
