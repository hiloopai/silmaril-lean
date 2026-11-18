module

public import Silmaril.Machine.Vex.Validate.Semantics.Defs

public section

namespace Silmaril.Machine.Vex.Proofs

open AMD64Scalar

theorem boundaryBeh {input output : Type} (run : input → Option output) (entry : input)
    (outcome : Behaviour.Outcome output Empty Empty) :
    (boundarySem run).Beh entry outcome ↔ ∃ value, run entry = some value ∧ outcome = .returned value := by
  rw [Behaviour.Semantics.beh_of_stop (fun _ step => step)]
  change ((∃ value, run entry = some value ∧ outcome = .returned value) ∧ outcome ≠ .diverges) ↔ _
  constructor
  · exact And.left
  · rintro ⟨value, evaluated, rfl⟩
    exact ⟨⟨value, evaluated, rfl⟩, by simp⟩

private theorem flagBit (value : Bool) : (flagWord value).getLsbD 0 = value := by
  cases value <;> decide

theorem selectBit (input : Input) (index : Nat) (term : Term) :
    (term.selectBit index).eval input = flagWord ((term.eval input).getLsbD index) := by
  cases term with
  | eq lhs rhs =>
    change (if index = 0 then Term.eq lhs rhs else .bit index (.eq lhs rhs)).eval input = _
    by_cases equal : index = 0
    · subst index
      rw [ite_eq_left rfl]
      exact congrArg flagWord (flagBit (lhs.eval input == rhs.eval input)).symm
    · rw [ite_eq_right equal]; rfl
  | initialZF =>
    change (if index = 0 then Term.initialZF else .bit index .initialZF).eval input = _
    by_cases equal : index = 0
    · subst index
      rw [ite_eq_left rfl]
      exact congrArg flagWord (flagBit input.zf).symm
    · rw [ite_eq_right equal]; rfl
  | initialFlags =>
    change (if index = 6 then Term.initialZF else .bit index .initialFlags).eval input = _
    by_cases equal : index = 6
    · subst index
      rw [ite_eq_left rfl]
      change flagWord input.zf = flagWord ((if input.zf then (64 : Word) else 0).getLsbD 6)
      generalize input.zf = value
      cases value <;> decide
    · rw [ite_eq_right equal]; rfl
  | const | reg | add | bit => rfl

private def evaluate (input : Input) (state : State Term Term) : Input :=
  ⟨state.rax.eval input, state.rdi.eval input, state.rsi.eval input, state.zf.test input, state.rip⟩

private theorem testEq (input : Input) (lhs rhs : Term) :
    (Term.eq lhs rhs).test input = (lhs.eval input == rhs.eval input) := by
  exact flagBit (lhs.eval input == rhs.eval input)

private theorem evaluateStep (input : Input) (state : State Term Term) (op : X86.Op) :
    evaluate input (op.step X86.symbolic state) = op.step X86.concrete (evaluate input state) := by
  cases op <;> simp [X86.Op.step, X86.symbolic, X86.concrete, evaluate, testEq, Term.eval]

private theorem evaluateBody (input : Input) (state : State Term Term) (body : List X86.Op) :
    evaluate input (body.foldl (X86.Op.step X86.symbolic) state) =
    body.foldl (X86.Op.step X86.concrete) (evaluate input state) := by
  induction body generalizing state with
  | nil => rfl
  | cons op rest ih => simp only [List.foldl_cons, ih, evaluateStep]

private theorem evaluateExit (input : Input) (zf : Term) (exit : X86.Exit) :
    (exit.next zf).map (Term.test input) = exit.next (zf.test input) := by
  cases exit with
  | jmp => rfl
  | jcc zero => cases zero <;> rfl

private theorem evaluateEntry (input : Input) : evaluate input (X86.entry input.rip) = input := by
  cases input with
  | mk rax rdi rsi zf rip => cases zf <;> simp [evaluate, X86.entry, Term.eval, Term.test, flagWord, State.read]

private theorem evaluatePlan (input : Input) (state : State Term Term) (exit : X86.Exit) :
    (Plan.mk state.rax state.rdi state.rsi state.zf (exit.next state.zf)).eval input =
      { evaluate input state with rip := (exit.next (evaluate input state).zf).target } := by
  simp [Plan.eval, evaluateExit, evaluate]

theorem x86Lower (block : X86.Block) (input : Input) :
    (block.lower input.rip).eval input = block.run input := by
  unfold X86.Block.lower X86.Block.run
  rw [evaluatePlan, evaluateBody, evaluateEntry]

theorem validateCertifies {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    Certificate pc bytes raw pair := by
  cases hd : X86.decode pc bytes with
  | error => simp [validate, hd] at accepted
  | ok source =>
    cases hc : check raw with
    | error => simp [validate, hd, hc] at accepted
    | ok target =>
      by_cases ha : target.address = pc
      · by_cases hm : source.marks = target.code.marks
        · cases hl : target.lower with
          | error => simp [validate, hd, hc, ha, hm, hl] at accepted
          | ok plan =>
            by_cases hp : source.lower pc = plan
            · simp [validate, hd, hc, ha, hm, hl, hp] at accepted
              cases accepted
              exact ⟨hd, hc, ⟨ha, hm.symm, by simpa only [hp] using hl⟩⟩
            · simp [validate, hd, hc, ha, hm, hl, hp] at accepted
        · simp [validate, hd, hc, ha, hm] at accepted
      · simp [validate, hd, hc, ha] at accepted

theorem translationRuns {pc : Word} {source : X86.Block} {target : Block}
    (related : Translates pc source target) (input : Input) (entry : input.rip = pc) :
    target.run input = .ok (source.run input) := by
  simp only [Block.run, related.plan, Except.map, ← entry, x86Lower]

theorem translationBeh {pc : Word} {source : X86.Block} {target : Block}
    (related : Translates pc source target) {srcInput tgtInput : Input}
    (initial : Initial pc srcInput tgtInput) (outcome : Behaviour.Outcome Input Empty Empty) :
    (targetSem target).Beh tgtInput outcome ↔ outcome = .returned (source.run srcInput) := by
  rcases initial with ⟨rfl, entry⟩
  unfold targetSem
  rw [boundaryBeh, translationRuns related srcInput entry]
  constructor
  · rintro ⟨value, evaluated, rfl⟩
    cases evaluated
    rfl
  · intro returned
    exact ⟨_, rfl, returned⟩

theorem translationSound (pc : Word) :
    Translation.Sound (Translates pc) .targetRefinesSource .strict sourceSem targetSem
      (fun _ _ => Initial pc) (fun _ _ _ _ => observations) := by
  intro source target related tgtInput srcInput initial _ outcome behavior
  have returned := (translationBeh related initial outcome).mp behavior
  subst outcome
  exact ⟨_, (boundaryBeh (fun input => some (source.run input)) srcInput _).mpr ⟨_, rfl, rfl⟩,
    rfl, rfl⟩

theorem wordErasure {ctx : Scope} (value : Word) :
    checkExpr ctx ((Expr.word (ctx := ctx) value).erase) = .ok ⟨.i64, Expr.word value⟩ := by
  have checked : checkWord value.toNat = .ok value := by simp [checkWord, value.isLt]
  let wrap (result : Word) : Except Error (Σ ty, Expr ctx ty) := .ok ⟨.i64, .word result⟩
  change (checkWord value.toNat >>= wrap) = _
  rw [checked]
  rfl

end Silmaril.Machine.Vex.Proofs
