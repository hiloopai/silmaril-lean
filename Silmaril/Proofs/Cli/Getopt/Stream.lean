module

public import Silmaril.Cli.Getopt.Stream.Defs

/-!
# Proofs: getopt as a stream of results

* `readClusterAll_ok`, `readClusterAll_error`, `readTokAll_ok`, `readTokAll_error`: one token,
  going on after errors, reads what `readTok` reads when it succeeds, and its first diagnostic
  is the error of `readTok` when it fails;
* **`parseAll_ok`**, **`parseAll_error`**: so for whole argument vectors;
* **`parseInOrder_permute`**: the in-order reading, its interleaving forgotten, is the GNU
  permuting reading.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Cli.Getopt

open Silmaril.Cli Silmaril.Cli.Getopt

/-! ## Events -/

@[simp] theorem ofOpts_nil : Event.ofOpts [] = [] := rfl

@[simp] theorem ofOpts_cons (p : String × Given) (ps : List (String × Given)) :
    Event.ofOpts (p :: ps) = .opt p.1 p.2 :: Event.ofOpts ps := rfl

@[simp] theorem opt?_operand (w : String) : (Event.operand w).opt? = none := rfl
@[simp] theorem operand?_operand (w : String) : (Event.operand w).operand? = some w := rfl

@[simp] theorem ofOpts_error (ps : List (String × Given)) :
    (Event.ofOpts ps).filterMap Event.error? = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [Event.error?] using ih

@[simp] theorem ofOpts_opt (ps : List (String × Given)) :
    (Event.ofOpts ps).filterMap Event.opt? = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [Event.opt?] using ih

@[simp] theorem ofOpts_operand (ps : List (String × Given)) :
    (Event.ofOpts ps).filterMap Event.operand? = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [Event.operand?] using ih

theorem errors_cons (es : List Event) (r : Report) :
    (r.cons es).errors = es.filterMap Event.error? ++ r.errors := by
  simp [Report.cons, Report.errors, List.filterMap_append]

theorem head_errors {es : List Event} {e : Error} (h : (es.filterMap Event.error?).head? = some e)
    (l : List Error) : (es.filterMap Event.error? ++ l).head? = some e := by
  cases hl : es.filterMap Event.error? with
  | nil => rw [hl] at h; cases h
  | cons a m => rw [hl] at h; simpa using h

/-! ## One token -/

theorem readClusterAll_ok {t : Table} {tok : String} {next : Option String} :
    ∀ {cs : List Char} {ps : List (String × Given)} {b : Bool},
      Getopt.readCluster t tok next cs = .ok (ps, b) →
      readClusterAll t tok next cs = (Event.ofOpts ps, b)
  | [], ps, b, h => by
    simp only [Getopt.readCluster, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | ch :: r, ps, b, h => by
    by_cases hw : (t.wLong && ch == 'W') = true
    · unfold readClusterAll; simp only [hw, ↓reduceIte]; rw [h]; rfl
    · have h' := h
      unfold Getopt.readCluster at h'
      simp only [Bool.not_eq_true] at hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte] at h'
      unfold readClusterAll
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      cases hf : findChar t ch with
      | none => simp [hf] at h'
      | some s =>
        simp only [hf] at h' ⊢
        cases ha : s.arg with
        | none =>
          simp only [ha] at h' ⊢
          cases hr : Getopt.readCluster t tok next r with
          | error e => simp [hr, Except.map] at h'
          | ok q =>
            obtain ⟨q1, q2⟩ := q
            simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            rw [readClusterAll_ok hr]
            rfl
        | optional => rw [h]; rfl
        | required => rw [h]; rfl

theorem readClusterAll_error {t : Table} {tok : String} {next : Option String} :
    ∀ {cs : List Char} {e : Error}, Getopt.readCluster t tok next cs = .error e →
      ((readClusterAll t tok next cs).1.filterMap Event.error?).head? = some e
  | [], e, h => by simp [Getopt.readCluster] at h
  | ch :: r, e, h => by
    by_cases hw : (t.wLong && ch == 'W') = true
    · unfold readClusterAll; simp only [hw, ↓reduceIte]; rw [h]; simp [Event.ofRead, Event.error?]
    · have h' := h
      unfold Getopt.readCluster at h'
      simp only [Bool.not_eq_true] at hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte] at h'
      unfold readClusterAll
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      cases hf : findChar t ch with
      | none =>
        simp only [hf, Except.error.injEq] at h'
        subst h'
        simp [Event.error?]
      | some s =>
        simp only [hf] at h' ⊢
        cases ha : s.arg with
        | none =>
          simp only [ha] at h' ⊢
          cases hr : Getopt.readCluster t tok next r with
          | error e' =>
            simp only [hr, Except.map, Except.error.injEq] at h'
            subst h'
            simpa [Event.error?, List.findSome?_cons] using readClusterAll_error hr
          | ok q => simp [hr, Except.map] at h'
        | optional => rw [h]; simp [Event.ofRead, Event.error?]
        | required => rw [h]; simp [Event.ofRead, Event.error?]

theorem readTokAll_ok {t : Table} {tok : String} {next : Option String}
    {ps : List (String × Given)} {b : Bool} (h : readTok t tok next = .ok (ps, b)) :
    readTokAll t tok next = (Event.ofOpts ps, b) := by
  unfold readTokAll
  have h' := h
  unfold readTok at h'
  cases hc : classify tok with
  | short n =>
    rw [hc] at h'
    cases hl : t.longOnly
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h' ⊢
      exact readClusterAll_ok h'
    · simp only [hl, ↓reduceIte] at h' ⊢
      rw [h']; rfl
  | dashdash => rw [h]; rfl
  | long n v => rw [h]; rfl
  | word w => rw [h]; rfl

theorem readTokAll_error {t : Table} {tok : String} {next : Option String} {e : Error}
    (h : readTok t tok next = .error e) :
    ((readTokAll t tok next).1.filterMap Event.error?).head? = some e := by
  unfold readTokAll
  have h' := h
  unfold readTok at h'
  cases hc : classify tok with
  | short n =>
    rw [hc] at h'
    cases hl : t.longOnly
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h' ⊢
      exact readClusterAll_error h'
    · simp only [hl, ↓reduceIte] at h' ⊢
      rw [h']; simp [Event.ofRead, Event.error?]
  | dashdash => rw [h]; simp [Event.ofRead, Event.error?]
  | long n v => rw [h]; simp [Event.ofRead, Event.error?]
  | word w => rw [h]; simp [Event.ofRead, Event.error?]

/-! ## The loop -/

/-- **Without a usage error the loop reads what `parse` reads.** -/
theorem parseAll_ok {t : Table} {ord : Order} :
    ∀ {argv : List String} {p : Parsed}, parse t ord argv = .ok p →
      parseAll t ord argv = Report.ofParsed p
  | [], p, h => by
    simp only [parse, Except.ok.injEq] at h; subst h; rfl
  | tok :: rest, p, h => by
    unfold parse at h
    unfold parseAll
    cases hc : classify tok with
    | dashdash =>
      simp only [hc, Except.ok.injEq] at h; subst h; rfl
    | word w =>
      simp only [hc] at h
      cases ord with
      | requireOrder => simp only [Except.ok.injEq] at h; subst h; rfl
      | permute =>
        cases hr : parse t .permute rest with
        | error e => simp [hr, Except.map] at h
        | ok q =>
          simp only [hr, Except.map, Except.ok.injEq] at h
          subst h
          simp only
          rw [parseAll_ok hr]
          rfl
    | long n v =>
      simp only [hc] at h
      cases hrt : readTok t tok rest.head? with
      | error e => simp [hrt] at h
      | ok q =>
        obtain ⟨ps, b⟩ := q
        simp only [readTokAll_ok hrt]
        simp only [hrt] at h
        cases b with
        | false =>
          cases hr : parse t ord rest with
          | error e => simp [hr, Except.map] at h
          | ok q =>
            simp only [hr, Except.map, Except.ok.injEq] at h
            subst h
            simp only
            rw [parseAll_ok hr]
            simp [Report.cons, Report.ofParsed, Event.ofOpts]
        | true =>
          cases rest with
          | nil => cases h
          | cons x rest' =>
            simp only at h ⊢
            cases hr : parse t ord rest' with
            | error e => simp [hr, Except.map] at h
            | ok q =>
              simp only [hr, Except.map, Except.ok.injEq] at h
              subst h
              rw [parseAll_ok hr]
              simp [Report.cons, Report.ofParsed, Event.ofOpts]
    | short n =>
      simp only [hc] at h
      cases hrt : readTok t tok rest.head? with
      | error e => simp [hrt] at h
      | ok q =>
        obtain ⟨ps, b⟩ := q
        simp only [readTokAll_ok hrt]
        simp only [hrt] at h
        cases b with
        | false =>
          cases hr : parse t ord rest with
          | error e => simp [hr, Except.map] at h
          | ok q =>
            simp only [hr, Except.map, Except.ok.injEq] at h
            subst h
            simp only
            rw [parseAll_ok hr]
            simp [Report.cons, Report.ofParsed, Event.ofOpts]
        | true =>
          cases rest with
          | nil => cases h
          | cons x rest' =>
            simp only at h ⊢
            cases hr : parse t ord rest' with
            | error e => simp [hr, Except.map] at h
            | ok q =>
              simp only [hr, Except.map, Except.ok.injEq] at h
              subst h
              rw [parseAll_ok hr]
              simp [Report.cons, Report.ofParsed, Event.ofOpts]

/-- The loop past an option token whose reading fails reports that error first. -/
theorem parseAll_tok_error {t : Table} {ord : Order} {tok : String} {rest : List String}
    {e : Error} (hc : classify tok ≠ .dashdash) (hw : ∀ w, classify tok ≠ .word w)
    (h : readTok t tok rest.head? = .error e) :
    (parseAll t ord (tok :: rest)).errors.head? = some e := by
  have he := readTokAll_error h
  unfold parseAll
  split
  · rename_i hc'; exact absurd hc' hc
  · rename_i w hc'; exact absurd hc' (hw w)
  · rcases hq : readTokAll t tok rest.head? with ⟨es, b⟩
    rw [hq] at he
    simp only at he
    cases b with
    | false => simp only; rw [errors_cons]; exact head_errors he _
    | true =>
      cases rest with
      | nil =>
        simp only [Report.errors, List.filterMap_append]
        exact head_errors he _
      | cons x rest' => simp only; rw [errors_cons]; exact head_errors he _

/-- **The first diagnostic of the loop is the error `parse` stops at.** -/
theorem parseAll_error {t : Table} {ord : Order} :
    ∀ {argv : List String} {e : Error}, parse t ord argv = .error e →
      (parseAll t ord argv).errors.head? = some e
  | [], e, h => by simp [parse] at h
  | tok :: rest, e, h => by
    have h0 := h
    unfold parse at h
    cases hc : classify tok with
    | dashdash => simp [hc] at h
    | word w =>
      simp only [hc] at h
      cases ord with
      | requireOrder => simp at h
      | permute =>
        cases hr : parse t .permute rest with
        | ok q => simp [hr, Except.map] at h
        | error e' =>
          simp only [hr, Except.map, Except.error.injEq] at h
          subst h
          unfold parseAll
          rw [hc]
          exact parseAll_error hr
    | long n v =>
      have hnd : classify tok ≠ .dashdash := by rw [hc]; simp
      have hnw : ∀ w, classify tok ≠ .word w := fun _ => by rw [hc]; simp
      simp only [hc] at h
      cases hrt : readTok t tok rest.head? with
      | error e' =>
        simp only [hrt, Except.error.injEq] at h
        subst h
        exact parseAll_tok_error hnd hnw hrt
      | ok q =>
        obtain ⟨ps, b⟩ := q
        simp only [hrt] at h
        unfold parseAll
        rw [hc]
        simp only [readTokAll_ok hrt]
        cases b with
        | false =>
          cases hr : parse t ord rest with
          | ok q => simp [hr, Except.map] at h
          | error e' =>
            simp only [hr, Except.map, Except.error.injEq] at h
            subst h
            simp only
            rw [errors_cons, ofOpts_error]
            exact parseAll_error hr
        | true =>
          cases rest with
          | nil =>
            simp only [Except.error.injEq] at h
            subst h
            simp [Report.errors, List.filterMap_append, Event.error?]
          | cons x rest' =>
            simp only at h ⊢
            cases hr : parse t ord rest' with
            | ok q => simp [hr, Except.map] at h
            | error e' =>
              simp only [hr, Except.map, Except.error.injEq] at h
              subst h
              rw [errors_cons, ofOpts_error]
              exact parseAll_error hr
    | short n =>
      have hnd : classify tok ≠ .dashdash := by rw [hc]; simp
      have hnw : ∀ w, classify tok ≠ .word w := fun _ => by rw [hc]; simp
      simp only [hc] at h
      cases hrt : readTok t tok rest.head? with
      | error e' =>
        simp only [hrt, Except.error.injEq] at h
        subst h
        exact parseAll_tok_error hnd hnw hrt
      | ok q =>
        obtain ⟨ps, b⟩ := q
        simp only [hrt] at h
        unfold parseAll
        rw [hc]
        simp only [readTokAll_ok hrt]
        cases b with
        | false =>
          cases hr : parse t ord rest with
          | ok q => simp [hr, Except.map] at h
          | error e' =>
            simp only [hr, Except.map, Except.error.injEq] at h
            subst h
            simp only
            rw [errors_cons, ofOpts_error]
            exact parseAll_error hr
        | true =>
          cases rest with
          | nil =>
            simp only [Except.error.injEq] at h
            subst h
            simp [Report.errors, List.filterMap_append, Event.error?]
          | cons x rest' =>
            simp only at h ⊢
            cases hr : parse t ord rest' with
            | ok q => simp [hr, Except.map] at h
            | error e' =>
              simp only [hr, Except.map, Except.error.injEq] at h
              subst h
              rw [errors_cons, ofOpts_error]
              exact parseAll_error hr

/-! ## Operands in order -/

/-- **The in-order reading, its interleaving forgotten, is the GNU permuting reading.** -/
theorem parseInOrder_permute {t : Table} :
    ∀ argv : List String, (parseInOrder t argv).map splitInOrder =
      (parse t .permute argv).map fun p => (p.opts, p.operands)
  | [] => rfl
  | tok :: rest => by
    unfold parseInOrder parse
    cases hc : classify tok with
    | dashdash => rfl
    | word w =>
      have ih := parseInOrder_permute (t := t) rest
      simp only
      cases h1 : parseInOrder t rest <;> cases h2 : parse t .permute rest <;>
        simp_all [Except.map, splitInOrder, List.filterMap_cons]
    | long n v =>
      simp only
      cases hrt : readTok t tok rest.head? with
      | error e => rfl
      | ok q =>
        obtain ⟨ps, b⟩ := q
        cases b with
        | false =>
          have ih := parseInOrder_permute (t := t) rest
          simp only
          cases h1 : parseInOrder t rest <;> cases h2 : parse t .permute rest <;>
            simp_all [Except.map, splitInOrder, List.filterMap_append]
        | true =>
          cases rest with
          | nil => rfl
          | cons x rest' =>
            have ih := parseInOrder_permute (t := t) rest'
            simp only
            cases h1 : parseInOrder t rest' <;> cases h2 : parse t .permute rest' <;>
              simp_all [Except.map, splitInOrder, List.filterMap_append]
    | short n =>
      simp only
      cases hrt : readTok t tok rest.head? with
      | error e => rfl
      | ok q =>
        obtain ⟨ps, b⟩ := q
        cases b with
        | false =>
          have ih := parseInOrder_permute (t := t) rest
          simp only
          cases h1 : parseInOrder t rest <;> cases h2 : parse t .permute rest <;>
            simp_all [Except.map, splitInOrder, List.filterMap_append]
        | true =>
          cases rest with
          | nil => rfl
          | cons x rest' =>
            have ih := parseInOrder_permute (t := t) rest'
            simp only
            cases h1 : parseInOrder t rest' <;> cases h2 : parse t .permute rest' <;>
              simp_all [Except.map, splitInOrder, List.filterMap_append]

end Silmaril.Proofs.Cli.Getopt
