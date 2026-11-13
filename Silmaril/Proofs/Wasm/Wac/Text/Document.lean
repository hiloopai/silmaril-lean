module

public import Silmaril.Proofs.Wasm.Wac.Text.Expr

/-!
# WAC text: statements and documents read back

`document_pr`: `Parse.document (Pr.document d) = some d` for well-formed `d`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

theorem importType_pr (n : Nat) (t : ImportType) (rest : Toks) (hw : Wf.importType t = true)
    (hl : (Pr.importType t).length < n) :
    Parse.importType n (Pr.importType t ++ sy ';' :: rest) = some (t, sy ';' :: rest) := by
  cases t with
  | package p =>
    simp [Pr.importType, Parse.importType, Pr.pkgPath, pkgPath_pr p _ (by simpa [Wf.importType] using hw)]
  | func f =>
    have h := funcType_pr n f (sy ';' :: rest) hw hl (by simp) (by simp)
    obtain ⟨a, ps, r⟩ := f
    cases a <;> simp_all [Pr.importType, Parse.importType, Pr.funcType]
  | interface items =>
    have h := inlineInterface_pr n items (sy ';' :: rest) (by simpa [Wf.importType] using hw) hl
    simp only [Pr.importType, Pr.inlineInterface, List.cons_append, List.append_assoc,
      List.nil_append] at h ⊢
    simp [Parse.importType, h]
  | ident id => simp [Pr.importType, Parse.importType]

theorem Pr.typeStatement_head (s : TypeStatement) : ∃ ds k l,
    Pr.typeStatement s = ⟨ds, .kw k⟩ :: l ∧ k ≠ .import ∧ k ≠ .let ∧ k ≠ .export := by
  cases s with
  | type d => cases d <;> exact ⟨_, _, _, rfl, by decide⟩
  | _ => exact ⟨_, _, _, rfl, by decide⟩

theorem externName_pr (x : ExternName) (rest : Toks) :
    Parse.externName (Pr.externName x :: rest) = some (x, rest) := by
  cases x <;> rfl

theorem import_pr (n : Nat) (ds : Docs) (id : String) (nm : Option ExternName) (t : ImportType)
    (rest : Toks) (hw : Wf.statement (.import_ ds id nm t) = true)
    (hl : (Pr.statement (.import_ ds id nm t)).length < n) :
    Parse.statement n (Pr.statement (.import_ ds id nm t) ++ rest) =
      some (.import_ ds id nm t, rest) := by
  have h := importType_pr n t rest (by simp [Wf.statement] at hw; exact hw.2)
    (by cases nm <;> simp [Pr.statement] at hl <;> omega)
  cases nm with
  | none => simp [Pr.statement, Parse.statement, Pr.first, h]
  | some x => simp [Pr.statement, Parse.statement, Pr.first, externName_pr, h]

theorem export_pr (n : Nat) (ds : Docs) (e : Expr) (o : ExportOptions) (rest : Toks)
    (hw : Wf.statement (.export_ ds e o) = true)
    (hl : 3 * (Pr.statement (.export_ ds e o)).length + 3 < n) :
    Parse.statement n (Pr.statement (.export_ ds e o) ++ rest) = some (.export_ ds e o, rest) := by
  have hw' : Wf.expr e = true := by simp [Wf.statement] at hw; exact hw.1.2
  have hle : 3 * (Pr.expr e).length + 2 < n := by
    simp only [Pr.statement, Pr.first, List.length_cons, List.length_append] at hl; omega
  cases o with
  | none =>
    have h := (exprIH n).1 e (sy ';' :: rest) hw' hle ⟨by simp, by simp⟩
    simp [Pr.statement, Parse.statement, Pr.first, h]
  | spread =>
    have h := (exprIH n).1 e (tk .ellipsis :: sy ';' :: rest) hw' hle ⟨by simp, by simp⟩
    simp [Pr.statement, Parse.statement, Pr.first, h]
  | rename x =>
    have h := (exprIH n).1 e (kw .as :: Pr.externName x :: sy ';' :: rest) hw' hle
      ⟨by simp, by simp⟩
    simp [Pr.statement, Parse.statement, Pr.first, h, externName_pr]

theorem statement_pr (n : Nat) (s : Statement) (rest : Toks) (hw : Wf.statement s = true)
    (hl : 3 * (Pr.statement s).length + 3 < n) :
    Parse.statement n (Pr.statement s ++ rest) = some (s, rest) := by
  cases s with
  | import_ ds id nm t => exact import_pr n ds id nm t rest hw (by omega)
  | type s =>
    have h := typeStatement_pr n s rest hw (by simp [Pr.statement] at hl; omega)
    obtain ⟨ds, k, l, he, h1, h2, h3⟩ := Pr.typeStatement_head s
    simp only [Pr.statement] at h ⊢
    rw [he] at h ⊢
    cases k <;> simp_all [Parse.statement]
  | let_ ds id e =>
    have h := (exprIH n).1 e (sy ';' :: rest) (by simp [Wf.statement] at hw; exact hw.2)
      (by simp only [Pr.statement, Pr.first, List.length_cons, List.length_append] at hl; omega)
      ⟨by simp, by simp⟩
    simp [Pr.statement, Parse.statement, Pr.first, h]
  | export_ ds e o => exact export_pr n ds e o rest hw hl

theorem Pr.statement_ne (s : Statement) : Pr.statement s ≠ [] := by
  cases s with
  | type s => obtain ⟨ds, k, l, he, -⟩ := Pr.typeStatement_head s; simp [Pr.statement, he]
  | _ => simp [Pr.statement]

theorem statements_pr (n : Nat) : ∀ (ss : List Statement) (k : Nat),
    (∀ s ∈ ss, Wf.statement s = true) → ss.length < k →
    3 * (ss.flatMap Pr.statement).length + 3 < n →
    Parse.statements n k (ss.flatMap Pr.statement) = some ss
  | [], k, _, _, _ => by cases k <;> simp [Parse.statements]
  | s :: ss, k + 1, hw, hk, hl => by
    have h := statement_pr n s (ss.flatMap Pr.statement) (hw s (by simp))
      (by simp only [List.flatMap_cons, List.length_append] at hl; omega)
    have ih := statements_pr n ss k (fun x hx => hw x (by simp [hx])) (by simp at hk; omega)
      (by simp only [List.flatMap_cons, List.length_append] at hl; omega)
    obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (Pr.statement_ne s)
    simp only [List.flatMap_cons] at h ⊢
    rw [hx] at h ⊢
    simp only [List.cons_append] at h ⊢
    simp [Parse.statements, h, ih]

theorem document_pr (d : Document) (hw : wf d = true) :
    Parse.document (Pr.document d) = some d := by
  obtain ⟨ds, pkg, tg, ss⟩ := d
  have hw' := hw
  simp only [wf, Bool.and_eq_true, List.all_eq_true] at hw'
  obtain ⟨⟨⟨-, hp⟩, ht⟩, hss⟩ := hw'
  have hlen := length_le_flatMap Pr.statement Pr.statement_ne ss
  unfold Parse.document
  generalize hN : 3 * (Pr.document ⟨ds, pkg, tg, ss⟩).length + 3 = N
  have hN' : 3 * (ss.flatMap Pr.statement).length + 3 < N := by
    cases tg <;> simp only [Pr.document, Pr.first, List.length_cons, List.length_append] at hN <;>
      omega
  have hs := statements_pr N ss N hss (by omega) hN'
  cases tg with
  | none => simp [Pr.document, Pr.first, docsOf, pkgName_pr pkg _ hp, hs]
  | some p =>
    simp [Pr.document, Pr.first, docsOf, pkgName_pr pkg _ hp, Pr.pkgPath,
      pkgPath_pr p _ (by simpa using ht), hs]

end Silmaril.Wasm.Wac.Text
