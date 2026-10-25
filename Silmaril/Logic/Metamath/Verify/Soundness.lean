module

public import Silmaril.Logic.Metamath.Verify.Check

@[expose] public section

/-!
# Soundness of the checker

If `check src = .ok db`, then `db` is sound (`check_sound`): every assertion
is well formed and every theorem is derivable from the assertions before it.
The proof follows the checker. Frames pass a decidable well-formedness test
(`wfCheck_sound`). Proof labels resolve to hypotheses of the extended frame or
to earlier assertions (`resolve_valid`), so every decoded instruction is
valid, and the proof machine is sound (`verify_sound`). The label index of the
checked assertions only points into the database (`Core.Inv`).

End to end (`check_provable`): every `$p` statement of an accepted source is
recorded, with its label and conclusion, as a well-formed theorem derivable
from the assertions before it. Given cut admissibility, it is derivable from
the `$a` statements before it alone (`check_provable_axioms`).
-/

namespace Silmaril.Logic.Metamath.Verify

open Std Text

/-! ## Helpers -/

theorem nodupAux_sound {α : Type} [BEq α] [Hashable α] [LawfulBEq α] :
    ∀ {seen : HashSet α} {l : List α}, nodupAux seen l = true →
      l.Nodup ∧ ∀ a ∈ l, seen.contains a = false
  | _, [], _ => ⟨List.nodup_nil, by simp⟩
  | seen, a :: l, h => by
    simp only [nodupAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨hl, hs⟩ := nodupAux_sound h
    have hs' : ∀ b ∈ l, a ≠ b ∧ seen.contains b = false := by
      intro b hb
      have := hs b hb
      rw [HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this
      exact this
    refine ⟨List.nodup_cons.2 ⟨fun hal => (hs' a hal).1 rfl, hl⟩, ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact (hs' b hb).2

theorem mem_floats {C V : Type} {A : Assertion C V} {tc : C} {v : V} :
    (tc, v) ∈ A.floats ↔ Hyp.float tc v ∈ A.hyps := by
  simp only [Assertion.floats, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

theorem wfCheck_sound {A : MAssertion} (h : wfCheck A = true) : A.WellFormed := by
  simp only [wfCheck, Bool.and_eq_true, List.all_eq_true, HashSet.contains_ofList,
    List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hv, hn⟩, hd⟩ := h
  refine ⟨fun v hv' => ?_, (nodupAux_sound hn).1, fun x y hxy => hd (x, y) hxy⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hv v hv')
  exact ⟨p.1, mem_floats.1 hp⟩

theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {b : β}, l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => by simp at h
  | (k', b') :: l, k, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      rw [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem disjTest_sound {F : MAssertion} {a b : String} (h : disjTest F a b = true) :
    F.Disjoint a b := by
  simp only [disjTest, Bool.or_eq_true, HashSet.contains_ofList, List.contains_iff_mem] at h
  exact h

/-! ## Proofs -/

section Proofs

variable {Γ : Set MAssertion} {asserts : HashMap String MAssertion} {sc : Scope}
  {A : MAssertion} {mand : List (String × MHyp)} {opt : List (String × String × String)}
  {hopt : ∀ p ∈ opt, p.2.2 ∉ A.allVars} {hnd : (opt.map fun p => p.2.2).Nodup}

theorem mem_hypExprs_extend {D : Dummies A} {e : MExpr} (h : e ∈ A.hypExprs) :
    e ∈ (A.extend D).hypExprs := by
  simp only [Assertion.hypExprs, Assertion.extend, List.map_append, List.mem_append] at h ⊢
  exact Or.inl h

theorem resolve_valid (hasserts : ∀ (l : String) B, asserts[l]? = some B → B ∈ Γ)
    (hmand : mand.map Prod.snd = A.hyps) {l : String} {i : Instr String String}
    (h : resolve asserts mand opt l = .ok i) :
    i.Valid Γ (A.extend (mkDummies sc A opt hopt hnd)) := by
  unfold resolve at h
  split at h
  · rename_i B hB
    cases h
    exact hasserts l B hB
  · split at h
    · rename_i hy hhy
      cases h
      apply mem_hypExprs_extend
      simp only [Assertion.hypExprs, ← hmand, List.map_map, List.mem_map]
      exact ⟨_, mem_of_lookup_eq_some hhy, rfl⟩
    · split at h
      · rename_i p hp
        cases h
        simp only [Instr.Valid, Assertion.hypExprs, Assertion.extend, mkDummies,
          List.map_append, List.map_map, List.mem_append, List.mem_map, Function.comp_apply]
        exact Or.inr ⟨(l, p), mem_of_lookup_eq_some hp, rfl⟩
      · cases h

theorem resolveSteps_valid {F : MAssertion} {r : String → Except ProofError (Instr String String)}
    (hr : ∀ l i, r l = .ok i → i.Valid Γ F) :
    ∀ {ls : List String} {out res : Array (Instr String String)},
      (∀ i ∈ out.toList, i.Valid Γ F) → resolveSteps r ls out = .ok res →
      ∀ i ∈ res.toList, i.Valid Γ F
  | [], _, _, hout, h => by cases h; exact hout
  | l :: ls, out, res, hout, h => by
    simp only [resolveSteps] at h
    split at h
    · cases h
    · split at h
      · rename_i i hi
        refine resolveSteps_valid hr ?_ h
        intro j hj
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact hout j hj
        · exact hr l _ hi
      · cases h

theorem resolveList_valid {F : MAssertion} {r : String → Except ProofError (Instr String String)}
    (hr : ∀ l i, r l = .ok i → i.Valid Γ F) :
    ∀ {ls : List String} {out res : Array (Instr String String)},
      (∀ i ∈ out.toList, i.Valid Γ F) → resolveList r mand ls out = .ok res →
      ∀ i ∈ res.toList, i.Valid Γ F
  | [], _, _, hout, h => by cases h; exact hout
  | l :: ls, out, res, hout, h => by
    simp only [resolveList] at h
    split at h
    · cases h
    · split at h
      · rename_i i hi
        refine resolveList_valid hr ?_ h
        intro j hj
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact hout j hj
        · exact hr l _ hi
      · cases h

theorem instrs_valid {F : MAssertion} {r : String → Except ProofError (Instr String String)}
    (hr : ∀ l i, r l = .ok i → i.Valid Γ F) (hA : ∀ e ∈ A.hypExprs, e ∈ F.hypExprs)
    {pf : ProofText} {is : List (Instr String String)} (h : instrs r A mand pf = .ok is) :
    ∀ i ∈ is, i.Valid Γ F := by
  cases pf with
  | normal steps =>
    simp only [instrs] at h
    split at h
    · rename_i out hout
      cases h
      exact resolveSteps_valid hr (by simp) hout
    · cases h
  | compressed labels letters =>
    simp only [instrs] at h
    split at h
    · rename_i list hlist
      refine decode_valid (fun e he => hA e (by simpa using he)) ?_ h
      exact resolveList_valid hr (by simp) hlist
    · cases h

/-- An accepted proof makes its assertion derivable. -/
theorem runProof_sound (hasserts : ∀ (l : String) B, asserts[l]? = some B → B ∈ Γ)
    (hmand : mand.map Prod.snd = A.hyps) {pf : ProofText}
    (h : runProof asserts sc A mand pf = .ok ()) : Derivable Γ A := by
  unfold runProof at h
  dsimp only at h
  split at h
  · rename_i is his
    refine derivable_iff.2 ⟨_, verify_sound (fun _ _ => disjTest_sound) ?_ h⟩
    exact instrs_valid (fun l i hi => resolve_valid hasserts hmand hi)
      (fun e he => mem_hypExprs_extend he) his
  · cases h

theorem proveTheorem_sound (hasserts : ∀ (l : String) B, asserts[l]? = some B → B ∈ Γ)
    (hmand : mand.map Prod.snd = A.hyps) {label : String} {pf : ProofText}
    (h : proveTheorem asserts sc label A mand pf = .ok ()) : Derivable Γ A := by
  unfold proveTheorem at h
  split at h
  · rename_i hr
    exact runProof_sound hasserts hmand hr
  · cases h
  · cases h

end Proofs

/-! ## The checker -/

/-- The invariant of the checked assertions: the database is sound and the
label index only points into it. -/
structure Core.Inv (c : Core) : Prop where
  sound : c.db.Sound
  asserts : ∀ (l : String) B, c.asserts[l]? = some B → B ∈ c.db.before c.db.entries.size

theorem Core.inv_empty : Core.Inv {} :=
  ⟨Database.sound_empty, fun l B h => by simp at h⟩

theorem Core.Inv.add {c : Core} (hc : c.Inv) {l : String} {k : Kind} {A : MAssertion}
    (wf : A.WellFormed) (hd : k = .theorem → Derivable (c.db.before c.db.entries.size) A) :
    (c.add l k A).Inv := by
  refine ⟨hc.sound.push wf hd, fun l' B h => ?_⟩
  simp only [Core.add, HashMap.getElem?_insert, beq_iff_eq] at h ⊢
  split at h
  · cases h
    exact Database.mem_before_push c.db ⟨l, k, A⟩
  · exact Database.before_subset_push c.db _ (hc.asserts l' B h)

namespace Checker

theorem addAssertion_inv {s s' : Checker} (hs : s.core.Inv) {l tc : String}
    {body : List String} {pf : Option ProofText} (h : s.addAssertion l tc body pf = .ok s') :
    s'.core.Inv := by
  unfold addAssertion at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · rename_i hwf
        have wf := wfCheck_sound hwf
        split at h
        · cases h
          exact hs.add wf (fun h => nomatch h)
        · split at h
          · rename_i hp
            cases h
            exact hs.add wf fun _ => proveTheorem_sound hs.asserts rfl hp
          · cases h
      · cases h

theorem step_inv {s s' : Checker} (hs : s.core.Inv) {st : Stmt} (h : s.step st = .ok s') :
    s'.core.Inv := by
  cases st with
  | «axiom» l tc body => simp only [step] at h; exact addAssertion_inv hs h
  | provable l tc body pf => simp only [step] at h; exact addAssertion_inv hs h
  | _ =>
    simp only [step] at h
    split at h
    · cases h; exact hs
    · cases h

theorem run_inv : ∀ {s s' : Checker} {sts : List Stmt}, s.core.Inv → run s sts = .ok s' →
    s'.core.Inv
  | _, _, [], hs, h => by cases h; exact hs
  | s, s', st :: sts, hs, h => by
    simp only [run] at h
    split at h
    · rename_i s₁ h₁
      exact run_inv (step_inv hs h₁) h
    · cases h

end Checker

/-- **Soundness of the checker.** An accepted database is sound: each of its
assertions is well formed, and each theorem is derivable from the assertions
(axioms and theorems) before it. -/
theorem check_sound {src : Source} {db : Database String String} (h : check src = .ok db) :
    db.Sound := by
  simp only [check] at h
  split at h
  · rename_i s hs
    split at h
    · cases h
      exact (Checker.run_inv Core.inv_empty hs).sound
    · cases h
  · cases h

/-! ## Statements of the source -/

/-- The token of a math symbol. -/
def symToken : Sym String String → String
  | .const c => c
  | .var v => v

/-- The database has an entry of kind `k`, label `l`, and conclusion with
typecode `tc` and math string `body` (as tokens). -/
def Database.Records (db : Database String String) (k : Kind) (l tc : String)
    (body : List String) : Prop :=
  ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧ db.entries[i].kind = k ∧
    db.entries[i].assertion.concl.tc = tc ∧ db.entries[i].assertion.concl.body.map symToken = body

/-- The database records the assertion statement `st`. -/
def Database.RecordsStmt (db : Database String String) : Stmt → Prop
  | .axiom l tc body => db.Records .axiom l tc body
  | .provable l tc body _ => db.Records .theorem l tc body
  | _ => True

/-- `db'` extends `db`. -/
def Database.Extends {C V : Type} (db db' : Database C V) : Prop :=
  ∃ h : db.entries.size ≤ db'.entries.size,
    ∀ i (hi : i < db.entries.size), db'.entries[i] = db.entries[i]

theorem Database.Extends.refl {C V : Type} (db : Database C V) : db.Extends db :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem Database.Extends.trans {C V : Type} {db₁ db₂ db₃ : Database C V} (h₁ : db₁.Extends db₂)
    (h₂ : db₂.Extends db₃) : db₁.Extends db₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi => by rw [h₂.2 i (by have := h₁.1; omega), h₁.2 i hi]⟩

theorem Database.extends_push {C V : Type} (db : Database C V) (e : Entry C V) :
    db.Extends (db.push e) :=
  ⟨by simp, fun i hi => by simp [Array.getElem_push_lt hi]⟩

theorem Database.RecordsStmt.mono {db db' : Database String String} (h : db.Extends db')
    {st : Stmt} (hst : db.RecordsStmt st) : db'.RecordsStmt st := by
  have key : ∀ {k l tc body}, db.Records k l tc body → db'.Records k l tc body := by
    rintro k l tc body ⟨i, hi, h1, h2, h3, h4⟩
    exact ⟨i, by have := h.1; omega, by rw [h.2 i hi]; exact ⟨h1, h2, h3, h4⟩⟩
  cases st <;> first | trivial | exact key hst

theorem Env.mkBody_ok {env : Env} {l : String} :
    ∀ {ss : List String} {out res : Array (Sym String String)}, env.mkBody l ss out = .ok res →
      res.toList.map symToken = out.toList.map symToken ++ ss
  | [], _, _, h => by cases h; simp
  | s :: ss, out, res, h => by
    simp only [Env.mkBody] at h
    split at h
    · rename_i x hx
      rw [Env.mkBody_ok h]
      have : symToken x = s := by
        simp only [Env.mkSym] at hx
        split at hx
        · cases hx; rfl
        · split at hx
          · split at hx
            · cases hx; rfl
            · cases hx
          · cases hx
      simp [this]
    · cases h

theorem Env.mkExpr_ok {env : Env} {l tc : String} {body : List String} {e : MExpr}
    (h : env.mkExpr l tc body = .ok e) : e.tc = tc ∧ e.body.map symToken = body := by
  simp only [Env.mkExpr] at h
  split at h
  · split at h
    · rename_i out hout
      cases h
      simpa using Env.mkBody_ok hout
    · cases h
  · cases h

namespace Checker

theorem addAssertion_records {s s' : Checker} {l tc : String} {body : List String}
    {pf : Option ProofText} (h : s.addAssertion l tc body pf = .ok s') :
    s.core.db.Extends s'.core.db ∧
      s'.core.db.Records (if pf.isSome then .theorem else .axiom) l tc body := by
  unfold addAssertion at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i env _ e he
      have ⟨htc, hbody⟩ := Env.mkExpr_ok he
      dsimp only at h
      split at h
      · have hrec : ∀ k A, A.concl = e →
            (s.core.add l k A).db.Records k l tc body ∧
              s.core.db.Extends (s.core.add l k A).db := by
          intro k A hA
          refine ⟨⟨s.core.db.entries.size, by simp [Core.add], ?_⟩, Database.extends_push _ _⟩
          simp [Core.add, hA, htc, hbody]
        split at h
        · cases h
          exact (hrec .axiom _ rfl).symm
        · split at h
          · cases h
            exact (hrec .theorem _ rfl).symm
          · cases h
      · cases h

theorem step_records {s s' : Checker} {st : Stmt} (h : s.step st = .ok s') :
    s.core.db.Extends s'.core.db ∧ s'.core.db.RecordsStmt st := by
  cases st with
  | «axiom» l tc body =>
    simp only [step] at h
    exact addAssertion_records h
  | provable l tc body pf =>
    simp only [step] at h
    exact addAssertion_records h
  | _ =>
    simp only [step] at h
    split at h
    · cases h
      exact ⟨Database.Extends.refl _, trivial⟩
    · cases h

theorem run_records : ∀ {s s' : Checker} {sts : List Stmt}, run s sts = .ok s' →
    s.core.db.Extends s'.core.db ∧ ∀ st ∈ sts, s'.core.db.RecordsStmt st
  | _, _, [], h => by cases h; exact ⟨Database.Extends.refl _, by simp⟩
  | s, s', st :: sts, h => by
    simp only [run] at h
    split at h
    · rename_i s₁ h₁
      obtain ⟨e₁, r₁⟩ := step_records h₁
      obtain ⟨e₂, r₂⟩ := run_records h
      refine ⟨e₁.trans e₂, ?_⟩
      intro st' hst'
      rcases List.mem_cons.1 hst' with rfl | hst'
      · exact r₁.mono e₂
      · exact r₂ st' hst'
    · cases h

end Checker

theorem check_records {src : Source} {db : Database String String} (h : check src = .ok db)
    {st : Stmt} (hst : st ∈ src) : db.RecordsStmt st := by
  simp only [check] at h
  split at h
  · rename_i s hs
    split at h
    · cases h
      exact (Checker.run_records hs).2 st hst
    · cases h
  · cases h

/-- **End-to-end soundness.** If the checker accepts a source, then every `$p`
statement `l $p tc body $= … $.` of it is recorded as a well-formed theorem
with label `l` and conclusion `tc body`, derivable from the assertions
(axioms and theorems) before it. -/
theorem check_provable {src : Source} {db : Database String String} (h : check src = .ok db)
    {l tc : String} {body : List String} {pf : ProofText}
    (hst : Stmt.provable l tc body pf ∈ src) :
    ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧
      db.entries[i].assertion.concl.tc = tc ∧
      db.entries[i].assertion.concl.body.map symToken = body ∧
      db.entries[i].assertion.WellFormed ∧
      Derivable (db.before i) db.entries[i].assertion := by
  obtain ⟨i, hi, h1, h2, h3, h4⟩ := check_records h hst
  have hdb := check_sound h
  exact ⟨i, hi, h1, h3, h4, hdb.wellFormed i hi, hdb.derivable i hi h2⟩

/-- **End-to-end soundness from axioms.** With cut admissible, every `$p`
statement of an accepted source is derivable from the `$a` statements before
it. -/
theorem check_provable_axioms (hcut : CutAdmissible String String) {src : Source}
    {db : Database String String} (h : check src = .ok db) {l tc : String}
    {body : List String} {pf : ProofText} (hst : Stmt.provable l tc body pf ∈ src) :
    ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧
      db.entries[i].assertion.concl.tc = tc ∧
      db.entries[i].assertion.concl.body.map symToken = body ∧
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion := by
  obtain ⟨i, hi, h1, h2, h3, h4⟩ := check_records h hst
  exact ⟨i, hi, h1, h3, h4, (check_sound h).derivable_axioms hcut i hi h2⟩

end Silmaril.Logic.Metamath.Verify
