module

public import Silmaril.Wasm.Validation.Check.Instrs

@[expose] public section

/-! # Completeness of the sequence checker (`checkBody?`, `checkExpr?`)

Given a complete oracle for the non-recursive instructions (`DirectComplete`) and
a complete type-validity oracle (`TyOkOracleComplete`), `checkSeq` accepts every typed
instruction sequence, in a well-formed context without `RECS`:
`checkBody?_complete`, `checkExpr?_complete`.

The key lemma is the mutual `SeqComplete.checkInstr_complete` /
`SeqComplete.checkSeq_complete`. The invariant of `checkSeq_complete` is that the
*virtual* stack `BOT^K ++ s` (with `K = 0` outside polymorphic mode) is a subtype
of the declared input of the remaining sequence. The finite padding used by the
checker in polymorphic mode (`padFor`, `arityBound`) covers every instruction's
operands beyond the arbitrary prefix of stack-polymorphic instructions
(`arity_nonpoly`, `arity_poly`).
-/

namespace Silmaril.Wasm.Validation

open CheckInstrs

/-- Completeness of `directStep` (for non-block instructions, excluding implicit
`select` on two `BOT` operands). -/
def DirectComplete (atom? : AtomOracle) (tyOk : TyOkOracle) : Prop :=
  ∀ (C : Context) (S : List CValType) (i : Instr) (t₁ t₂ : List CValType) (xs : List Nat),
    C.Wf → C.recs = [] →
    (∀ bt b, i ≠ .block bt b) → (∀ bt b, i ≠ .loop bt b) → (∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) →
    (∀ bt cs b, i ≠ .tryTable bt cs b) →
    ¬ (i = .select none ∧ ∃ S₀ c, S = S₀ ++ [.botv, .botv, c]) →
    InstrOk C i ⟨t₁, xs, t₂⟩ → ResultOk C.toTypeCtx S → t₁.length ≤ S.length →
    ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁ →
    ∃ r, directStep atom? tyOk C S i = some r ∧
      (match r with
        | .normal n xs' out => n = t₁.length ∧ xs' = xs ∧ ResultOk C.toTypeCtx out ∧
            ResultSub C.toTypeCtx out t₂
        | .poly t' => t'.length ≤ t₁.length)

/-- Completeness of the type-validity oracle. -/
def TyOkOracleComplete (tyOk : TyOkOracle) : Prop :=
  ∀ (Δ : TypeCtx) (k : TKind) (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true

namespace SeqComplete

variable {atom? : AtomOracle} {tyOk : TyOkOracle}

/-! ## Small checkers -/

theorem resSub_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {a b : List CValType}
    (h : ResultSub Δ a b) (ha : ResultOk Δ a) (hb : ResultOk Δ b) : resSub Δ a b = true :=
  Sub.check_complete hΔ hr ((ResultSub.iff_sub Δ a b).1 h) (TyOk.ofList a ha) (TyOk.ofList b hb)

theorem resOk_complete (hT : TyOkOracleComplete tyOk) {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = [])
    {ts : List CValType} (h : ResultOk Δ ts) : resOk tyOk Δ ts = true :=
  List.all_eq_true.2 fun t ht => hT Δ _ t hΔ hr (h t ht)

theorem localsOk_complete {C : Context} {xs : List Nat}
    (h : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) : localsOk C xs = true :=
  List.all_eq_true.2 fun x hx => Option.isSome_iff_exists.2 (h x hx)

theorem topSub_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {S t₁ : List CValType}
    (hl : t₁.length ≤ S.length) (hs : ResultSub Δ (S.drop (S.length - t₁.length)) t₁)
    (hS : ResultOk Δ S) (ht : ResultOk Δ t₁) : topSub Δ S t₁ = true := by
  simp only [topSub, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hl, resSub_complete hΔ hr hs (hS.drop' _) ht⟩

theorem stepA_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {S t₁ : List CValType}
    {xs : List Nat} {out : List CValType}
    (hl : t₁.length ≤ S.length) (hs : ResultSub Δ (S.drop (S.length - t₁.length)) t₁)
    (hS : ResultOk Δ S) (ht : ResultOk Δ t₁) :
    stepA Δ S t₁ xs out = some (.normal t₁.length xs out) := by
  simp [stepA, topSub_complete hΔ hr hl hs hS ht]

theorem stepA_eq {Δ : TypeCtx} {S t₁ : List CValType} {xs : List Nat} {out : List CValType}
    {r : StepRes} (h : stepA Δ S t₁ xs out = some r) : r = .normal t₁.length xs out := by
  unfold stepA at h
  split at h
  · cases h; rfl
  · cases h

theorem stepB_poly {Δ : TypeCtx} {S t₁ : List CValType} {r : StepRes}
    (h : stepB Δ S t₁ = some r) : r = .poly t₁ := by
  unfold stepB at h
  split at h
  · cases h; rfl
  · cases h

theorem blockType?_complete (hT : TyOkOracleComplete tyOk) {C : Context} (hC : C.Wf)
    (hr : C.recs = []) {bt : BlockType} {t₁ t₂ : List CValType} (h : BlockTypeOk C bt t₁ t₂) :
    blockType? tyOk C bt = some (t₁, t₂) := by
  cases h with
  | empty => rfl
  | value h => simp [blockType?, hT _ _ _ hC.types hr h]
  | typeIdx hd he => simp [blockType?, hd, Expand.iff.1 he]

theorem tagParams?_complete {C : Context} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil)) :
    tagParams? C x = some ts.toList := by
  simp [tagParams?, hx, Expand.iff.1 he]

theorem catchOk?_complete {C : Context} (hC : C.Wf) (hr : C.recs = []) {c : Catch}
    (h : CatchOk C c) : catchOk? C c = true := by
  cases h with
  | catch_ hx he hl hs =>
    have hts := (Expand.func_ok (hC.tags _ (List.mem_of_getElem? hx)) he).1
    simp only [catchOk?, tagParams?_complete hx he, hl]
    exact resSub_complete hC.types hr hs hts (hC.label hl)
  | catchRef hx he hl hs =>
    have hts := (Expand.func_ok (hC.tags _ (List.mem_of_getElem? hx)) he).1
    simp only [catchOk?, tagParams?_complete hx he, hl]
    exact resSub_complete hC.types hr hs (ResultOk.append hts (by simp)) (hC.label hl)
  | catchAll hl hs =>
    simp only [catchOk?, hl]
    exact resSub_complete hC.types hr hs (by simp) (hC.label hl)
  | catchAllRef hl hs =>
    simp only [catchOk?, hl]
    exact resSub_complete hC.types hr hs (by simp) (hC.label hl)

theorem Wf_withLabel {C : Context} (hC : C.Wf) {ts : List CValType}
    (h : ResultOk C.toTypeCtx ts) : (C.withLabel ts).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_, hC.elems⟩
  intro l hl
  simp only [Context.withLabel, List.mem_cons] at hl
  rcases hl with rfl | hl
  exacts [h, hC.labels _ hl]

theorem recs_initLocals {C : Context} (hr : C.recs = []) (xs : List Nat) :
    (C.initLocals xs).recs = [] :=
  (congrArg TypeCtx.recs (Context.initLocals_toTypeCtx C xs)).trans hr

/-! ## Stack arithmetic -/

theorem rs_split {Δ : TypeCtx} {V A B : List CValType} (h : ResultSub Δ V (A ++ B)) :
    ResultSub Δ (V.take (V.length - B.length)) A ∧
      ResultSub Δ (V.drop (V.length - B.length)) B := by
  have hl := List.Forall₂.length_eq h
  simp only [List.length_append] at hl
  have e : V.length - B.length = A.length := by omega
  rw [e]
  exact ⟨List.forall₂_take_append _ _ _ h, List.forall₂_drop_append _ _ _ h⟩

theorem take_pad (K : Nat) (s : List CValType) (n : Nat) (hn : n ≤ K + s.length) :
    (List.replicate K Ty.botv ++ s).take ((List.replicate K Ty.botv ++ s).length - n) =
      List.replicate (K - (n - s.length)) Ty.botv ++ s.take (s.length - n) := by
  rw [List.take_append, List.take_replicate]
  simp only [List.length_append, List.length_replicate]
  congr 2 <;> omega

theorem resSub_bot {Δ : TypeCtx} (M : List CValType) :
    ResultSub Δ (List.replicate M.length .botv) M := by
  induction M with
  | nil => exact .nil
  | cons a M ih => exact .cons .botv ih

/-- The top `q` entries of two `BOT`-paddings of `s` agree. -/
theorem top_pad (a b : Nat) (s : List CValType) (q : Nat) (ha : q ≤ a + s.length)
    (hb : q ≤ b + s.length) :
    (List.replicate a Ty.botv ++ s).drop ((List.replicate a Ty.botv ++ s).length - q) =
      (List.replicate b Ty.botv ++ s).drop ((List.replicate b Ty.botv ++ s).length - q) := by
  rw [drop_pad a s q ha, drop_pad b s q hb]

/-! ## Principal single-instruction inversion with a valid frame -/

theorem single_inv'_aux {C : Context} {is : List Instr} {i : Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C is it) (his : is = [i]) :
    ∃ ts it₀, InstrOk C i it₀ ∧ ResultOk C.toTypeCtx ts ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  induction h using InstrsOk.ind with
  | nil => cases his
  | @instr C i' it₀ h =>
      cases his
      exact ⟨[], it₀, h, by simp, by simpa using InstrTypeSub.refl C it₀⟩
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi _ hs _ =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
      obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) hs
      simp only [Context.initLocals_toTypeCtx] at s
      exact ⟨[], ⟨t₁, xs₁, t₂⟩, hi, by simp, by simpa using InstrTypeSub.seq_nil s i₂⟩
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨s₁, i₁⟩ := InstrsOk.nil_inv hC h₁
        have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
        obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih₂ (hC.initLocals _) rfl
        rw [hC₁] at hi hsub h₂ hts
        refine ⟨ts, it₀, hi, hts,
          InstrTypeSub.trans hC.types (InstrsOk.regular hC h₂) hsub ?_⟩
        refine ⟨s₁, ResultSub.refl _ _, ?_⟩
        intro x hx hn
        rcases List.mem_append.mp hx with hx | hx
        · exact i₁ x hx
        · exact absurd hx hn
      · obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih₁ hC rfl
        obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) h₂
        simp only [Context.initLocals_toTypeCtx] at s
        exact ⟨ts, it₀, hi, hts, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₁) hsub
          (InstrTypeSub.seq_nil s i₂)⟩
  | sub h hs hok ih =>
      obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih hC his
      exact ⟨ts, it₀, hi, hts, InstrTypeSub.trans hC.types (InstrsOk.regular hC h) hsub hs⟩
  | @frame C is ts' t₁ t₂ xs h hok ih =>
      obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih hC his
      refine ⟨ts' ++ ts, it₀, hi, ResultOk.append hok hts, ?_⟩
      simpa using InstrTypeSub.frame hsub ts'

theorem single_inv' {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C [i] it) :
    ∃ ts it₀, InstrOk C i it₀ ∧ ResultOk C.toTypeCtx ts ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it :=
  single_inv'_aux hC h rfl

/-! ## Arity -/

/-- The stack-polymorphic instructions (arbitrary operand prefix). -/
def isPolyI : Instr → Bool
  | .unreachable => true
  | .br _ => true
  | .brTable _ _ => true
  | .return_ => true
  | .returnCall _ => true
  | .returnCallRef _ => true
  | .returnCallIndirect _ _ => true
  | .throw _ => true
  | .throwRef => true
  | _ => false

theorem isPolyI_cases {i : Instr} (hp : isPolyI i = true) :
    i = .unreachable ∨ (∃ l, i = .br l) ∨ (∃ ls l, i = .brTable ls l) ∨ i = .return_ ∨
      (∃ x, i = .returnCall x) ∨ (∃ x, i = .returnCallRef x) ∨
      (∃ x y, i = .returnCallIndirect x y) ∨ (∃ x, i = .throw x) ∨ i = .throwRef := by
  cases i <;> simp [isPolyI] at hp ⊢

theorem le_arityBound {k : Nat} (h : k ≤ 8) (C : Context) (i : Instr) : k ≤ arityBound C i := by
  unfold arityBound; omega

section FamilyArity

variable {C : Context} {i : Instr} {it : InstrType}

theorem numeric_arity (h : NumericInstrOk C i it) : it.params.length ≤ 8 := by
  cases h <;> simp

theorem vector_arity (h : VectorInstrOk C i it) : it.params.length ≤ 8 := by
  cases h <;> simp

theorem variable_arity (h : VariableInstrOk C i it) : it.params.length ≤ 8 := by
  cases h <;> simp

theorem memory_arity (h : MemoryInstrOk C i it) : it.params.length ≤ 8 := by
  cases h <;> simp

theorem table_arity (h : TableInstrOk C i it) : it.params.length ≤ 8 := by
  cases h <;> simp

theorem ref_arity (h : RefInstrOk C i it) : it.params.length ≤ arityBound C i := by
  cases h with
  | structNew hd he =>
    show _ ≤ 8 + typeArity C _
    simp [typeArity, hd, defArity, Expand.iff.1 he]
  | arrayNewFixed hd he =>
    show (List.replicate _ _).length ≤ 8 + Fin.val _
    simp
  | _ => exact le_arityBound (by simp) _ _

end FamilyArity

theorem bt_arity {C : Context} {bt : BlockType} {t₁ t₂ : List CValType}
    (h : BlockTypeOk C bt t₁ t₂) : t₁.length ≤ btArity C bt := by
  cases h with
  | empty => simp
  | value => simp
  | typeIdx hd he => simp [btArity, typeArity, hd, defArity, Expand.iff.1 he]

theorem arity_nonpoly {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (hp : isPolyI i = false) : it.params.length ≤ arityBound C i := by
  cases h with
  | parametric h =>
    cases h with
    | unreachable => simp [isPolyI] at hp
    | _ => exact le_arityBound (by simp) _ _
  | numeric h => exact le_arityBound (numeric_arity h) _ _
  | vector h => exact le_arityBound (vector_arity h) _ _
  | «variable» h => exact le_arityBound (variable_arity h) _ _
  | memory h => exact le_arityBound (memory_arity h) _ _
  | table h => exact le_arityBound (table_arity h) _ _
  | reference h => exact ref_arity h
  | block hbt => show _ ≤ 8 + btArity C _; have := bt_arity hbt; simp; omega
  | loop hbt => show _ ≤ 8 + btArity C _; have := bt_arity hbt; simp; omega
  | if_ hbt => show _ ≤ 8 + btArity C _; have := bt_arity hbt; simp; omega
  | tryTable hbt => show _ ≤ 8 + btArity C _; have := bt_arity hbt; simp; omega
  | brIf hl => show _ ≤ 8 + labelArity C _; simp [labelArity, hl]; omega
  | brOnNull hl => show _ ≤ 8 + labelArity C _; simp [labelArity, hl]; omega
  | brOnNonNull hl => show _ ≤ 8 + labelArity C _; simp [labelArity, hl]
  | brOnCast hl => show _ ≤ 8 + labelArity C _; simp [labelArity, hl]
  | brOnCastFail hl => show _ ≤ 8 + labelArity C _; simp [labelArity, hl]
  | call hf he => show _ ≤ 8 + funcArity C _; simp [funcArity, hf, defArity, Expand.iff.1 he]
  | callRef hd he =>
    show _ ≤ 8 + typeArity C _; simp [typeArity, hd, defArity, Expand.iff.1 he]; omega
  | callIndirect _ _ hd he =>
    show _ ≤ 8 + typeArity C _; simp [typeArity, hd, defArity, Expand.iff.1 he]; omega
  | _ => simp [isPolyI] at hp

theorem arity_poly {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf) (h : InstrOk C i it)
    (hp : isPolyI i = true) :
    it.inits = [] ∧ ∃ pre q r, it.params = pre ++ q ∧ q.length ≤ arityBound C i ∧
      InstrOk C i ⟨q, [], r⟩ := by
  have hreg := h.regular hC
  cases h with
  | parametric h =>
    cases h with
    | unreachable hok =>
      exact ⟨rfl, _, [], _, (List.append_nil _).symm, Nat.zero_le _,
        .parametric (.unreachable (plainOk (by simp) hok.2.1))⟩
    | _ => simp [isPolyI] at hp
  | numeric h => cases h <;> simp [isPolyI] at hp
  | vector h => cases h <;> simp [isPolyI] at hp
  | «variable» h => cases h <;> simp [isPolyI] at hp
  | memory h => cases h <;> simp [isPolyI] at hp
  | table h => cases h <;> simp [isPolyI] at hp
  | reference h => cases h <;> simp [isPolyI] at hp
  | br hl hok =>
    refine ⟨rfl, _, _, _, rfl, ?_, .br (t₁ := []) hl (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + labelArity C _; simp [labelArity, hl]
  | brTable hls hl' hok =>
    obtain ⟨lt, hlt, hsl⟩ := hl'
    refine ⟨rfl, _, _, _, List.append_assoc _ _ _, ?_,
      .brTable (t₁ := []) hls ⟨lt, hlt, hsl⟩ (plainOk ?_ hok.2.1)⟩
    · show _ ≤ 8 + labelArity C _
      have := List.Forall₂.length_eq hsl
      simp [labelArity, hlt]; omega
    · have := hok.1
      simp only [ResultOk.append_iff] at this ⊢
      simp [this.1.2]
  | return_ hr hok =>
    refine ⟨rfl, _, _, _, rfl, ?_, .return_ (t₁ := []) hr (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + (C.return_.map List.length).getD 0; simp [hr]
  | returnCall hf he hr hs hok =>
    refine ⟨rfl, _, _, _, rfl, ?_, .returnCall (t₃ := []) hf he hr hs (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + funcArity C _; simp [funcArity, hf, defArity, Expand.iff.1 he]
  | returnCallRef hd he hr hs hok =>
    refine ⟨rfl, _, _, _, List.append_assoc _ _ _, ?_,
      .returnCallRef (t₃ := []) hd he hr hs (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + typeArity C _; simp [typeArity, hd, defArity, Expand.iff.1 he]; omega
  | returnCallIndirect ht hs hd he hr hrs hok =>
    refine ⟨rfl, _, _, _, List.append_assoc _ _ _, ?_,
      .returnCallIndirect (t₃ := []) ht hs hd he hr hrs (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + typeArity C _; simp [typeArity, hd, defArity, Expand.iff.1 he]; omega
  | throw hx he hok =>
    refine ⟨rfl, _, _, _, rfl, ?_, .throw (t₁ := []) hx he (plainOk (by simp) hok.2.1)⟩
    show _ ≤ 8 + tagArity C _; simp [tagArity, hx, defArity, Expand.iff.1 he]
  | throwRef hok =>
    refine ⟨rfl, _, _, _, rfl, ?_, .throwRef (t₁ := []) (plainOk (by simp) hok.2.1)⟩
    exact le_arityBound (by simp) _ _
  | _ => simp [isPolyI] at hp

/-! ## Shape of checker results -/

theorem checkInstr_eq_direct {C : Context} {S : List CValType} {i : Instr}
    (h1 : ∀ bt b, i ≠ .block bt b) (h2 : ∀ bt b, i ≠ .loop bt b)
    (h3 : ∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) (h4 : ∀ bt cs b, i ≠ .tryTable bt cs b)
    (h5 : i ≠ .select none) :
    checkInstr atom? tyOk C S i = directStep atom? tyOk C S i := by
  cases i
  case block => exact absurd rfl (h1 _ _)
  case loop => exact absurd rfl (h2 _ _)
  case if_ => exact absurd rfl (h3 _ _ _)
  case tryTable => exact absurd rfl (h4 _ _ _)
  case select ts =>
    cases ts
    · exact absurd rfl h5
    · rfl
  all_goals rfl

theorem directStep_isPoly {C : Context} {S : List CValType} {i : Instr} {t : List CValType}
    (h : directStep atom? tyOk C S i = some (.poly t)) : isPolyI i = true := by
  unfold directStep at h
  split at h
  all_goals first
    | rfl
    | (simp only [stepA] at h; repeat' split at h
       all_goals cases h)
    | (repeat' split at h
       all_goals cases h)

theorem checkInstr_isPoly {C : Context} {S : List CValType} {i : Instr} {t : List CValType}
    (h : checkInstr atom? tyOk C S i = some (.poly t)) : isPolyI i = true := by
  by_cases hb : ∃ bt b, i = .block bt b
  · obtain ⟨bt, b, rfl⟩ := hb
    simp only [checkInstr, stepA] at h
    repeat' split at h
    all_goals cases h
  by_cases hl : ∃ bt b, i = .loop bt b
  · obtain ⟨bt, b, rfl⟩ := hl
    simp only [checkInstr, stepA] at h
    repeat' split at h
    all_goals cases h
  by_cases hi : ∃ bt b₁ b₂, i = .if_ bt b₁ b₂
  · obtain ⟨bt, b₁, b₂, rfl⟩ := hi
    simp only [checkInstr, stepA] at h
    repeat' split at h
    all_goals cases h
  by_cases ht : ∃ bt cs b, i = .tryTable bt cs b
  · obtain ⟨bt, cs, b, rfl⟩ := ht
    simp only [checkInstr, stepA] at h
    repeat' split at h
    all_goals cases h
  by_cases hs : i = .select none
  · subst hs
    simp only [checkInstr] at h
    split at h
    · rename_i r hr
      cases h
      cases stepA_eq hr
    · exact directStep_isPoly h
  rw [checkInstr_eq_direct (fun bt b e => hb ⟨bt, b, e⟩) (fun bt b e => hl ⟨bt, b, e⟩)
    (fun bt b₁ b₂ e => hi ⟨bt, b₁, b₂, e⟩) (fun bt cs b e => ht ⟨bt, cs, b, e⟩) hs] at h
  exact directStep_isPoly h

theorem checkInstr_poly {C : Context} {S : List CValType} {i : Instr} {r : StepRes}
    (hp : isPolyI i = true) (h : checkInstr atom? tyOk C S i = some r) : ∃ t, r = .poly t := by
  rcases isPolyI_cases hp with rfl | ⟨l, rfl⟩ | ⟨ls, l, rfl⟩ | rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩ |
    ⟨x, y, rfl⟩ | ⟨x, rfl⟩ | rfl
  all_goals
    rw [checkInstr_eq_direct (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e) (fun e => by cases e)] at h
    simp only [directStep] at h
    repeat' split at h
    all_goals first | exact ⟨_, stepB_poly h⟩ | cases h

/-- The locals a checked sequence initialises exist. -/
theorem checkSeq_locals : ∀ (l : List Instr) {C : Context} {s : List CValType} {poly : Bool}
    {goal : Option (List CValType)} {o : List CValType} {xs : List Nat} {k : Nat},
    checkSeq atom? tyOk C s poly goal l = some (o, xs, k) →
    ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt
  | [], C, s, poly, goal, o, xs, k, h => by
    cases goal with
    | none =>
      simp only [checkSeq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      intro x hx; cases hx
    | some g =>
      simp only [checkSeq] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        intro x hx; cases hx
      · cases h
  | i :: rest, C, s, poly, goal, o, xs, k, h => by
    simp only [checkSeq] at h
    split at h
    · rename_i n xs₁ out₁ _
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        split at h
        · rename_i out' xs' k' hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, -⟩ := h
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact localsOk_sound hc.1 x hx
          · exact Context.initLocals_exists.1 (checkSeq_locals rest hrec x hx)
        · cases h
      · cases h
    · split at h
      · rename_i out' xs' k' hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        exact checkSeq_locals rest hrec
      · cases h
    · cases h

/-! ## Inversion for the block-like instructions -/

theorem inv_block {C : Context} {bt : BlockType} {body : List Instr} {it : InstrType}
    (h : InstrOk C (.block bt body) it) : ∃ t₁ t₂ xsb, it = .plain t₁ t₂ ∧
      BlockTypeOk C bt t₁ t₂ ∧ InstrsOk (C.withLabel t₂) body ⟨t₁, xsb, t₂⟩ := by
  cases h
  case block hbt hb => exact ⟨_, _, _, rfl, hbt, hb⟩
  all_goals (rename_i h; cases h)

theorem inv_loop {C : Context} {bt : BlockType} {body : List Instr} {it : InstrType}
    (h : InstrOk C (.loop bt body) it) : ∃ t₁ t₂ xsb, it = .plain t₁ t₂ ∧
      BlockTypeOk C bt t₁ t₂ ∧ InstrsOk (C.withLabel t₁) body ⟨t₁, xsb, t₂⟩ := by
  cases h
  case loop hbt hb => exact ⟨_, _, _, rfl, hbt, hb⟩
  all_goals (rename_i h; cases h)

theorem inv_if {C : Context} {bt : BlockType} {b₁ b₂ : List Instr} {it : InstrType}
    (h : InstrOk C (.if_ bt b₁ b₂) it) : ∃ t₁ t₂ xs₁ xs₂, it = .plain (t₁ ++ [.i32]) t₂ ∧
      BlockTypeOk C bt t₁ t₂ ∧ InstrsOk (C.withLabel t₂) b₁ ⟨t₁, xs₁, t₂⟩ ∧
      InstrsOk (C.withLabel t₂) b₂ ⟨t₁, xs₂, t₂⟩ := by
  cases h
  case if_ hbt h₁ h₂ => exact ⟨_, _, _, _, rfl, hbt, h₁, h₂⟩
  all_goals (rename_i h; cases h)

theorem inv_tryTable {C : Context} {bt : BlockType} {cs : List Catch} {body : List Instr}
    {it : InstrType} (h : InstrOk C (.tryTable bt cs body) it) : ∃ t₁ t₂ xsb,
      it = .plain t₁ t₂ ∧ BlockTypeOk C bt t₁ t₂ ∧
      InstrsOk (C.withLabel t₂) body ⟨t₁, xsb, t₂⟩ ∧ ∀ c ∈ cs, CatchOk C c := by
  cases h
  case tryTable => exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›⟩
  all_goals (rename_i h; cases h)

theorem inv_select {C : Context} {it : InstrType} (h : InstrOk C (.select none) it) :
    ∃ t, it = .plain [t, t, .i32] [t] ∧ TyOk C.toTypeCtx t := by
  cases h
  case parametric h =>
    cases h
    exact ⟨_, rfl, by assumption⟩
  all_goals (rename_i h; cases h)

/-! ## The main lemma -/

/-- What a complete step result promises. -/
def StepOk (C : Context) (t₁ : List CValType) (xs : List Nat) (t₂ : List CValType) :
    StepRes → Prop
  | .normal n xs' out => n = t₁.length ∧ xs' = xs ∧ ResultOk C.toTypeCtx out ∧
      ResultSub C.toTypeCtx out t₂
  | .poly t' => t'.length ≤ t₁.length

theorem drop_three (S₀ : List CValType) (a b c : CValType) (l : List CValType)
    (hl : l.length = 3) :
    (S₀ ++ [a, b, c]).drop ((S₀ ++ [a, b, c]).length - l.length) = [a, b, c] :=
  List.drop_left' (by simp [hl])

mutual

theorem checkInstr_complete (hD : DirectComplete atom? tyOk) (hT : TyOkOracleComplete tyOk)
    (i : Instr) {C : Context} {S t₁ t₂ : List CValType} {xs : List Nat}
    (hC : C.Wf) (hr : C.recs = []) (h : InstrOk C i ⟨t₁, xs, t₂⟩)
    (hS : ResultOk C.toTypeCtx S) (hl : t₁.length ≤ S.length)
    (hsub : ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁) :
    ∃ r, checkInstr atom? tyOk C S i = some r ∧ StepOk C t₁ xs t₂ r := by
  by_cases hb : ∃ bt b, i = .block bt b
  · obtain ⟨bt, body, rfl⟩ := hb
    obtain ⟨u₁, u₂, xsb, he, hbt, hbody⟩ := inv_block h
    simp only [InstrType.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hr₁₂ := hbt.regular hC
    obtain ⟨⟨o, xsb', k⟩, hcs⟩ := checkSeq_complete hD hT body (C := C.withLabel t₂)
      (s := t₁) (poly := false) (K := 0) (Wf_withLabel hC hr₁₂.2) hr hbody hr₁₂.1
      (fun _ => rfl) (by simpa using ResultSub.refl _ t₁)
    have hloc : localsOk C xsb' = true := localsOk_complete (by have := checkSeq_locals _ hcs; exact this)
    refine ⟨.normal t₁.length [] t₂, ?_, rfl, rfl, hr₁₂.2, ResultSub.refl _ _⟩
    simp only [checkInstr, blockType?_complete hT hC hr hbt,
      resOk_complete hT hC.types hr hr₁₂.1, resOk_complete hT hC.types hr hr₁₂.2,
      Bool.and_self, ↓reduceIte, hcs, hloc]
    exact stepA_complete hC.types hr hl hsub hS hr₁₂.1
  by_cases hlp : ∃ bt b, i = .loop bt b
  · obtain ⟨bt, body, rfl⟩ := hlp
    obtain ⟨u₁, u₂, xsb, he, hbt, hbody⟩ := inv_loop h
    simp only [InstrType.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hr₁₂ := hbt.regular hC
    obtain ⟨⟨o, xsb', k⟩, hcs⟩ := checkSeq_complete hD hT body (C := C.withLabel t₁)
      (s := t₁) (poly := false) (K := 0) (Wf_withLabel hC hr₁₂.1) hr hbody hr₁₂.1
      (fun _ => rfl) (by simpa using ResultSub.refl _ t₁)
    have hloc : localsOk C xsb' = true := localsOk_complete (by have := checkSeq_locals _ hcs; exact this)
    refine ⟨.normal t₁.length [] t₂, ?_, rfl, rfl, hr₁₂.2, ResultSub.refl _ _⟩
    simp only [checkInstr, blockType?_complete hT hC hr hbt,
      resOk_complete hT hC.types hr hr₁₂.1, resOk_complete hT hC.types hr hr₁₂.2,
      Bool.and_self, ↓reduceIte, hcs, hloc]
    exact stepA_complete hC.types hr hl hsub hS hr₁₂.1
  by_cases hif : ∃ bt b₁ b₂, i = .if_ bt b₁ b₂
  · obtain ⟨bt, b₁, b₂, rfl⟩ := hif
    obtain ⟨u₁, t₂, xs₁, xs₂, he, hbt, hb₁, hb₂⟩ := inv_if h
    simp only [InstrType.mk.injEq] at he
    obtain ⟨h1, h2, h3⟩ := he
    subst h1 h2 h3
    have hr₁₂ := hbt.regular hC
    obtain ⟨⟨o₁, xs₁', k₁⟩, hcs₁⟩ := checkSeq_complete hD hT b₁ (C := C.withLabel t₂)
      (s := u₁) (poly := false) (K := 0) (Wf_withLabel hC hr₁₂.2) hr hb₁ hr₁₂.1
      (fun _ => rfl) (by simpa using ResultSub.refl _ u₁)
    obtain ⟨⟨o₂, xs₂', k₂⟩, hcs₂⟩ := checkSeq_complete hD hT b₂ (C := C.withLabel t₂)
      (s := u₁) (poly := false) (K := 0) (Wf_withLabel hC hr₁₂.2) hr hb₂ hr₁₂.1
      (fun _ => rfl) (by simpa using ResultSub.refl _ u₁)
    have hloc₁ : localsOk C xs₁' = true := localsOk_complete (by have := checkSeq_locals _ hcs₁; exact this)
    have hloc₂ : localsOk C xs₂' = true := localsOk_complete (by have := checkSeq_locals _ hcs₂; exact this)
    refine ⟨.normal (u₁ ++ [Ty.i32]).length [] t₂, ?_, rfl, rfl, hr₁₂.2, ResultSub.refl _ _⟩
    simp only [checkInstr, blockType?_complete hT hC hr hbt,
      resOk_complete hT hC.types hr hr₁₂.1, resOk_complete hT hC.types hr hr₁₂.2,
      Bool.and_self, ↓reduceIte, hcs₁, hcs₂, hloc₁, hloc₂]
    exact stepA_complete hC.types hr hl hsub hS (ResultOk.append hr₁₂.1 (resultOk_i32 _))
  by_cases hty : ∃ bt cs b, i = .tryTable bt cs b
  · obtain ⟨bt, cs, body, rfl⟩ := hty
    obtain ⟨u₁, u₂, xsb, he, hbt, hbody, hcatch⟩ := inv_tryTable h
    simp only [InstrType.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hr₁₂ := hbt.regular hC
    obtain ⟨⟨o, xsb', k⟩, hcs⟩ := checkSeq_complete hD hT body (C := C.withLabel t₂)
      (s := t₁) (poly := false) (K := 0) (Wf_withLabel hC hr₁₂.2) hr hbody hr₁₂.1
      (fun _ => rfl) (by simpa using ResultSub.refl _ t₁)
    have hloc : localsOk C xsb' = true := localsOk_complete (by have := checkSeq_locals _ hcs; exact this)
    have hcall : cs.all (catchOk? C) = true :=
      List.all_eq_true.2 fun c hc => catchOk?_complete hC hr (hcatch c hc)
    refine ⟨.normal t₁.length [] t₂, ?_, rfl, rfl, hr₁₂.2, ResultSub.refl _ _⟩
    simp only [checkInstr, blockType?_complete hT hC hr hbt,
      resOk_complete hT hC.types hr hr₁₂.1, resOk_complete hT hC.types hr hr₁₂.2, hcall,
      Bool.and_self, ↓reduceIte, hcs, hloc]
    exact stepA_complete hC.types hr hl hsub hS hr₁₂.1
  by_cases hsel : i = .select none
  · subst hsel
    obtain ⟨t, he, ht⟩ := inv_select h
    simp only [InstrType.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    cases hst : stepA C.toTypeCtx S [.botv, .botv, .i32] [] [.botv] with
    | some r =>
      obtain rfl := stepA_eq hst
      refine ⟨StepRes.normal [Ty.botv, Ty.botv, .i32].length [] [.botv], ?_, rfl, rfl,
        resultOk_replicate _ 1, .cons .botv .nil⟩
      simp only [checkInstr, hst]
    | none =>
      have hns : ¬ (Instr.select none = .select none ∧
          ∃ S₀ c, S = S₀ ++ [.botv, .botv, c]) := by
        rintro ⟨-, S₀, c, rfl⟩
        have hsub' := hsub
        rw [drop_three _ _ _ _ _ rfl] at hsub'
        simp only [ResultSub, List.forall₂_cons] at hsub'
        have hstep := stepA_complete (xs := []) (out := [Ty.botv]) hC.types hr
          (S := S₀ ++ [.botv, .botv, c]) (t₁ := [.botv, .botv, .i32]) (by simp)
          (by rw [drop_three _ _ _ _ _ rfl]; exact .cons .botv (.cons .botv (.cons hsub'.2.2.1 .nil)))
          hS (by simp [TyOk.botv])
        rw [hstep] at hst
        cases hst
      obtain ⟨r, hr', hok⟩ := hD C S _ _ _ _ hC hr (fun _ _ e => by cases e)
        (fun _ _ e => by cases e) (fun _ _ _ e => by cases e) (fun _ _ _ e => by cases e)
        hns h hS hl hsub
      refine ⟨r, ?_, by cases r <;> exact hok⟩
      simp only [checkInstr, hst]
      exact hr'
  have hne := checkInstr_eq_direct (atom? := atom?) (tyOk := tyOk) (C := C) (S := S)
    (fun bt b e => hb ⟨bt, b, e⟩) (fun bt b e => hlp ⟨bt, b, e⟩)
    (fun bt b₁ b₂ e => hif ⟨bt, b₁, b₂, e⟩) (fun bt cs b e => hty ⟨bt, cs, b, e⟩) hsel
  obtain ⟨r, hr', hok⟩ := hD C S i t₁ t₂ xs hC hr (fun bt b e => hb ⟨bt, b, e⟩)
    (fun bt b e => hlp ⟨bt, b, e⟩) (fun bt b₁ b₂ e => hif ⟨bt, b₁, b₂, e⟩)
    (fun bt cs b e => hty ⟨bt, cs, b, e⟩) (fun h' => hsel h'.1) h hS hl hsub
  exact ⟨r, hne ▸ hr', by cases r <;> exact hok⟩
termination_by sizeOf i
decreasing_by all_goals ((try subst_vars); (try simp) <;> omega)

theorem checkSeq_complete (hD : DirectComplete atom? tyOk) (hT : TyOkOracleComplete tyOk)
    (l : List Instr) {C : Context} {s : List CValType} {poly : Bool}
    {g T : List CValType} {xs : List Nat} {K : Nat} (hC : C.Wf) (hr : C.recs = [])
    (h : InstrsOk C l ⟨T, xs, g⟩) (hs : ResultOk C.toTypeCtx s) (hK : poly = false → K = 0)
    (hV : ResultSub C.toTypeCtx (List.replicate K .botv ++ s) T) :
    ∃ r, checkSeq atom? tyOk C s poly (some g) l = some r := by
  have hreg := InstrsOk.regular hC h
  have hVok : ResultOk C.toTypeCtx (List.replicate K .botv ++ s) :=
    ResultOk.append (resultOk_replicate _ _) hs
  match l with
  | [] =>
    obtain ⟨hTg, -⟩ := InstrsOk.nil_inv hC h
    have hVg : ResultSub C.toTypeCtx (List.replicate K .botv ++ s) g :=
      ResultSub.trans hC.types hreg.1 hV hTg
    have hlen := List.Forall₂.length_eq hVg
    simp only [List.length_append, List.length_replicate] at hlen
    have hpad : endPad poly s g = K := by
      cases poly
      · simp [endPad, hK rfl]
      · simp [endPad]; omega
    refine ⟨(g, [], K), ?_⟩
    simp only [checkSeq, hpad, resSub_complete hC.types hr hVg hVok hreg.2.1,
      resOk_complete hT hC.types hr hreg.2.1, Bool.and_self, ↓reduceIte]
  | i :: rest =>
    obtain ⟨M, xs₁, xs₂, h₁, h₂⟩ := InstrsOk.append_inv (is₁ := [i]) (is₂ := rest) hC h
    have h₁ : InstrsOk C [i] ⟨T, xs₁, M⟩ := h₁
    have h₂ : InstrsOk (C.initLocals xs₁) rest ⟨M, xs₂, g⟩ := h₂
    obtain ⟨ts, ⟨p₀, xs₀, r₀⟩, hi, hts, hsub⟩ := single_inv' hC h₁
    have hs1 : ResultSub C.toTypeCtx T (ts ++ p₀) := hsub.1
    have hs2 : ResultSub C.toTypeCtx (ts ++ r₀) M := hsub.2.1
    have hs3 : ∀ x ∈ xs₁, x ∉ xs₀ → ∃ t, C.locals[x]? = some ⟨.set, t⟩ := hsub.2.2
    have hreg₀ := hi.regular hC
    have hV' : ResultSub C.toTypeCtx (List.replicate K .botv ++ s) (ts ++ p₀) :=
      ResultSub.trans hC.types hreg.1 hV hs1
    have hVlen := List.Forall₂.length_eq hV'
    simp only [List.length_append, List.length_replicate] at hVlen
    have hSok : ResultOk C.toTypeCtx (padStack (padFor C poly i) s) :=
      resultOk_padStack hs _
    cases hpoly : isPolyI i
    · -- a normal instruction
      have har : p₀.length ≤ arityBound C i := arity_nonpoly hi hpoly
      have hle : p₀.length ≤ padFor C poly i + s.length := by
        cases poly
        · have := hK rfl; simp [padFor]; omega
        · simp [padFor]; omega
      have hlS : p₀.length ≤ (padStack (padFor C poly i) s).length := by
        rw [padStack_length]; exact hle
      have htop : ResultSub C.toTypeCtx ((padStack (padFor C poly i) s).drop
          ((padStack (padFor C poly i) s).length - p₀.length)) p₀ := by
        unfold padStack
        rw [top_pad _ K s _ hle (by omega)]
        simpa using (rs_split hV').2
      obtain ⟨r, hci, hok⟩ := checkInstr_complete hD hT i hC hr hi hSok hlS htop
      cases r with
      | poly t =>
        have := checkInstr_isPoly hci
        rw [hpoly] at this
        cases this
      | normal n xs' out =>
        obtain ⟨rfl, rfl, hout, hsubo⟩ := hok
        have h₂' : InstrsOk (C.initLocals xs') rest ⟨M, xs₂, g⟩ :=
          h₂.initLocals_relocal (LocalsLe.initLocals_of_sub hs3)
        have hA := (rs_split hV').1
        rw [take_pad K s _ (by omega)] at hA
        have hV2 : ResultSub C.toTypeCtx
            (List.replicate (K - (p₀.length - s.length)) .botv ++
              (s.take (s.length - p₀.length) ++ out)) M := by
          rw [← List.append_assoc]
          exact ResultSub.trans hC.types (ResultOk.append hts hreg₀.2.1)
            (ResultSub.append hA hsubo) hs2
        have hs' : ResultOk (C.initLocals xs').toTypeCtx
            (s.take (s.length - p₀.length) ++ out) := by
          rw [Context.initLocals_toTypeCtx]; exact ResultOk.append (hs.take' _) hout
        obtain ⟨⟨o', xs'', k'⟩, hrest⟩ := checkSeq_complete hD hT rest (K := K - (p₀.length - s.length))
          (hC.initLocals xs')
          (recs_initLocals hr xs') h₂' hs' (fun hp => by rw [hK hp]; simp)
          (by rw [Context.initLocals_toTypeCtx]; exact hV2)
        refine ⟨(o', xs' ++ xs'', k' + (p₀.length - s.length)), ?_⟩
        simp only [checkSeq, hci, localsOk_complete hreg₀.2.2,
          resOk_complete hT hC.types hr hout, Bool.and_self, ↓reduceIte, hrest]
    · -- a stack-polymorphic instruction
      obtain ⟨hinit, pre, q, r₁, hpq, hqlen, hiq⟩ := arity_poly hC hi hpoly
      simp only at hinit hpq
      subst hinit hpq
      have hle : q.length ≤ padFor C poly i + s.length := by
        cases poly
        · have := hK rfl; simp at hVlen; simp [padFor]; omega
        · simp [padFor]; omega
      have hlS : q.length ≤ (padStack (padFor C poly i) s).length := by
        rw [padStack_length]; exact hle
      have htop : ResultSub C.toTypeCtx ((padStack (padFor C poly i) s).drop
          ((padStack (padFor C poly i) s).length - q.length)) q := by
        unfold padStack
        rw [top_pad _ K s _ hle (by simp at hVlen; omega)]
        rw [← List.append_assoc] at hV'
        simpa using (rs_split hV').2
      obtain ⟨r, hci, -⟩ := checkInstr_complete hD hT i hC hr hiq hSok hlS htop
      obtain ⟨t, rfl⟩ := checkInstr_poly hpoly hci
      have hCeq : C.initLocals xs₁ = C :=
        Context.initLocals_of_set (fun x hx => hs3 x hx (by simp))
      rw [hCeq] at h₂
      obtain ⟨⟨o', xs'', k'⟩, hrest⟩ := checkSeq_complete hD hT rest (s := []) (poly := true)
        (K := M.length) hC hr h₂ (by simp) (fun h => by cases h) (by simpa using resSub_bot M)
      refine ⟨(o', xs'', t.length - s.length), ?_⟩
      simp only [checkSeq, hci, hrest]
termination_by sizeOf l
decreasing_by all_goals (simp_wf <;> (try subst_vars) <;> omega)

end

/-! ## Entry points -/

end SeqComplete

open SeqComplete in
/-- **Completeness** of `checkBody?`. -/
theorem checkBody?_complete {atom? : AtomOracle} {tyOk : TyOkOracle}
    (hD : DirectComplete atom? tyOk) (hT : TyOkOracleComplete tyOk) {C : Context} (hC : C.Wf)
    (hr : C.recs = []) {t₁ t₂ : List CValType} {xs : List Nat} {is : List Instr}
    (h : InstrsOk C is ⟨t₁, xs, t₂⟩) (_hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) :
    checkBody? atom? tyOk C t₁ t₂ is = true := by
  have hreg := InstrsOk.regular hC h
  obtain ⟨⟨o, xs', k⟩, hcs⟩ := checkSeq_complete hD hT is (s := t₁) (poly := false) (K := 0)
    hC hr h hreg.1 (fun _ => rfl) (by simpa using ResultSub.refl _ t₁)
  simp only [checkBody?, resOk_complete hT hC.types hr hreg.1,
    resOk_complete hT hC.types hr hreg.2.1, Bool.true_and, hcs]
  exact localsOk_complete (by have := checkSeq_locals _ hcs; exact this)

open SeqComplete in
/-- **Completeness** of `checkExpr?`. -/
theorem checkExpr?_complete {atom? : AtomOracle} {tyOk : TyOkOracle}
    (hD : DirectComplete atom? tyOk) (hT : TyOkOracleComplete tyOk) {C : Context} (hC : C.Wf)
    (hr : C.recs = []) {e : Expr} {ts : List CValType} (h : ExprOk C e ts) :
    checkExpr? atom? tyOk C e ts = true := by
  have hreg := InstrsOk.regular hC h
  obtain ⟨⟨o, xs', k⟩, hcs⟩ := checkSeq_complete hD hT e (s := []) (poly := false) (K := 0)
    hC hr h (by simp) (fun _ => rfl) (by simpa using ResultSub.refl _ ([] : List CValType))
  simp only [checkExpr?, resOk_complete hT hC.types hr hreg.2.1, Bool.true_and, hcs]

end Silmaril.Wasm.Validation
