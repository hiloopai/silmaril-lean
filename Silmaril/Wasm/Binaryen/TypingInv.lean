module

public import Silmaril.Wasm.Validation.Instructions.Properties

@[expose] public section

/-! # Principal-typing infrastructure for typing by lowering

Generic facts about Core 3.0 instruction typing (`Validation.InstrsOk`) used by the
inference theorems of `Binaryen/Typing.lean`:

* `single_inv_ok`: `InstrsOk.single_inv` that also records that the frame is valid;
* `Principal D is ts`: every typing of `is` in `D` is `ps → rs` with `ps ++ ts ≤ rs`,
  and `is` is typable from the empty stack at exactly `ts` (initialising at least
  as many locals);
* `Principal.nil`, `Principal.append`, `Principal.snoc`: the closure properties
  the induction over trees needs.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-- Splitting a pointwise subtyping of two concatenations whose right parts have
the same length. -/
theorem resultSub_append_split {Δ : TypeCtx} {b d : List CValType} (hbd : b.length = d.length) :
    ∀ {a c : List CValType}, ResultSub Δ (a ++ b) (c ++ d) → ResultSub Δ a c ∧ ResultSub Δ b d
  | [], [], h => ⟨List.Forall₂.nil, h⟩
  | [], _ :: c, h => by
      have := List.Forall₂.length_eq h
      simp at this
      omega
  | _ :: a, [], h => by
      have := List.Forall₂.length_eq h
      simp at this
      omega
  | _ :: a, _ :: c, h => by
      simp only [ResultSub, List.cons_append, List.forall₂_cons] at h
      obtain ⟨hxy, h'⟩ := h
      obtain ⟨h1, h2⟩ := resultSub_append_split hbd h'
      exact ⟨List.Forall₂.cons hxy h1, h2⟩

theorem single_inv_ok_aux {C : Context} {is : List Instr} {i : Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C is it) (his : is = [i]) :
    ∃ ts it₀, ResultOk C.toTypeCtx ts ∧ InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  induction h using InstrsOk.ind with
  | nil => cases his
  | @instr C i' it₀ h =>
      cases his
      exact ⟨[], it₀, by simp [ResultOk], h, by simpa using InstrTypeSub.refl C it₀⟩
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi _ hs _ =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
      obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) hs
      simp only [Context.initLocals_toTypeCtx] at s
      exact ⟨[], ⟨t₁, xs₁, t₂⟩, by simp [ResultOk], hi, by simpa using InstrTypeSub.seq_nil s i₂⟩
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨s₁, i₁⟩ := InstrsOk.nil_inv hC h₁
        have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
        obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih₂ (hC.initLocals _) rfl
        rw [hC₁] at hi hsub h₂ hts
        refine ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₂) hsub ?_⟩
        refine ⟨s₁, ResultSub.refl _ _, ?_⟩
        intro x hx hn
        rcases List.mem_append.mp hx with hx | hx
        · exact i₁ x hx
        · exact absurd hx hn
      · obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih₁ hC rfl
        obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) h₂
        simp only [Context.initLocals_toTypeCtx] at s
        exact ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₁) hsub
          (InstrTypeSub.seq_nil s i₂)⟩
  | sub h hs hok ih =>
      obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih hC his
      exact ⟨ts, it₀, hts, hi, InstrTypeSub.trans hC.types (InstrsOk.regular hC h) hsub hs⟩
  | @frame C is ts' t₁ t₂ xs h hok ih =>
      obtain ⟨ts, it₀, hts, hi, hsub⟩ := ih hC his
      refine ⟨ts' ++ ts, it₀, ResultOk.append hok hts, hi, ?_⟩
      simpa using InstrTypeSub.frame hsub ts'

/-- `InstrsOk.single_inv`, also recording that the frame is valid. -/
theorem single_inv_ok {C : Context} {i : Instr} {it : InstrType} (hC : C.Wf)
    (h : InstrsOk C [i] it) :
    ∃ ts it₀, ResultOk C.toTypeCtx ts ∧ InstrOk C i it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it :=
  single_inv_ok_aux hC h rfl

/-- Stack heights of a typed single instruction. -/
theorem single_len {C : Context} (hC : C.Wf) {i : Instr} {ps rs : List CValType} {xs : List Nat}
    (h : InstrsOk C [i] ⟨ps, xs, rs⟩) :
    ∃ k it₀, InstrOk C i it₀ ∧ ps.length = k + it₀.params.length ∧
      rs.length = k + it₀.results.length := by
  obtain ⟨ts, it₀, -, hi, hsub⟩ := single_inv_ok hC h
  have h1 := List.Forall₂.length_eq hsub.1
  have h2 := List.Forall₂.length_eq hsub.2.1
  simp only [List.length_append] at h1 h2
  exact ⟨ts.length, it₀, hi, h1, h2.symm⟩

/-- **Principal typing of a sequence.** Every typing of `is` in `D` from `ps` to `rs`
has `ps ++ ts ≤ rs`, and `is` is typable from the empty stack at `ts`, initialising
at least the locals the given typing does. -/
def Principal (D : Context) (is : List Instr) (ts : List CValType) : Prop :=
  ∀ ps xs rs, InstrsOk D is ⟨ps, xs, rs⟩ → ResultSub D.toTypeCtx (ps ++ ts) rs ∧
    ∃ xs', InstrsOk D is ⟨[], xs', ts⟩ ∧
      LocalsLe (D.initLocals xs).locals (D.initLocals xs').locals

theorem Principal.nil {D : Context} (hD : D.Wf) : Principal D [] [] := by
  intro ps xs rs h
  obtain ⟨s, i⟩ := InstrsOk.nil_inv hD h
  refine ⟨by simpa using s, [], InstrsOk.nil, ?_⟩
  rw [Context.initLocals_of_set i]
  exact LocalsLe.refl _

theorem Principal.append {D : Context} (hD : D.Wf) {is₁ is₂ : List Instr} {a b : List CValType}
    (h1 : Principal D is₁ a) (h2 : ∀ ya, Principal (D.initLocals ya) is₂ b) :
    Principal D (is₁ ++ is₂) (a ++ b) := by
  intro ps xs rs h
  obtain ⟨m, ya, yb, ha, hb, hL⟩ := InstrsOk.split hD h rfl
  obtain ⟨s1, ya', ha', hL1⟩ := h1 ps ya m ha
  obtain ⟨s2, yb', hb', hL2⟩ := h2 ya m yb rs hb
  have rm : ResultOk D.toTypeCtx m := (InstrsOk.regular hD ha).2.1
  have ra : ResultOk D.toTypeCtx a := (InstrsOk.regular hD ha').2.1
  have rb : ResultOk D.toTypeCtx b := by
    simpa using (InstrsOk.regular (hD.initLocals ya) hb').2.1
  simp only [Context.initLocals_toTypeCtx] at s2
  refine ⟨?_, ya' ++ yb', ?_, ?_⟩
  · rw [← List.append_assoc]
    exact ResultSub.trans hD.types (ResultOk.append rm rb)
      (ResultSub.append s1 (ResultSub.refl _ _)) s2
  · have hb2 : InstrsOk (D.initLocals ya) is₂ ⟨a ++ [], yb', a ++ b⟩ :=
      InstrsOk.frame hb' (by simpa using ra)
    have hb3 : InstrsOk (D.initLocals ya') is₂ ⟨a ++ [], yb', a ++ b⟩ :=
      hb2.initLocals_relocal hL1
    rw [List.append_nil] at hb3
    exact InstrsOk.append ha' (InstrsOk.regular hD ha').2.2 hb3
  · rw [Context.initLocals_append] at hL ⊢
    exact LocalsLe.trans hL (LocalsLe.trans hL2 (LocalsLe.initLocals hL1 yb'))

/-- Appending one instruction whose typing has the arity of the values `vs` the
prefix leaves, and fixed results `r`. -/
theorem Principal.snoc {D : Context} (hD : D.Wf) {args : List Instr} {j : Instr}
    {vs r : List CValType} (hargs : Principal D args vs)
    (hj : ∀ ya it₀, InstrOk (D.initLocals ya) j it₀ →
      it₀.params.length = vs.length ∧ it₀.results = r) :
    Principal D (args ++ [j]) r := by
  intro ps xs rs h
  obtain ⟨m, ya, yb, ha, hb, hL⟩ := InstrsOk.split hD h rfl
  obtain ⟨s1, ya', ha', hL1⟩ := hargs ps ya m ha
  have hDa := hD.initLocals ya
  obtain ⟨fr, it₀, hfr, hi, hsub⟩ := single_inv_ok hDa hb
  obtain ⟨hlen, hres⟩ := hj ya it₀ hi
  have rm : ResultOk D.toTypeCtx m := (InstrsOk.regular hD ha).2.1
  have rvs : ResultOk D.toTypeCtx vs := (InstrsOk.regular hD ha').2.1
  have ri := hi.regular hDa
  have rr : ResultOk D.toTypeCtx r := by rw [← hres]; simpa using ri.2.1
  obtain ⟨sp, sr, sx⟩ := hsub
  simp only [Context.initLocals_toTypeCtx] at sp sr hfr
  have s2 : ResultSub D.toTypeCtx (ps ++ vs) (fr ++ it₀.params) :=
    ResultSub.trans hD.types rm s1 sp
  obtain ⟨sps, svs⟩ := resultSub_append_split hlen.symm s2
  refine ⟨?_, ya' ++ it₀.inits, ?_, ?_⟩
  · rw [hres] at sr
    exact ResultSub.trans hD.types (ResultOk.append hfr rr)
      (ResultSub.append sps (ResultSub.refl _ _)) sr
  · have hj1 : InstrsOk (D.initLocals ya) [j] ⟨vs, it₀.inits, r⟩ :=
      .sub (.instr hi)
        ⟨by simpa using svs, by rw [hres]; exact ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
        ⟨by simpa using rvs, by simpa using rr, ri.2.2⟩
    exact InstrsOk.append ha' (InstrsOk.regular hD ha').2.2 (hj1.initLocals_relocal hL1)
  · rw [Context.initLocals_append] at hL ⊢
    have h3 : LocalsLe ((D.initLocals ya).initLocals yb).locals
        ((D.initLocals ya).initLocals it₀.inits).locals :=
      LocalsLe.initLocals_of_sub (C := D.initLocals ya) sx
    exact LocalsLe.trans hL (LocalsLe.trans h3 (LocalsLe.initLocals hL1 _))

/-! ## Contexts that differ only in local initialisation -/

theorem initLocals_globals (C : Context) (ys : List Nat) :
    (C.initLocals ys).globals = C.globals := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec ys
  rw [hL]

theorem initLocals_funcs (C : Context) (ys : List Nat) :
    (C.initLocals ys).funcs = C.funcs := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec ys
  rw [hL]

theorem initLocals_localType (C : Context) (ys : List Nat) (y : Nat) :
    ((C.initLocals ys).locals[y]?).map LocalType.type = (C.locals[y]?).map LocalType.type := by
  rw [Context.initLocals_locals]
  split <;> cases C.locals[y]? <;> simp

/-! ## Inversion for structured instructions -/

theorem instrOk_block_inv {D : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk D (.block bt b) it) :
    ∃ t₁ t₂, BlockTypeOk D bt t₁ t₂ ∧ it = .plain t₁ t₂ := by
  cases h
  all_goals first | exact ⟨_, _, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_loop_inv {D : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk D (.loop bt b) it) :
    ∃ t₁ t₂, BlockTypeOk D bt t₁ t₂ ∧ it = .plain t₁ t₂ := by
  cases h
  all_goals first | exact ⟨_, _, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_tryTable_inv {D : Context} {bt : BlockType} {cs : List Catch} {b : List Instr}
    {it : InstrType} (h : InstrOk D (.tryTable bt cs b) it) :
    ∃ t₁ t₂, BlockTypeOk D bt t₁ t₂ ∧ it = .plain t₁ t₂ := by
  cases h
  all_goals first | exact ⟨_, _, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_if_inv {D : Context} {bt : BlockType} {b₁ b₂ : List Instr} {it : InstrType}
    (h : InstrOk D (.if_ bt b₁ b₂) it) :
    ∃ t₁ t₂, BlockTypeOk D bt t₁ t₂ ∧ it = .plain (t₁ ++ [Ty.i32]) t₂ := by
  cases h
  all_goals first | exact ⟨_, _, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_nop_inv {D : Context} {it : InstrType} (h : InstrOk D .nop it) :
    it = .plain [] [] := by
  cases h
  all_goals (rename_i h; cases h; try rfl)

theorem instrOk_intConst_inv {D : Context} {t : IntType} {b : BitVec t.width} {it : InstrType}
    (h : InstrOk D (.intConst t b) it) : it = .plain [] [.num (.int t)] := by
  cases h
  all_goals (rename_i h; cases h; try rfl)

/-- The empty context is well formed. -/
theorem wf_emptyContext : ({} : Context).Wf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [TypeCtx.Ok]

end Silmaril.Wasm.Binaryen
