module

public import Silmaril.Wasm.Binaryen.Pass.CodeFolding
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Binaryen.TypingInv
public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.Exe.StageContract

@[expose] public section

/-! # CodeFolding is sound

`codeFolding` (`Pass/CodeFolding.lean`) hoists the common closed void tails `X` of the
arms of an `if`: `if bt (T ++ X) (E ++ X)` becomes `if bt T E ; X`.

* **Semantics.** The lowered body before and after are related by the block-unwrap
  relation extended with folded `if`s (`UIL.fold`, `Binaryen/InlUnwrapRel.lean`), whose
  simulation covers a running arm `C ++ X` inside the `if`'s label against `C` inside it
  and `X` after it. The arms never branch out or return, so the label is never targeted.
  One function at a time, each step is an export equivalence under the closed host
  (`exportEquiv_withBody`), and the steps compose (`codeFolding_sound`).
* **Typing.** `X` is a sequence of closed trees of integer operators, `nop`, `drop`,
  `local.set` and `global.set`: its principal type is `[] → []` (`principal_list`), so
  the arm before it has the `if`'s result type, and its typing does not depend on the
  labels or on which locals are initialised (`transfer`), so it is typed after the `if`
  (`tyRepl_fold`).
-/

namespace Silmaril.Wasm.Binaryen.CodeFolding

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Numerics

/-! ## Closed trees -/

/-- The instructions of a closed tree. -/
def SimpleInstr (i : Instr) : Prop := (simpleArity i).isSome = true

mutual
theorem closedRes_simple : ∀ {x : BExpr} {r : Nat}, closedRes x = some r →
    ∀ i ∈ x.lower, SimpleInstr i
  | .op i args, r, h => by
    unfold closedRes at h
    split at h
    · next n r' hs =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        intro j hj
        rw [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact closedArgs_simple hc.2 j hj
        · simp [SimpleInstr, hs]
      · cases h
    · cases h
  | .block .., _, h | .loop .., _, h | .if_ .., _, h | .tryTable .., _, h => by
    simp [closedRes] at h
theorem closedArgs_simple : ∀ {as : List BExpr}, closedArgs as = true →
    ∀ i ∈ BExpr.lowerList as, SimpleInstr i
  | [], _ => by simp
  | a :: as, h => by
    simp only [closedArgs, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    rw [BExpr.lowerList_cons, List.mem_append] at hj
    rcases hj with hj | hj
    · exact closedRes_simple h.1 j hj
    · exact closedArgs_simple h.2 j hj
end

mutual
/-- A closed tree is saturated and inferred, at its result count, in every context. -/
theorem closedRes_infer (C : Context) : ∀ {x : BExpr} {r : Nat}, closedRes x = some r →
    x.saturated C = true ∧ ∃ ts : List CValType, ts.length = r ∧ infer C x = some (.vals ts)
  | .op i args, r, h => by
    unfold closedRes at h
    split at h
    · next n r' hs =>
      split at h
      · next hc =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hsat, us, hus, hinf⟩ := closedArgs_infer C hc.2
        simp only [BExpr.saturated, infer, hsat, hinf, Bool.true_and]
        cases i <;> simp [simpleArity] at hs <;> obtain ⟨rfl, rfl⟩ := hs <;>
          simp_all [botInstr, flatArity, flatResults]
      · cases h
    · cases h
  | .block .., _, h | .loop .., _, h | .if_ .., _, h | .tryTable .., _, h => by
    simp [closedRes] at h
theorem closedArgs_infer (C : Context) : ∀ {as : List BExpr}, closedArgs as = true →
    BExpr.saturatedList C as = true ∧ ∃ us : List CValType, us.length = as.length ∧
      inferList C as = some (.vals us)
  | [], _ => ⟨rfl, [], rfl, rfl⟩
  | a :: as, h => by
    simp only [closedArgs, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hs₁, ts, hts, hi₁⟩ := closedRes_infer C h.1
    obtain ⟨hs₂, us, hus, hi₂⟩ := closedArgs_infer C h.2
    refine ⟨by simp [BExpr.saturatedList, hs₁, hs₂], ts ++ us, by simp [hts, hus]; omega, ?_⟩
    simp [inferList, hi₁, hi₂]
end

/-- A sequence of closed void trees is saturated and inferred at `[]`. -/
theorem closedVoid_infer (C : Context) : ∀ {xs : List BExpr}, (∀ x ∈ xs, closedRes x = some 0) →
    BExpr.saturatedList C xs = true ∧ inferList C xs = some (.vals [])
  | [], _ => ⟨rfl, rfl⟩
  | x :: xs, h => by
    obtain ⟨hs₁, ts, hts, hi₁⟩ := closedRes_infer C (h x (by simp))
    obtain ⟨hs₂, hi₂⟩ := closedVoid_infer C (xs := xs) (fun y hy => h y (by simp [hy]))
    rw [List.length_eq_zero_iff] at hts
    subst hts
    exact ⟨by simp [BExpr.saturatedList, hs₁, hs₂], by simp [inferList, hi₁, hi₂]⟩

/-! ## Typing does not depend on labels and initialisation -/

/-- Contexts with the same types, globals and local types. -/
structure SameTy (D C : Context) : Prop where
  ty : D.toTypeCtx = C.toTypeCtx
  globals : D.globals = C.globals
  locals : ∀ x : Nat, (D.locals[x]?).map LocalType.type = (C.locals[x]?).map LocalType.type

theorem SameTy.initLocals {D C : Context} (h : SameTy D C) (xs ys : List Nat) :
    SameTy (D.initLocals xs) (C.initLocals ys) :=
  ⟨by simpa using h.ty, by simpa [initLocals_globals] using h.globals,
    fun x => by rw [initLocals_localType, initLocals_localType]; exact h.locals x⟩

theorem transfer_instr {D C : Context} {i : Instr} {it : InstrType} (h : InstrOk D i it)
    (hs : SimpleInstr i) (hDC : SameTy D C) : InstrOk C i it := by
  cases h with
  | numeric h => exact .numeric (by cases h <;> constructor; assumption)
  | parametric h =>
    cases h with
    | nop => exact .parametric .nop
    | drop h => exact .parametric (.drop (hDC.ty ▸ h))
    | _ => simp [SimpleInstr, simpleArity] at hs
  | «variable» h =>
    cases h with
    | @localSet x i' t h =>
      have := hDC.locals x.toNat
      rw [h] at this
      obtain ⟨lt, hlt, hty⟩ := Option.map_eq_some_iff.mp this.symm
      obtain ⟨i'', t'⟩ := lt
      simp only at hty
      subst hty
      exact .variable (.localSet hlt)
    | globalSet h => exact .variable (.globalSet (hDC.globals ▸ h))
    | _ => simp [SimpleInstr, simpleArity] at hs
  | vector h | memory h | table h | reference h => cases h <;> simp [SimpleInstr, simpleArity] at hs
  | _ => simp [SimpleInstr, simpleArity] at hs

/-- **Transfer.** A typing of a sequence of tail instructions holds, up to the locals it
claims to initialise, in every context with the same types. -/
theorem transfer {D : Context} {is : List Instr} {it : InstrType} (h : InstrsOk D is it) :
    (∀ i ∈ is, SimpleInstr i) → ∀ {C : Context}, C.Wf → SameTy D C →
      ∃ xs, InstrsOk C is ⟨it.params, xs, it.results⟩ := by
  induction h using InstrsOk.ind with
  | nil => intro _ C _ _; exact ⟨[], .nil⟩
  | instr h =>
    intro hs C hC hDC
    exact ⟨_, .instr (transfer_instr h (hs _ (by simp)) hDC)⟩
  | @seq D is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
    intro hs C hC hDC
    obtain ⟨ys₁, k₁⟩ := ih₁ (fun i hi => hs i (by simp [hi])) hC hDC
    obtain ⟨ys₂, k₂⟩ := ih₂ (fun i hi => hs i (by simp [hi])) (hC.initLocals ys₁)
      (hDC.initLocals xs₁ ys₁)
    exact ⟨_, .seq k₁ (InstrsOk.regular hC k₁).2.2 k₂⟩
  | @cons D i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs' ih =>
    intro hs C hC hDC
    have hi' := transfer_instr hi (hs i (by simp)) hDC
    obtain ⟨ys, k⟩ := ih (fun j hj => hs j (by simp [hj])) (hC.initLocals xs₁)
      (hDC.initLocals xs₁ xs₁)
    exact ⟨_, .cons hi' (InstrOk.regular hC hi').2.2 k⟩
  | @sub D is it it' h hsub hok ih =>
    intro hs C hC hDC
    obtain ⟨ys, k⟩ := ih hs hC hDC
    have hr := InstrsOk.regular hC k
    refine ⟨ys, .sub k ⟨?_, ?_, fun x hx hn => absurd hx hn⟩ ⟨?_, ?_, hr.2.2⟩⟩
    · rw [← hDC.ty]; exact hsub.1
    · rw [← hDC.ty]; exact hsub.2.1
    · rw [← hDC.ty]; exact hok.1
    · rw [← hDC.ty]; exact hok.2.1
  | @frame D is ts t₁ t₂ xs h hok ih =>
    intro hs C hC hDC
    obtain ⟨ys, k⟩ := ih hs hC hDC
    exact ⟨ys, .frame k (hDC.ty ▸ hok)⟩

theorem closedVoid_simple {xs : List BExpr} (hx : ∀ x ∈ xs, closedRes x = some 0) :
    ∀ i ∈ BExpr.lowerList xs, SimpleInstr i := by
  intro i hi
  obtain ⟨x, hx', hi'⟩ : ∃ x ∈ xs, i ∈ x.lower := by
    induction xs with
    | nil => simp at hi
    | cons y ys ih =>
      rw [BExpr.lowerList_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ⟨y, by simp, hi⟩
      · obtain ⟨x, hx₁, hx₂⟩ := ih (fun z hz => hx z (by simp [hz])) hi
        exact ⟨x, by simp [hx₁], hx₂⟩
  exact closedRes_simple (hx x hx') i hi'

/-- **Typing of a hoist**: the common closed void tail `X` of the arms may follow the
`if` instead. -/
theorem tyRepl_fold (bt : BlockType) {T E : List Instr} {xs : List BExpr}
    (hx : ∀ x ∈ xs, closedRes x = some 0) :
    TyRepl [.if_ bt (T ++ BExpr.lowerList xs) (E ++ BExpr.lowerList xs)]
      (.if_ bt T E :: BExpr.lowerList xs) := by
  refine TyRepl.of_instr fun C it hC hi => ?_
  have hreg := InstrOk.regular hC hi
  cases hi with
  | if_ hbt h₁ h₂ =>
    rename_i t₁ t₂ ys₁ ys₂
    have hD : (C.withLabel t₂).Wf := wf_withLabel hC (hbt.regular hC).2
    have arm : ∀ {B : List Instr} {ys : List Nat},
        InstrsOk (C.withLabel t₂) (B ++ BExpr.lowerList xs) ⟨t₁, ys, t₂⟩ →
        (∃ zs, InstrsOk (C.withLabel t₂) B ⟨t₁, zs, t₂⟩) ∧
          ∃ zs, InstrsOk C (BExpr.lowerList xs) ⟨[], zs, []⟩ := by
      intro B ys h
      obtain ⟨m, zB, zX, hB, hX, -⟩ := InstrsOk.split hD h rfl
      obtain ⟨hsat, hinf⟩ := closedVoid_infer (C.withLabel t₂) hx
      obtain ⟨hsub, zs, hX', -⟩ := principal_list hD xs zB [] hsat hinf m zX t₂ hX
      have rB := InstrsOk.regular hD hB
      have rA := InstrsOk.regular hD h
      refine ⟨⟨zB, .sub hB ⟨ResultSub.refl _ _, by simpa using hsub, fun x hx hn => absurd hx hn⟩
        ⟨rB.1, rA.2.1, rB.2.2⟩⟩, ?_⟩
      obtain ⟨zs', hC'⟩ := transfer hX' (closedVoid_simple hx) hC
        ⟨by simp [Context.withLabel], by simp [initLocals_globals, Context.withLabel],
          fun x => by rw [initLocals_localType]; rfl⟩
      exact ⟨zs', hC'⟩
    obtain ⟨⟨zT, hT⟩, zs, hX⟩ := arm h₁
    obtain ⟨⟨zE, hE⟩, -⟩ := arm h₂
    have hX₂ : InstrsOk (C.initLocals []) (BExpr.lowerList xs) ⟨t₂, zs, t₂⟩ := by
      rw [Validation.Context.initLocals_nil]
      simpa using InstrsOk.frame hX (hbt.regular hC).2
    have hseq := InstrsOk.cons (InstrOk.if_ hbt hT hE) (by simp) hX₂
    exact .sub hseq ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => by simp at hx⟩ hreg
  | _ => rename_i h; cases h

/-! ## The tails -/

theorem commonRev_spec : ∀ (xs ys : List BExpr),
    commonRev xs ys ≤ xs.length ∧ commonRev xs ys ≤ ys.length ∧
      (∀ x ∈ xs.take (commonRev xs ys), closedRes x = some 0) ∧
      BExpr.lowerList (xs.take (commonRev xs ys)).reverse =
        BExpr.lowerList (ys.take (commonRev xs ys)).reverse
  | x :: xs, y :: ys => by
    unfold commonRev
    split
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := commonRev_spec xs ys
      refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
      · intro z hz
        simp only [List.take_succ_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        exacts [hc.1, h3 z hz]
      · simp [List.take_succ_cons, BExpr.lowerList_append, h4, Exe.instrsEqb_sound hc.2]
    · simp
  | [], _ => by simp [commonRev]
  | _ :: _, [] => by simp [commonRev]

theorem sizeOf_take_le : ∀ (l : List BExpr) (n : Nat), sizeOf (l.take n) ≤ sizeOf l
  | [], _ => by simp
  | _ :: _, 0 => by simp; omega
  | a :: l, n + 1 => by simpa using sizeOf_take_le l n

mutual
theorem expr_closed : ∀ {x : BExpr} {r : Nat}, closedRes x = some r → expr x = x
  | .op i args, r, h => by
    unfold closedRes at h
    split at h
    · split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp [expr, exprs_closed hc.2]
      · cases h
    · cases h
  | .block .., _, h | .loop .., _, h | .if_ .., _, h | .tryTable .., _, h => by
    simp [closedRes] at h
theorem exprs_closed : ∀ {as : List BExpr}, closedArgs as = true → exprs as = as
  | [], _ => by simp [exprs]
  | a :: as, h => by
    simp only [closedArgs, Bool.and_eq_true, beq_iff_eq] at h
    have ha := expr_closed h.1
    have hitem : item a = [a] := by
      cases a with
      | if_ => simp [closedRes] at h
      | _ => simp only [item]; rw [ha]
    simp [exprs, hitem, exprs_closed h.2]
end

theorem exprs_append : ∀ (a b : List BExpr), exprs (a ++ b) = exprs a ++ exprs b
  | [], _ => by simp [exprs]
  | x :: a, b => by simp [exprs, exprs_append a b]

theorem exprs_closedVoid : ∀ {xs : List BExpr}, (∀ x ∈ xs, closedRes x = some 0) → exprs xs = xs
  | [], _ => by simp [exprs]
  | x :: xs, h => by
    have hx := h x (by simp)
    have hitem : item x = [x] := by
      cases x with
      | if_ => simp [closedRes] at hx
      | _ => simp only [item]; rw [expr_closed hx]
    simp [exprs, hitem, exprs_closedVoid (xs := xs) (fun y hy => h y (by simp [hy]))]

/-- The shape of a folded `if`: the arms split at the hoisted tails. -/
theorem tail_split (t e : List BExpr) {k : Nat} (hk : k = commonRev t.reverse e.reverse) :
    ∃ t₀ e₀ tx, t = t₀ ++ tx ∧ e = e₀ ++ (e.drop (e.length - k)) ∧ tx = t.drop (t.length - k) ∧
      t₀ = t.take (t.length - k) ∧ e₀ = e.take (e.length - k) ∧ tx.length = k ∧
      (∀ x ∈ tx, closedRes x = some 0) ∧
      BExpr.lowerList (e.drop (e.length - k)) = BExpr.lowerList tx := by
  obtain ⟨h1, h2, h3, h4⟩ := commonRev_spec t.reverse e.reverse
  rw [← hk] at h1 h2 h3 h4
  simp only [List.length_reverse] at h1 h2
  rw [List.take_reverse, List.take_reverse, List.reverse_reverse, List.reverse_reverse] at h4
  refine ⟨t.take (t.length - k), e.take (e.length - k), t.drop (t.length - k),
    (List.take_append_drop _ _).symm, (List.take_append_drop _ _).symm, rfl, rfl, rfl,
    by simp; omega, fun x hx => h3 x ?_, h4.symm⟩
  rw [List.take_reverse, List.mem_reverse]
  exact hx

mutual
/-- A tree whose lowering has only tail instructions has no `if` to fold. -/
theorem expr_simple : ∀ {x : BExpr}, (∀ i ∈ x.lower, SimpleInstr i) → expr x = x
  | .op i args, h => by
    rw [BExpr.lower_op] at h
    simp [expr, exprs_simple (fun j hj => h j (List.mem_append_left _ hj))]
  | .block bt b, h =>
    absurd (h (.block bt (BExpr.lowerList b)) (by simp [BExpr.lower])) (by simp [SimpleInstr, simpleArity])
  | .loop bt b, h =>
    absurd (h (.loop bt (BExpr.lowerList b)) (by simp [BExpr.lower])) (by simp [SimpleInstr, simpleArity])
  | .tryTable bt cs b, h =>
    absurd (h (.tryTable bt cs (BExpr.lowerList b)) (by simp [BExpr.lower]))
      (by simp [SimpleInstr, simpleArity])
  | .if_ bt c t e, h =>
    absurd (h (.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)) (by simp [BExpr.lower]))
      (by simp [SimpleInstr, simpleArity])
theorem exprs_simple : ∀ {xs : List BExpr}, (∀ i ∈ BExpr.lowerList xs, SimpleInstr i) →
    exprs xs = xs
  | [], _ => by simp [exprs]
  | x :: xs, h => by
    rw [BExpr.lowerList_cons] at h
    have hx := expr_simple (fun j hj => h j (List.mem_append_left _ hj))
    have hitem : item x = [x] := by
      cases x with
      | if_ bt c t e =>
        exact absurd (h (.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)) (by simp [BExpr.lower]))
          (by simp [SimpleInstr, simpleArity])
      | _ => simp only [item]; rw [hx]
    simp [exprs, hitem, exprs_simple (fun j hj => h j (List.mem_append_right _ hj))]
end

theorem foldOk_of_eligible {t : List BExpr} (h : UnusedBlocks.eligible t = true) :
    Unwrap.FoldOk (BExpr.lowerList t) := by
  simp only [UnusedBlocks.eligible, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at h
  exact ⟨⟨_, Unwrap.region_bud h.1.1 h.1.2 h.2⟩, h.1.1⟩

/-! ## Bodies -/

/-- What the pass keeps between a body and its result: the unwrap relation (for the
semantics) and typing. -/
def Rel (A B : List Instr) : Prop := Unwrap.UIL [] A B ∧ TyRepl A B

theorem Rel.refl (A : List Instr) : Rel A A := ⟨Unwrap.UIL.refl A, TyRepl.refl A⟩

theorem Rel.append {A B A' B' : List Instr} (h : Rel A B) (h' : Rel A' B') :
    Rel (A ++ A') (B ++ B') :=
  ⟨Unwrap.UIL.append h.1 h'.1, TyRepl.append h.2 h'.2⟩

/-- The tails split off a folded `if`. -/
theorem fold_shape {bt : BlockType} {t e : List BExpr} (hk : tailCount bt t e ≠ 0) :
    UnusedBlocks.eligible t = true ∧ UnusedBlocks.eligible e = true ∧
      tailCount bt t e = commonRev t.reverse e.reverse := by
  unfold tailCount at hk ⊢
  split at hk
  · next hc => simp_all
  · exact absurd rfl hk

mutual
theorem item_rel : ∀ e : BExpr, Rel e.lower (BExpr.lowerList (item e))
  | .op i args => by
    simpa [item, expr] using (exprs_rel args).append (Rel.refl [i])
  | .block bt b => by
    have h := exprs_rel b
    have k : Rel [.block bt (BExpr.lowerList b)] [.block bt (BExpr.lowerList (exprs b))] :=
      ⟨.cons (.block h.1) .nil, TyRepl.block h.2 bt⟩
    simpa [item, expr, BExpr.lower] using k
  | .loop bt b => by
    have h := exprs_rel b
    have k : Rel [.loop bt (BExpr.lowerList b)] [.loop bt (BExpr.lowerList (exprs b))] :=
      ⟨.cons (.loop h.1) .nil, TyRepl.loop h.2 bt⟩
    simpa [item, expr, BExpr.lower] using k
  | .tryTable bt cs b => by
    have h := exprs_rel b
    have k : Rel [.tryTable bt cs (BExpr.lowerList b)] [.tryTable bt cs (BExpr.lowerList (exprs b))] :=
      ⟨.cons (.tryTable h.1) .nil, TyRepl.tryTable h.2 bt cs⟩
    simpa [item, expr, BExpr.lower] using k
  | .if_ bt c t e => by
    have hT := exprs_rel (t.take (t.length - tailCount bt t e))
    have hE := exprs_rel (e.take (e.length - tailCount bt t e))
    have hc := exprs_rel c
    by_cases hk : tailCount bt t e = 0
    · rw [hk] at hT hE
      simp at hT hE
      simp only [item, hk]
      simpa [BExpr.lower] using hc.append ⟨.cons (.if_ hT.1 hE.1) .nil, TyRepl.if_ hT.2 hE.2 bt⟩
    · obtain ⟨hTe, hEe, hk'⟩ := fold_shape hk
      obtain ⟨t₀, e₀, tx, ht, he, htx, ht₀, he₀, hlen, hcl, hlow⟩ := tail_split t e hk'
      rw [← ht₀] at hT
      rw [← he₀] at hE
      have hsx := closedVoid_simple hcl
      have hsy : ∀ i ∈ BExpr.lowerList (e.drop (e.length - tailCount bt t e)), SimpleInstr i := by
        rw [hlow]; exact hsx
      have hlen' : (e.drop (e.length - tailCount bt t e)).length = tailCount bt t e := by
        have := (commonRev_spec t.reverse e.reverse).2.1
        rw [← hk'] at this
        simp at this ⊢
        omega
      have hexT : (exprs t).take ((exprs t).length - tailCount bt t e) = exprs t₀ := by
        have hx : exprs t = exprs t₀ ++ tx := by
          conv => lhs; rw [ht]
          rw [exprs_append, exprs_closedVoid hcl]
        rw [hx]
        simp [← hlen]
      have hexE : (exprs e).take ((exprs e).length - tailCount bt t e) = exprs e₀ := by
        have hx : exprs e = exprs e₀ ++ e.drop (e.length - tailCount bt t e) := by
          conv => lhs; rw [he]
          rw [exprs_append, exprs_simple hsy]
        have hl : (exprs e₀ ++ e.drop (e.length - tailCount bt t e)).length - tailCount bt t e =
            (exprs e₀).length := by
          simp [hlen']
        rw [hx, hl]
        simp
      have hFT := foldOk_of_eligible hTe
      have hFE := foldOk_of_eligible hEe
      rw [ht, BExpr.lowerList_append] at hFT
      rw [he, BExpr.lowerList_append, hlow] at hFE
      simp only [item]
      rw [hexT, hexE, ← htx]
      have key : Rel [.if_ bt (BExpr.lowerList t₀ ++ BExpr.lowerList tx)
          (BExpr.lowerList e₀ ++ BExpr.lowerList tx)]
          (.if_ bt (BExpr.lowerList (exprs t₀)) (BExpr.lowerList (exprs e₀)) ::
            BExpr.lowerList tx) := by
        refine ⟨by simpa using Unwrap.UIL.fold (R := []) bt hT.1 hE.1 hFT hFE Unwrap.UIL.nil, ?_⟩
        exact TyRepl.trans (TyRepl.if_ (TyRepl.append hT.2 (TyRepl.refl _))
          (TyRepl.append hE.2 (TyRepl.refl _)) bt) (tyRepl_fold bt hcl)
      have hsrc : (BExpr.if_ bt c t e).lower = BExpr.lowerList c ++
          [.if_ bt (BExpr.lowerList t₀ ++ BExpr.lowerList tx)
            (BExpr.lowerList e₀ ++ BExpr.lowerList tx)] := by
        conv => lhs; rw [ht, he]
        simp [BExpr.lower, BExpr.lowerList_append, hlow]
      rw [hsrc]
      simpa [BExpr.lowerList_cons, BExpr.lower] using hc.append key
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := sizeOf_take_le t (t.length - tailCount bt t e); omega)
    | (have := sizeOf_take_le e (e.length - tailCount bt t e); omega)
theorem exprs_rel : ∀ es : List BExpr, Rel (BExpr.lowerList es) (BExpr.lowerList (exprs es))
  | [] => by simpa [exprs] using Rel.refl []
  | e :: es => by
    simpa [exprs, BExpr.lowerList_append] using (item_rel e).append (exprs_rel es)
termination_by es => sizeOf es
end

/-! ## Modules -/

/-- Fold one function's body. -/
def foldF (f : BFunc) : BFunc := { f with body := exprs f.body }

theorem withBody_self' {m : BModule} {g : Nat} {fg : BFunc} (h : m.funcs[g]? = some fg) :
    m.withBody g fg.body = m := by
  obtain ⟨hg, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [BModule.withBody, Unwrap.modifyAt_eq_set _ g _ h]
  have he : ({ fg with body := fg.body } : BFunc) = fg := rfl
  rw [he, ← hget, List.set_getElem_self]

variable (o : GrowKind → Nat → Nat → Nat → Bool) (H : Type)

/-- **One function**: folding the body of function `g` keeps validity and is an export
equivalence under the closed host. -/
theorem withBody_sound {m : BModule} {g : Nat} {fg : BFunc} (hfg : m.funcs[g]? = some fg)
    (hok : m.Ok) : (m.withBody g (exprs fg.body)).Ok ∧
      ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
        (m.withBody g (exprs fg.body)).lower m.lower := by
  have hrel := exprs_rel fg.body
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hmt₀' : ModuleOk (m.withBody g fg.body).lower mt₀ := by rw [withBody_self' hfg]; exact hmt₀
  have hvalid : ModuleOk (m.withBody g (exprs fg.body)).lower mt₀ := Unwrap.ok_transfer_mt hrel.2 hmt₀'
  refine ⟨⟨mt₀, hvalid⟩, ?_⟩
  have hL : m.lower.funcs[g]? = some (fg.mapBody BExpr.lowerList) := by
    simp only [BModule.lower, List.getElem?_map, hfg]
    rfl
  have hRm : (m.withBody g (exprs fg.body)).lower =
      { m.lower with funcs := (m.lower.funcs.set g
        (({ fg with body := exprs fg.body } : BFunc).mapBody BExpr.lowerList)) } := by
    simp only [BModule.lower, withBody_eq_set hfg, List.map_set]
    rfl
  rw [hRm]
  refine Unwrap.exportEquiv_of_instCorr_closed (Unwrap.instCorr_of_set (R := []) hL rfl
    (fun mt => ?_) (fun mi dg ag => ⟨rfl, hrel.1, ⟨fun _ => False, by simp⟩, rfl⟩))
  rw [← hRm]
  constructor
  · intro h; rw [ModuleOk.unique h hmt₀]; exact hvalid
  · intro h'; rw [ModuleOk.unique h' hvalid]; exact hmt₀

/-- The module with the first `i` functions folded. -/
def prefixFold (m : BModule) (i : Nat) : BModule :=
  { m with funcs := (m.funcs.take i).map foldF ++ m.funcs.drop i }

theorem prefixFold_succ {m : BModule} {i : Nat} {fg : BFunc} (h : m.funcs[i]? = some fg) :
    (prefixFold m i).funcs[i]? = some fg ∧
      prefixFold m (i + 1) = (prefixFold m i).withBody i (exprs fg.body) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
  have hlen : ((m.funcs.take i).map foldF).length = i := by simp; omega
  have h₁ : (prefixFold m i).funcs[i]? = some fg := by
    simp only [prefixFold]
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_drop,
      Nat.add_zero, h]
  refine ⟨h₁, ?_⟩
  rw [BModule.withBody, Unwrap.modifyAt_eq_set _ i _ h₁]
  simp only [prefixFold, BModule.mk.injEq, true_and]
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self,
    List.drop_eq_getElem_cons hi, List.set_cons_zero, List.take_add_one, List.map_append,
    List.getElem?_eq_getElem hi]
  simp [foldF, hget]

theorem prefixFold_sound {m : BModule} (hm : m.Ok) : ∀ i, i ≤ m.funcs.length →
    (prefixFold m i).Ok ∧ ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (prefixFold m i).lower m.lower
  | 0, _ => by
    have e : prefixFold m 0 = m := by simp [prefixFold]
    rw [e]
    exact ⟨hm, Exe.exportEquiv_refl _⟩
  | i + 1, hi => by
    obtain ⟨hok, he⟩ := prefixFold_sound hm i (by omega)
    obtain ⟨fg, hfg⟩ : ∃ fg, m.funcs[i]? = some fg := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hfg', heq⟩ := prefixFold_succ hfg
    obtain ⟨hok', he'⟩ := withBody_sound o H hfg' hok
    rw [heq]
    exact ⟨hok', he'.1.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) he.1,
      he.2.trans (fun _ _ _ h₁ h₂ => h₂.trans h₁) he'.2⟩

/-- **CodeFolding keeps validity and is an export equivalence** under the closed host. -/
theorem codeFolding_sound {m : BModule} (hm : m.Ok) :
    (codeFolding m).Ok ∧ ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (codeFolding m).lower m.lower := by
  have h := prefixFold_sound o H hm m.funcs.length le_rfl
  have e : prefixFold m m.funcs.length = codeFolding m := by
    simp [prefixFold, codeFolding, foldF]
  rwa [e] at h

end Silmaril.Wasm.Binaryen.CodeFolding
