module

public import Silmaril.Wasm.Binaryen.InlineDefs
public import Silmaril.Wasm.Binaryen.Effects

@[expose] public section

/-! # Resolution of Binaryen's inlined block

The syntactic half of `inlineN_resolves` (`Binaryen/Inline.lean`): what the named
shape `inlineN callee base args fresh` resolves to.

* `resolve_inlined_body`: the relocated callee body
  `(body.shiftLocals base).returnToBr fresh`, resolved under the break stack of
  the inlined block, is `retToBrL 0 (shiftLocalsL base bsBody)` where `bsBody` is
  the callee body resolved on its own (`fresh` not bound in the body).
* `resolve_outer_irrel`: an expression whose free labels are all bound by the
  inner part `S` of the break stack resolves the same under any outer part.
* `resolve_free_breakTargets`: a free label of an expression shows up in the
  `breakTargets` of the resolved code; so operands whose resolution has no
  `breakTargets` have no free labels.
* `inlineN_resolve_shape`: putting it together, Binaryen's block resolves to one
  `block` whose body is the operand stores and the re-zeroing resolved *outside*
  the block, followed by the D-level relocated body; `resolve_sets` spells out
  the operand stores.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

namespace InlineRes

/-! ## Except and index helpers -/

theorem eok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem eok_pure {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem toIdx_ok {k : IndexKind} {n : Nat} {x : Idx k} :
    (toIdx n : Except ResolveErr (Idx k)) = .ok x ↔ Idx.ofNat? n = some x := by
  unfold toIdx
  cases h : (Idx.ofNat? n : Option (Idx k)) with
  | none => simp
  | some y => simp

theorem toNat_of_toIdx {k : IndexKind} {n : Nat} {x : Idx k}
    (h : (toIdx n : Except ResolveErr (Idx k)) = .ok x) : x.toNat = n :=
  ((Idx.ofNat?_eq_some_iff n x).mp (toIdx_ok.mp h)).symm

theorem labelIdx_of_toIdx {n : Nat} {x : LabelIdx} (h : (toIdx n : Except ResolveErr LabelIdx) = .ok x) :
    labelIdx n = x := by
  unfold labelIdx
  rw [toIdx_ok.mp h]
  rfl

theorem shiftIdx_of_toIdx {k : IndexKind} {i base : Nat} {x x' : Idx k}
    (h : (toIdx i : Except ResolveErr (Idx k)) = .ok x)
    (h' : (toIdx (i + base) : Except ResolveErr (Idx k)) = .ok x') : shiftIdx base x = x' := by
  unfold shiftIdx
  rw [toNat_of_toIdx h, toIdx_ok.mp h']
  rfl

theorem ite_pos' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_neg' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

/-! ## Break-stack lookups -/

theorem findIdx_append_some (p : Option Name → Bool) :
    ∀ (M X : List (Option Name)) (k : Nat), M.findIdx? p = some k → (M ++ X).findIdx? p = some k
  | [], _, _, h => by simp at h
  | b :: M, X, k, h => by
    rw [List.cons_append, List.findIdx?_cons]
    rw [List.findIdx?_cons] at h
    by_cases hb : p b = true
    · rw [ite_pos' hb] at h ⊢
      exact h
    · rw [ite_neg' hb] at h ⊢
      cases hM : M.findIdx? p with
      | none => rw [hM] at h; simp at h
      | some k' =>
        rw [hM] at h
        rw [findIdx_append_some p M X k' hM]
        exact h

theorem findIdx_append_not (p : Option Name → Bool) :
    ∀ (M X : List (Option Name)), (∀ a ∈ M, p a = false) →
      (M ++ X).findIdx? p = (X.findIdx? p).map (· + M.length)
  | [], X, _ => by simp
  | b :: M, X, h => by
    have hb : p b = false := h b (by simp)
    have ih := findIdx_append_not p M X (fun a ha => h a (by simp [ha]))
    rw [List.cons_append, List.findIdx?_cons, ite_neg' (by simp [hb]), ih, Option.map_map]
    congr 1

theorem labelDepth_append_ok {M : List (Option Name)} {l : Name} {n : LabelIdx}
    (X : List (Option Name)) (h : labelDepth M l = .ok n) : labelDepth (M ++ X) l = .ok n := by
  unfold labelDepth at h ⊢
  cases hk : M.findIdx? (· == some l) with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h
    rw [findIdx_append_some _ M X k hk]
    exact h

theorem labelDepth_append_of_mem {S : List (Option Name)} {l : Name} (h : some l ∈ S)
    (X : List (Option Name)) : labelDepth (S ++ X) l = labelDepth S l := by
  unfold labelDepth
  cases hk : S.findIdx? (· == some l) with
  | none =>
    exfalso
    rw [List.findIdx?_eq_none_iff] at hk
    simpa using hk _ h
  | some k => rw [findIdx_append_some _ S X k hk]

theorem labelDepth_fresh {M : List (Option Name)} {fresh : Name} (hM : some fresh ∉ M)
    (L : List (Option Name)) : labelDepth (M ++ some fresh :: L) fresh = toIdx M.length := by
  unfold labelDepth
  have hnot : ∀ a ∈ M, (a == some fresh) = false := by
    intro a ha
    cases h : (a == some fresh)
    · rfl
    · exfalso
      rw [beq_iff_eq] at h
      exact hM (h ▸ ha)
  rw [findIdx_append_not _ M _ hnot, List.findIdx?_cons, ite_pos' (by simp)]
  simp

theorem labelDepth_cons_ne {a : Option Name} {S : List (Option Name)} {l : Name} {n' : LabelIdx}
    (ha : a ≠ some l) (h : labelDepth (a :: S) l = .ok n') :
    ∃ n : LabelIdx, labelDepth S l = .ok n ∧ n'.toNat = n.toNat + 1 := by
  unfold labelDepth at h
  have hp : ¬ ((a == some l) = true) := by simpa using ha
  rw [List.findIdx?_cons, ite_neg' hp] at h
  cases hk : S.findIdx? (· == some l) with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h
    change toIdx (k + 1) = _ at h
    have h1 := toNat_of_toIdx h
    have h2 : n'.toNat < 2 ^ 32 := n'.value.isLt
    rw [h1] at h2
    have hlt : k < 2 ^ 32 := Nat.lt_of_succ_lt h2
    refine ⟨⟨⟨k, hlt⟩⟩, ?_, ?_⟩
    · unfold labelDepth
      rw [hk]
      show toIdx k = _
      rw [toIdx_ok, Idx.ofNat?_eq_some_iff]
      rfl
    · rw [h1]; rfl

theorem mapM_labelDepth_append {M : List (Option Name)} (X : List (Option Name)) :
    ∀ {ls : List Name} {ds : List LabelIdx}, ls.mapM (labelDepth M) = .ok ds →
      ls.mapM (labelDepth (M ++ X)) = .ok ds
  | [], ds, h => by simpa using h
  | l :: ls, ds, h => by
    simp only [List.mapM_cons, eok_bind, eok_pure] at h ⊢
    obtain ⟨d, hd, ds', hds', rfl⟩ := h
    exact ⟨d, labelDepth_append_ok X hd, ds', mapM_labelDepth_append X hds', rfl⟩

/-! ## Relocation of resolved code -/

theorem shiftLocalsL_append (base : Nat) :
    ∀ a b : List BExpr, shiftLocalsL base (a ++ b) = shiftLocalsL base a ++ shiftLocalsL base b
  | [], _ => rfl
  | e :: a, b => by
    simp only [List.cons_append, shiftLocalsL, shiftLocalsL_append base a b]

theorem retToBrL_append (d : Nat) :
    ∀ a b : List BExpr, retToBrL d (a ++ b) = retToBrL d a ++ retToBrL d b
  | [], _ => rfl
  | e :: a, b => by
    simp only [List.cons_append, retToBrL, retToBrL_append d a b]

theorem rel_append (d base : Nat) (a b : List BExpr) :
    retToBrL d (shiftLocalsL base (a ++ b)) =
      retToBrL d (shiftLocalsL base a) ++ retToBrL d (shiftLocalsL base b) := by
  rw [shiftLocalsL_append, retToBrL_append]

theorem rel_cons (d base : Nat) (e : BExpr) (a : List BExpr) :
    retToBrL d (shiftLocalsL base (e :: a)) =
      retToBrE d (shiftLocalsE base e) :: retToBrL d (shiftLocalsL base a) := rfl

theorem rel_nil (d base : Nat) : retToBrL d (shiftLocalsL base []) = [] := rfl

theorem rel_tail (d base : Nat) (ty : NTy) : retToBrL d (shiftLocalsL base ty.tail) = ty.tail := by
  cases ty <;> rfl

/-- A flat instruction that touches no local and is not `return`. -/
theorem rel_op (d base : Nat) (i : Instr) (args : List BExpr) (hs : shiftLocalInstr base i = i)
    (hr : i ≠ .return_) :
    retToBrE d (shiftLocalsE base (.op i args)) = .op i (retToBrL d (shiftLocalsL base args)) := by
  show retToBrE d (.op (shiftLocalInstr base i) (shiftLocalsL base args)) = _
  rw [hs]
  cases i <;> first | exact absurd rfl hr | rfl

/-- A flat instruction after relocation, when it is not `return`. -/
theorem rel_op' (d base : Nat) (i : Instr) (args : List BExpr)
    (hr : shiftLocalInstr base i ≠ .return_) :
    retToBrE d (shiftLocalsE base (.op i args)) =
      .op (shiftLocalInstr base i) (retToBrL d (shiftLocalsL base args)) := by
  show retToBrE d (.op (shiftLocalInstr base i) (shiftLocalsL base args)) = _
  generalize shiftLocalInstr base i = j at hr ⊢
  cases j <;> first | exact absurd rfl hr | rfl

theorem shift_lit (base : Nat) (c : Lit) : shiftLocalInstr base c.instr = c.instr := by
  cases c <;> rfl

theorem ne_lit (c : Lit) : c.instr ≠ .return_ := by
  cases c <;> simp [Lit.instr]

theorem shift_un (base : Nat) (op : UnOp) : shiftLocalInstr base op.instr = op.instr := by
  cases op <;> rfl

theorem ne_un (op : UnOp) : op.instr ≠ .return_ := by
  cases op <;> simp [UnOp.instr]

theorem shift_bin (base : Nat) (op : BinOp) : shiftLocalInstr base op.instr = op.instr := by
  cases op <;> rfl

theorem ne_bin (op : BinOp) : op.instr ≠ .return_ := by
  cases op <;> simp [BinOp.instr]

theorem gO_isSome (base : Nat) (fresh : Name) (c : Option NExpr) :
    (NExpr.returnToBrOpt fresh (NExpr.shiftLocalsOpt base c)).isSome = c.isSome := by
  cases c <;> rfl

/-! ## The relocated callee body -/

section Body

variable (E : NameEnv) (base : Nat) (fresh : Name) (L : List (Option Name))

mutual
/-- **The relocated body resolves to the relocated resolution.** -/
theorem resolve_inlined_body : ∀ (e : NExpr) (M : List (Option Name)) (bs bs' : List BExpr),
    some fresh ∉ M → fresh ∉ e.boundLabels → resolveE E M e = .ok bs →
    resolveE E (M ++ some fresh :: L) ((e.shiftLocals base).returnToBr fresh) = .ok bs' →
    bs' = retToBrL M.length (shiftLocalsL base bs)
  | .block none body ty, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE] at h h'
    have hb' : fresh ∉ NExpr.boundLabelsList body := fun hm => hb (by simp [NExpr.boundLabels, hm])
    exact resolve_inlined_bodyL body M bs bs' hM hb' h h'
  | .block (some l) body ty, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨b, hb1, rfl⟩ := h
    obtain ⟨b', hb1', rfl⟩ := h'
    have hl : l ≠ fresh := by rintro rfl; simp [NExpr.boundLabels] at hb
    have hb' : fresh ∉ NExpr.boundLabelsList body := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hM' : some fresh ∉ some l :: M := by
      simp only [List.mem_cons, not_or, Option.some.injEq]
      exact ⟨fun h => hl h.symm, hM⟩
    have ih := resolve_inlined_bodyL body (some l :: M) b b' hM' hb' hb1 hb1'
    rw [rel_cons, rel_tail, ih]
    simp [shiftLocalsE, retToBrE]
  | .loop lo body ty, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨b, hb1, rfl⟩ := h
    obtain ⟨b', hb1', rfl⟩ := h'
    have hb' : fresh ∉ NExpr.boundLabels body := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hM' : some fresh ∉ lo :: M := by
      simp only [List.mem_cons, not_or]
      refine ⟨?_, hM⟩
      intro hlo
      subst hlo
      simp [NExpr.boundLabels] at hb
    have ih := resolve_inlined_body body (lo :: M) b b' hM' hb' hb1 hb1'
    rw [rel_cons, rel_tail, ih]
    simp [shiftLocalsE, retToBrE]
  | .if_ c t e ty, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨c₁, hc, t₁, ht, e₁, he, rfl⟩ := h
    obtain ⟨c₂, hc', t₂, ht', e₂, he', rfl⟩ := h'
    have hbc : fresh ∉ NExpr.boundLabels c := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbt : fresh ∉ NExpr.boundLabels t := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbe : fresh ∉ NExpr.boundLabelsOpt e := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hM' : some fresh ∉ none :: M := by simp [hM]
    have ic := resolve_inlined_body c M c₁ c₂ hM hbc hc hc'
    have it := resolve_inlined_body t (none :: M) t₁ t₂ hM' hbt ht ht'
    have ie := resolve_inlined_bodyO e (none :: M) e₁ e₂ hM' hbe he he'
    rw [rel_cons, rel_tail, ic, it, ie]
    simp [shiftLocalsE, retToBrE]
  | .br l v c, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨d, hd, v₁, hv, c₁, hc, rfl⟩ := h
    obtain ⟨d', hd', v₂, hv', c₂, hc', rfl⟩ := h'
    rw [labelDepth_append_ok _ hd] at hd'
    cases hd'
    have hbv : fresh ∉ NExpr.boundLabelsOpt v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbc : fresh ∉ NExpr.boundLabelsOpt c := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_bodyO v M v₁ v₂ hM hbv hv hv'
    have ic := resolve_inlined_bodyO c M c₁ c₂ hM hbc hc hc'
    rw [gO_isSome, rel_cons, rel_nil, iv, ic]
    by_cases hcs : c.isSome = true
    · rw [ite_pos' hcs, rel_op M.length base (.brIf d) (v₁ ++ c₁) rfl (by simp), rel_append]
    · rw [ite_neg' hcs, rel_op M.length base (.br d) (v₁ ++ c₁) rfl (by simp), rel_append]
  | .switch ls dl v c, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨ds, hds, d, hd, v₁, hv, c₁, hc, rfl⟩ := h
    obtain ⟨ds', hds', d', hd', v₂, hv', c₂, hc', rfl⟩ := h'
    rw [labelDepth_append_ok _ hd] at hd'
    cases hd'
    rw [mapM_labelDepth_append _ hds] at hds'
    cases hds'
    have hbv : fresh ∉ NExpr.boundLabelsOpt v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbc : fresh ∉ NExpr.boundLabels c := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_bodyO v M v₁ v₂ hM hbv hv hv'
    have ic := resolve_inlined_body c M c₁ c₂ hM hbc hc hc'
    rw [rel_cons, rel_nil, rel_op M.length base (.brTable ds d) (v₁ ++ c₁) rfl (by simp),
      rel_append, iv, ic]
  | .call f args, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨fi, hf, a₁, ha, rfl⟩ := h
    obtain ⟨fi', hf', a₂, ha', rfl⟩ := h'
    rw [hf] at hf'
    cases hf'
    have hba : fresh ∉ NExpr.boundLabelsList args := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have ia := resolve_inlined_bodyL args M a₁ a₂ hM hba ha ha'
    rw [rel_cons, rel_nil, rel_op M.length base (.call fi) a₁ rfl (by simp), ia]
  | .localGet i, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨x', hx', rfl⟩ := h'
    rw [rel_cons, rel_nil, rel_op' M.length base (.localGet x) [] (by simp [shiftLocalInstr])]
    simp only [shiftLocalInstr, shiftIdx_of_toIdx hx hx']
    rfl
  | .localSet i v tee, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨x, hx, v₁, hv, rfl⟩ := h
    obtain ⟨x', hx', v₂, hv', rfl⟩ := h'
    have hbv : fresh ∉ NExpr.boundLabels v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_body v M v₁ v₂ hM hbv hv hv'
    rw [rel_cons, rel_nil, iv]
    cases tee
    · rw [ite_neg' (by simp), ite_neg' (by simp),
        rel_op' M.length base (.localSet x) v₁ (by simp [shiftLocalInstr])]
      simp only [shiftLocalInstr, shiftIdx_of_toIdx hx hx']
    · rw [ite_pos' rfl, ite_pos' rfl,
        rel_op' M.length base (.localTee x) v₁ (by simp [shiftLocalInstr])]
      simp only [shiftLocalInstr, shiftIdx_of_toIdx hx hx']
  | .globalGet g, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨x', hx', rfl⟩ := h'
    rw [hx] at hx'
    cases hx'
    rw [rel_cons, rel_nil, rel_op M.length base (.globalGet x) [] rfl (by simp)]
    rfl
  | .globalSet g v, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨x, hx, v₁, hv, rfl⟩ := h
    obtain ⟨x', hx', v₂, hv', rfl⟩ := h'
    rw [hx] at hx'
    cases hx'
    have hbv : fresh ∉ NExpr.boundLabels v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_body v M v₁ v₂ hM hbv hv hv'
    rw [rel_cons, rel_nil, rel_op M.length base (.globalSet x) v₁ rfl (by simp), iv]
  | .const c, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_pure] at h h'
    subst h h'
    rw [rel_cons, rel_nil, rel_op M.length base c.instr [] (shift_lit base c) (ne_lit c)]
    rfl
  | .unary op v, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨v₁, hv, rfl⟩ := h
    obtain ⟨v₂, hv', rfl⟩ := h'
    have hbv : fresh ∉ NExpr.boundLabels v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_body v M v₁ v₂ hM hbv hv hv'
    rw [rel_cons, rel_nil, rel_op M.length base op.instr v₁ (shift_un base op) (ne_un op), iv]
  | .drop v, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨v₁, hv, rfl⟩ := h
    obtain ⟨v₂, hv', rfl⟩ := h'
    have hbv : fresh ∉ NExpr.boundLabels v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_body v M v₁ v₂ hM hbv hv hv'
    rw [rel_cons, rel_nil, rel_op M.length base .drop v₁ rfl (by simp), iv]
  | .binary op a b, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨a₁, ha, b₁, hb₁, rfl⟩ := h
    obtain ⟨a₂, ha', b₂, hb₂, rfl⟩ := h'
    have hba : fresh ∉ NExpr.boundLabels a := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbb : fresh ∉ NExpr.boundLabels b := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have ia := resolve_inlined_body a M a₁ a₂ hM hba ha ha'
    have ib := resolve_inlined_body b M b₁ b₂ hM hbb hb₁ hb₂
    rw [rel_cons, rel_nil, rel_op M.length base op.instr (a₁ ++ b₁) (shift_bin base op) (ne_bin op),
      rel_append, ia, ib]
  | .select a b c, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨a₁, ha, b₁, hb₁, c₁, hc₁, rfl⟩ := h
    obtain ⟨a₂, ha', b₂, hb₂, c₂, hc₂, rfl⟩ := h'
    have hba : fresh ∉ NExpr.boundLabels a := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbb : fresh ∉ NExpr.boundLabels b := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have hbc : fresh ∉ NExpr.boundLabels c := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have ia := resolve_inlined_body a M a₁ a₂ hM hba ha ha'
    have ib := resolve_inlined_body b M b₁ b₂ hM hbb hb₁ hb₂
    have ic := resolve_inlined_body c M c₁ c₂ hM hbc hc₁ hc₂
    rw [rel_cons, rel_nil, rel_op M.length base (.select none) (a₁ ++ b₁ ++ c₁) rfl (by simp),
      rel_append, rel_append, ia, ib, ic]
  | .return_ v, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨v₁, hv, rfl⟩ := h
    obtain ⟨d, hd, v₂, hv', c₂, hc₂, rfl⟩ := h'
    rw [labelDepth_fresh hM L] at hd
    have hc₂' : c₂ = [] := by
      simp only [resolveO, eok_pure] at hc₂
      exact hc₂.symm
    subst hc₂'
    have hbv : fresh ∉ NExpr.boundLabelsOpt v := fun hm => hb (by simp [NExpr.boundLabels, hm])
    have iv := resolve_inlined_bodyO v M v₁ v₂ hM hbv hv hv'
    rw [rel_cons, rel_nil, iv, ← labelIdx_of_toIdx hd]
    simp [shiftLocalsE, shiftLocalInstr, retToBrE]
  | .nop, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_pure] at h h'
    subst h h'
    rw [rel_cons, rel_nil, rel_op M.length base .nop [] rfl (by simp)]
    rfl
  | .unreachable, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocals, NExpr.returnToBr, resolveE, eok_pure] at h h'
    subst h h'
    rw [rel_cons, rel_nil, rel_op M.length base .unreachable [] rfl (by simp)]
    rfl

/-- `resolve_inlined_body` on a list. -/
theorem resolve_inlined_bodyL : ∀ (es : List NExpr) (M : List (Option Name)) (bs bs' : List BExpr),
    some fresh ∉ M → fresh ∉ NExpr.boundLabelsList es → resolveL E M es = .ok bs →
    resolveL E (M ++ some fresh :: L)
      (NExpr.returnToBrList fresh (NExpr.shiftLocalsList base es)) = .ok bs' →
    bs' = retToBrL M.length (shiftLocalsL base bs)
  | [], M, bs, bs', _, _, h, h' => by
    simp only [NExpr.shiftLocalsList, NExpr.returnToBrList, resolveL, eok_pure] at h h'
    subst h h'
    rfl
  | e :: es, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocalsList, NExpr.returnToBrList, resolveL, eok_bind, eok_pure] at h h'
    obtain ⟨a, ha, b, hb₁, rfl⟩ := h
    obtain ⟨a', ha', b', hb₁', rfl⟩ := h'
    have hbe : fresh ∉ NExpr.boundLabels e := fun hm => hb (by simp [NExpr.boundLabelsList, hm])
    have hbs : fresh ∉ NExpr.boundLabelsList es :=
      fun hm => hb (by simp [NExpr.boundLabelsList, hm])
    rw [rel_append, resolve_inlined_body e M a a' hM hbe ha ha',
      resolve_inlined_bodyL es M b b' hM hbs hb₁ hb₁']

/-- `resolve_inlined_body` on an optional child. -/
theorem resolve_inlined_bodyO : ∀ (e : Option NExpr) (M : List (Option Name)) (bs bs' : List BExpr),
    some fresh ∉ M → fresh ∉ NExpr.boundLabelsOpt e → resolveO E M e = .ok bs →
    resolveO E (M ++ some fresh :: L)
      (NExpr.returnToBrOpt fresh (NExpr.shiftLocalsOpt base e)) = .ok bs' →
    bs' = retToBrL M.length (shiftLocalsL base bs)
  | none, M, bs, bs', _, _, h, h' => by
    simp only [NExpr.shiftLocalsOpt, NExpr.returnToBrOpt, resolveO, eok_pure] at h h'
    subst h h'
    rfl
  | some e, M, bs, bs', hM, hb, h, h' => by
    simp only [NExpr.shiftLocalsOpt, NExpr.returnToBrOpt, resolveO] at h h'
    have hb' : fresh ∉ NExpr.boundLabels e := fun hm => hb (by simp [NExpr.boundLabelsOpt, hm])
    exact resolve_inlined_body e M bs bs' hM hb' h h'
end

end Body

/-! ## Expressions without free labels ignore the outer break stack -/

theorem mapM_labelDepth_irrel {S : List (Option Name)} (X Y : List (Option Name)) :
    ∀ {ls : List Name}, (∀ l ∈ ls, some l ∈ S) →
      ls.mapM (labelDepth (S ++ X)) = ls.mapM (labelDepth (S ++ Y))
  | [], _ => by simp
  | l :: ls, h => by
    have h1 := h l (by simp)
    have ih := mapM_labelDepth_irrel X Y (ls := ls) (fun l' hl' => h l' (by simp [hl']))
    simp only [List.mapM_cons, labelDepth_append_of_mem h1, ih]

section Outer

variable (E : NameEnv)

mutual
/-- **Outer-stack irrelevance.** -/
theorem resolve_outer_irrel : ∀ (e : NExpr) (S X Y : List (Option Name)),
    (∀ l ∈ e.freeLabels, some l ∈ S) → resolveE E (S ++ X) e = resolveE E (S ++ Y) e
  | .block none body ty, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE]
    exact resolve_outer_irrelL body S X Y (fun l hl => h l (by simpa using hl))
  | .block (some l) body ty, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_filter] at h
    have ih := resolve_outer_irrelL body (some l :: S) X Y (fun l' hl' => by
      by_cases hll : l' = l
      · simp [hll]
      · exact List.mem_cons_of_mem _ (h l' ⟨hl', by simpa using hll⟩))
    simp only [List.cons_append] at ih
    simp only [resolveE, ih]
  | .loop lo body ty, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_filter] at h
    have ih := resolve_outer_irrel body (lo :: S) X Y (fun l' hl' => by
      by_cases hll : some l' = lo
      · simp [hll]
      · exact List.mem_cons_of_mem _ (h l' ⟨hl', by simpa using hll⟩))
    simp only [List.cons_append] at ih
    simp only [resolveE, ih]
  | .if_ c t e ty, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_append] at h
    have ic := resolve_outer_irrel c S X Y (fun l hl => h l (Or.inl (Or.inl hl)))
    have it := resolve_outer_irrel t (none :: S) X Y
      (fun l hl => List.mem_cons_of_mem _ (h l (Or.inl (Or.inr hl))))
    have ie := resolve_outer_irrelO e (none :: S) X Y
      (fun l hl => List.mem_cons_of_mem _ (h l (Or.inr hl)))
    simp only [List.cons_append] at it ie
    simp only [resolveE, ic, it, ie]
  | .br l v c, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_cons, List.mem_append] at h
    have iv := resolve_outer_irrelO v S X Y (fun l' hl' => h l' (Or.inr (Or.inl hl')))
    have ic := resolve_outer_irrelO c S X Y (fun l' hl' => h l' (Or.inr (Or.inr hl')))
    simp only [resolveE, iv, ic, labelDepth_append_of_mem (h l (Or.inl rfl))]
  | .switch ls dl v c, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_cons, List.mem_append] at h
    have iv := resolve_outer_irrelO v S X Y (fun l' hl' => h l' (Or.inr (Or.inr (Or.inl hl'))))
    have ic := resolve_outer_irrel c S X Y (fun l' hl' => h l' (Or.inr (Or.inr (Or.inr hl'))))
    have ils := mapM_labelDepth_irrel X Y (S := S) (ls := ls) (fun l' hl' => h l' (Or.inl hl'))
    simp only [resolveE, iv, ic, ils, labelDepth_append_of_mem (h dl (Or.inr (Or.inl rfl)))]
  | .call f args, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrelL args S X Y h]
  | .localGet i, S, X, Y, _ => by simp only [resolveE]
  | .localSet i v tee, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrel v S X Y h]
  | .globalGet g, S, X, Y, _ => by simp only [resolveE]
  | .globalSet g v, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrel v S X Y h]
  | .const c, S, X, Y, _ => by simp only [resolveE]
  | .unary op v, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrel v S X Y h]
  | .drop v, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrel v S X Y h]
  | .binary op a b, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_append] at h
    simp only [resolveE, resolve_outer_irrel a S X Y (fun l hl => h l (Or.inl hl)),
      resolve_outer_irrel b S X Y (fun l hl => h l (Or.inr hl))]
  | .select a b c, S, X, Y, h => by
    simp only [NExpr.freeLabels, List.mem_append] at h
    simp only [resolveE, resolve_outer_irrel a S X Y (fun l hl => h l (Or.inl (Or.inl hl))),
      resolve_outer_irrel b S X Y (fun l hl => h l (Or.inl (Or.inr hl))),
      resolve_outer_irrel c S X Y (fun l hl => h l (Or.inr hl))]
  | .return_ v, S, X, Y, h => by
    simp only [NExpr.freeLabels] at h
    simp only [resolveE, resolve_outer_irrelO v S X Y h]
  | .nop, S, X, Y, _ => by simp only [resolveE]
  | .unreachable, S, X, Y, _ => by simp only [resolveE]

/-- `resolve_outer_irrel` on a list. -/
theorem resolve_outer_irrelL : ∀ (es : List NExpr) (S X Y : List (Option Name)),
    (∀ l ∈ NExpr.freeLabelsList es, some l ∈ S) → resolveL E (S ++ X) es = resolveL E (S ++ Y) es
  | [], _, _, _, _ => by simp only [resolveL]
  | e :: es, S, X, Y, h => by
    simp only [NExpr.freeLabelsList, List.mem_append] at h
    simp only [resolveL, resolve_outer_irrel e S X Y (fun l hl => h l (Or.inl hl)),
      resolve_outer_irrelL es S X Y (fun l hl => h l (Or.inr hl))]

/-- `resolve_outer_irrel` on an optional child. -/
theorem resolve_outer_irrelO : ∀ (e : Option NExpr) (S X Y : List (Option Name)),
    (∀ l ∈ NExpr.freeLabelsOpt e, some l ∈ S) → resolveO E (S ++ X) e = resolveO E (S ++ Y) e
  | none, _, _, _, _ => by simp only [resolveO]
  | some e, S, X, Y, h => by
    simp only [NExpr.freeLabelsOpt] at h
    simp only [resolveO, resolve_outer_irrel e S X Y h]
end

end Outer

/-! ## Free labels appear among the break targets -/

theorem bt_nil : (effectsList []).breakTargets = [] := rfl

theorem bt_cons (e : BExpr) (es : List BExpr) :
    (effectsList (e :: es)).breakTargets =
      (effects e).breakTargets ++ (effectsList es).breakTargets := by
  simp [effectsList, Effects.merge]

theorem bt_append : ∀ (a b : List BExpr),
    (effectsList (a ++ b)).breakTargets =
      (effectsList a).breakTargets ++ (effectsList b).breakTargets
  | [], b => by simp [bt_nil]
  | e :: a, b => by simp [bt_cons, bt_append a b]

theorem bt_op (i : Instr) (args : List BExpr) :
    (effects (.op i args)).breakTargets =
      (effectsList args).breakTargets ++ (instrEffects i).breakTargets := by
  simp [effects, Effects.merge]

theorem bt_block (bt : BlockType) (b : List BExpr) :
    (effects (.block bt b)).breakTargets = unbind (effectsList b).breakTargets := by
  simp [effects, Effects.unbindLabel]

theorem bt_loop (bt : BlockType) (b : List BExpr) :
    (effects (.loop bt b)).breakTargets = unbind (effectsList b).breakTargets := by
  simp [effects, Effects.unbindLabel]

theorem bt_if (bt : BlockType) (c t e : List BExpr) :
    (effects (.if_ bt c t e)).breakTargets = (effectsList c).breakTargets ++
      unbind ((effectsList t).breakTargets ++ (effectsList e).breakTargets) := by
  simp [effects, Effects.merge, Effects.unbindLabel]

theorem mem_unbind {n : Nat} {ns : List Nat} (h : n + 1 ∈ ns) : n ∈ unbind ns := by
  unfold unbind
  rw [List.mem_filterMap]
  exact ⟨n + 1, h, by simp⟩

theorem mapM_labelDepth_mem {S : List (Option Name)} :
    ∀ {ls : List Name} {ds : List LabelIdx}, ls.mapM (labelDepth S) = .ok ds →
      ∀ l ∈ ls, ∃ n, labelDepth S l = .ok n ∧ n ∈ ds
  | [], _, _, l, hl => by simp at hl
  | l₀ :: ls, ds, h, l, hl => by
    simp only [List.mapM_cons, eok_bind, eok_pure] at h
    obtain ⟨d, hd, ds', hds', rfl⟩ := h
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨d, hd, by simp⟩
    · obtain ⟨n, hn, hmem⟩ := mapM_labelDepth_mem hds' l hl
      exact ⟨n, hn, by simp [hmem]⟩

/-- Leaving a scope: a free label of the body other than the scope's own. -/
theorem free_scope {a : Option Name} {S : List (Option Name)} {l : Name} {bts : List Nat}
    (ha : a ≠ some l)
    (h : ∃ n : LabelIdx, labelDepth (a :: S) l = .ok n ∧ n.toNat ∈ bts) :
    ∃ n : LabelIdx, labelDepth S l = .ok n ∧ n.toNat ∈ unbind bts := by
  obtain ⟨n', hn', hmem⟩ := h
  obtain ⟨n, hn, hnn⟩ := labelDepth_cons_ne ha hn'
  exact ⟨n, hn, mem_unbind (hnn ▸ hmem)⟩

section Free

variable (E : NameEnv)

mutual
/-- **A free label is a break target of the resolved code.** -/
theorem resolve_free_breakTargets : ∀ (e : NExpr) (S : List (Option Name)) (bs : List BExpr),
    resolveE E S e = .ok bs → ∀ l ∈ e.freeLabels,
      ∃ n : LabelIdx, labelDepth S l = .ok n ∧ n.toNat ∈ (effectsList bs).breakTargets
  | .block none body ty, S, bs, h, l, hl => by
    simp only [resolveE] at h
    simp only [NExpr.freeLabels, List.mem_filter] at hl
    exact resolve_free_breakTargetsL body S bs h l hl.1
  | .block (some l') body ty, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_filter] at hl
    have hne : some l' ≠ some l := by
      intro he; simp [← Option.some.inj he] at hl
    obtain ⟨n, hn, hmem⟩ := free_scope hne (resolve_free_breakTargetsL body _ b hb l hl.1)
    exact ⟨n, hn, by rw [bt_cons, bt_block]; exact List.mem_append_left _ hmem⟩
  | .loop lo body ty, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_filter] at hl
    have hne : lo ≠ some l := by
      intro he; simp [he] at hl
    obtain ⟨n, hn, hmem⟩ := free_scope hne (resolve_free_breakTargets body _ b hb l hl.1)
    exact ⟨n, hn, by rw [bt_cons, bt_loop]; exact List.mem_append_left _ hmem⟩
  | .if_ c t e ty, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨c₁, hc, t₁, ht, e₁, he, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_append] at hl
    rw [bt_cons, bt_if]
    rcases hl with (hl | hl) | hl
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets c S c₁ hc l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _ hmem)⟩
    · obtain ⟨n, hn, hmem⟩ := free_scope (by simp) (resolve_free_breakTargets t _ t₁ ht l hl)
      refine ⟨n, hn, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      unfold unbind at hmem ⊢
      rw [List.mem_filterMap] at hmem ⊢
      obtain ⟨a, ha, hfa⟩ := hmem
      exact ⟨a, List.mem_append_left _ ha, hfa⟩
    · obtain ⟨n, hn, hmem⟩ := free_scope (by simp) (resolve_free_breakTargetsO e _ e₁ he l hl)
      refine ⟨n, hn, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      unfold unbind at hmem ⊢
      rw [List.mem_filterMap] at hmem ⊢
      obtain ⟨a, ha, hfa⟩ := hmem
      exact ⟨a, List.mem_append_right _ ha, hfa⟩
  | .br l₀ v c, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨d, hd, v₁, hv, c₁, hc, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_cons, List.mem_append] at hl
    rw [bt_cons, bt_op, bt_append]
    rcases hl with rfl | hl | hl
    · refine ⟨d, hd, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      cases c.isSome <;> simp [instrEffects]
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsO v S v₁ hv l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsO c S c₁ hc l hl
      exact ⟨n, hn,
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))⟩
  | .switch ls dl v c, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨ds, hds, d, hd, v₁, hv, c₁, hc, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_cons, List.mem_append] at hl
    rw [bt_cons, bt_op, bt_append]
    rcases hl with hl | rfl | hl | hl
    · obtain ⟨n, hn, hmem⟩ := mapM_labelDepth_mem hds l hl
      refine ⟨n, hn, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      simp only [instrEffects, List.mem_cons, List.mem_map]
      exact Or.inr ⟨n, hmem, rfl⟩
    · exact ⟨d, hd, List.mem_append_left _ (List.mem_append_right _ (by simp [instrEffects]))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsO v S v₁ hv l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets c S c₁ hc l hl
      exact ⟨n, hn,
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))⟩
  | .call f args, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨fi, _, a₁, ha, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsL args S a₁ ha l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .localGet i, S, bs, h, l, hl => by simp [NExpr.freeLabels] at hl
  | .localSet i v tee, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨x, _, v₁, hv, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets v S v₁ hv l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .globalGet g, S, bs, h, l, hl => by simp [NExpr.freeLabels] at hl
  | .globalSet g v, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨x, _, v₁, hv, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets v S v₁ hv l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .const c, S, bs, h, l, hl => by simp [NExpr.freeLabels] at hl
  | .unary op v, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨v₁, hv, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets v S v₁ hv l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .drop v, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨v₁, hv, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets v S v₁ hv l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .binary op a b, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨a₁, ha, b₁, hb, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_append] at hl
    rw [bt_cons, bt_op, bt_append]
    rcases hl with hl | hl
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets a S a₁ ha l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets b S b₁ hb l hl
      exact ⟨n, hn,
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))⟩
  | .select a b c, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨a₁, ha, b₁, hb, c₁, hc, rfl⟩ := h
    simp only [NExpr.freeLabels, List.mem_append] at hl
    rw [bt_cons, bt_op, bt_append, bt_append]
    rcases hl with (hl | hl) | hl
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets a S a₁ ha l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hmem)))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets b S b₁ hb l hl
      exact ⟨n, hn, List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ hmem)))⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets c S c₁ hc l hl
      exact ⟨n, hn,
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))⟩
  | .return_ v, S, bs, h, l, hl => by
    simp only [resolveE, eok_bind, eok_pure] at h
    obtain ⟨v₁, hv, rfl⟩ := h
    simp only [NExpr.freeLabels] at hl
    obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsO v S v₁ hv l hl
    exact ⟨n, hn, by
      rw [bt_cons, bt_op]; exact List.mem_append_left _ (List.mem_append_left _ hmem)⟩
  | .nop, S, bs, h, l, hl => by simp [NExpr.freeLabels] at hl
  | .unreachable, S, bs, h, l, hl => by simp [NExpr.freeLabels] at hl

/-- `resolve_free_breakTargets` on a list. -/
theorem resolve_free_breakTargetsL : ∀ (es : List NExpr) (S : List (Option Name))
    (bs : List BExpr), resolveL E S es = .ok bs → ∀ l ∈ NExpr.freeLabelsList es,
      ∃ n : LabelIdx, labelDepth S l = .ok n ∧ n.toNat ∈ (effectsList bs).breakTargets
  | [], S, bs, h, l, hl => by simp [NExpr.freeLabelsList] at hl
  | e :: es, S, bs, h, l, hl => by
    simp only [resolveL, eok_bind, eok_pure] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [NExpr.freeLabelsList, List.mem_append] at hl
    rw [bt_append]
    rcases hl with hl | hl
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargets e S a ha l hl
      exact ⟨n, hn, List.mem_append_left _ hmem⟩
    · obtain ⟨n, hn, hmem⟩ := resolve_free_breakTargetsL es S b hb l hl
      exact ⟨n, hn, List.mem_append_right _ hmem⟩

/-- `resolve_free_breakTargets` on an optional child. -/
theorem resolve_free_breakTargetsO : ∀ (e : Option NExpr) (S : List (Option Name))
    (bs : List BExpr), resolveO E S e = .ok bs → ∀ l ∈ NExpr.freeLabelsOpt e,
      ∃ n : LabelIdx, labelDepth S l = .ok n ∧ n.toNat ∈ (effectsList bs).breakTargets
  | none, S, bs, h, l, hl => by simp [NExpr.freeLabelsOpt] at hl
  | some e, S, bs, h, l, hl => by
    simp only [resolveO] at h
    simp only [NExpr.freeLabelsOpt] at hl
    exact resolve_free_breakTargets e S bs h l hl
end

end Free

/-! ## Lists of stores -/

theorem resolveL_append_inv {E : NameEnv} {S : List (Option Name)} :
    ∀ {a b : List NExpr} {c : List BExpr}, resolveL E S (a ++ b) = .ok c →
      ∃ x y, resolveL E S a = .ok x ∧ resolveL E S b = .ok y ∧ c = x ++ y
  | [], b, c, h => ⟨[], c, by simp [resolveL, pure, Except.pure], by simpa using h, by simp⟩
  | e :: a, b, c, h => by
    simp only [List.cons_append, resolveL, eok_bind, eok_pure] at h
    obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := h
    obtain ⟨x, y, hx, hy, rfl⟩ := resolveL_append_inv hy₀
    refine ⟨x₀ ++ x, y, ?_, hy, by simp⟩
    simp only [resolveL, eok_bind, eok_pure]
    exact ⟨x₀, hx₀, x, hx, rfl⟩

theorem freeLabelsList_mapIdx {α : Type} (g : α → List Name) :
    ∀ (xs : List α) (f : Nat → α → NExpr), (∀ j a, (f j a).freeLabels = g a) →
      NExpr.freeLabelsList (xs.mapIdx f) = xs.flatMap g
  | [], _, _ => by simp [NExpr.freeLabelsList]
  | a :: xs, f, hf => by
    rw [List.mapIdx_cons]
    simp only [NExpr.freeLabelsList, hf, List.flatMap_cons,
      freeLabelsList_mapIdx g xs (fun i => f (i + 1)) (fun j a => hf (j + 1) a)]

theorem freeLabelsList_flatMap : ∀ (xs : List NExpr),
    xs.flatMap NExpr.freeLabels = NExpr.freeLabelsList xs
  | [] => by simp [NExpr.freeLabelsList]
  | a :: xs => by simp [NExpr.freeLabelsList, freeLabelsList_flatMap xs]

theorem resultTy_tail (rs : List ValType) : (resultTy rs).tail = [] := by
  unfold resultTy
  split <;> rfl

/-- **The shape of Binaryen's inlined block after resolution.** The operand
stores and the re-zeroing resolve as they would outside the block (the operands
have no free labels), and the relocated body resolves to the D-level relocation of
the body's own resolution. -/
theorem inlineN_resolve_shape {E : NameEnv} {L : List (Option Name)} {callee : NFunc}
    {base : Nat} {args : List NExpr} {fresh : Name} {bsN bsArgs bsBody : List BExpr}
    (hfresh : fresh ∉ callee.body.boundLabels)
    (hN : resolveE E L (inlineN callee base args fresh) = .ok bsN)
    (hA : resolveL E L args = .ok bsArgs) (hB : resolveE E [] callee.body = .ok bsBody)
    (hbt : (effectsList bsArgs).breakTargets = []) :
    ∃ SB ZB, resolveL E L (args.mapIdx fun j a => NExpr.localSet (base + j) a false) = .ok SB ∧
      resolveL E L (callee.vars.mapIdx fun j t =>
        NExpr.localSet (base + callee.params.length + j) (.const (zeroLit t)) false) = .ok ZB ∧
      bsN = [.block (resultTy callee.results).blockType
        (SB ++ ZB ++ retToBrL 0 (shiftLocalsL base bsBody))] := by
  -- the operands have no free labels
  have hnf : ∀ l ∈ NExpr.freeLabelsList args, False := by
    intro l hl
    obtain ⟨n, _, hmem⟩ := resolve_free_breakTargetsL E args L bsArgs hA l hl
    rw [hbt] at hmem
    simp at hmem
  simp only [inlineN, resolveE, eok_bind, eok_pure] at hN
  obtain ⟨b, hb, rfl⟩ := hN
  obtain ⟨xz, yb, hxz, hyb, rfl⟩ := resolveL_append_inv hb
  obtain ⟨x, z, hx, hz, rfl⟩ := resolveL_append_inv hxz
  -- the relocated body
  simp only [resolveL, eok_bind, eok_pure] at hyb
  obtain ⟨bb, hbb, yy, hyy, rfl⟩ := hyb
  have hyy' : yy = [] := hyy.symm
  subst hyy'
  have hbody := resolve_inlined_body E base fresh L callee.body [] bsBody bb (by simp) hfresh hB
    (by simpa using hbb)
  -- the stores, outside the block
  have hsets := resolve_outer_irrelL E (args.mapIdx fun j a => NExpr.localSet (base + j) a false)
    [] (some fresh :: L) L (by
      intro l hl
      rw [freeLabelsList_mapIdx NExpr.freeLabels args
        (fun j a => NExpr.localSet (base + j) a false) (fun _ _ => rfl),
        freeLabelsList_flatMap] at hl
      exact (hnf l hl).elim)
  have hzeros := resolve_outer_irrelL E (callee.vars.mapIdx fun j t =>
      NExpr.localSet (base + callee.params.length + j) (.const (zeroLit t)) false)
    [] (some fresh :: L) L (by
      intro l hl
      rw [freeLabelsList_mapIdx (fun _ => []) callee.vars
        (fun j t => NExpr.localSet (base + callee.params.length + j) (.const (zeroLit t)) false)
        (fun _ _ => rfl)] at hl
      simp at hl)
  simp only [List.nil_append] at hsets hzeros
  refine ⟨x, z, ?_, ?_, ?_⟩
  · rw [← hsets]; exact hx
  · rw [← hzeros]; exact hz
  · rw [resultTy_tail, hbody]
    simp

/-- **The operand stores, spelled out.** Each operand `aⱼ` resolves (outside the
block) to `bsⱼ`, the operands together to `bsArgs = bs₀ ++ bs₁ ++ …`, and the stores to
`local.set (base + j)` applied to `bsⱼ`. -/
theorem resolve_sets {E : NameEnv} {L : List (Option Name)} :
    ∀ (args : List NExpr) (base : Nat) (f : Nat → NExpr → NExpr) (SB bsArgs : List BExpr),
      (∀ j a, f j a = NExpr.localSet (base + j) a false) →
      resolveL E L (args.mapIdx f) = .ok SB → resolveL E L args = .ok bsArgs →
      ∃ (bss : List (List BExpr)) (xs : List LocalIdx),
        bss.length = args.length ∧ xs.length = args.length ∧
        (∀ (j : Nat) (x : LocalIdx), xs[j]? = some x → x.toNat = base + j) ∧
        (∀ (j : Nat) (a : NExpr) (bs : List BExpr), args[j]? = some a → bss[j]? = some bs →
          resolveE E L a = .ok bs) ∧
        bsArgs = bss.flatten ∧
        SB = List.zipWith (fun x bs => BExpr.op (.localSet x) bs) xs bss
  | [], base, f, SB, bsArgs, _, h, h' => by
    simp only [List.mapIdx_nil, resolveL, eok_pure] at h h'
    subst h h'
    exact ⟨[], [], rfl, rfl, by simp, by simp, rfl, rfl⟩
  | a :: args, base, f, SB, bsArgs, hf, h, h' => by
    rw [List.mapIdx_cons, hf] at h
    simp only [resolveL, resolveE, eok_bind, eok_pure] at h h'
    obtain ⟨s₀, ⟨x₀, hx₀, v₀, hv₀, rfl⟩, rest, hrest, rfl⟩ := h
    obtain ⟨a₀, ha₀, as₀, has₀, rfl⟩ := h'
    rw [hv₀] at ha₀
    cases ha₀
    obtain ⟨bss, xs, hl1, hl2, hxs, hres, rfl, rfl⟩ :=
      resolve_sets args (base + 1) (fun i => f (i + 1)) rest as₀
        (fun j a => by show f (j + 1) a = _; rw [hf]; congr 1; omega) hrest has₀
    refine ⟨v₀ :: bss, x₀ :: xs, by simp [hl1], by simp [hl2], ?_, ?_, by simp, ?_⟩
    · intro j x hx
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        simpa using toNat_of_toIdx hx₀
      | succ j =>
        simp only [List.getElem?_cons_succ] at hx
        rw [hxs j x hx]
        omega
    · intro j a' bs ha' hbs
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha' hbs
        subst ha' hbs
        exact hv₀
      | succ j =>
        simp only [List.getElem?_cons_succ] at ha' hbs
        exact hres j a' bs ha' hbs
    · simp

end InlineRes

end Silmaril.Wasm.Binaryen
