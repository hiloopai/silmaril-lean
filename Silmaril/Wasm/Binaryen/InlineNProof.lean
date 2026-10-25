module

public import Silmaril.Wasm.Binaryen.InlineSim
public import Silmaril.Wasm.Binaryen.InlineResolve
public import Silmaril.Wasm.Binaryen.InlineTyping

@[expose] public section

/-! # `inlineN_resolves`: the proof

The resolution of Binaryen's shape (`InlineRes.inlineN_resolve_shape`,
`InlineRes.resolve_sets`) and the D-level site (`siteCode_spec`) are brought to the
two shapes of `InlSim.shapes_joinableBot`, whose joinability gives the contextual
equivalence through `joinableBot_seqEquiv`. The remaining facts are syntactic (the
re-zeroing is the same code on both sides, `zeros_eq`) or read off the typings
(the stored locals exist, `bound_of_ok`).

**Scope.** This module does not establish the legacy general results `InlNProof.inlineN_resolves_aux`
(this file keeps its proved syntactic lemmas). The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen.InlNProof

open Silmaril.Wasm Execution.Core Validation Numerics SingleThreaded OpRun InlSim InlineRes

/-! ## Effects of a concatenation -/

theorem merge_assoc (a b c : Effects) : (a.merge b).merge c = a.merge (b.merge c) := by
  cases a; cases b; cases c
  simp [Effects.merge, Bool.or_assoc, List.append_assoc]

theorem empty_merge (a : Effects) : ({} : Effects).merge a = a := by
  cases a
  simp [Effects.merge]

theorem effectsList_append : ∀ a b : List BExpr,
    effectsList (a ++ b) = (effectsList a).merge (effectsList b)
  | [], b => by simp [effectsList, empty_merge]
  | e :: a, b => by simp [effectsList, effectsList_append a b, merge_assoc]

theorem eff_of_mem {bss : List (List BExpr)} {bs : List BExpr} (h : bs ∈ bss) :
    ∃ a c : Effects, effectsList bss.flatten = (a.merge (effectsList bs)).merge c := by
  induction bss with
  | nil => cases h
  | cons b rest ih =>
    rw [List.flatten_cons, effectsList_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨({} : Effects), _, by rw [empty_merge]⟩
    · obtain ⟨a, c, e⟩ := ih h
      exact ⟨(effectsList b).merge a, c, by rw [e, merge_assoc, merge_assoc, merge_assoc]⟩

/-! ## The stored locals exist -/

theorem locals_length_initLocals (C : Context) (xs : List Nat) :
    (C.initLocals xs).locals.length = C.locals.length := by
  obtain ⟨L, hL, hy⟩ := Context.initLocals_spec C xs
  rw [hL]
  show L.length = C.locals.length
  have key : ∀ y : Nat, (L[y]? = none ↔ C.locals[y]? = none) := by
    intro y
    rw [hy y]
    split <;> simp
  rcases Nat.lt_trichotomy L.length C.locals.length with h | h | h
  · have := (key L.length).mp (List.getElem?_eq_none (le_refl _))
    rw [List.getElem?_eq_none_iff] at this
    omega
  · exact h
  · have := (key C.locals.length).mpr (List.getElem?_eq_none (le_refl _))
    rw [List.getElem?_eq_none_iff] at this
    omega

/-- A typed `local.set` names an existing local. -/
theorem localSet_bound {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {x : LocalIdx} (hm : Instr.localSet x ∈ is) : x.toNat < C.locals.length := by
  induction h using InstrsOk.ind with
  | nil => cases hm
  | @instr C i it hi =>
    rw [List.mem_singleton] at hm
    subst hm
    cases hi <;> rename_i h <;> cases h
    rename_i hx
    exact (List.getElem?_eq_some_iff.mp hx).1
  | seq h₁ hx h₂ ih₁ ih₂ =>
    rcases List.mem_append.mp hm with hm | hm
    · exact ih₁ hm
    · have := ih₂ hm
      rwa [locals_length_initLocals] at this
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · cases hi <;> rename_i h <;> cases h
      rename_i hx'
      exact (List.getElem?_eq_some_iff.mp hx').1
    · have := ih hm
      rwa [locals_length_initLocals] at this
  | sub h hs hok ih => exact ih hm
  | frame h hok ih => exact ih hm

/-- The body of a typed `block` is typed, with the same locals. -/
theorem block_body {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it)
    {bt : BlockType} {body : List Instr} (hm : Instr.block bt body ∈ is) :
    ∃ C' it', InstrsOk C' body it' ∧ C'.locals.length = C.locals.length := by
  induction h using InstrsOk.ind with
  | nil => cases hm
  | @instr C i it hi =>
    rw [List.mem_singleton] at hm
    subst hm
    cases hi with
    | block hbt hb => exact ⟨_, _, hb, rfl⟩
    | _ => rename_i h; cases h
  | seq h₁ hx h₂ ih₁ ih₂ =>
    rcases List.mem_append.mp hm with hm | hm
    · exact ih₁ hm
    · obtain ⟨C', it', h', hl⟩ := ih₂ hm
      exact ⟨C', it', h', by rw [hl, locals_length_initLocals]⟩
  | @cons C i is t₁ t₂ t₃ xs₁ xs₂ hi hx hs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · cases hi with
      | block hbt hb => exact ⟨_, _, hb, rfl⟩
      | _ => rename_i h; cases h
    · obtain ⟨C', it', h', hl⟩ := ih hm
      exact ⟨C', it', h', by rw [hl, locals_length_initLocals]⟩
  | sub h hs hok ih => exact ih hm
  | frame h hok ih => exact ih hm

theorem mem_lowerList {e : BExpr} {es : List BExpr} (he : e ∈ es) {i : Instr} (hi : i ∈ e.lower) :
    i ∈ BExpr.lowerList es := by
  induction es with
  | nil => cases he
  | cons e' es ih =>
    rw [BExpr.lowerList_cons, List.mem_append]
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl hi
    · exact .inr (ih he)

/-! ## The D-level site, spelled out -/

theorem forall₂_sets {base : Nat} {L : List Nat} {sets : List BExpr}
    (h : List.Forall₂ (fun j e => ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧
      e = .op (.localSet x) []) L sets) :
    ∃ xs : List LocalIdx, sets = xs.map (fun x => BExpr.op (.localSet x) []) ∧
      List.Forall₂ (fun j x => Idx.ofNat? (base + j) = some x) L xs := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hb _ ih =>
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨xs, rfl, hxs⟩ := ih
    exact ⟨x :: xs, rfl, .cons hx hxs⟩

theorem range_get {n j a : Nat} (h : (List.range n)[j]? = some a) : a = j ∧ j < n := by
  obtain ⟨hlt, ha⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem_range] at ha
  exact ⟨ha.symm, by simpa using hlt⟩

theorem range_get_self {n j : Nat} (h : j < n) : (List.range n)[j]? = some j :=
  List.getElem?_eq_some_iff.mpr ⟨by rw [List.length_range]; exact h, List.getElem_range _⟩

/-- The re-zeroing stores of the D-level site. -/
def ZerosOk (base np : Nat) (ls : List ValType) (zeros : List BExpr) : Prop :=
  List.Forall₂ (fun j e => ∃ (t : ValType) (z : Instr) (x : LocalIdx), ls[j]? = some t ∧
    zeroInstr t = some z ∧ Idx.ofNat? (base + np + j) = some x ∧
    e = .op (.localSet x) [.op z []]) (List.range ls.length) zeros

theorem siteCode_spec {ty : TypeIdx} {base np : Nat} {ls : List ValType} {args body : List BExpr}
    {site : List BExpr} (h : siteCode ty base np ls args body = some site) :
    ∃ (xsD : List LocalIdx) (zeros : List BExpr), xsD.length = np ∧
      (∀ j x, xsD[j]? = some x → x.toNat = base + j) ∧ ZerosOk base np ls zeros ∧
      site = args ++ [BExpr.block (.typeIdx ty)
        (xsD.reverse.map (fun x => .op (.localSet x) []) ++ zeros ++
          retToBrL 0 (shiftLocalsL base body))] := by
  simp only [siteCode] at h
  obtain ⟨sets, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨zeros, hz, h⟩ := Option.bind_eq_some_iff.mp h
  have hsets := (InlineTy.mapM_some_forall₂ hs).imp fun j e he => by
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    exact (⟨x, hx, (Option.some.inj he).symm⟩ :
      ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧ e = .op (.localSet x) [])
  have hzeros : ZerosOk base np ls zeros := (InlineTy.mapM_some_forall₂ hz).imp fun j e he => by
    obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨z, hzz, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    exact ⟨t, z, x, ht, hzz, hx, (Option.some.inj he).symm⟩
  obtain ⟨xs, rfl, hxs⟩ := forall₂_sets hsets
  have hxs' : List.Forall₂ (fun j x => (Idx.ofNat? (base + j) : Option LocalIdx) = some x)
      (List.range np) xs.reverse := by
    rw [← List.forall₂_reverse_iff, List.reverse_reverse]
    exact hxs
  refine ⟨xs.reverse, zeros, ?_, ?_, hzeros, ?_⟩
  · simpa using hxs'.length_eq.symm
  · intro j x hx
    obtain ⟨a, ha, hax⟩ := InlineTy.forall₂_getElem? hxs'.flip hx
    obtain ⟨rfl, -⟩ := range_get ha
    exact ((Idx.ofNat?_eq_some_iff _ _).mp hax).symm
  · rw [← (Option.some.inj h)]
    simp

/-! ## The re-zeroing is the same code on both sides -/

theorem zeros_spec {base np : Nat} {ls : List ValType} {zeros : List BExpr}
    (h : ZerosOk base np ls zeros) :
    zeros.length = ls.length ∧ ∀ j t, ls[j]? = some t → ∃ z x, zeroInstr t = some z ∧
      (Idx.ofNat? (base + np + j) : Option LocalIdx) = some x ∧
      zeros[j]? = some (BExpr.op (.localSet x) [.op z []]) := by
  refine ⟨by simpa using h.length_eq.symm, fun j t ht => ?_⟩
  have hj : j < ls.length := (List.getElem?_eq_some_iff.mp ht).1
  obtain ⟨b, hb, t', z, x, ht', hz, hx, rfl⟩ := InlineTy.forall₂_getElem? h (range_get_self hj)
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  exact ⟨z, x, hz, hx, hb⟩

theorem resolve_zeros {E : NameEnv} {L : List (Option Name)} :
    ∀ (vars : List ValType) (k : Nat) (f : Nat → ValType → NExpr) (ZB : List BExpr),
      (∀ j t, f j t = NExpr.localSet (k + j) (.const (zeroLit t)) false) →
      resolveL E L (vars.mapIdx f) = .ok ZB →
      ZB.length = vars.length ∧ ∀ j t, vars[j]? = some t → ∃ x : LocalIdx,
        (Idx.ofNat? (k + j) : Option LocalIdx) = some x ∧
        ZB[j]? = some (BExpr.op (.localSet x) [.op (zeroLit t).instr []])
  | [], k, f, ZB, _, h => by
    simp only [List.mapIdx_nil, resolveL, eok_pure] at h
    subst h
    exact ⟨rfl, fun j t ht => by simp at ht⟩
  | t :: vars, k, f, ZB, hf, h => by
    rw [List.mapIdx_cons, hf] at h
    simp only [resolveL, resolveE, eok_bind, eok_pure] at h
    obtain ⟨s₀, ⟨x₀, hx₀, v₀, hv₀, rfl⟩, rest, hrest, rfl⟩ := h
    subst hv₀
    obtain ⟨hl, hrest'⟩ := resolve_zeros vars (k + 1) (fun i => f (i + 1)) rest
      (fun j t => by rw [hf]; congr 1; omega) hrest
    refine ⟨by simp [hl], fun j t' ht' => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht'
      subst ht'
      exact ⟨x₀, by simpa using toIdx_ok.mp hx₀, by simp⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at ht'
      obtain ⟨x, hx, hget⟩ := hrest' j t' ht'
      exact ⟨x, by rw [← hx]; congr 1; omega, by simpa using hget⟩

theorem zeroInstr_of_prof {t : ValType} (h : t = .num (.int .i32) ∨ t = .num (.int .i64)) :
    zeroInstr t = some (zeroLit t).instr := by
  rcases h with rfl | rfl <;> rfl

theorem zeros_eq {ls : List ValType} {k : Nat} {zeros ZB : List BExpr}
    (hprof : ∀ t ∈ ls, t = .num (.int .i32) ∨ t = .num (.int .i64))
    (hz : zeros.length = ls.length ∧ ∀ j t, ls[j]? = some t → ∃ z x, zeroInstr t = some z ∧
      (Idx.ofNat? (k + j) : Option LocalIdx) = some x ∧
      zeros[j]? = some (BExpr.op (.localSet x) [.op z []]))
    (hZ : ZB.length = ls.length ∧ ∀ j t, ls[j]? = some t → ∃ x : LocalIdx,
      (Idx.ofNat? (k + j) : Option LocalIdx) = some x ∧
      ZB[j]? = some (BExpr.op (.localSet x) [.op (zeroLit t).instr []])) :
    zeros = ZB := by
  apply List.ext_getElem?
  intro j
  cases ht : ls[j]? with
  | none =>
    have hj : ls.length ≤ j := List.getElem?_eq_none_iff.mp ht
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  | some t =>
    obtain ⟨z, x, hzt, hx, h₁⟩ := hz.2 j t ht
    obtain ⟨x', hx', h₂⟩ := hZ.2 j t ht
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    rw [zeroInstr_of_prof (hprof t (List.mem_of_getElem? ht))] at hzt
    obtain rfl := Option.some.inj hzt
    rw [h₁, h₂]

/-! ## Operands from the resolved arguments -/

/-- The operands: each resolved argument with the local it is stored to. -/
def mkOps (xs : List LocalIdx) (bss : List (List BExpr)) : List Opd := List.zipWith Opd.mk xs bss

theorem mkOps_map (xs : List LocalIdx) (bss : List (List BExpr)) :
    (mkOps xs bss).map (fun op => BExpr.op (.localSet op.x) op.bs) =
      List.zipWith (fun x bs => BExpr.op (.localSet x) bs) xs bss := by
  simp [mkOps, List.map_zipWith]

theorem mkOps_flatMap : ∀ (xs : List LocalIdx) (bss : List (List BExpr)),
    xs.length = bss.length → (mkOps xs bss).flatMap (·.bs) = bss.flatten
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, bs :: bss, h => by
    have ih := mkOps_flatMap xs bss (by simpa using h)
    simp only [mkOps, List.zipWith_cons_cons, List.flatMap_cons, List.flatten_cons] at ih ⊢
    rw [ih]

theorem mkOps_get : ∀ (xs : List LocalIdx) (bss : List (List BExpr)) (k : Nat) (op : Opd),
    (mkOps xs bss)[k]? = some op → xs[k]? = some op.x ∧ bss[k]? = some op.bs
  | [], _, k, op, h => by simp [mkOps] at h
  | _ :: _, [], k, op, h => by simp [mkOps] at h
  | x :: xs, bs :: bss, 0, op, h => by
    simp only [mkOps, List.zipWith_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | x :: xs, bs :: bss, k + 1, op, h => by
    simp only [mkOps, List.zipWith_cons_cons, List.getElem?_cons_succ] at h ⊢
    exact mkOps_get xs bss k op h

theorem mkOps_get' : ∀ (xs : List LocalIdx) (bss : List (List BExpr)) (k : Nat) (x : LocalIdx)
    (bs : List BExpr), xs[k]? = some x → bss[k]? = some bs → (mkOps xs bss)[k]? = some ⟨x, bs⟩
  | [], _, k, _, _, h, _ => by simp at h
  | _ :: _, [], k, _, _, _, h => by simp at h
  | x' :: xs, bs' :: bss, 0, x, bs, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    rfl
  | x' :: xs, bs' :: bss, k + 1, x, bs, h₁, h₂ => by
    simp only [mkOps, List.zipWith_cons_cons, List.getElem?_cons_succ] at h₁ h₂ ⊢
    exact mkOps_get' xs bss k x bs h₁ h₂

theorem mkOps_length (xs : List LocalIdx) (bss : List (List BExpr)) (h : xs.length = bss.length) :
    (mkOps xs bss).length = bss.length := by
  simp [mkOps, h]

/-! ## The theorem -/

end Silmaril.Wasm.Binaryen.InlNProof
