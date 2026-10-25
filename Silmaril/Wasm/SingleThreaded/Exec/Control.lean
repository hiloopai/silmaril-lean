module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: control head rules

`controlStep?` decides the `Det.Head` rules whose instruction is a plain
control instruction or a `CALL_REF`-like administrative instruction: blocks,
branches that reduce at the head, calls, `THROW`, `THROW_REF` on null and
`TRY_TABLE`. `vs` is the whole bottom-first value prefix before `e`; a result
`(k, c)` consumes the top `k` values.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace Ctl

theorem drop_suffix {α : Type _} (q a : List α) :
    (q ++ a).drop ((q ++ a).length - a.length) = a := by
  have : (q ++ a).length - a.length = q.length := by simp
  rw [this, List.drop_left]

theorem drop_one_of_getLast? {α : Type _} {vs : List α} {v : α} (h : vs.getLast? = some v) :
    vs.drop (vs.length - 1) = [v] := by
  obtain ⟨w, rfl⟩ : ∃ w, vs = w ++ [v] := List.getLast?_eq_some_iff.mp h
  simp

theorem drop_succ_of_getLast? {α : Type _} {vs : List α} {v : α} (h : vs.getLast? = some v)
    (n : Nat) (hn : n ≤ vs.dropLast.length) :
    vs.drop (vs.length - (n + 1)) = vs.dropLast.drop (vs.dropLast.length - n) ++ [v] := by
  obtain ⟨w, rfl⟩ : ∃ w, vs = w ++ [v] := List.getLast?_eq_some_iff.mp h
  simp only [List.dropLast_concat] at hn ⊢
  simp only [List.length_append, List.length_singleton]
  rw [show w.length + 1 - (n + 1) = w.length - n by omega,
    List.drop_append_of_le_length (by omega)]

/-- `CALL_REF` at the top of the stack. -/
def callRef? (s : Store H) (f : Frame) (vs : List Val) : Option (Nat × Config H) :=
  match vs.getLast? with
  | some (.ref .null) => some (1, ⟨s, f, [.trap]⟩)
  | some (.ref (.func a)) =>
    match s.funcs[a]? with
    | some fi =>
      match fi.type.expand?, fi.code with
      | some (.func ps rs), .wasm code =>
        if ps.length ≤ vs.dropLast.length then
          some (ps.length + 1, ⟨s, f, [.frame rs.length
            (Frame.forCall fi.module (vs.dropLast.drop (vs.dropLast.length - ps.length))
              code.locals) [.label rs.length [] (expression code.body)]]⟩)
        else none
      | _, _ => none
    | none => none
  | _ => none

/-- A block-like instruction consuming `t₁.length` values. -/
def block? (s : Store H) (f : Frame) (vs : List Val) (bt : BlockType)
    (mk : List CValType → List CValType → List Val → Admin) : Option (Nat × Config H) :=
  match f.module.blockType? bt with
  | some (t₁, t₂) =>
    if t₁.length ≤ vs.length then
      some (t₁.length, ⟨s, f, [mk t₁ t₂ (vs.drop (vs.length - t₁.length))]⟩)
    else none
  | none => none

/-- Plain control instructions. -/
def plainStep? (cast : Store H → Ref → CRefType → Bool) (s : Store H) (f : Frame)
    (vs : List Val) : Instr → Option (Nat × Config H)
  | .block bt body => block? s f vs bt fun _ t₂ a =>
      .label t₂.length [] (vals a ++ expression body)
  | .loop bt body => block? s f vs bt fun t₁ _ a =>
      .label t₁.length [.loop bt body] (vals a ++ expression body)
  | .tryTable bt cs body => block? s f vs bt fun _ t₂ a =>
      .handler t₂.length cs [.label t₂.length [] (vals a ++ expression body)]
  | .if_ bt b₁ b₂ =>
    match vs.getLast? with
    | some (.num ⟨.int .i32, c⟩) =>
      if c = 0 then some (1, ⟨s, f, [.plain (.block bt b₂)]⟩)
      else some (1, ⟨s, f, [.plain (.block bt b₁)]⟩)
    | _ => none
  | .brIf l =>
    match vs.getLast? with
    | some (.num ⟨.int .i32, c⟩) =>
      if c = 0 then some (1, ⟨s, f, []⟩) else some (1, ⟨s, f, [.plain (.br l)]⟩)
    | _ => none
  | .brTable ls l' =>
    match vs.getLast? with
    | some (.num ⟨.int .i32, i⟩) =>
      match ls[i.toNat]? with
      | some l => some (1, ⟨s, f, [.plain (.br l)]⟩)
      | none => some (1, ⟨s, f, [.plain (.br l')]⟩)
    | _ => none
  | .brOnNull l =>
    match vs.getLast? with
    | some v =>
      if v = .ref .null then some (1, ⟨s, f, [.plain (.br l)]⟩)
      else some (1, ⟨s, f, [v.toAdmin]⟩)
    | none => none
  | .brOnNonNull l =>
    match vs.getLast? with
    | some v =>
      if v = .ref .null then some (1, ⟨s, f, []⟩)
      else some (1, ⟨s, f, [v.toAdmin, .plain (.br l)]⟩)
    | none => none
  | .brOnCast l _ rt₂ =>
    match vs.getLast? with
    | some (.ref r) =>
      if cast s r (f.module.instRef rt₂) then some (1, ⟨s, f, [.ref r, .plain (.br l)]⟩)
      else some (1, ⟨s, f, [.ref r]⟩)
    | _ => none
  | .brOnCastFail l _ rt₂ =>
    match vs.getLast? with
    | some (.ref r) =>
      if cast s r (f.module.instRef rt₂) then some (1, ⟨s, f, [.ref r]⟩)
      else some (1, ⟨s, f, [.ref r, .plain (.br l)]⟩)
    | _ => none
  | .call x =>
    match f.module.funcs[x.toNat]? with
    | some a =>
      match s.funcs[a]? with
      | some fi => some (0, ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩)
      | none => none
    | none => none
  | .returnCall x =>
    match f.module.funcs[x.toNat]? with
    | some a =>
      match s.funcs[a]? with
      | some fi => some (0, ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩)
      | none => none
    | none => none
  | .callIndirect x y =>
    some (0, ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.callRef y)]⟩)
  | .returnCallIndirect x y =>
    some (0, ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.returnCallRef y)]⟩)
  | .throw x =>
    match s.tag? f x with
    | some (ta, ti) =>
      match ti.type.expand? with
      | some (.func ts rs) =>
        if rs = .nil ∧ ts.length ≤ vs.length then
          some (ts.length, ⟨s.addExn ⟨ta, vs.drop (vs.length - ts.length)⟩, f,
            [.ref (.exn s.exns.length), .plain .throwRef]⟩)
        else none
      | _ => none
    | none => none
  | .throwRef =>
    match vs.getLast? with
    | some (.ref .null) => some (1, ⟨s, f, [.trap]⟩)
    | _ => none
  | _ => none

end Ctl

/-- One control head step at the instruction `e` under the value prefix `vs`. -/
def controlStep? (cast : Store H → Ref → CRefType → Bool) (_o : GrowOracle) (s : Store H)
    (f : Frame) (vs : List Val) (e : Admin) : Option (Nat × Config H) :=
  if e.isCallRef then Ctl.callRef? s f vs
  else
    match e with
    | .plain i => Ctl.plainStep? cast s f vs i
    | _ => none

namespace Ctl

theorem top1 {vs : List Val} {v : Val} (h : vs.getLast? = some v) :
    1 ≤ vs.length ∧ vs.drop (vs.length - 1) = [v] := by
  refine ⟨?_, drop_one_of_getLast? h⟩
  cases vs with
  | nil => simp at h
  | cons _ _ => simp

theorem some_inj {k k' : Nat} {c c' : Config H} (h : some (k, c) = some (k', c')) :
    k = k' ∧ c = c' := by
  simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h

theorem block?_sound {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {mk : List CValType → List CValType → List Val → Admin} {k : Nat} {c : Config H}
    (h : block? s f vs bt mk = some (k, c)) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ k = t₁.length ∧ k ≤ vs.length ∧
      c = ⟨s, f, [mk t₁ t₂ (vs.drop (vs.length - k))]⟩ := by
  unfold block? at h
  split at h
  · rename_i t₁ t₂ hbt
    split at h
    · obtain ⟨rfl, rfl⟩ := some_inj h
      exact ⟨t₁, t₂, hbt, rfl, ‹_›, rfl⟩
    · simp at h
  · simp at h

theorem callRef?_sound {P : Profile} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (he : e.IsCallRef) (h : callRef? s f vs = some (k, c)) :
    k ≤ vs.length ∧ Head P s f (vs.drop (vs.length - k)) e c := by
  unfold callRef? at h
  split at h
  · rename_i hl
    obtain ⟨rfl, rfl⟩ := some_inj h
    obtain ⟨h1, h2⟩ := top1 hl
    rw [h2]
    exact ⟨h1, Head.callRefNull he⟩
  · rename_i a hl
    split at h
    · rename_i fi hfi
      split at h
      · rename_i ps rs code hexp hcode
        split at h
        · rename_i hle
          obtain ⟨rfl, rfl⟩ := some_inj h
          have hlen : 1 ≤ vs.length := (top1 hl).1
          rw [drop_succ_of_getLast? hl _ hle]
          refine ⟨by simp at hle; omega, Head.callRefFunc rfl he hfi (Expand.iff.mpr hexp)
            (by rw [List.length_drop]; omega) hcode⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

set_option hygiene false in
/-- Close a soundness goal for a rule consuming the top value. -/
macro "snd1" rule:term : tactic => `(tactic| (
  obtain ⟨rfl, rfl⟩ := some_inj h
  obtain ⟨h1, h2⟩ := top1 ‹_›
  rw [h2]
  exact ⟨h1, $rule⟩))

set_option hygiene false in
/-- Close a soundness goal for a rule consuming no value. -/
macro "snd0" rule:term : tactic => `(tactic| (
  obtain ⟨rfl, rfl⟩ := some_inj h
  simp only [Nat.sub_zero, List.drop_length]
  exact ⟨Nat.zero_le _, $rule⟩))

theorem plainStep?_sound {P : Profile} {cast : Store H → Ref → CRefType → Bool} {s : Store H}
    {f : Frame} {vs : List Val} {i : Instr} {k : Nat} {c : Config H}
    (hcast : ∀ r rt, TyOk {} rt → (cast s r rt = true ↔ RefOk s r rt))
    (htgt : ∀ l rt₁ rt₂, (i = .brOnCast l rt₁ rt₂ ∨ i = .brOnCastFail l rt₁ rt₂) →
      TyOk {} (f.module.instRef rt₂))
    (h : plainStep? cast s f vs i = some (k, c)) :
    k ≤ vs.length ∧ Head P s f (vs.drop (vs.length - k)) (.plain i) c := by
  cases i <;> simp only [plainStep?] at h <;> try contradiction
  case block bt body =>
    obtain ⟨t₁, t₂, hbt, rfl, hle, rfl⟩ := block?_sound h
    exact ⟨hle, Head.block hbt (by simp; omega)⟩
  case loop bt body =>
    obtain ⟨t₁, t₂, hbt, rfl, hle, rfl⟩ := block?_sound h
    exact ⟨hle, Head.loop hbt (by simp; omega)⟩
  case tryTable bt cs body =>
    obtain ⟨t₁, t₂, hbt, rfl, hle, rfl⟩ := block?_sound h
    exact ⟨hle, Head.tryTable hbt (by simp; omega)⟩
  case if_ bt b₁ b₂ =>
    split at h
    · split at h
      · snd1 Head.ifFalse ‹_›
      · snd1 Head.ifTrue ‹_›
    · simp at h
  case brIf l =>
    split at h
    · split at h
      · snd1 Head.brIfFalse ‹_›
      · snd1 Head.brIfTrue ‹_›
    · simp at h
  case brTable ls l' =>
    split at h
    · split at h
      · snd1 Head.brTableLt ‹_›
      · snd1 Head.brTableGe (List.getElem?_eq_none_iff.mp ‹_›)
    · simp at h
  case brOnNull l =>
    split at h
    · split at h
      · subst_vars; snd1 Head.brOnNullNull
      · snd1 Head.brOnNullAddr ‹_›
    · simp at h
  case brOnNonNull l =>
    split at h
    · split at h
      · subst_vars; snd1 Head.brOnNonNullNull
      · snd1 Head.brOnNonNullAddr ‹_›
    · simp at h
  case brOnCast l rt₁ rt₂ =>
    have ht := htgt l rt₁ rt₂ (.inl rfl)
    split at h
    · split at h
      · snd1 Head.brOnCastSucceed ((hcast _ _ ht).mp ‹_›)
      · snd1 Head.brOnCastFail (fun hr => ‹¬ _› ((hcast _ _ ht).mpr hr))
    · simp at h
  case brOnCastFail l rt₁ rt₂ =>
    have ht := htgt l rt₁ rt₂ (.inr rfl)
    split at h
    · split at h
      · snd1 Head.brOnCastFailSucceed ((hcast _ _ ht).mp ‹_›)
      · snd1 Head.brOnCastFailFail (fun hr => ‹¬ _› ((hcast _ _ ht).mpr hr))
    · simp at h
  case call x =>
    split at h
    · split at h
      · snd0 Head.call ‹_› ‹_›
      · simp at h
    · simp at h
  case returnCall x =>
    split at h
    · split at h
      · snd0 Head.returnCall ‹_› ‹_›
      · simp at h
    · simp at h
  case callIndirect x y => snd0 Head.callIndirect
  case returnCallIndirect x y => snd0 Head.returnCallIndirect
  case throw x =>
    split at h
    · rename_i ta ti ht
      split at h
      · rename_i ts rs hexp
        split at h
        · rename_i hc
          obtain ⟨rfl, hle⟩ := hc
          obtain ⟨rfl, rfl⟩ := some_inj h
          exact ⟨hle, Head.throw ht (Expand.iff.mpr hexp) (by simp; omega)⟩
        · simp at h
      · simp at h
    · simp at h
  case throwRef =>
    split at h
    · snd1 Head.throwRefNull
    · simp at h

end Ctl

theorem controlStep?_sound {cast : Store H → Ref → CRefType → Bool} {o : GrowOracle}
    {s : Store H} {f : Frame} {vs : List Val} {e : Admin} {k : Nat} {c : Config H}
    (hcast : ∀ r rt, TyOk {} rt → (cast s r rt = true ↔ RefOk s r rt))
    (htgt : ∀ l rt₁ rt₂, (e = .plain (.brOnCast l rt₁ rt₂) ∨ e = .plain (.brOnCastFail l rt₁ rt₂)) →
      TyOk {} (f.module.instRef rt₂)) :
    controlStep? cast o s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  intro h
  unfold controlStep? at h
  split at h
  · exact Ctl.callRef?_sound (Admin.IsCallRef_of_isCallRef ‹_›) h
  · split at h
    · rename_i i
      exact Ctl.plainStep?_sound hcast
        (fun l rt₁ rt₂ hi => htgt l rt₁ rt₂ (by rcases hi with rfl | rfl <;> simp)) h
    · simp at h

theorem Ctl.getLast?_snoc {α : Type _} (q : List α) (v : α) : (q ++ [v]).getLast? = some v := by
  simp

theorem Ctl.plain_eq {cast : Store H → Ref → CRefType → Bool} {o : GrowOracle} {s : Store H}
    {f : Frame} {vs : List Val} {i : Instr} (hi : (Admin.plain i).isCallRef = false) :
    controlStep? cast o s f vs (.plain i) = Ctl.plainStep? cast s f vs i := by
  simp [controlStep?, hi]

set_option hygiene false in
/-- Close a completeness goal for a rule consuming the top value. -/
macro "cmp1" : tactic => `(tactic| (
  rw [Ctl.plain_eq rfl]
  simp only [Ctl.plainStep?, Ctl.getLast?_snoc, List.length_singleton]
  try simp_all))

theorem controlStep?_complete {cast : Store H → Ref → CRefType → Bool} {o : GrowOracle}
    {s : Store H} {f : Frame} {vs args : List Val} {e : Admin} {c : Config H}
    (hcast : ∀ r rt, TyOk {} rt → (cast s r rt = true ↔ RefOk s r rt))
    (htgt : ∀ l rt₁ rt₂, (e = .plain (.brOnCast l rt₁ rt₂) ∨ e = .plain (.brOnCastFail l rt₁ rt₂)) →
      TyOk {} (f.module.instRef rt₂)) :
    Head (profile o) s f args e c → famOf e = .control →
      (∀ n cont is, e ≠ .label n cont is) → (∀ n cs is, e ≠ .handler n cs is) →
      (∀ n fi is, e ≠ .frame n fi is) → (∃ q, vs = q ++ args) →
      controlStep? cast o s f vs e = some (args.length, c) := by
  intro hd hk hl hh hfr ⟨q, hq⟩
  subst hq
  have hc : ∀ {k : Fam}, famOf e = k → k ≠ .control → False := fun h hk' => hk' (h ▸ hk)
  cases hd <;> try fam_excl
  all_goals try (exfalso; first | exact hl _ _ _ rfl | exact hh _ _ _ rfl | exact hfr _ _ _ rfl)
  case block t₁ t₂ hbt hm | loop t₁ t₂ hbt hm | tryTable t₁ t₂ hbt hm =>
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, Ctl.block?, hbt, ← hm, Ctl.drop_suffix]
    simp
  case ifTrue | brIfTrue =>
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, Ctl.getLast?_snoc]
    exact ite_eq_right ‹¬ _ = _›
  case ifFalse | brIfFalse =>
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, Ctl.getLast?_snoc]
    exact ite_eq_left ‹_ = (0 : BitVec 32)›
  case brTableLt i ls l' l hi =>
    have hi' : ls[BitVec.toNat (w := (NumType.int IntType.i32).width) i]? = some l := hi
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, Ctl.getLast?_snoc, hi']
    rfl
  case brTableGe i ls l' hi =>
    have hi' : ls[BitVec.toNat (w := (NumType.int IntType.i32).width) i]? = none :=
      List.getElem?_eq_none_iff.mpr hi
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, Ctl.getLast?_snoc, hi']
    rfl
  case brOnNullNull | brOnNullAddr | brOnNonNullNull | brOnNonNullAddr => cmp1
  case brOnCastSucceed l rt₁ rt₂ hr =>
    have := (hcast _ _ (htgt l rt₁ rt₂ (.inl rfl))).mpr hr
    cmp1
  case brOnCastFail l rt₁ rt₂ hr =>
    have := fun h => hr ((hcast _ _ (htgt l rt₁ rt₂ (.inl rfl))).mp h)
    cmp1
  case brOnCastFailSucceed l rt₁ rt₂ hr =>
    have := (hcast _ _ (htgt l rt₁ rt₂ (.inr rfl))).mpr hr
    cmp1
  case brOnCastFailFail l rt₁ rt₂ hr =>
    have := fun h => hr ((hcast _ _ (htgt l rt₁ rt₂ (.inr rfl))).mp h)
    cmp1
  case call | returnCall | callIndirect | returnCallIndirect =>
    rw [Ctl.plain_eq rfl]
    simp_all [Ctl.plainStep?]
  case throw =>
    rw [Ctl.plain_eq rfl]
    simp only [Ctl.plainStep?, ‹s.tag? f _ = _›, Expand.iff.mp ‹Expand _ _›,
      ← ‹List.length _ = Ty.length _›, Ctl.drop_suffix]
    try simp
  case throwRefNull => cmp1
  case callRefNull =>
    unfold controlStep?
    rw [ite_eq_left (Admin.isCallRef_of_IsCallRef ‹Admin.IsCallRef _›)]
    simp [Ctl.callRef?]
  case callRefFunc =>
    unfold controlStep?
    rw [ite_eq_left (Admin.isCallRef_of_IsCallRef ‹Admin.IsCallRef _›)]
    subst_vars
    rw [← List.append_assoc]
    simp only [Ctl.callRef?, Ctl.getLast?_snoc, List.dropLast_concat, ‹s.funcs[_]? = _›,
      Expand.iff.mp ‹Expand _ _›, ‹FuncInst.code _ = _›, ← ‹List.length _ = Ty.length _›,
      Ctl.drop_suffix]
    try simp

end Silmaril.Wasm.SingleThreaded.Exec
