module

public import Silmaril.Compiler.Core.Verified.ArgvChar.Defs
public import Silmaril.Compiler.Core.Verified.IntExpr.Defs

/-! # `int` expressions over one character of the arguments

`term file argv ij e`: Cerberus's elaboration of an `int` expression whose leaves are `int`
literals and one character `argv[i][j]` (`ij = (i, j)`, `ArgvChar.charOf`), combined by the guarded
operators and the comparisons of `IntExpr` (the `unseq` of the operands, then the pure guard). The
result is an `IntExpr.Term` whose variable is the character: the compiled code computes it with
`Term.ops` from the character it loads, so nothing of the program is evaluated by the compiler.

`termL file leaf e` is the same recogniser with any leaf (`leaf e = true`) as the character;
`term` is its instance for `argv[i][j]`, and `ArgvVar` uses it with `argv[i][x]`.

`term_ev`: when the expression is in range for the character's value `c` (`Term.Ok c`), it runs to
`Specified (t.val c)` or reaches undefined behaviour (from the character's run); otherwise it
always reaches undefined behaviour (an operator out of range, UB036, or the character's).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalReaches taskFlag)
open ReturnLit (Eff)
open ArgvChar (Ev Bad Stable FailsUB RunsTo charOf)
open ArgvMem (Reads)
open IntExpr (Term spec)
open ConvInt (IsInt)

/-- The recogniser: literals, the character (an expression with `leaf e`), guarded operators
and comparisons. -/
def termL (file : File Codec.wireModel Unit Unit) (leaf : Eff → Bool) (e : Eff) :
    Option Term :=
  if leaf e = true then some .var else
  match e with
  | .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))) =>
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.lit n) else none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk _ (.pure g))) =>
      match termL file leaf e₁, termL file leaf e₂ with
      | some t₁, some t₂ =>
        match Guard.guard file a b g, Guard.cmpGuard file a b g with
        | some op, _ => some (.bin op t₁ t₂)
        | none, some (r, c₁, c₂) => some (.cmp r c₁ c₂ t₁ t₂)
        | none, none => none
      | _, _ => none
  | _ => none
termination_by sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The expressions over the character `argv[i][j]` (`ij`). -/
def term (file : File Codec.wireModel Unit Unit) (argv : Sym) (ij : Nat × Nat) (e : Eff) :
    Option Term :=
  termL file (fun e => charOf argv e == some ij) e

theorem termL_var {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    (h : termL file leaf e = some .var) : leaf e = true := by
  unfold termL at h
  split at h
  · assumption
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

/-- `term` builds no division by a literal. -/
theorem termL_divpos {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {o : DivRem.Op} {d : DivRem.Divisor} {t : Term} (h : termL file leaf e = some (.divpos o d t)) :
    False := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

theorem termL_lit {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {c : Int} (h : termL file leaf e = some (.lit c)) :
    ∃ an pa, e = .mk an (.pure (.mk pa () (.val (.loaded (.specified (.integer c)))))) ∧ IsInt c := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hc
        cases h; exact ⟨_, _, rfl, hc⟩
      · cases h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

theorem termL_bin {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {op : IntOp} {t₁ t₂ : Term} (h : termL file leaf e = some (.bin op t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : ConvInt.Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Guard.guard file a b g = some op ∧ termL file leaf e₁ = some t₁ ∧
      termL file leaf e₂ = some t₂ := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h
        · cases h
          exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
            by assumption⟩
        · cases h
        · cases h
      · cases h
    · cases h

theorem termL_cmp {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {r : BinOp} {c₁ c₂ : Int} {t₁ t₂ : Term} (h : termL file leaf e = some (.cmp r c₁ c₂ t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : ConvInt.Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Guard.cmpGuard file a b g = some (r, c₁, c₂) ∧ termL file leaf e₁ = some t₁ ∧
      termL file leaf e₂ = some t₂ := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h
        · cases h
        · cases h
          exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
            by assumption⟩
        · cases h
      · cases h
    · cases h

theorem termL_cond {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {tc ta tb : Term} (h : termL file leaf e = some (.cond tc ta tb)) : False := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

theorem termL_bit {file : File Codec.wireModel Unit Unit} {leaf : Eff → Bool} {e : Eff}
    {o : Bitwise.Op} {ta tb : Term} (h : termL file leaf e = some (.bit o ta tb)) : False := by
  unfold termL at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

/-! ## Runs -/

variable {file : Program} {labels : Labels}

/-- `unseq [e₁, e₂]` reaches undefined behaviour when `e₂` (run first) always does. -/
theorem bad_pair_right {I : Mem.Concrete.State → Prop} {env : Env} {e₁ e₂ : EE}
    (c₁ : hasCCall e₁ = false) (h₂ : Bad (file := file) (labels := labels) I env e₂)
    (annots : List Annot) (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    FailsUB (file := file) (labels := labels) env (.mk annots (.unseq [e₁, e₂])) k m := by
  obtain ⟨loc, ub, f⟩ := h₂.2 [] m hm
  exact ⟨loc, ub, ArenaFail.fail_pair file labels (.inl (by rw [ArgvChar.taskFlag_one c₁]; exact f))⟩

/-- `unseq [e₁, e₂]` reaches undefined behaviour when `e₂` runs or does, and then `e₁` always does. -/
theorem bad_pair_left {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env} {e₁ e₂ : EE} {v₂ : Val}
    (h₁ : Bad (file := file) (labels := labels) I env e₁) (h₂ : Ev (file := file) (labels := labels) I env e₂ v₂)
    (annots : List Annot) (k : List Frame) (m : Mem.Concrete.State) (hm : I m) :
    FailsUB (file := file) (labels := labels) env (.mk annots (.unseq [e₁, e₂])) k m := by
  have flag₁ := ArgvChar.taskFlag_one h₁.1 env k
  rcases h₂.2 [] m hm with r₂ | ⟨loc, ub, f₂⟩
  · obtain ⟨xs₂, m₁, -, g₁, run₂⟩ := r₂.task
    obtain ⟨loc, ub, f₁⟩ := h₁.2 [] m₁ (hI m m₁ hm g₁)
    exact ⟨loc, ub, ArenaFail.fail_pair file labels
      (.inr ⟨v₂, xs₂, m₁, by rw [flag₁]; exact run₂, by simpa [taskFlag] using f₁⟩)⟩
  · exact ⟨loc, ub, ArenaFail.fail_pair file labels (.inl (by rw [flag₁]; exact f₂))⟩

theorem bin_calls {an pp p1 p2 au ag : List Annot} {a b : Sym} {ta tb : BaseType} {e₁ e₂ : Eff}
    {g : ConvInt.Pure} (c₁ : hasCCall e₁ = false) (c₂ : hasCCall e₂ = false) :
    hasCCall (.mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
      .mk p2 (.base (some b, tb))])) (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) = false := by
  simp [hasCCall, c₁, c₂]

/-- The run of an operator or a comparison up to its pure guard, given the runs of its operands. -/
theorem guard_prefix {I : Mem.Concrete.State → Prop} (hI : Stable I) {an pp p1 p2 au ag : List Annot}
    {a b : Sym} {ta tb : BaseType} {e₁ e₂ : Eff} {g : ConvInt.Pure} {env : Env} {v₁ v₂ : Int}
    (h₁ : Ev (file := file) (labels := labels) I env e₁ (spec v₁))
    (h₂ : Ev (file := file) (labels := labels) I env e₂ (spec v₂)) (k : List Frame)
    (m : Mem.Concrete.State) (hm : I m) :
    FailsUB (file := file) (labels := labels) env (.mk an (.wseq (.mk pp (.ctor .tuple
      [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])) (.mk au (.unseq [e₁, e₂]))
      (.mk ag (.pure g)))) k m ∨
    ∃ xs m₂ l, (∀ x ∈ xs, x.write = false) ∧ Reads m m₂ ∧ LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
        .mk p2 (.base (some b, tb))])) (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
      ⟨.pureExpr g (Guard.operands a b v₁ v₂ env), .diagnosticLocation l ::
        .annotations xs :: k, m₂⟩ := by
  let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  have s₀ := ArgvChar.wseq_enter (file := file) (labels := labels) an PAT (.mk au (.unseq [e₁, e₂]))
    (.mk ag (.pure g)) env k m
  rcases ArgvChar.ev_pair hI h₁ h₂ au (.effectBind PAT (.mk ag (.pure g)) env :: k) m hm with
    ⟨xs, m₁, rd, g₁, s₁⟩ | f
  · have s₂ : LocalReaches file labels false
        ⟨.value (.tuple [spec v₁, spec v₂]), .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b v₁ v₂ env), .annotations xs :: k, m₁⟩ :=
      .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (ArgvChar.plain_effectExpr _ _))
    obtain ⟨l', s₃⟩ := IntExpr.guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b v₁ v₂ env) (.annotations xs :: k) m₁
    exact .inr ⟨xs, {m₁ with currentLocation := l'}, _, rd, g₁.location l', s₀.trans (s₁.trans (s₂.trans s₃))⟩
  · exact .inl (FailsUB.pre s₀ f)

/-- **An expression over the character**: in range, it runs to its value or reaches undefined
behaviour; out of range, it always reaches undefined behaviour. -/
theorem termL_ev {leaf : Eff → Bool} {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env}
    {c : Int} (hc : IsInt c)
    (hchar : ∀ e, leaf e = true → Ev (file := file) (labels := labels) I env e (spec c)) :
    (t : Term) → {e : Eff} → termL file leaf e = some t →
      (t.Ok c → Ev (file := file) (labels := labels) I env e (spec (t.val c))) ∧
      (¬ t.Ok c → Bad (file := file) (labels := labels) I env e)
  | .lit n, e, h => by
    obtain ⟨an, pa, rfl, hn⟩ := termL_lit h
    exact ⟨fun _ => ArgvChar.ev_val I an pa _ env, fun bad => absurd hn bad⟩
  | .var, e, h => ⟨fun _ => hchar e (termL_var h), fun bad => absurd hc bad⟩
  | .divpos _ _ _, _, h => (termL_divpos h).elim
  | .bin op t₁ t₂, e, h => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termL_bin h
    obtain ⟨r₁, b₁⟩ := termL_ev hI hc hchar t₁ h₁
    obtain ⟨r₂, b₂⟩ := termL_ev hI hc hchar t₂ h₂
    have calls₁ : hasCCall e₁ = false := by
      by_cases o : t₁.Ok c
      · exact (r₁ o).1
      · exact (b₁ o).1
    have calls₂ : hasCCall e₂ = false := by
      by_cases o : t₂.Ok c
      · exact (r₂ o).1
      · exact (b₂ o).1
    have calls := bin_calls (an := an) (pp := pp) (p1 := p1) (p2 := p2) (au := au) (ag := ag) (a := a)
      (b := b) (ta := ta) (tb := tb) (g := g) calls₁ calls₂
    refine ⟨fun ok => ⟨calls, fun k m hm => ?_⟩, fun bad => ⟨calls, fun k m hm => ?_⟩⟩
    · obtain ⟨ok₁, ok₂, okr⟩ := ok
      rcases guard_prefix hI (r₁ ok₁) (r₂ ok₂) k m hm with f | ⟨xs, m₂, l₂, rd, g₂, s⟩
      · exact .inr f
      · have i₁ := Term.int_of_ok t₁ ok₁
        have i₂ := Term.int_of_ok t₂ ok₂
        have s' := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
          (Guard.guard_eval hg env i₁ i₂ okr) (.diagnosticLocation l₂ :: .annotations xs :: k)
          m₂ rfl
        exact .inl ⟨xs, m₂, [.annotations xs], .inr rfl, rd, g₂, s.trans (s'.tail
          (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (ArgvChar.plain_value _)))⟩
    · by_cases ok₂ : t₂.Ok c
      · by_cases ok₁ : t₁.Ok c
        · have okr : ¬ IsInt (Guard.apply op (t₁.val c) (t₂.val c)) := fun hr => bad ⟨ok₁, ok₂, hr⟩
          rcases guard_prefix hI (r₁ ok₁) (r₂ ok₂) k m hm with f | ⟨xs, m₂, l₂, rd, g₂, s⟩
          · exact f
          · obtain ⟨k', s', hend⟩ := Guard.guard_fails (labels := labels) hg env (Term.int_of_ok t₁ ok₁)
              (Term.int_of_ok t₂ ok₂) okr false (.diagnosticLocation l₂ :: .annotations xs :: k) m₂
            refine ⟨.unknown, _, _, s.trans s', ?_, .inl hend⟩
            intro v hv; cases hv
        · exact FailsUB.pre (ArgvChar.wseq_enter (file := file) (labels := labels) an _ _ _ env k m)
            (bad_pair_left hI (b₁ ok₁) (r₂ ok₂) au _ m hm)
      · exact FailsUB.pre (ArgvChar.wseq_enter (file := file) (labels := labels) an _ _ _ env k m)
          (bad_pair_right calls₁ (b₂ ok₂) au _ m hm)
  | .cmp rl c₁ c₂ t₁ t₂, e, h => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := termL_cmp h
    obtain ⟨r₁, b₁⟩ := termL_ev hI hc hchar t₁ h₁
    obtain ⟨r₂, b₂⟩ := termL_ev hI hc hchar t₂ h₂
    have calls₁ : hasCCall e₁ = false := by
      by_cases o : t₁.Ok c
      · exact (r₁ o).1
      · exact (b₁ o).1
    have calls₂ : hasCCall e₂ = false := by
      by_cases o : t₂.Ok c
      · exact (r₂ o).1
      · exact (b₂ o).1
    have calls := bin_calls (an := an) (pp := pp) (p1 := p1) (p2 := p2) (au := au) (ag := ag) (a := a)
      (b := b) (ta := ta) (tb := tb) (g := g) calls₁ calls₂
    refine ⟨fun ok => ⟨calls, fun k m hm => ?_⟩, fun bad => ⟨calls, fun k m hm => ?_⟩⟩
    · obtain ⟨ok₁, ok₂, -, -⟩ := ok
      rcases guard_prefix hI (r₁ ok₁) (r₂ ok₂) k m hm with f | ⟨xs, m₂, l₂, rd, g₂, s⟩
      · exact .inr f
      · have i₁ := Term.int_of_ok t₁ ok₁
        have i₂ := Term.int_of_ok t₂ ok₂
        have s' := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
          (Guard.cmpGuard_eval hg env i₁ i₂) (.diagnosticLocation l₂ :: .annotations xs :: k)
          m₂ rfl
        exact .inl ⟨xs, m₂, [.annotations xs], .inr rfl, rd, g₂, s.trans (s'.tail
          (.next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false) (ArgvChar.plain_value _)))⟩
    · by_cases ok₂ : t₂.Ok c
      · by_cases ok₁ : t₁.Ok c
        · exact absurd ⟨ok₁, ok₂, Guard.cmpGuard_int hg⟩ bad
        · exact FailsUB.pre (ArgvChar.wseq_enter (file := file) (labels := labels) an _ _ _ env k m)
            (bad_pair_left hI (b₁ ok₁) (r₂ ok₂) au _ m hm)
      · exact FailsUB.pre (ArgvChar.wseq_enter (file := file) (labels := labels) an _ _ _ env k m)
          (bad_pair_right calls₁ (b₂ ok₂) au _ m hm)
  | .cond _ _ _, _, h => (termL_cond h).elim
  | .bit _ _ _, _, h => (termL_bit h).elim

theorem term_ev {argv : Sym} {ij : Nat × Nat} {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env}
    {c : Int} (hc : IsInt c)
    (hchar : ∀ e, charOf argv e = some ij → Ev (file := file) (labels := labels) I env e (spec c))
    (t : Term) {e : Eff} (h : term file argv ij e = some t) :
    (t.Ok c → Ev (file := file) (labels := labels) I env e (spec (t.val c))) ∧
      (¬ t.Ok c → Bad (file := file) (labels := labels) I env e) :=
  termL_ev hI hc (fun e he => hchar e (by simpa using he)) t h

end Silmaril.Compile.Core.Verified.ArgvExpr
