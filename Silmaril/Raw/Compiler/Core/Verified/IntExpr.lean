module

public import Silmaril.Compiler.Core.Verified.LoadTask.Defs
public import Silmaril.Compiler.Core.Verified.Guard.Defs
public import Silmaril.Compiler.Core.Verified.Bitwise.Defs
public import Silmaril.Compiler.Core.Verified.DivRem.Defs
public import Silmaril.Cerberus.Core.ArenaFail.Defs
public import Silmaril.Compiler.Core.Verified.Cond.Defs

/-! # `int` expressions over one local

`term file x e = some t` recognises Cerberus's elaboration of an `int` expression built from
literals, reads of the local `x` and the guarded operators `+`, `-`, `*`:

* a literal: `pure(Specified(n))`, `n` an `int`;
* a read of `x`: `let weak p = pure(x) in load(int, p)`;
* `e₁ op e₂`: `let weak (a, b) = unseq(e₁, e₂) in pure(guard)` with the guard of `Guard`.

`t.val n` is the integer value with `x` holding `n`, computed exactly; `t.Ok n` says no
intermediate value leaves `int`. From a memory where `x` points to the slot of `n`:

* `term_runs`: if `t.Ok n`, local steps reach `Specified (t.val n)`, with read accesses only,
  over any continuation (so the expression is also a task of an enclosing `unseq`);
* `term_fails`: otherwise they reach undefined behaviour `UB036_exceptional_condition`
  (`ArenaFail.Fails`), raised through every enclosing `unseq` arena.

Both are proved by induction on `t`; the operands run last first (`Interleave`).

`Term` also has the bitwise operators `&`, `|`, `^` (`.bit`, `Bitwise`), which `term` never
recognises here; the statement fragment (`StateExpr`) produces them, and the Lir code
(`IntExprLir`) computes them.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.IntExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns taskFlag unseqTasks)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open ReturnLit (Eff lookup_key)
open LoadTask (Touched ReadTask)
open Locals (Slot)
open ConvInt (IsInt Pure)

/-- `int` expressions over one local. -/
inductive Term where
  | lit (n : Int)
  | var
  | bin (op : IntOp) (a b : Term)
  /-- A comparison: `c₁` when `a r b` holds, `c₂` otherwise. -/
  | cmp (r : BinOp) (c₁ c₂ : Int) (a b : Term)
  /-- `c == 0 ? a : b`, the elaboration of `e ? b : a` (whose test is `e == 0`). -/
  | cond (c a b : Term)
  /-- `a & b`, `a | b`, `a ^ b`. -/
  | bit (o : Bitwise.Op) (a b : Term)
  /-- Division/remainder by a positive literal; produced by `StateExpr`. -/
  | divpos (o : DivRem.Op) (d : DivRem.Divisor) (a : Term)

/-- The recogniser. -/
def term (file : File Codec.wireModel Unit Unit) (x : Sym) : Eff → Option Term
  | .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))) =>
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then some (.lit n) else none
  | .mk _ (.wseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x'))))
      (.mk _ (.action (.mk .pos (.mk _ _ (.load
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
        (.mk _ () (.sym p')) .na)))))) =>
      if x'.key = x.key ∧ p'.key = p.key then some .var else none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk _ (.pure g))) =>
      match term file x e₁, term file x e₂ with
      | some t₁, some t₂ =>
        match Guard.guard file a b g, Guard.cmpGuard file a b g with
        | some op, _ => some (.bin op t₁ t₂)
        | none, some (r, c₁, c₂) => some (.cmp r c₁ c₂ t₁ t₂)
        | none, none => none
      | _, _ => none
  | .mk _ (.sseq (.mk _ (.base (some c, _))) ec
      (.mk _ (.case_ (.mk _ () (.sym c'))
        [(.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
          .mk _ (.if_ (.mk _ () (.op .eq (.mk _ () (.sym z')) (.mk _ () (.val (.object (.integer 0))))))
            (.mk _ (.sseq (.mk _ (.base (some u, _))) ea
              (.mk _ (.pure (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _
                (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')]))))))
            (.mk _ (.sseq (.mk _ (.base (some w, _))) eb
              (.mk _ (.pure (.mk _ () (.call (.sym s') [.mk _ () (.val (.ctype (.mk _
                (.basic (.integer (.signed .int)))))), .mk _ () (.sym w')])))))))),
         (.mk _ (.ctor .unspecified _), .mk _ (.pure _))]))) =>
      if c'.key = c.key ∧ z'.key = z.key ∧ u'.key = u.key ∧ w'.key = w.key ∧ c.key ≠ x.key ∧
          z.key ≠ x.key ∧ u.key ≠ x.key ∧ w.key ≠ x.key ∧ ConvInt.isConvLoadedInt file s = true ∧
          ConvInt.isConvLoadedInt file s' = true then
        match term file x ec, term file x ea, term file x eb with
        | some tc, some ta, some tb => some (.cond tc ta tb)
        | _, _, _ => none
      else none
  | _ => none
termination_by e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The value with the local holding `n`. -/
def Term.val (n : Int) : Term → Int
  | .lit c => c
  | .var => n
  | .bin op a b => Guard.apply op (a.val n) (b.val n)
  | .cmp r c₁ c₂ a b => Guard.compare r c₁ c₂ (a.val n) (b.val n)
  | .cond c a b => if c.val n = 0 then a.val n else b.val n
  | .bit o a b => o.apply (a.val n) (b.val n)
  | .divpos o d a => o.apply (a.val n) d.val

/-- `t` reads the local. -/
def Term.reads : Term → Bool
  | .lit _ => false
  | .var => true
  | .bin _ a b => a.reads || b.reads
  | .cmp _ _ _ a b => a.reads || b.reads
  | .cond c a b => c.reads || a.reads || b.reads
  | .bit _ a b => a.reads || b.reads
  | .divpos _ _ a => a.reads

/-- The local holds an `int`, no intermediate value leaves `int`, and the results of comparisons
are `int`s. -/
def Term.Ok (n : Int) : Term → Prop
  | .lit c => IsInt c
  | .var => IsInt n
  | .bin op a b => a.Ok n ∧ b.Ok n ∧ IsInt (Guard.apply op (a.val n) (b.val n))
  | .cmp _ c₁ c₂ a b => a.Ok n ∧ b.Ok n ∧ IsInt c₁ ∧ IsInt c₂
  | .cond c a b => c.Ok n ∧ if c.val n = 0 then a.Ok n else b.Ok n
  | .bit _ a b => a.Ok n ∧ b.Ok n
  | .divpos _ _ a => a.Ok n

theorem Term.ok_int {n : Int} (hn : IsInt n) : (t : Term) → t.Ok n → IsInt (t.val n)
  | .lit _, h => h
  | .var, h => h
  | .bin _ _ _, h => h.2.2
  | .cmp r c₁ c₂ a b, h => by
    unfold Term.val Guard.compare
    split
    · exact h.2.2.1
    · exact h.2.2.2
  | .cond c a b, h => by
    unfold Term.val
    obtain ⟨-, h⟩ := h
    split
    · rename_i hc; rw [ite_eq_left hc] at h; exact Term.ok_int hn a h
    · rename_i hc; rw [ite_eq_right hc] at h; exact Term.ok_int hn b h
  | .bit o a b, h => Bitwise.apply_int o (Term.ok_int hn a h.1) (Term.ok_int hn b h.2)
  | .divpos o d a, h => DivRem.apply_int o (Term.ok_int hn a h) d

/-- The value of an expression in range is an `int`. -/
theorem Term.int_of_ok {n : Int} : (t : Term) → t.Ok n → IsInt (t.val n)
  | .lit _, h => h
  | .var, h => h
  | .bin _ _ _, h => h.2.2
  | .cmp r c₁ c₂ a b, h => by
    unfold Term.val Guard.compare
    split
    · exact h.2.2.1
    · exact h.2.2.2
  | .cond c a b, h => by
    unfold Term.val
    obtain ⟨-, h⟩ := h
    split
    · rename_i hc; rw [ite_eq_left hc] at h; exact Term.int_of_ok a h
    · rename_i hc; rw [ite_eq_right hc] at h; exact Term.int_of_ok b h
  | .bit o a b, h => Bitwise.apply_int o (Term.int_of_ok a h.1) (Term.int_of_ok b h.2)
  | .divpos o d a, h => DivRem.apply_int o (Term.int_of_ok a h) d

/-- The outcome of an operator out of range. -/
abbrev overflow : Outcome := .ub .unknown .UB036_exceptional_condition

/-! ## Inversion -/

theorem term_lit {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {c : Int}
    (h : term file x e = some (.lit c)) :
    ∃ an pa, e = .mk an (.pure (.mk pa () (.val (.loaded (.specified (.integer c)))))) ∧ IsInt c := by
  unfold term at h
  split at h
  · split at h
    · rename_i hc
      cases h; exact ⟨_, _, rfl, hc⟩
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_var {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff}
    (h : term file x e = some .var) :
    ∃ (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x' : Sym) (l : Loc) (u : Unit),
      e = LoadTask.loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x' l u ∧ x'.key = x.key ∧
        p'.key = p.key := by
  unfold term at h
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i hc
      cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2⟩
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_bin {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {op : IntOp}
    {t₁ t₂ : Term} (h : term file x e = some (.bin op t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Guard.guard file a b g = some op ∧ term file x e₁ = some t₁ ∧ term file x e₂ = some t₂ := by
  unfold term at h
  split at h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
          by assumption⟩
      · cases h
      · cases h
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_cmp {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {r : BinOp}
    {c₁ c₂ : Int} {t₁ t₂ : Term} (h : term file x e = some (.cmp r c₁ c₂ t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (g : Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g))) ∧
      Guard.cmpGuard file a b g = some (r, c₁, c₂) ∧ term file x e₁ = some t₁ ∧
        term file x e₂ = some t₂ := by
  unfold term at h
  split at h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption,
          by assumption⟩
      · cases h
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_cond {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {tc ta tb : Term}
    (h : term file x e = some (.cond tc ta tb)) :
    ∃ ec ea eb : Eff, term file x ec = some tc ∧ term file x ea = some ta ∧
      term file x eb = some tb ∧
      (hasCCall ec = false → hasCCall ea = false → hasCCall eb = false → hasCCall e = false) ∧
      ∀ labels, Cond.CondRuns (file := file) (labels := labels) x e ec ea eb := by
  unfold term at h
  split at h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · rename_i cond
      obtain ⟨hc, hz, hu, hw, hcx, hzx, -, -, hs, hs'⟩ := cond
      split at h
      · cases h
        refine ⟨_, _, _, by assumption, by assumption, by assumption, ?_,
          fun labels => Cond.cond_runs_of_shape hc hz hu hw hcx hzx hs hs'⟩
        intro c₁ c₂ c₃
        simp [hasCCall, c₁, c₂, c₃]
      · cases h
    · cases h
  · cases h

theorem term_bit {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {o : Bitwise.Op}
    {t₁ t₂ : Term} (h : term file x e = some (.bit o t₁ t₂)) : False := by
  unfold term at h
  repeat' split at h
  all_goals cases h

theorem term_divpos {file : File Codec.wireModel Unit Unit} {x : Sym} {e : Eff} {o : DivRem.Op}
    {d : DivRem.Divisor} {a : Term} (h : term file x e = some (.divpos o d a)) : False := by
  unfold term at h
  repeat' split at h
  all_goals cases h

/-- Recognised expressions make no procedure call. -/
theorem term_calls {file : File Codec.wireModel Unit Unit} {x : Sym} :
    (t : Term) → {e : Eff} → term file x e = some t → hasCCall e = false
  | .lit _, _, h => by
    obtain ⟨an, pa, rfl, _⟩ := term_lit h
    rw [hasCCall.eq_def]
  | .var, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := term_var h
    simp [LoadTask.loadExpr, hasCCall]
  | .bin _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, rfl, _, h₁, h₂⟩ := term_bin h
    simp [hasCCall, term_calls t₁ h₁, term_calls t₂ h₂]
  | .cmp _ _ _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, rfl, _, h₁, h₂⟩ := term_cmp h
    simp [hasCCall, term_calls t₁ h₁, term_calls t₂ h₂]
  | .cond tc ta tb, _, h => by
    obtain ⟨_, _, _, h₁, h₂, h₃, hc, -⟩ := term_cond h
    exact hc (term_calls tc h₁) (term_calls ta h₂) (term_calls tb h₃)
  | .bit _ _ _, _, h => (term_bit h).elim
  | .divpos _ _ _, _, h => (term_divpos h).elim

/-! ## Runs -/

variable {file : Program} {labels : Labels}

/-- `Specified n`. -/
abbrev spec (n : Int) : Val := .loaded (.specified (.integer n))

theorem requestAux_tuple_bind (m : Mem.Concrete.State) (xs : List Access) (pp p1 p2 : List Annot)
    (a b : Sym) (ta tb : BaseType) (v₁ v₂ : Val) (body : EE) (env : Env) (k : List Frame) :
    requestAux file labels m (.value (.tuple [v₁, v₂]))
      (.annotations xs :: .effectBind (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
        .mk p2 (.base (some b, tb))])) body env :: k) false =
      .next (.effectExpr body (extendEnv [(a, v₁), (b, v₂)] env)) (.annotations xs :: k) := by
  simp [requestAux, awaitsScheduling, matchPattern, matchPatterns]

/-- `unseq [e₁, e₂]` of reads. -/
theorem unseq_pair {k : List Frame} {annots : List Annot} {e₁ e₂ : EE} {env : Env}
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → Touched m m' → I m') {v₁ v₂ : Val}
    (r₁ : ReadTask (file := file) (labels := labels) I env e₁ v₁)
    (r₂ : ReadTask (file := file) (labels := labels) I env e₂ v₂)
    (same : e₁ = e₂ → v₁ = v₂) (m : Mem.Concrete.State) (hm : I m) :
    ∃ xs m', (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false ⟨.effectExpr (.mk annots (.unseq [e₁, e₂])) env, k, m⟩
        ⟨.value (.tuple [v₁, v₂]), .annotations xs :: k, m'⟩ := by
  classical
  let val : EE → Val := fun e => if e = e₂ then v₂ else v₁
  have h₁ : val e₁ = v₁ := by
    by_cases h : e₁ = e₂
    · simp [val, h, same h]
    · simp [val, h]
  have h₂ : val e₂ = v₂ := by simp [val]
  obtain ⟨xs, m', rd, tch, run⟩ := LoadTask.unseq_reads (k := k) (annots := annots) (es := [e₁, e₂])
    (env := env) I hI val (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rw [h₁]; exact r₁
      · rw [h₂]; exact r₂) m hm
  simp only [List.map_cons, List.map_nil, h₁, h₂] at run
  exact ⟨xs, m', rd, tch, run⟩

/-- The pure guard after the operands: a focus, then its expression above a diagnostic frame. -/
theorem guard_local (annots : List Annot) (p : PE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ∃ l', LocalReaches file labels false ⟨.effectExpr (.mk annots (.pure p)) env, k, m⟩
      ⟨.pureExpr p env, .diagnosticLocation m.currentLocation :: k, {m with currentLocation := l'}⟩ := by
  obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m annots p env k false
  exact LoadTask.focus_local (LoadTask.plain_pureExpr p env) (by simpa using hr)

theorem reads_left {op : IntOp} {a b : Term} (h : a.reads = true) :
    (Term.bin op a b).reads = true := by simp [Term.reads, h]

theorem reads_right {op : IntOp} {a b : Term} (h : b.reads = true) :
    (Term.bin op a b).reads = true := by simp [Term.reads, h]

theorem reads_cmp_left {rl : BinOp} {c₁ c₂ : Int} {a b : Term} (h : a.reads = true) :
    (Term.cmp rl c₁ c₂ a b).reads = true := by simp [Term.reads, h]

theorem reads_cmp_right {rl : BinOp} {c₁ c₂ : Int} {a b : Term} (h : b.reads = true) :
    (Term.cmp rl c₁ c₂ a b).reads = true := by simp [Term.reads, h]

/-- **Value arm.** The local's slot is needed only when the expression reads it. -/
theorem term_runs {x : Sym} : (t : Term) → {e : Eff} → term file x e = some t →
    {env : Env} → {id addr n : Int} →
    (t.reads = true → env.lookup x = some (.object (.pointer (.allocated id addr)))) → IsInt n →
    t.Ok n → ∀ (k : List Frame) (m : Mem.Concrete.State), (t.reads = true → Slot m id addr n) →
      ∃ xs m' fr, (fr = [] ∧ xs = [] ∨ fr = [.annotations xs]) ∧ (∀ a ∈ xs, a.write = false) ∧
        Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
          ⟨.value (spec (t.val n)), fr ++ k, m'⟩
  | .lit c, e, h, env, id, addr, n, hx, hn, ok, k, m, slot => by
    obtain ⟨an, pa, rfl, _⟩ := term_lit h
    obtain ⟨l', run⟩ := LoadTask.pure_val_local (file := file) (labels := labels) (wc := false) an pa
      (.loaded (.specified (.integer c))) env k m
    exact ⟨[], _, [], .inl ⟨rfl, rfl⟩, by simp, ⟨l', m.lastUsed, rfl⟩, run⟩
  | .var, e, h, env, id, addr, n, hx, hn, ok, k, m, slot => by
    obtain ⟨a0, pa, a1, a2, la, a3, c1, a4, pt, p, p', x', l, u, rfl, hx', hp'⟩ := term_var h
    have hx₁ : env.lookup x' = some (.object (.pointer (.allocated id addr))) := by
      rw [lookup_key hx']; exact hx rfl
    obtain ⟨a, m', ha, t, run⟩ := LoadTask.load_local (file := file) (labels := labels) a0 pa a1 a2
      la a3 c1 a4 pt p p' x' l u hp' env k m hx₁ hn (slot rfl)
    exact ⟨[a], m', [.annotations [a]], .inr rfl, by simpa using ha, t, run⟩
  | .bin op t₁ t₂, e, h, env, id, addr, n, hx, hn, ok, k, m, slot => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := term_bin h
    obtain ⟨ok₁, ok₂, okr⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => (Term.bin op t₁ t₂).reads = true → Slot m id addr n
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t r => t.slot (s r)
    have task : ∀ (t : Term) (e : Eff), term file x e = some t →
        (∀ m, I m → ∃ xs m' fr, (fr = [] ∧ xs = [] ∨ fr = [.annotations xs]) ∧
          (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
          LocalReaches file labels false ⟨.effectExpr e env, [], m⟩
            ⟨.value (spec (t.val n)), fr ++ [], m'⟩) →
        ReadTask (file := file) (labels := labels) I env e (spec (t.val n)) := by
      intro t e he runs
      refine ⟨term_calls t he, fun m hm => ?_⟩
      obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := runs m hm
      refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
      rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (task t₁ e₁ h₁ fun m hm => term_runs t₁ h₁ (fun r => hx (reads_left r)) hn ok₁ [] m
        (fun r => hm (reads_left r)))
      (task t₂ e₂ h₂ fun m hm => term_runs t₂ h₂ (fun r => hx (reads_right r)) hn ok₂ [] m
        (fun r => hm (reads_right r)))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m slot
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val n), spec (t₂.val n)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val n) (t₂.val n) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    have i₁ := Term.ok_int hn t₁ ok₁
    have i₂ := Term.ok_int hn t₂ ok₂
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val n) (t₂.val n) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (Guard.guard_eval hg env i₁ i₂ okr) (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
      m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)

  | .cmp rl c₁ c₂ t₁ t₂, e, h, env, id, addr, n, hx, hn, ok, k, m, slot => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := term_cmp h
    obtain ⟨ok₁, ok₂, -, -⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => (Term.cmp rl c₁ c₂ t₁ t₂).reads = true → Slot m id addr n
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t r => t.slot (s r)
    have task : ∀ (t : Term) (e : Eff), term file x e = some t →
        (∀ m, I m → ∃ xs m' fr, (fr = [] ∧ xs = [] ∨ fr = [.annotations xs]) ∧
          (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
          LocalReaches file labels false ⟨.effectExpr e env, [], m⟩
            ⟨.value (spec (t.val n)), fr ++ [], m'⟩) →
        ReadTask (file := file) (labels := labels) I env e (spec (t.val n)) := by
      intro t e he runs
      refine ⟨term_calls t he, fun m hm => ?_⟩
      obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := runs m hm
      refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
      rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (task t₁ e₁ h₁ fun m hm => term_runs t₁ h₁ (fun r => hx (reads_cmp_left r)) hn ok₁ [] m
        (fun r => hm (reads_cmp_left r)))
      (task t₂ e₂ h₂ fun m hm => term_runs t₂ h₂ (fun r => hx (reads_cmp_right r)) hn ok₂ [] m
        (fun r => hm (reads_cmp_right r)))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m slot
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val n), spec (t₂.val n)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val n) (t₂.val n) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    have i₁ := Term.ok_int hn t₁ ok₁
    have i₂ := Term.ok_int hn t₂ ok₂
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val n) (t₂.val n) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (Guard.cmpGuard_eval hg env i₁ i₂) (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
      m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)

  | .cond tc ta tb, e, h, env, id, addr, n, hx, hn, ok, k, m, slot => by
    obtain ⟨ec, ea, eb, h₁, h₂, h₃, -, cr⟩ := term_cond h
    obtain ⟨okc, okb⟩ := ok
    obtain ⟨K, s₁, rest⟩ := cr labels env k m
    obtain ⟨xs, m₁, fr, hfr, rd, tch, run⟩ := term_runs tc h₁
      (fun r => hx (by simp [Term.reads, r])) hn okc (K :: k) m (fun r => slot (by simp [Term.reads, r]))
    obtain ⟨env₂, KB, m₂, hx₂, tch₂, s₃, fin⟩ := rest (tc.val n) fr xs hfr m₁
    have slot₂ : (Term.cond tc ta tb).reads = true → Slot m₂ id addr n :=
      fun r => (tch.trans tch₂).slot (slot r)
    by_cases h0 : tc.val n = 0
    · rw [ite_eq_left h0] at s₃ okb
      obtain ⟨ys, m₃, fr', hfr', rd', tch', run'⟩ := term_runs ta h₂
        (fun r => by rw [hx₂]; exact hx (by simp [Term.reads, r])) hn okb (KB :: (fr ++ k)) m₂
        (fun r => slot₂ (by simp [Term.reads, r]))
      obtain ⟨m₄, tch₄, s₅⟩ := fin (ta.val n) (Term.ok_int hn ta okb) fr' ys hfr' m₃
      obtain ⟨zs, fr'', hfr'', hzs, s₆⟩ := Cond.merge (file := file) (labels := labels) hfr hfr'
        (spec (ta.val n)) k m₄
      have hv : Term.val n (.cond tc ta tb) = ta.val n := by simp [Term.val, h0]
      rw [hv]
      exact ⟨zs, m₄, fr'', hfr'', fun a ha => (hzs a ha).elim (rd' a) (rd a),
        tch.trans (tch₂.trans (tch'.trans tch₄)), s₁.trans (run.trans (s₃.trans (run'.trans
          (s₅.trans s₆))))⟩
    · rw [ite_eq_right h0] at s₃ okb
      obtain ⟨ys, m₃, fr', hfr', rd', tch', run'⟩ := term_runs tb h₃
        (fun r => by rw [hx₂]; exact hx (by simp [Term.reads, r])) hn okb (KB :: (fr ++ k)) m₂
        (fun r => slot₂ (by simp [Term.reads, r]))
      obtain ⟨m₄, tch₄, s₅⟩ := fin (tb.val n) (Term.ok_int hn tb okb) fr' ys hfr' m₃
      obtain ⟨zs, fr'', hfr'', hzs, s₆⟩ := Cond.merge (file := file) (labels := labels) hfr hfr'
        (spec (tb.val n)) k m₄
      have hv : Term.val n (.cond tc ta tb) = tb.val n := by simp [Term.val, h0]
      rw [hv]
      exact ⟨zs, m₄, fr'', hfr'', fun a ha => (hzs a ha).elim (rd' a) (rd a),
        tch.trans (tch₂.trans (tch'.trans tch₄)), s₁.trans (run.trans (s₃.trans (run'.trans
          (s₅.trans s₆))))⟩
  | .bit _ _ _, _, h, _, _, _, _, _, _, _, _, _, _ => (term_bit h).elim
  | .divpos _ _ _, _, h, _, _, _, _, _, _, _, _, _, _ => (term_divpos h).elim

/-- A recognised expression in range is a read-only task, from every memory satisfying `I`
in which the local holds `n` when the expression reads it. -/
theorem term_task {x : Sym} (t : Term) {e : Eff} (h : term file x e = some t) {env : Env}
    {id addr n : Int}
    (hx : t.reads = true → env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IsInt n) (ok : t.Ok n) (I : Mem.Concrete.State → Prop)
    (hs : ∀ m, I m → t.reads = true → Slot m id addr n) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val n)) := by
  refine ⟨term_calls t h, fun m hm => ?_⟩
  obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := term_runs (file := file) (labels := labels) t h hx hn ok
    [] m (hs m hm)
  refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
  rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]

/-- **Undefined-behaviour arm.** -/
theorem term_fails {x : Sym} : (t : Term) → {e : Eff} → term file x e = some t →
    {env : Env} → {id addr n : Int} →
    (t.reads = true → env.lookup x = some (.object (.pointer (.allocated id addr)))) → IsInt n →
    ¬ t.Ok n → ∀ (k : List Frame) (m : Mem.Concrete.State), (t.reads = true → Slot m id addr n) →
      Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow
  | .lit c, e, h, env, id, addr, n, hx, hn, bad, k, m, slot => by
    obtain ⟨_, _, _, hc⟩ := term_lit h
    exact absurd hc bad
  | .var, _, _, _, _, _, _, _, hn, bad, _, _, _ => absurd hn bad
  | .bin op t₁ t₂, e, h, env, id, addr, n, hx, hn, bad, k, m, slot => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := term_bin h
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure g)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, term_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok n
    · by_cases ok₁ : t₁.Ok n
      · have okr : ¬ IsInt (Guard.apply op (t₁.val n) (t₂.val n)) := fun hr => bad ⟨ok₁, ok₂, hr⟩
        let I : Mem.Concrete.State → Prop := fun m => (Term.bin op t₁ t₂).reads = true → Slot m id addr n
        have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t r => t.slot (s r)
        obtain ⟨xs, m₁, -, -, s₂⟩ := unseq_pair (file := file) (labels := labels) (k := K)
          (annots := au) I hI
          (term_task t₁ h₁ (fun r => hx (reads_left r)) hn ok₁ I (fun _ hm r => hm (reads_left r)))
          (term_task t₂ h₂ (fun r => hx (reads_right r)) hn ok₂ I (fun _ hm r => hm (reads_right r)))
          (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m slot
        have s₃ : LocalReaches file labels false
            ⟨.value (.tuple [spec (t₁.val n), spec (t₂.val n)]), .annotations xs :: K, m₁⟩
            ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val n) (t₂.val n) env),
              .annotations xs :: k, m₁⟩ :=
          .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
            (LoadTask.plain_effectExpr _ _))
        obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
          (Guard.operands a b (t₁.val n) (t₂.val n) env) (.annotations xs :: k) m₁
        obtain ⟨k', s₅, hend⟩ := Guard.guard_fails (labels := labels) hg env (Term.ok_int hn t₁ ok₁)
          (Term.ok_int hn t₂ ok₂) okr false
          (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
          {m₁ with currentLocation := l'}
        refine ⟨_, s₂.trans (s₃.trans (s₄.trans s₅)), ?_, Or.inl hend⟩
        intro v h
        cases h
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := term_runs (file := file) (labels := labels) t₂ h₂
          (fun r => hx (reads_right r)) hn ok₂ [] m (fun r => slot (reads_right r))
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val n), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact term_fails t₁ h₁ (fun r => hx (reads_left r)) hn ok₁ [] m'
            (fun r => tch.slot (slot (reads_left r)))
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact term_fails t₂ h₂ (fun r => hx (reads_right r)) hn ok₂ [] m (fun r => slot (reads_right r))

  | .cmp rl c₁ c₂ t₁ t₂, e, h, env, id, addr, n, hx, hn, bad, k, m, slot => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := term_cmp h
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure g)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, term_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok n
    · by_cases ok₁ : t₁.Ok n
      · exact absurd ⟨ok₁, ok₂, Guard.cmpGuard_int hg⟩ bad
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := term_runs (file := file) (labels := labels) t₂ h₂
          (fun r => hx (reads_cmp_right r)) hn ok₂ [] m (fun r => slot (reads_cmp_right r))
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val n), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact term_fails t₁ h₁ (fun r => hx (reads_cmp_left r)) hn ok₁ [] m'
            (fun r => tch.slot (slot (reads_cmp_left r)))
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact term_fails t₂ h₂ (fun r => hx (reads_cmp_right r)) hn ok₂ [] m (fun r => slot (reads_cmp_right r))
  | .cond tc ta tb, e, h, env, id, addr, n, hx, hn, bad, k, m, slot => by
    obtain ⟨ec, ea, eb, h₁, h₂, h₃, -, cr⟩ := term_cond h
    obtain ⟨K, s₁, rest⟩ := cr labels env k m
    refine ArenaFail.Fails.pre file labels s₁ ?_
    by_cases okc : tc.Ok n
    · obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := term_runs tc h₁
        (fun r => hx (by simp [Term.reads, r])) hn okc (K :: k) m (fun r => slot (by simp [Term.reads, r]))
      obtain ⟨env₂, KB, m₂, hx₂, tch₂, s₃, -⟩ := rest (tc.val n) fr xs hfr m₁
      refine ArenaFail.Fails.pre file labels (run.trans s₃) ?_
      have slot₂ : (Term.cond tc ta tb).reads = true → Slot m₂ id addr n :=
        fun r => (tch.trans tch₂).slot (slot r)
      by_cases h0 : tc.val n = 0
      · have okb : ¬ ta.Ok n := fun o => bad ⟨okc, by rw [ite_eq_left h0]; exact o⟩
        rw [ite_eq_left h0]
        exact term_fails ta h₂ (fun r => by rw [hx₂]; exact hx (by simp [Term.reads, r])) hn okb
          (KB :: (fr ++ k)) m₂ (fun r => slot₂ (by simp [Term.reads, r]))
      · have okb : ¬ tb.Ok n := fun o => bad ⟨okc, by rw [ite_eq_right h0]; exact o⟩
        rw [ite_eq_right h0]
        exact term_fails tb h₃ (fun r => by rw [hx₂]; exact hx (by simp [Term.reads, r])) hn okb
          (KB :: (fr ++ k)) m₂ (fun r => slot₂ (by simp [Term.reads, r]))
    · exact term_fails tc h₁ (fun r => hx (by simp [Term.reads, r])) hn okc (K :: k) m
        (fun r => slot (by simp [Term.reads, r]))
  | .bit _ _ _, _, h, _, _, _, _, _, _, _, _, _, _ => (term_bit h).elim
  | .divpos _ _ _, _, h, _, _, _, _, _, _, _, _, _, _ => (term_divpos h).elim

end Silmaril.Compile.Core.Verified.IntExpr
