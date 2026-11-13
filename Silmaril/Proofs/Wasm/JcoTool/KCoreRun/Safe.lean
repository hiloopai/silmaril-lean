module

public import Silmaril.Wasm.JcoTool.KCoreRun.Defs

/-!
# A Hoare-style safety logic for the checked semantics

`Safe nl P S Q`: every `KDrop.dexec` run of `S` from a state satisfying `P` is a `bexec nl` run
(Core does not trap where the fragment does not) and ends in a state satisfying `Q`. The rules
follow the statements: `EOk` (the conditions `cev` adds to an expression: local and global
indices in range, nonzero divisors, loads below `MSZ`) with `cev_ok`; `safe_lset`,
`safe_gset`, `safe_st8`, `safe_mcopy`, `safe_seq`, `safe_ite`, `safe_block`, `safe_loop`
(an invariant `I`), `safe_br`, `safe_brIf`, `safe_ret`, `safe_call` (with `bcall_read`, `bcall_write`,
`bcall_dropR`, `bcall_dropW`: a built-in call `dexec` runs is a `bcall` run when its buffer lies
in memory and its result local is in range). The guards of the generated code enter through the condition of `safe_ite`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd mcopy writeBytes byteOf slice u8v)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec dcallBI)
open Silmaril.Wasm.Component.Streams.Drop (dstep)

variable {nl : Nat} {P : DSt → Prop} {Q : Out → DSt → Prop}

/-- **The safety triple**: where `dexec` runs `S` from a `P`-state, `bexec nl` runs it to the same
result, which satisfies `Q`. -/
def Safe (nl : Nat) (P : DSt → Prop) (S : S) (Q : Out → DSt → Prop) : Prop :=
  ∀ f s o s', P s → dexec S f s = some (o, s') → bexec nl S f s = some (o, s') ∧ Q o s'

/-- The conditions under which `cev` computes an expression. -/
def EOk (nl : Nat) (s : DSt) : E → Prop
  | .c _ => True
  | .l i => i < nl
  | .g i => i < NG
  | .bin o a b => EOk nl s a ∧ EOk nl s b ∧ ((o = .divu ∨ o = .remu) → b.eval s.down ≠ 0)
  | .eqz a => EOk nl s a
  | .ld8 a => EOk nl s a ∧ a.eval s.down < MSZ

theorem cev_ok {s : DSt} : ∀ {e : E}, EOk nl s e → cev nl s e = some (e.eval s.down)
  | .c _, _ => rfl
  | .l i, h => by simp only [cev, ite_eq_left (show i < nl from h)]; rfl
  | .g i, h => by simp only [cev, ite_eq_left (show i < NG from h)]; rfl
  | .bin o a b, ⟨ha, hb, hd⟩ => by
    have hb0 : ¬((o = .divu ∨ o = .remu) ∧ b.eval s.down = 0) := fun ⟨h1, h2⟩ => hd h1 h2
    simp only [cev, cev_ok ha, cev_ok hb, Option.bind_eq_bind, Option.bind_some, ite_eq_right hb0]
    rfl
  | .eqz a, h => by simp only [cev, cev_ok (e := a) h, Option.map_some]; rfl
  | .ld8 a, ⟨ha, hl⟩ => by
    simp only [cev, cev_ok ha, Option.bind_eq_bind, Option.bind_some, ite_eq_left hl]
    rfl

theorem mapM_ok {s : DSt} : ∀ {args : List E}, (∀ a ∈ args, EOk nl s a) →
    args.mapM (cev nl s) = some (args.map (·.eval s.down))
  | [], _ => rfl
  | a :: as, h => by
    have h₁ : cev nl s a = some (a.eval s.down) := cev_ok (h a List.mem_cons_self)
    have h₂ := mapM_ok (args := as) fun x hx => h x (List.mem_cons_of_mem a hx)
    simp only [List.mapM_cons, h₁, h₂, List.map_cons]
    rfl

/-! ## Labels -/

/-- How a statement ends after the label around it (`dexec.dlab`). -/
def lout : Out → Out
  | .br 0 => .norm
  | .br (k + 1) => .br k
  | o => o

theorem dlab_lout (o : Out) (s : DSt) : dexec.dlab (some (o, s)) = some (lout o, s) := by
  rcases o with _ | (_ | k) | v <;> rfl

theorem dlab_inv {r : Option (Out × DSt)} {o : Out} {s : DSt} (h : dexec.dlab r = some (o, s)) :
    ∃ o₁, r = some (o₁, s) ∧ o = lout o₁ := by
  rcases r with _ | ⟨o₁, s₁⟩
  · cases h
  · have h' : some (lout o₁, s₁) = some (o, s) := (dlab_lout o₁ s₁).symm.trans h
    obtain ⟨rfl, rfl⟩ : lout o₁ = o ∧ s₁ = s := by simpa only [Option.some.injEq, Prod.mk.injEq] using h'
    exact ⟨o₁, rfl, rfl⟩

/-! ## The rules -/

theorem Safe.conseq {P' : DSt → Prop} {S : S} {Q' : Out → DSt → Prop} (h : Safe nl P S Q)
    (hp : ∀ s, P' s → P s) (hq : ∀ o s, Q o s → Q' o s) : Safe nl P' S Q' := fun f s o s' hs hd =>
  ⟨(h f s o s' (hp s hs) hd).1, hq o s' (h f s o s' (hp s hs) hd).2⟩

/-- A triple from no precondition holds from any. -/
theorem Safe.conseq_pre {S : S} (h : Safe nl (fun _ => True) S Q) : Safe nl P S Q :=
  h.conseq (fun _ _ => trivial) fun _ _ h => h

theorem safe_unreachable : Safe nl P .unreachable Q := fun _ _ _ _ _ h => by cases h

theorem safe_nop (hq : ∀ s, P s → Q .norm s) : Safe nl P .nop Q := fun _ s o s' hs h => by
  obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ s = s' := by simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using h
  exact ⟨rfl, hq s hs⟩

theorem safe_lset {i : Nat} {e : E} (hi : i < nl)
    (h : ∀ s, P s → EOk nl s e ∧ Q .norm { s with l := upd s.l i (e.eval s.down) }) :
    Safe nl P (.lset i e) Q := fun _ s o s' hs hd => by
  obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ { s with l := upd s.l i (e.eval s.down) } = s' := by
    simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
  exact ⟨by simp only [bexec, ite_eq_left hi, cev_ok (h s hs).1, Option.map_some], (h s hs).2⟩

theorem safe_gset {i : Nat} {e : E} (hi : i < NG)
    (h : ∀ s, P s → EOk nl s e ∧ Q .norm { s with g := upd s.g i (e.eval s.down) }) :
    Safe nl P (.gset i e) Q := fun _ s o s' hs hd => by
  obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ { s with g := upd s.g i (e.eval s.down) } = s' := by
    simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
  exact ⟨by simp only [bexec, ite_eq_left hi, cev_ok (h s hs).1, Option.map_some], (h s hs).2⟩

theorem safe_st8 {a v : E}
    (h : ∀ s, P s → EOk nl s a ∧ EOk nl s v ∧ a.eval s.down < MSZ ∧
      Q .norm { s with m := upd s.m (a.eval s.down) (v.eval s.down % 256) }) :
    Safe nl P (.st8 a v) Q := fun _ s o s' hs hd => by
  obtain ⟨ha, hv, hl, hq⟩ := h s hs
  obtain ⟨rfl, rfl⟩ : Out.norm = o ∧
      { s with m := upd s.m (a.eval s.down) (v.eval s.down % 256) } = s' := by
    simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
  exact ⟨by simp only [bexec, cev_ok ha, cev_ok hv, Option.bind_eq_bind, Option.bind_some, ite_eq_left hl], hq⟩

theorem safe_mcopy {d src n : E}
    (h : ∀ s, P s → EOk nl s d ∧ EOk nl s src ∧ EOk nl s n ∧
      (d.eval s.down ≤ src.eval s.down ∧ src.eval s.down + n.eval s.down ≤ MSZ) ∧
      Q .norm { s with m := (mcopy s.m (d.eval s.down) (src.eval s.down)
        (n.eval s.down)) }) :
    Safe nl P (.mcopy d src n) Q := fun _ s o s' hs hd => by
  obtain ⟨hd', hs', hn, hl, hq⟩ := h s hs
  obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ { s with m := (mcopy s.m (d.eval s.down)
      (src.eval s.down) (n.eval s.down)) } = s' := by
    simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
  exact ⟨by simp only [bexec, cev_ok hd', cev_ok hs', cev_ok hn, Option.bind_eq_bind,
    Option.bind_some, ite_eq_left hl], hq⟩

theorem safe_br {k : Nat} (hk : k < M32) (h : ∀ s, P s → Q (.br k) s) : Safe nl P (.br k) Q :=
  fun _ s o s' hs hd => by
    obtain ⟨rfl, rfl⟩ : Out.br k = o ∧ s = s' := by
      simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
    exact ⟨by simp only [bexec, ite_eq_left hk], h s hs⟩

theorem safe_ret {e : E} (h : ∀ s, P s → EOk nl s e ∧ Q (.ret (e.eval s.down)) s) :
    Safe nl P (.ret e) Q := fun _ s o s' hs hd => by
  obtain ⟨rfl, rfl⟩ : Out.ret (e.eval s.down) = o ∧ s = s' := by
    simpa only [dexec, Option.some.injEq, Prod.mk.injEq] using hd
  exact ⟨by simp only [bexec, cev_ok (h s hs).1, Option.map_some], (h s hs).2⟩

theorem safe_brIf {k : Nat} {c : E} (hk : k < M32)
    (h : ∀ s, P s → EOk nl s c ∧ (c.eval s.down ≠ 0 → Q (.br k) s) ∧ (c.eval s.down = 0 → Q .norm s)) :
    Safe nl P (.brIf k c) Q := fun _ s o s' hs hd => by
  obtain ⟨hc, h1, h0⟩ := h s hs
  by_cases hv : c.eval s.down ≠ 0
  · obtain ⟨rfl, rfl⟩ : Out.br k = o ∧ s = s' := by
      simpa only [dexec, ite_eq_left hv, Option.some.injEq, Prod.mk.injEq] using hd
    exact ⟨by simp only [bexec, ite_eq_left hk, cev_ok hc, Option.map_some, ite_eq_left hv], h1 hv⟩
  · obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ s = s' := by
      simpa only [dexec, ite_eq_right hv, Option.some.injEq, Prod.mk.injEq] using hd
    exact ⟨by simp only [bexec, ite_eq_left hk, cev_ok hc, Option.map_some, ite_eq_right hv], h0 (not_not.mp hv)⟩

theorem safe_seq {a b : S} {R : Out → DSt → Prop} (ha : Safe nl P a R) (hb : Safe nl (R .norm) b Q)
    (hr : ∀ o s, o ≠ .norm → R o s → Q o s) : Safe nl P (.seq a b) Q := by
  intro f s o s' hs hd
  cases h₁ : dexec a f s with
  | none => simp only [dexec, h₁, reduceCtorEq] at hd
  | some x =>
    obtain ⟨o₁, s₁⟩ := x
    obtain ⟨hb₁, hr₁⟩ := ha f s o₁ s₁ hs h₁
    rcases o₁ with _ | k | v
    · have hd' : dexec b f s₁ = some (o, s') := by simpa only [dexec, h₁] using hd
      exact ⟨by simp only [bexec, hb₁, (hb f s₁ o s' hr₁ hd').1], (hb f s₁ o s' hr₁ hd').2⟩
    · obtain ⟨rfl, rfl⟩ : Out.br k = o ∧ s₁ = s' := by
        simpa only [dexec, h₁, Option.some.injEq, Prod.mk.injEq] using hd
      exact ⟨by simp only [bexec, hb₁], hr _ _ (fun h => by cases h) hr₁⟩
    · obtain ⟨rfl, rfl⟩ : Out.ret v = o ∧ s₁ = s' := by
        simpa only [dexec, h₁, Option.some.injEq, Prod.mk.injEq] using hd
      exact ⟨by simp only [bexec, hb₁], hr _ _ (fun h => by cases h) hr₁⟩

theorem safe_ite {c : E} {t e : S} {R : Out → DSt → Prop} (hc : ∀ s, P s → EOk nl s c)
    (ht : Safe nl (fun s => P s ∧ c.eval s.down ≠ 0) t R)
    (he : Safe nl (fun s => P s ∧ c.eval s.down = 0) e R)
    (hr : ∀ o s, R o s → Q (lout o) s) : Safe nl P (.ite c t e) Q := by
  intro f s o s' hs hd
  have hv : cev nl s c = some (c.eval s.down) := cev_ok (hc s hs)
  have hd' : dexec.dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s) = some (o, s') := by
    simpa only [dexec] using hd
  obtain ⟨o₁, h₁, rfl⟩ := dlab_inv hd'
  by_cases h0 : c.eval s.down ≠ 0
  · have ht' := ht f s o₁ s' ⟨hs, h0⟩ (by simpa only [ite_eq_left h0] using h₁)
    exact ⟨by simp only [bexec, hv, ite_eq_left h0, ht'.1, dlab_lout], hr _ _ ht'.2⟩
  · have he' := he f s o₁ s' ⟨hs, not_not.mp h0⟩ (by simpa only [ite_eq_right h0] using h₁)
    exact ⟨by simp only [bexec, hv, ite_eq_right h0, he'.1, dlab_lout], hr _ _ he'.2⟩

theorem safe_block {b : S} {R : Out → DSt → Prop} (hb : Safe nl P b R)
    (hr : ∀ o s, R o s → Q (lout o) s) : Safe nl P (.block b) Q := by
  intro f s o s' hs hd
  have hd' : dexec.dlab (dexec b f s) = some (o, s') := by simpa only [dexec] using hd
  obtain ⟨o₁, h₁, rfl⟩ := dlab_inv hd'
  exact ⟨by simp only [bexec, (hb f s o₁ s' hs h₁).1, dlab_lout], hr _ _ (hb f s o₁ s' hs h₁).2⟩

/-- How a loop's body ends, for the loop: `br 0` goes round again (`I`), every other end is the
loop's (`br (k + 1)` as `br k`). -/
def LoopQ (I : DSt → Prop) (Q : Out → DSt → Prop) : Out → DSt → Prop
  | .br 0, s => I s
  | .br (k + 1), s => Q (.br k) s
  | o, s => Q o s

theorem loopN_safe {b : S} {I : DSt → Prop} (hb : Safe nl I b (LoopQ I Q)) (f : Nat) :
    ∀ (n : Nat) (s : DSt) {o : Out} {s' : DSt}, I s →
      dexec.dloopN (dexec b f) n s = some (o, s') →
      dexec.dloopN (bexec nl b f) n s = some (o, s') ∧ Q o s'
  | 0, _, _, _, _, hd => by cases hd
  | n + 1, s, o, s', hs, hd => by
    cases h₁ : dexec b f s with
    | none => simp only [dexec.dloopN, h₁, reduceCtorEq] at hd
    | some x =>
      obtain ⟨o₁, s₁⟩ := x
      obtain ⟨hb₁, hq₁⟩ := hb f s o₁ s₁ hs h₁
      rcases o₁ with _ | (_ | k) | v
      · obtain ⟨rfl, rfl⟩ : Out.norm = o ∧ s₁ = s' := by
          simpa only [dexec.dloopN, h₁, Option.some.injEq, Prod.mk.injEq] using hd
        exact ⟨by simp only [dexec.dloopN, hb₁], hq₁⟩
      · have hd' : dexec.dloopN (dexec b f) n s₁ = some (o, s') := by
          simpa only [dexec.dloopN, h₁] using hd
        have ih := loopN_safe hb f n s₁ hq₁ hd'
        exact ⟨by simp only [dexec.dloopN, hb₁, ih.1], ih.2⟩
      · obtain ⟨rfl, rfl⟩ : Out.br k = o ∧ s₁ = s' := by
          simpa only [dexec.dloopN, h₁, Option.some.injEq, Prod.mk.injEq] using hd
        exact ⟨by simp only [dexec.dloopN, hb₁], hq₁⟩
      · obtain ⟨rfl, rfl⟩ : Out.ret v = o ∧ s₁ = s' := by
          simpa only [dexec.dloopN, h₁, Option.some.injEq, Prod.mk.injEq] using hd
        exact ⟨by simp only [dexec.dloopN, hb₁], hq₁⟩

theorem safe_loop {b : S} {I : DSt → Prop} (hb : Safe nl I b (LoopQ I Q)) :
    Safe nl I (.loop b) Q := fun f s o s' hs hd => by
  have hd' : dexec.dloopN (dexec b f) f s = some (o, s') := by simpa only [dexec] using hd
  simpa only [bexec] using loopN_safe hb f f s hs hd'

/-! ## Built-in calls -/

theorem blocked_lt : Silmaril.Wasm.Component.Async.blocked < M32 := by decide

/-- A completed `stream.read` is a `bcall` run. -/
theorem bcall_read_done {hh p n d code : Nat} {xs : List Silmaril.Wasm.Component.Val} {st'} {s : DSt}
    {r : Out × DSt} (hm : memOK MSZ .streamRead [hh, p, n] = true) (hd : d < nl)
    (hds : dstep s.st (.streamRead hh n) = some (st', .read code xs))
    (h : dcallBI .streamRead [hh, p, n] [d] s = some r) : bcall nl .streamRead [hh, p, n] [d] s = some r := by
  have hc : code < M32 ∧ code / 16 = xs.length ∧ xs.length ≤ n := by
    by_contra hc
    simp only [dcallBI, hds, hc, ↓reduceIte, reduceCtorEq] at h
  have e : r = (.norm,
      { s with st := st', m := writeBytes s.m p (xs.map byteOf), l := upd s.l d code }) := by
    simpa only [dcallBI, hds, hc, and_self, ↓reduceIte, Option.some.injEq] using h.symm
  rw [e]
  simp only [bcall, hm, ↓reduceIte, bi, hds, hc, and_self, List.length_singleton,
    List.mem_singleton, forall_eq, hd]
  rfl

/-- A blocked `stream.read` is a `bcall` run. -/
theorem bcall_read_nat {hh p n d rv : Nat} {st'} {s : DSt} {r : Out × DSt}
    (hm : memOK MSZ .streamRead [hh, p, n] = true) (hd : d < nl)
    (hds : dstep s.st (.streamRead hh n) = some (st', .nat rv))
    (h : dcallBI .streamRead [hh, p, n] [d] s = some r) : bcall nl .streamRead [hh, p, n] [d] s = some r := by
  have hc : rv = Silmaril.Wasm.Component.Async.blocked := by
    by_contra hc
    simp only [dcallBI, hds, hc, ↓reduceIte, reduceCtorEq] at h
  have e : r = (.norm, { s with st := st', rp := some (hh, p), l := upd s.l d rv }) := by
    simpa only [dcallBI, hds, hc, ↓reduceIte, Option.some.injEq] using h.symm
  rw [e]
  simp only [bcall, hm, ↓reduceIte, bi, hds, hc, List.length_singleton, List.mem_singleton,
    forall_eq, hd, blocked_lt, and_self]
  rfl

/-- **A `stream.read` `dexec` runs** with its buffer in memory is a `bcall` run. -/
theorem bcall_read {hh p n d : Nat} {s : DSt} {r : Out × DSt} (hm : memOK MSZ .streamRead [hh, p, n] = true)
    (hd : d < nl) (h : dcallBI .streamRead [hh, p, n] [d] s = some r) :
    bcall nl .streamRead [hh, p, n] [d] s = some r := by
  rcases hds : dstep s.st (.streamRead hh n) with _ | ⟨st', _ | rv | ⟨_, _⟩ | ⟨code, xs⟩ | _ | _⟩
  · simp only [dcallBI, hds, reduceCtorEq] at h
  · simp only [dcallBI, hds, reduceCtorEq] at h
  · exact bcall_read_nat hm hd hds h
  · simp only [dcallBI, hds, reduceCtorEq] at h
  · exact bcall_read_done hm hd hds h
  all_goals simp only [dcallBI, hds, reduceCtorEq] at h

/-- **A `stream.write` `dexec` runs** with its buffer in memory is a `bcall` run. -/
theorem bcall_write {hh p n d : Nat} {s : DSt} {r : Out × DSt}
    (hm : memOK MSZ .streamWrite [hh, p, n] = true) (hd : d < nl)
    (h : dcallBI .streamWrite [hh, p, n] [d] s = some r) :
    bcall nl .streamWrite [hh, p, n] [d] s = some r := by
  obtain ⟨st', rv, hds, hc, e⟩ : ∃ st' rv, dstep s.st (.streamWrite hh ((slice s.m p n).map u8v)) =
      some (st', .nat rv) ∧ rv < M32 ∧ r = (.norm, { s with st := st', l := upd s.l d rv }) := by
    simp only [dcallBI] at h
    split at h
    · split at h
      · exact ⟨_, _, by assumption, by assumption, (Option.some.inj h).symm⟩
      · cases h
    · cases h
  rw [e]
  simp only [bcall, hm, ↓reduceIte, bi, hds, hc, List.length_singleton, List.mem_singleton,
    forall_eq, hd, and_self]
  rfl

/-- **A drop `dexec` runs** is a `bcall` run. -/
theorem bcall_dropR {as : List Nat} {s : DSt} {r : Out × DSt} (h : dcallBI .dropR as [] s = some r) :
    bcall nl .dropR as [] s = some r := by
  match as, h with
  | [hh], h =>
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp h
    rw [← e]
    simp only [bcall, memOK, ↓reduceIte, bi, hx, Option.map_some]
    rfl
  | [], h => cases h
  | _ :: _ :: _, h => cases h

theorem bcall_dropW {as : List Nat} {s : DSt} {r : Out × DSt} (h : dcallBI .dropW as [] s = some r) :
    bcall nl .dropW as [] s = some r := by
  match as, h with
  | [hh], h =>
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp h
    rw [← e]
    simp only [bcall, memOK, ↓reduceIte, bi, hx, Option.map_some]
    rfl
  | [], h => cases h
  | _ :: _ :: _, h => cases h

/-- **A call**, given that its `dexec` runs are `bcall` runs (`bcall_read`, `bcall_write`,
`bcall_dropR`, `bcall_dropW`). -/
theorem safe_call {b : BI} {args : List E} {dst : List Nat}
    (h : ∀ s, P s → (∀ a ∈ args, EOk nl s a) ∧
      (∀ r, dcallBI b (args.map (·.eval s.down)) dst s = some r →
        bcall nl b (args.map (·.eval s.down)) dst s = some r) ∧
      ∀ o s', dcallBI b (args.map (·.eval s.down)) dst s = some (o, s') → Q o s') :
    Safe nl P (.call b args dst) Q := fun _ s o s' hs hd => by
  obtain ⟨ha, hbc, hq⟩ := h s hs
  have hd' : dcallBI b (args.map (·.eval s.down)) dst s = some (o, s') := by simpa only [dexec] using hd
  exact ⟨by simp only [bexec, mapM_ok ha, Option.bind_eq_bind, Option.bind_some, hbc _ hd'],
    hq o s' hd'⟩

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
