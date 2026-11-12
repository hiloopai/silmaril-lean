module

public import Silmaril.Proofs.Wasm.Auto.ESeg.XCheck

/-! # Lifting straight-line code with locals: the symbolic run is the concrete run

`lift_exec`: if `lift Γ.length a = some A`, then in every frame typed by `Γ` (and with any
operand stack `rs` below), `exec` of the segment is what the summary `A` denotes:
`exec s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs)`. In particular the segment fails
(traps or gets stuck) exactly when a term of `A` (a guard, a local or a stack slot) has no
value.

Unrefined proofs (an instruction-by-instruction case split).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph

variable {f : Frame}

/-! ## Lists of values -/

theorem evalL_length : ∀ {es : List Term} {ls : List Val}, evalL f es = some ls →
    ls.length = es.length
  | [], ls, h => by cases h; rfl
  | e :: es, ls, h => by
    simp only [evalL] at h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [evalL_length hvs]

theorem evalL_cons_inv {e : Term} {es : List Term} {ls : List Val}
    (h : evalL f (e :: es) = some ls) :
    ∃ v vs, e.eval f = some v ∧ evalL f es = some vs ∧ ls = v :: vs := by
  simp only [evalL] at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨v, vs, hv, hvs, rfl⟩

theorem evalL_cons_some {e : Term} {es : List Term} {v : Val} {vs : List Val}
    (h₁ : e.eval f = some v) (h₂ : evalL f es = some vs) : evalL f (e :: es) = some (v :: vs) := by
  simp [evalL, h₁, h₂]

theorem evalL_getElem? : ∀ {es : List Term} {ls : List Val} {i : Nat} {e : Term},
    evalL f es = some ls → es[i]? = some e → ∃ v, e.eval f = some v ∧ ls[i]? = some v
  | [], _, _, _, _, he => by simp at he
  | e₀ :: es, ls, 0, e, h, he => by
    obtain ⟨v, vs, hv, -, rfl⟩ := evalL_cons_inv h
    have : e₀ = e := by simpa using he
    subst this
    exact ⟨v, hv, rfl⟩
  | e₀ :: es, ls, i + 1, e, h, he => by
    obtain ⟨v, vs, -, hvs, rfl⟩ := evalL_cons_inv h
    exact evalL_getElem? (es := es) (ls := vs) hvs (by simpa using he)

theorem evalL_set : ∀ {es : List Term} {ls : List Val} {i : Nat} {e : Term} {v : Val},
    evalL f es = some ls → e.eval f = some v → evalL f (es.set i e) = some (ls.set i v)
  | [], ls, i, e, v, h, _ => by cases h; rfl
  | e₀ :: es, ls, 0, e, v, h, hv => by
    obtain ⟨v₀, vs, -, hvs, rfl⟩ := evalL_cons_inv h
    simp [evalL, hv, hvs]
  | e₀ :: es, ls, i + 1, e, v, h, hv => by
    obtain ⟨v₀, vs, hv₀, hvs, rfl⟩ := evalL_cons_inv h
    simp [evalL, hv₀, evalL_set hvs hv]

theorem evalL_none_iff : ∀ {es : List Term}, evalL f es = none ↔ ∃ e ∈ es, e.eval f = none
  | [] => by simp [evalL]
  | e :: es => by
    have ih : evalL f es = none ↔ ∃ e ∈ es, e.eval f = none := evalL_none_iff
    cases he : e.eval f with
    | none => simp [evalL, he]
    | some v =>
      cases hes : evalL f es with
      | none =>
        simp only [evalL, he, Option.bind_some, hes, Option.map_none, true_iff]
        obtain ⟨e', hm, hn⟩ := ih.mp hes
        exact ⟨e', List.mem_cons_of_mem _ hm, hn⟩
      | some vs =>
        simp only [evalL, he, Option.bind_some, hes, Option.map_some, reduceCtorEq, false_iff,
          not_exists, not_and]
        intro e' hm hn
        rcases List.mem_cons.mp hm with rfl | hm'
        · simp [he] at hn
        · have : evalL f es = none := ih.mpr ⟨e', hm', hn⟩
          simp [hes] at this

/-! ## Frames -/

theorem setLocs_locals_length (g : Frame) (ls : List Val) (hl : ls.length ≤ g.locals.length) :
    (setLocs g ls).locals.length = g.locals.length := by
  simp [setLocs]; omega

theorem local?_setLocs (g : Frame) (ls : List Val) (x : LocalIdx) (v : Val)
    (h : ls[x.toNat]? = some v) : (setLocs g ls).local? x = some (some v) := by
  have hx : x.toNat < ls.length := (List.getElem?_eq_some_iff.mp h).1
  simp only [Frame.local?, setLocs]
  rw [List.getElem?_append_left (by simpa using hx)]
  simp [h]

theorem setLocs_set (g : Frame) (ls : List Val) (i : Nat) (v : Val) (hi : i < ls.length) :
    setLocs g (ls.set i v) = { setLocs g ls with locals := (setLocs g ls).locals.set i (some v) } := by
  simp only [setLocs, List.length_set, List.map_set]
  congr 1
  rw [List.set_append_left _ _ (by simpa using hi)]

/-! ## Covers of one step: every old term is a subterm of a new one -/

/-- Every term of `S` is a subterm of a term of `S'`. -/
def Covered (S S' : Sym) : Prop :=
  ∀ e ∈ S.terms, ∃ e' ∈ S'.terms, ∃ p, e'.get? p = some e

theorem covered_none {S S' : Sym} (hc : Covered S S') (h : den f S = none) : den f S' = none := by
  have hn : ∃ e ∈ S.terms, e.eval f = none := by
    simp only [den] at h
    cases hG : evalL f S.guards with
    | none =>
      obtain ⟨e, hm, he⟩ := evalL_none_iff.mp hG
      exact ⟨e, by simp [Sym.terms, hm], he⟩
    | some gs =>
      rw [hG, Option.bind_some] at h
      cases hL : evalL f S.locs with
      | none =>
        obtain ⟨e, hm, he⟩ := evalL_none_iff.mp hL
        exact ⟨e, by simp [Sym.terms, hm], he⟩
      | some ls =>
        rw [hL, Option.bind_some] at h
        cases hS : evalL f S.stack with
        | none =>
          obtain ⟨e, hm, he⟩ := evalL_none_iff.mp hS
          exact ⟨e, by simp [Sym.terms, hm], he⟩
        | some vs => simp [hS] at h
  obtain ⟨e, hm, he⟩ := hn
  obtain ⟨e', hm', p, hp⟩ := hc e hm
  have he' : e'.eval f = none := by
    cases h' : e'.eval f with
    | none => rfl
    | some v =>
      have := get?_isSome (f := f) hp (by simp [h'])
      simp [he] at this
  simp only [Sym.terms, List.mem_append] at hm'
  simp only [den]
  rcases hm' with (hm' | hm') | hm'
  · rw [evalL_none_iff.mpr ⟨e', hm', he'⟩]; rfl
  · cases evalL f S'.guards <;> simp [evalL_none_iff.mpr ⟨e', hm', he'⟩]
  · cases evalL f S'.guards <;> cases evalL f S'.locs <;> simp [evalL_none_iff.mpr ⟨e', hm', he'⟩]

theorem mem_set_or {l : List Term} {i : Nat} {e a : Term} (ha : a ∈ l) :
    a ∈ l.set i e ∨ l[i]? = some a := by
  induction l generalizing i with
  | nil => simp at ha
  | cons b l ih =>
    cases i with
    | zero =>
      rcases List.mem_cons.mp ha with rfl | h
      · right; rfl
      · left; exact List.mem_cons_of_mem _ h
    | succ i =>
      rcases List.mem_cons.mp ha with rfl | h
      · left; simp
      · rcases ih h with h' | h'
        · left; exact List.mem_cons_of_mem _ h'
        · right; simpa using h'

theorem self_cover {e : Term} {l : List Term} (h : e ∈ l) : ∃ e' ∈ l, ∃ p, e'.get? p = some e :=
  ⟨e, h, [], by simp [Term.get?]⟩

theorem lstep_covered {S S' : Sym} {i : Instr} (h : lstep S i = some S') : Covered S S' := by
  rcases S with ⟨st, ls, gs⟩
  intro e he
  simp only [Sym.terms, List.mem_append] at he
  cases i <;> simp only [lstep] at h <;> try cases h
  case nop => exact self_cover (by simp [Sym.terms]; tauto)
  case drop =>
    rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact self_cover (by simp [Sym.terms] at he ⊢; tauto)
  case intConst => exact self_cover (by simp [Sym.terms]; tauto)
  case localGet x =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact self_cover (by simp [Sym.terms]; tauto)
  case localSet x =>
    rcases st with _ | ⟨a, st⟩ <;> cases hold : ls[x.toNat]? <;>
      simp only [hold, reduceCtorEq, Option.some.injEq] at h
    rename_i old
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · rcases mem_set_or (i := x.toNat) (e := a) he with h' | h'
      · exact self_cover (by simp [Sym.terms, h'])
      · rw [hold] at h'; cases h'; exact self_cover (by simp [Sym.terms])
    · rcases List.mem_cons.mp he with rfl | he'
      · have hx := (List.getElem?_eq_some_iff.mp hold).1
        refine self_cover ?_
        simp only [Sym.terms, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (List.mem_iff_getElem.mpr ⟨x.toNat, by simpa using hx, by simp⟩))
      · exact self_cover (by simp [Sym.terms, he'])
  case localTee x =>
    rcases st with _ | ⟨a, st⟩ <;> cases hold : ls[x.toNat]? <;>
      simp only [hold, reduceCtorEq, Option.some.injEq] at h
    rename_i old
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · rcases mem_set_or (i := x.toNat) (e := a) he with h' | h'
      · exact self_cover (by simp [Sym.terms, h'])
      · rw [hold] at h'; cases h'; exact self_cover (by simp [Sym.terms])
    · exact self_cover (by simp [Sym.terms] at he ⊢; tauto)
  case intUnOp t op =>
    rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · exact self_cover (by simp [Sym.terms, he])
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨.un t op e, by simp [Sym.terms], [0], by simp [Term.get?]⟩
      · exact self_cover (by simp [Sym.terms, he'])
  case intTestOp t op =>
    rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · exact self_cover (by simp [Sym.terms, he])
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨.test t e, by simp [Sym.terms], [0], by simp [Term.get?]⟩
      · exact self_cover (by simp [Sym.terms, he'])
  case intBinOp t op =>
    rcases st with _ | ⟨b, _ | ⟨a, st⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · exact self_cover (by simp [Sym.terms, he])
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨.bin t op a e, by simp [Sym.terms], [1], by simp [Term.get?]⟩
      · rcases List.mem_cons.mp he' with rfl | he''
        · exact ⟨.bin t op e b, by simp [Sym.terms], [0], by simp [Term.get?]⟩
        · exact self_cover (by simp [Sym.terms, he''])
  case intRelOp t op =>
    rcases st with _ | ⟨b, _ | ⟨a, st⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    rcases he with (he | he) | he
    · exact self_cover (by simp [Sym.terms, he])
    · exact self_cover (by simp [Sym.terms, he])
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨.rel t op a e, by simp [Sym.terms], [1], by simp [Term.get?]⟩
      · rcases List.mem_cons.mp he' with rfl | he''
        · exact ⟨.rel t op e b, by simp [Sym.terms], [0], by simp [Term.get?]⟩
        · exact self_cover (by simp [Sym.terms, he''])

/-! ## One step -/

theorem den_eq_some {S : Sym} {p : Frame × List Val} (h : den f S = some p) :
    ∃ gs ls vs, evalL f S.guards = some gs ∧ evalL f S.locs = some ls ∧
      evalL f S.stack = some vs ∧ p = (setLocs f ls, vs) := by
  simp only [den] at h
  obtain ⟨gs, hg, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ls, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨vs, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨gs, ls, vs, hg, hl, hv, rfl⟩

theorem den_of {S : Sym} {gs ls vs : List Val} (hg : evalL f S.guards = some gs)
    (hl : evalL f S.locs = some ls) (hv : evalL f S.stack = some vs) :
    den f S = some (setLocs f ls, vs) := by
  simp [den, hg, hl, hv]

theorem lstep_locs_length {S S' : Sym} {i : Instr} (h : lstep S i = some S') :
    S'.locs.length = S.locs.length := by
  rcases S with ⟨st, ls, gs⟩
  cases i <;> simp only [lstep] at h <;> try cases h
  all_goals first
    | rfl
    | (rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
       subst h; rfl)
    | (rcases st with _ | ⟨b, _ | ⟨a, st⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
       subst h; rfl)
    | (obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)
    | (rcases st with _ | ⟨a, st⟩ <;> rename_i x <;> cases hold : ls[x.toNat]? <;>
         simp only [hold, reduceCtorEq, Option.some.injEq] at h
       subst h; simp)

/-- **One instruction**: the concrete step from what `S` denotes is what `S'` denotes. -/
theorem lstep_exec {H : Type} {S S' : Sym} {i : Instr} (h : lstep S i = some S') (s : Store H)
    (rs : List Val) (hlen : S.locs.length ≤ f.locals.length) :
    (den f S).bind (fun p => exec1 s p.1 (p.2 ++ rs) i) =
      (den f S').map fun p => (s, p.1, p.2 ++ rs) := by
  match hd : den f S with
  | none => rw [covered_none (lstep_covered h) hd]; rfl
  | some p =>
    obtain ⟨gs, ls, vs, hg, hl, hv, rfl⟩ := den_eq_some hd
    have hll : ls.length = S.locs.length := evalL_length hl
    rw [Option.bind_some]
    rcases S with ⟨st, lc, gd⟩
    simp only at hg hl hv hlen hll
    cases i <;> simp only [lstep] at h <;> try cases h
    case nop.refl => rw [den_of hg hl hv]; rfl
    case drop =>
      rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨va, vst, ha, hst, rfl⟩ := evalL_cons_inv hv
      rw [den_of (S := ⟨st, lc, a :: gd⟩) (evalL_cons_some ha hg) hl hst]
      rfl
    case intConst.refl t c =>
      have hc : (Term.const t c.toNat).eval f = some (.num ⟨.int t, c⟩) := by
        simp [Term.eval, intVal]
      rw [den_of (S := ⟨_ :: st, lc, gd⟩) hg hl (evalL_cons_some hc hv)]
      rfl
    case localGet x =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨va, hva, hlv⟩ := evalL_getElem? hl ha
      rw [den_of (S := ⟨a :: st, lc, gd⟩) hg hl (evalL_cons_some hva hv)]
      simp [exec1, localVal?, local?_setLocs f ls x va hlv]
    case localSet x =>
      rcases st with _ | ⟨a, st'⟩ <;> cases hold : lc[x.toNat]? <;>
        simp only [hold, reduceCtorEq, Option.some.injEq] at h
      rename_i old
      subst h
      obtain ⟨va, vst, ha, hvst, rfl⟩ := evalL_cons_inv hv
      obtain ⟨vo, hvo, -⟩ := evalL_getElem? hl hold
      have hx : x.toNat < lc.length := (List.getElem?_eq_some_iff.mp hold).1
      rw [den_of (S := ⟨st', lc.set x.toNat a, old :: gd⟩) (evalL_cons_some hvo hg)
        (evalL_set hl ha) hvst]
      have hx' : x.toNat < (setLocs f ls).locals.length := by
        rw [setLocs_locals_length f ls (by omega)]; omega
      simp [exec1, popV, hx', setLocs_set f ls x.toNat va (by omega), Frame.setLocal]
    case localTee x =>
      rcases st with _ | ⟨a, st'⟩ <;> cases hold : lc[x.toNat]? <;>
        simp only [hold, reduceCtorEq, Option.some.injEq] at h
      rename_i old
      subst h
      obtain ⟨va, vst, ha, hvst, rfl⟩ := evalL_cons_inv hv
      obtain ⟨vo, hvo, -⟩ := evalL_getElem? hl hold
      have hx : x.toNat < lc.length := (List.getElem?_eq_some_iff.mp hold).1
      rw [den_of (S := ⟨a :: st', lc.set x.toNat a, old :: gd⟩) (evalL_cons_some hvo hg)
        (evalL_set hl ha) (evalL_cons_some ha hvst)]
      have hx' : x.toNat < (setLocs f ls).locals.length := by
        rw [setLocs_locals_length f ls (by omega)]; omega
      simp [exec1, popV, hx', setLocs_set f ls x.toNat va (by omega), Frame.setLocal]
    case intUnOp t op =>
      rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨va, vst, ha, hst, rfl⟩ := evalL_cons_inv hv
      rw [List.cons_append, exec1_un]
      cases hu : unV t op (some va) with
      | none =>
        have : evalL f (Term.un t op a :: st) = none := by simp [evalL, Term.eval, ha, hu]
        simp [den, hg, hl, this]
      | some u =>
        have hu' : (Term.un t op a).eval f = some u := by simp [Term.eval, ha, hu]
        rw [den_of (S := ⟨_ :: st, lc, gd⟩) hg hl (evalL_cons_some hu' hst)]
        rfl
    case intTestOp t op =>
      rcases st with _ | ⟨a, st⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨va, vst, ha, hst, rfl⟩ := evalL_cons_inv hv
      cases op
      rw [List.cons_append, exec1_test]
      cases hu : testV t (some va) with
      | none =>
        have : evalL f (Term.test t a :: st) = none := by simp [evalL, Term.eval, ha, hu]
        simp [den, hg, hl, this]
      | some u =>
        have hu' : (Term.test t a).eval f = some u := by simp [Term.eval, ha, hu]
        rw [den_of (S := ⟨_ :: st, lc, gd⟩) hg hl (evalL_cons_some hu' hst)]
        rfl
    case intBinOp t op =>
      rcases st with _ | ⟨b, _ | ⟨a, st⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨vb, vs₁, hb, hv₁, rfl⟩ := evalL_cons_inv hv
      obtain ⟨va, vst, ha, hst, rfl⟩ := evalL_cons_inv hv₁
      rw [List.cons_append, List.cons_append, exec1_bin]
      cases hu : binV t op (some va) (some vb) with
      | none =>
        have : evalL f (Term.bin t op a b :: st) = none := by simp [evalL, Term.eval, ha, hb, hu]
        simp [den, hg, hl, this]
      | some u =>
        have hu' : (Term.bin t op a b).eval f = some u := by simp [Term.eval, ha, hb, hu]
        rw [den_of (S := ⟨_ :: st, lc, gd⟩) hg hl (evalL_cons_some hu' hst)]
        rfl
    case intRelOp t op =>
      rcases st with _ | ⟨b, _ | ⟨a, st⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨vb, vs₁, hb, hv₁, rfl⟩ := evalL_cons_inv hv
      obtain ⟨va, vst, ha, hst, rfl⟩ := evalL_cons_inv hv₁
      rw [List.cons_append, List.cons_append, exec1_rel]
      cases hu : relV t op (some va) (some vb) with
      | none =>
        have : evalL f (Term.rel t op a b :: st) = none := by simp [evalL, Term.eval, ha, hb, hu]
        simp [den, hg, hl, this]
      | some u =>
        have hu' : (Term.rel t op a b).eval f = some u := by simp [Term.eval, ha, hb, hu]
        rw [den_of (S := ⟨_ :: st, lc, gd⟩) hg hl (evalL_cons_some hu' hst)]
        rfl

/-- **A sequence of instructions.** -/
theorem lsteps_exec {H : Type} (s : Store H) (rs : List Val) :
    ∀ {is : List Instr} {S S' : Sym}, lsteps S is = some S' → S.locs.length ≤ f.locals.length →
      (den f S).bind (fun p => exec s p.1 (p.2 ++ rs) is) =
        (den f S').map fun p => (s, p.1, p.2 ++ rs)
  | [], S, S', h, _ => by
    cases h
    cases den f S <;> rfl
  | i :: is, S, S', h, hlen => by
    simp only [lsteps] at h
    split at h
    · rename_i S₁ h₁
      have k₁ := lstep_exec (f := f) h₁ s rs hlen
      have hlen₁ : S₁.locs.length ≤ f.locals.length := by rw [lstep_locs_length h₁]; exact hlen
      have k₂ := lsteps_exec s rs h hlen₁
      rw [← k₂]
      cases hd : den f S with
      | none =>
        have h1 : den f S₁ = none := by
          cases h' : den f S₁ with
          | none => rfl
          | some q => rw [hd, h'] at k₁; simp at k₁
        rw [h1]; rfl
      | some p =>
        rw [hd, Option.bind_some] at k₁
        rw [Option.bind_some, exec_cons]
        cases he : exec1 s p.1 (p.2 ++ rs) i with
        | none =>
          rw [he] at k₁
          have : den f S₁ = none := by
            cases h' : den f S₁ with
            | none => rfl
            | some q => rw [h'] at k₁; cases k₁
          rw [this]; rfl
        | some r =>
          rw [he] at k₁
          obtain ⟨q, hq, hr⟩ := Option.map_eq_some_iff.mp k₁.symm
          rw [hq, Option.bind_some]
          subst hr
          rfl
    · cases h

/-! ## The initial state -/

theorem lidx_toNat {i : Nat} (hi : i < 2 ^ 32) : (lidx i).toNat = i := by
  simp [lidx, Idx.toNat]; omega

theorem den_init {Γ : List IntType} (hl : Γ.length < 2 ^ 32) (hf : FrameOk Γ f) :
    den f (Sym.init Γ.length) = some (f, []) := by
  -- the values of the locals, in order
  have key : ∀ m, m ≤ Γ.length → ∃ ls : List Val, ls.length = m ∧
      evalL f ((List.range m).map Term.lget) = some ls ∧
      ∀ i, i < m → f.locals[i]? = (ls[i]?).map some := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨[], rfl, rfl, fun i hi => absurd hi (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨ls, hlen, hev, hget⟩ := ih (by omega)
      obtain ⟨t, ht⟩ : ∃ t, Γ[m]? = some t := ⟨Γ[m], List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨x, hx⟩ := hf m t ht
      have hloc : f.locals[m]? = some (some (intVal t x)) := by
        have := hx
        simp only [localVal?, Frame.local?, lidx_toNat (by omega : m < 2 ^ 32)] at this
        split at this
        · rename_i v hv; cases this; exact hv
        · cases this
      refine ⟨ls ++ [intVal t x], by simp [hlen], ?_, ?_⟩
      · have hm' : (Term.lget m).eval f = some (intVal t x) := hx
        have hev2 : ∀ (es₁ es₂ : List Term) (v₁ v₂ : List Val), evalL f es₁ = some v₁ →
            evalL f es₂ = some v₂ → evalL f (es₁ ++ es₂) = some (v₁ ++ v₂) := by
          intro es₁ es₂ v₁ v₂ h₁ h₂
          induction es₁ generalizing v₁ with
          | nil => cases h₁; simpa using h₂
          | cons e es ih' =>
            obtain ⟨v, vs, hv, hvs, rfl⟩ := evalL_cons_inv h₁
            simp [evalL, hv, ih' vs hvs]
        rw [List.range_succ, List.map_append]
        exact hev2 _ _ _ _ hev (by simp [evalL, hm'])
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hget i hi', List.getElem?_append_left (by omega)]
        · rw [hloc, List.getElem?_append_right (by omega)]; simp [hlen]
  obtain ⟨ls, hlen, hev, hget⟩ := key Γ.length (le_refl _)
  have hframe : setLocs f ls = f := by
    have hle : ls.length ≤ f.locals.length := by
      rcases Nat.eq_zero_or_pos Γ.length with h0 | hpos
      · omega
      · have h1 := hget (Γ.length - 1) (by omega)
        rw [List.getElem?_eq_getElem (l := ls) (by omega), Option.map_some] at h1
        have := (List.getElem?_eq_some_iff.mp h1).1
        omega
    cases f with
    | mk locals module =>
      simp only [setLocs, Frame.mk.injEq, and_true]
      apply List.ext_getElem?
      intro i
      by_cases hi : i < ls.length
      · rw [List.getElem?_append_left (by simpa using hi), hget i (by omega)]
        simp
      · rw [List.getElem?_append_right (by simpa using hi)]
        simp only [List.length_map, List.getElem?_drop]
        congr 1
        omega
  simp only [den, Sym.init, evalL, Option.bind_some, hev, Option.map_some, hframe]

/-- **Lifting is sound**: the run of a lifted segment is what its summary denotes. -/
theorem lift_exec {Γ : List IntType} {a : List Instr} {A : Sym} (hl : Γ.length < 2 ^ 32)
    (h : lift Γ.length a = some A) {H : Type} (s : Store H) (rs : List Val) (hf : FrameOk Γ f) :
    exec s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) := by
  have hlen : (Sym.init Γ.length).locs.length ≤ f.locals.length := by
    simp only [Sym.init, List.length_map, List.length_range]
    rcases Nat.eq_zero_or_pos Γ.length with h0 | hpos
    · omega
    · obtain ⟨t, ht⟩ : ∃ t, Γ[Γ.length - 1]? = some t :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨x, hx⟩ := hf _ t ht
      simp only [localVal?, Frame.local?, lidx_toNat (by omega : Γ.length - 1 < 2 ^ 32)] at hx
      split at hx
      · rename_i v hv
        have := (List.getElem?_eq_some_iff.mp hv).1
        omega
      · cases hx
  have k := lsteps_exec (f := f) s rs h hlen
  rw [den_init hl hf, Option.bind_some] at k
  simpa using k

end Silmaril.Proofs.Wasm.Auto.ESeg