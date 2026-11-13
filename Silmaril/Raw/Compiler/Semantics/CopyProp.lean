module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Silmaril.Machine.CBackend.RTL.Construct.Defs
public import Silmaril.Foundations.ForwardSim

@[expose] public section

/-!
# Copy propagation on RTL.SSA, with its local lemma

`copyProp` is block-local copy propagation: walking each block, a `move d s` makes the copy
`d ↦ s` available, and every later read of `d` in the block (an operand, a block argument, a
returned value) reads `s` instead, until an operation writes `d` or `s`. The moves themselves
stay; a dead-code pass would remove the ones no longer read.

The analysis is syntactic and the pass needs no well-formedness: it is correct on every
program, SSA or not. Its correctness is the **local lemma** `behaves_copyProp_iff`: the
original and the propagated program have the same behaviours from every start state, by a
lock-step simulation in which the two machines are in the *same* state. The invariant
(`Inv`) is that every available copy holds in the frame: at a point `(f, l, i)` the copies
available before the `i`-th operation of block `l` (`envAt`) have equal values, and the same
for every suspended caller at its `call`. A read of `sub env r` then reads what `r` holds
(`get_sub`), so one step of the propagated program is the step of the original one
(`step_copyProp`), and the invariant is preserved by every step (`Inv.step`).

`Silmaril.Compile.Semantics.copyPropPass` packages it as an `EndoPass` on the zoo language
`ssaLang`, and so as a verified Mir → Lir optimization through `mirOptimize`.
-/

namespace Silmaril.Machine.RTL.SSA.CopyProp

open Silmaril.Machine.Lir (Word Memory)

variable {R : Type} [DecidableEq R]

/-! ## The analysis -/

/-- Available copies: `(d, s)` says `d` holds what `s` holds. -/
abbrev Env (R : Type) := List (R × R)

/-- The register to read for `r`. -/
def sub (env : Env R) (r : R) : R := (env.lookup r).getD r

/-- Forget the copies that mention a register of `ds`. -/
def kill (env : Env R) (ds : List R) : Env R :=
  env.filter fun p => !(ds.contains p.1) && !(ds.contains p.2)

/-- The copies available after an operation. -/
def update (env : Env R) : Op R → Env R
  | .move d s => (d, sub env s) :: kill env [d]
  | o => kill env o.defs

/-- The copies available before the `i`-th operation of a block. -/
def envAt (ops : List (Op R)) (i : Nat) : Env R := (ops.take i).foldl update []

/-- An operation with its reads propagated. -/
def renameOp (env : Env R) : Op R → Op R
  | .const d v => .const d v
  | .move d s => .move d (sub env s)
  | .unary op d s => .unary op d (sub env s)
  | .binary op d a b => .binary op d (sub env a) (sub env b)
  | .load w e d b o => .load w e d (sub env b) o
  | .store w b o s => .store w (sub env b) o (sub env s)
  | .call f as rs => .call f (as.map (sub env)) rs

/-- A terminator with its reads propagated. -/
def renameTerm (env : Env R) : Term R → Term R
  | .jump t as => .jump t (as.map (sub env))
  | .cond c t₁ a₁ t₂ a₂ => .cond (sub env c) t₁ (a₁.map (sub env)) t₂ (a₂.map (sub env))
  | .ret vs => .ret (vs.map (sub env))
  | .trap => .trap

/-- Copy propagation in one block. -/
def block (b : Block R) : Block R :=
  ⟨b.params, b.ops.mapIdx fun i o => renameOp (envAt b.ops i) o,
    renameTerm (envAt b.ops b.ops.length) b.term⟩

/-- Copy propagation in a function. -/
def func (fn : Func R) : Func R := ⟨fn.sig, fn.entry, fn.blocks.map block⟩

/-- **Copy propagation** in a program. -/
def copyProp (p : Prog R) : Prog R := ⟨p.funcs.map func⟩

/-! ## Lookup -/

theorem block?_copyProp (p : Prog R) (f : FuncId) (l : Label) :
    (copyProp p).block? f l = (p.block? f l).map block := by
  simp only [Prog.block?, Prog.func?, copyProp, List.getElem?_map]
  cases p.funcs[f]? <;> simp [Func.block?, func]

/-- The environment of a point. -/
def envOf (p : Prog R) (pt : Point) : Env R :=
  match p.block? pt.func pt.label with
  | some b => envAt b.ops pt.index
  | none => []

/-- Fetched code with its reads propagated. -/
def renameCode (env : Env R) : Code R → Code R
  | .op o => .op (renameOp env o)
  | .term t => .term (renameTerm env t)

theorem fetch_copyProp (p : Prog R) (pt : Point) :
    (copyProp p).fetch pt = (p.fetch pt).map (renameCode (envOf p pt)) := by
  simp only [Prog.fetch, block?_copyProp, envOf]
  cases p.block? pt.func pt.label with
  | none => rfl
  | some b =>
    simp only [Option.map_some, Option.bind_some, block, List.getElem?_mapIdx]
    cases hi : b.ops[pt.index]? with
    | some o => rfl
    | none =>
      simp only [Option.map_none, List.length_mapIdx]
      split
      · rename_i h
        simp [renameCode, h]
      · rfl

theorem enter_copyProp (p : Prog R) (f : FuncId) (vals : List Word) :
    (copyProp p).enter f vals = p.enter f vals := by
  simp only [Prog.enter, Prog.func?, copyProp, List.getElem?_map]
  cases p.funcs[f]? with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, Option.bind_some, func, Func.block?, List.getElem?_map]
    cases fn.blocks[fn.entry]? <;> rfl

theorem start_copyProp (p : Prog R) (f : FuncId) (args : List Word) (mem : Memory) :
    (copyProp p).start f args mem = p.start f args mem := by
  simp [Prog.start, enter_copyProp]

/-! ## Available copies hold -/

/-- Every available copy holds in a frame. -/
def Holds (env : Env R) (fr : Frame R) : Prop := ∀ q ∈ env, fr.get q.1 = fr.get q.2

theorem mem_of_lookup : ∀ {env : Env R} {r s : R}, env.lookup r = some s → (r, s) ∈ env
  | [], _, _, h => by simp at h
  | (a, b) :: env, r, s, h => by
    by_cases hr : r = a
    · subst hr
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · rw [List.lookup_cons, show (r == a) = false from beq_false_of_ne hr] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem get_sub {env : Env R} {fr : Frame R} (h : Holds env fr) (r : R) :
    fr.get (sub env r) = fr.get r := by
  unfold sub
  cases hl : env.lookup r with
  | none => rfl
  | some s => exact (h _ (mem_of_lookup hl)).symm

theorem readAll_sub {env : Env R} {fr : Frame R} (h : Holds env fr) (rs : List R) :
    fr.readAll (rs.map (sub env)) = fr.readAll rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, readAll_cons, readAll_cons, get_sub h, ih]

omit [DecidableEq R] in
theorem holds_nil (fr : Frame R) : Holds ([] : Env R) fr := fun _ h => by simp at h

theorem holds_kill {env : Env R} {fr fr' : Frame R} {ds : List R} (h : Holds env fr)
    (hfr : ∀ r, r ∉ ds → fr'.get r = fr.get r) : Holds (kill env ds) fr' := by
  intro q hq
  simp only [kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not] at hq
  rw [hfr _ hq.2.1, hfr _ hq.2.2]
  exact h q hq.1

/-- Executing an operation keeps the copies available after it. -/
theorem holds_update {env : Env R} {fr fr' : Frame R} {m m' : Memory} {o : Op R}
    (h : Holds env fr) (he : o.exec fr m = some (fr', m')) : Holds (update env o) fr' := by
  have hset : ∀ (d : R) (v : Word) (r : R), r ∉ [d] → (fr.set d v).get r = fr.get r := by
    intro d v r hr
    simp only [List.mem_singleton] at hr
    simp [hr]
  cases o with
  | const d v =>
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact holds_kill h (hset d v)
  | move d s =>
    simp only [Op.exec] at he
    cases hs : fr.get s with
    | none => simp [hs] at he
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only [Frame.get_set, ite_true]
        split
        · rfl
        · rw [get_sub h, hs]
      · exact holds_kill h (hset d x) q hq
  | unary op d s =>
    simp only [Op.exec] at he
    cases hs : fr.get s with
    | none => simp [hs] at he
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact holds_kill h (hset d _)
  | binary op d a b =>
    simp only [Op.exec] at he
    cases ha : fr.get a <;> cases hb : fr.get b <;> simp [ha, hb] at he
    rename_i x y
    cases hz : op.eval x y <;> simp [hz] at he
    obtain ⟨rfl, -⟩ := he
    exact holds_kill h (hset d _)
  | load w e d base off =>
    simp only [Op.exec] at he
    cases ha : fr.get base <;> simp [ha] at he
    rename_i x
    cases hz : m.load w e (x.toNat + off) <;> simp [hz] at he
    obtain ⟨rfl, -⟩ := he
    exact holds_kill h (hset d _)
  | store w base off src =>
    simp only [Op.exec] at he
    cases ha : fr.get base <;> cases hb : fr.get src <;> simp [ha, hb] at he
    rename_i x y
    cases hz : m.store w (x.toNat + off) y <;> simp [hz] at he
    obtain ⟨-, rfl⟩ := he
    exact holds_kill h fun _ _ => rfl
  | call f args results => simp [Op.exec] at he

/-- An operation with its reads propagated executes as the operation. -/
theorem exec_renameOp {env : Env R} {fr : Frame R} (h : Holds env fr) (m : Memory) (o : Op R) :
    (renameOp env o).exec fr m = o.exec fr m := by
  cases o <;> simp [renameOp, Op.exec, get_sub h]

theorem envAt_zero (ops : List (Op R)) : envAt ops 0 = [] := rfl

theorem envAt_succ {ops : List (Op R)} {i : Nat} {o : Op R} (h : ops[i]? = some o) :
    envAt ops (i + 1) = update (envAt ops i) o := by
  simp only [envAt, List.take_add_one, h, Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-! ## The invariant -/

/-- The copies available at a point hold in a frame. -/
def PtInv (p : Prog R) (pt : Point) (fr : Frame R) : Prop := Holds (envOf p pt) fr

/-- The invariant: at the current point and at every suspended call. -/
def Inv (p : Prog R) (s : State R) : Prop :=
  PtInv p s.point s.frame ∧ ∀ a ∈ s.stack, PtInv p a.point a.frame

theorem ptInv_entry (p : Prog R) (f : FuncId) (l : Label) (fr : Frame R) :
    PtInv p ⟨f, l, 0⟩ fr := by
  unfold PtInv envOf
  split <;> exact holds_nil fr

omit [DecidableEq R] in
theorem fetch_block {p : Prog R} {pt : Point} {c : Code R} (h : p.fetch pt = some c) :
    ∃ b, p.block? pt.func pt.label = some b ∧
      ((∃ o, b.ops[pt.index]? = some o ∧ c = .op o) ∨ (pt.index = b.ops.length ∧ c = .term b.term)) := by
  unfold Prog.fetch at h
  cases hb : p.block? pt.func pt.label with
  | none => simp [hb] at h
  | some b =>
    refine ⟨b, rfl, ?_⟩
    simp only [hb, Option.bind_some] at h
    cases hi : b.ops[pt.index]? with
    | some o => simp only [hi, Option.some.injEq] at h; exact .inl ⟨o, rfl, h.symm⟩
    | none =>
      simp only [hi] at h
      split at h
      · cases h; exact .inr ⟨by assumption, rfl⟩
      · cases h

theorem envOf_next {p : Prog R} {pt : Point} {o : Op R} (h : p.fetch pt = some (.op o)) :
    envOf p pt.next = update (envOf p pt) o := by
  obtain ⟨b, hb, hc⟩ := fetch_block h
  rcases hc with ⟨o', ho', he⟩ | ⟨-, he⟩
  · cases he
    simp only [envOf, Point.next_func, Point.next_label, hb, Point.next_index]
    exact envAt_succ ho'
  · cases he

theorem enter_index {p : Prog R} {f : FuncId} {vals : List Word} {pt : Point} {fr : Frame R}
    (h : p.enter f vals = some (pt, fr)) : pt = ⟨pt.func, pt.label, 0⟩ := by
  unfold Prog.enter at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨fn, -, b, -, fr', -, he, -⟩ := h
  rw [← he]

/-- **The invariant is preserved by every step.** -/
theorem Inv.step {p : Prog R} {s t : State R} (hi : Inv p s) (h : Step p s t) : Inv p t := by
  have tr := Transition.of_step h (by nofun)
  cases tr with
  | op hf he =>
    exact ⟨by rw [PtInv, envOf_next hf]; exact holds_update hi.1 he, hi.2⟩
  | call hf ha he =>
    refine ⟨?_, ?_⟩
    · rw [enter_index he]
      exact ptInv_entry p _ _ _
    · intro a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hi.1
      · exact hi.2 a ha'
  | jump hf hv hb hw => exact ⟨ptInv_entry p _ _ _, hi.2⟩
  | cond hf hc hv hb hw => exact ⟨ptInv_entry p _ _ _, hi.2⟩
  | ret hf hv hs ha hw =>
    rename_i locs vals a rest g args results fr
    have h2 := hi.2
    rw [hs] at h2
    refine ⟨?_, fun a' ha' => h2 a' (List.mem_cons_of_mem _ ha')⟩
    rw [PtInv, envOf_next ha]
    exact holds_kill (h2 a List.mem_cons_self) fun r hr => writeAll_get_of_not_mem hw hr

theorem Inv.start {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory} {s : State R}
    (h : p.start f args mem = some s) : Inv p s := by
  simp only [Prog.start, Option.map_eq_some_iff] at h
  obtain ⟨⟨pt, fr⟩, he, rfl⟩ := h
  refine ⟨?_, fun a ha => by simp at ha⟩
  show PtInv p pt fr
  rw [enter_index he]
  exact ptInv_entry p _ _ _

/-! ## The simulation -/

theorem transfer_copyProp {p : Prog R} {s : State R} (hi : Inv p s) (t : Label) (as : List R) :
    transfer (copyProp p) s t (as.map (sub (envOf p s.point))) = transfer p s t as := by
  simp only [transfer, readAll_sub hi.1, block?_copyProp]
  cases s.frame.readAll as with
  | none => rfl
  | some vals => cases p.block? s.point.func t <;> rfl

/-- **One step of the propagated program is the step of the original**, wherever the
available copies hold. -/
theorem step_copyProp {p : Prog R} {s : State R} (hi : Inv p s) :
    step (copyProp p) s = step p s := by
  have h1 : Holds (envOf p s.point) s.frame := hi.1
  unfold step
  rw [fetch_copyProp]
  cases hc : p.fetch s.point with
  | none => rfl
  | some c =>
    cases c with
    | op o =>
      cases o with
      | call f args results =>
        simp only [Option.map_some, renameCode, renameOp, readAll_sub h1, enter_copyProp]
      | _ => simp [renameCode, renameOp, Op.exec, get_sub h1]
    | term t =>
      cases t with
      | jump tg as =>
        simp only [Option.map_some, renameCode, renameTerm]
        exact transfer_copyProp hi _ _
      | cond c t₁ a₁ t₂ a₂ =>
        simp only [Option.map_some, renameCode, renameTerm, get_sub h1]
        cases s.frame.get c with
        | none => rfl
        | some x =>
          simp only
          rw [← apply_ite (List.map (sub (envOf p s.point))), transfer_copyProp hi]
      | ret vs =>
        simp only [Option.map_some, renameCode, renameTerm, readAll_sub h1]
        cases s.frame.readAll vs with
        | none => rfl
        | some vals =>
          simp only
          cases s.stack with
          | nil => rfl
          | cons a rest =>
            simp only [fetch_copyProp]
            cases p.fetch a.point with
            | none => rfl
            | some c =>
              cases c with
              | op o => cases o <;> rfl
              | term t => rfl
      | trap => rfl

theorem Step.copyProp {p : Prog R} {s t : State R} (hi : Inv p s) (h : Step p s t) :
    Step (copyProp p) s t := by
  unfold Step at h ⊢
  rw [step_copyProp hi]
  exact h

theorem Steps.copyProp {p : Prog R} {s t : State R} (hi : Inv p s) (h : Steps p s t) :
    Steps (copyProp p) s t ∧ Inv p t := by
  induction h with
  | refl => exact ⟨.refl, hi⟩
  | tail _ hst ih => exact ⟨ih.1.tail (ih.2 |> fun h => Step.copyProp h hst), ih.2.step hst⟩

theorem behaves_copyProp {p : Prog R} {s : State R} (hi : Inv p s) {b : Behavior}
    (hb : Behaves p s b) : Behaves (copyProp p) s b := by
  cases b with
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := hb
    obtain ⟨ht', hit⟩ := Steps.copyProp hi ht
    exact ⟨t, ht', by rw [step_copyProp hit, hf]⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := hb
    obtain ⟨ht', hit⟩ := Steps.copyProp hi ht
    exact ⟨t, ht', by rw [step_copyProp hit, hf]⟩
  | stuck =>
    obtain ⟨t, ht, hf⟩ := hb
    obtain ⟨ht', hit⟩ := Steps.copyProp hi ht
    exact ⟨t, ht', by rw [step_copyProp hit, hf]⟩
  | diverges =>
    have sim : Silmaril.LockstepSim (Step p) (Step (copyProp p)) (fun u v => v = u ∧ Inv p u) :=
      ⟨by
        rintro u u' v hst ⟨rfl, hiu⟩
        exact ⟨u', .single (Step.copyProp hiu hst), rfl, hiu.step hst⟩⟩
    exact sim.diverges hb ⟨rfl, hi⟩

/-- **The local lemma of copy propagation**: from every state where the available copies
hold (every start state, `Inv.start`), the propagated program has exactly the behaviours of
the original. -/
theorem behaves_copyProp_iff {p : Prog R} {s : State R} (hi : Inv p s) {b : Behavior} :
    Behaves (copyProp p) s b ↔ Behaves p s b := by
  refine ⟨fun h => ?_, behaves_copyProp hi⟩
  obtain ⟨b₀, hb₀⟩ := Behaves.exists p s
  rw [Behaves.unique h (behaves_copyProp hi hb₀)]
  exact hb₀

end Silmaril.Machine.RTL.SSA.CopyProp
