module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.AvailableExpressions
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Execution
public import Silmaril.Courses.Cambridge.OptimisingCompilers.PlusSim

/-! # §5 Uses of AVAIL: common-subexpression elimination and copy propagation
(notes pp. 13–14; slides pp. 79–83)

CSE (notes p. 13), for an expression `e = a ⊕ b` and a new temporary `t`:

* "for each node `n` containing `x := a ⊕ b` with `a ⊕ b` available at `n`":
  replace `n : x := a ⊕ b` with `n : x := t`;
* "on each path scanning backwards from `n`, for the first occurrence of `a ⊕ b`
  (say `n′ : y := a ⊕ b`) … replace `n′` with two instructions
  `n′ : t := a ⊕ b; n″ : y := t`".

Here every occurrence `y := e` is split (a superset of the first occurrences on
each path, which is simpler and equally correct). The new nodes `n″` are
`Sum.inr n′`; original nodes are `Sum.inl n`.

*Copy propagation* (notes p. 14) replaces a use of `x` by `y` where the copy
`x := y` is known to hold. Which copies hold is the must gen/kill problem
`copyProblem`: `MOV x, y` generates the fact `(x, y)`, and any definition of
`x` or `y` kills it.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

open Silmaril.Semantics.Dataflow

/-- Replace `x` by `y` in an operand. -/
def Operand.subst {V : Type*} [DecidableEq V] (x y : V) : Operand V → Operand V
  | .var z => if z = x then .var y else .var z
  | .imm k => .imm k

namespace Instr

variable {V ι κ : Type*}

/-- Relabel the successors of an instruction. -/
def mapLabels (f : ι → κ) : Instr V ι → Instr V κ
  | .entry n => .entry (f n)
  | .nop n => .nop (f n)
  | .alu op d a b n => .alu op d a b (f n)
  | .alu2 op d a n => .alu2 op d a (f n)
  | .ldi d a n => .ldi d a (f n)
  | .sti a b n => .sti a b (f n)
  | .cmp c a b t e => .cmp c a b (f t) (f e)
  | .print a n => .print a (f n)
  | .exit rs => .exit rs

/-- The instruction `dst := rhs` with successor `n`. -/
def ofAssignment (dst : V) (n : ι) : Rhs V → Instr V ι
  | .bin op a b => .alu op dst a b n
  | .un op a => .alu2 op dst a n

/-- The successor of an ALU instruction. -/
def aluNext? : Instr V ι → Option ι
  | .alu _ _ _ _ n | .alu2 _ _ _ n => some n
  | _ => none

/-- Replace the uses of `x` by `y` in an instruction (definitions unchanged). -/
def substUses [DecidableEq V] (x y : V) : Instr V ι → Instr V ι
  | .alu op d a b n => .alu op d (a.subst x y) (b.subst x y) n
  | .alu2 op d a n => .alu2 op d (a.subst x y) n
  | .ldi d a n => .ldi d (a.subst x y) n
  | .sti a b n => .sti (a.subst x y) (b.subst x y) n
  | .cmp c a b t f => .cmp c (a.subst x y) (b.subst x y) t f
  | .print a n => .print (a.subst x y) n
  | .exit rs => .exit (rs.map fun z => if z = x then y else z)
  | i => i

end Instr

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- CSE of `e` into the temporary `t` at the nodes `targets` (notes p. 13). -/
def cse (e : Rhs V) (t : V) (targets : ι → Bool) : Flowgraph V (ι ⊕ ι) where
  entry := .inl G.entry
  code
    | .inl n =>
      match (G.code n).assignment?, (G.code n).aluNext? with
      | some (x, e'), some m =>
        if e' = e then
          if targets n then .alu2 .mov x (.var t) (.inl m)
          else Instr.ofAssignment t (.inr n) e
        else (G.code n).mapLabels .inl
      | _, _ => (G.code n).mapLabels .inl
    | .inr n =>
      match (G.code n).assignment?, (G.code n).aluNext? with
      | some (y, _), some m => .alu2 .mov y (.var t) (.inl m)
      | _, _ => .exit []

/-- `t` is fresh for `G`: no instruction mentions it. -/
def Fresh (t : V) : Prop := ∀ n, t ∉ (G.code n).vars

/-! ## Correctness of CSE

The proof is a one-or-two-step simulation (`PlusSim`). Original node `n` is
related to `Sum.inl n` with the same memory, the same values on every variable
other than `t`, and `t` holding the value of `e` whenever `e` is available at
`n`. A split node `n′ : y := e` is matched by the two steps `t := e; y := t`. -/

omit [DecidableEq V] in
theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Operand.eval_congr {env₁ env₂ : Env V}
    {a : Operand V} (h : ∀ z ∈ a.vars, env₁ z = env₂ z) : a.eval env₁ = a.eval env₂ := by
  cases a with
  | var x => exact h x (by simp [Operand.vars])
  | imm k => rfl

theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Rhs.eval_congr {env₁ env₂ : Env V}
    {e : Rhs V} (h : ∀ z ∈ e.vars, env₁ z = env₂ z) : e.eval env₁ = e.eval env₂ := by
  cases e <;> simp only [Rhs.eval] <;> congr 1 <;> apply Operand.eval_congr <;>
    intro z hz <;> apply h <;> simp [Rhs.vars, hz]

theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Instr.exec_ofAssignment {κ : Type*}
    (dst : V) (k : κ) (e : Rhs V) (env : Env V) (mem : Mem) :
    (Instr.ofAssignment dst k e).exec env mem =
      some (k, Function.update env dst (e.eval env), mem, none) := by
  cases e <;> rfl

/-- An assignment `x := e` steps to its successor, updating `x` to the value of `e`. -/
theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Instr.exec_of_assignment {κ : Type*}
    {i : Instr V κ} {x : V} {e : Rhs V} (ha : i.assignment? = some (x, e)) (env : Env V)
    (mem : Mem) :
    ∃ m, i.aluNext? = some m ∧
      i.exec env mem = some (m, Function.update env x (e.eval env), mem, none) ∧
      x ∈ i.defs ∧ e.vars ⊆ i.refs := by
  cases i <;> simp only [Instr.assignment?, reduceCtorEq, Option.some.injEq,
    Prod.mk.injEq] at ha
  all_goals
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨_, rfl, rfl, by simp [Instr.defs], fun z hz => by simpa [Instr.refs, Rhs.vars] using hz⟩

/-- Relabelling an instruction that does not mention `t` commutes with execution
in environments agreeing off `t`; `t` is left unchanged. -/
theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Instr.exec_mapLabels_of_agree
    {κ κ' : Type*} (f : κ → κ') {i : Instr V κ} {t : V} (ht : t ∉ i.vars) {env₁ env₂ : Env V}
    (h : ∀ z ≠ t, env₂ z = env₁ z) (mem : Mem) {n : κ} {env₁' : Env V} {mem' : Mem}
    {o : Option ℤ} (hi : i.exec env₁ mem = some (n, env₁', mem', o)) :
    ∃ env₂', (i.mapLabels f).exec env₂ mem = some (f n, env₂', mem', o) ∧ env₂' t = env₂ t ∧
      ∀ z ≠ t, env₂' z = env₁' z := by
  have hop : ∀ a : Operand V, (∀ z ∈ a.vars, z ∈ i.vars) → a.eval env₂ = a.eval env₁ :=
    fun a ha => Operand.eval_congr fun z hz => h z fun hzt => ht (hzt ▸ ha z hz)
  have hupd : ∀ (d : V) (v : ℤ), d ∈ i.vars → Function.update env₂ d v t = env₂ t ∧
      ∀ z ≠ t, Function.update env₂ d v z = Function.update env₁ d v z := by
    intro d v hd
    refine ⟨Function.update_of_ne (fun (htd : t = d) => ht (htd ▸ hd)) _ _, fun z hz => ?_⟩
    rw [Function.update_apply, Function.update_apply]
    split_ifs
    · rfl
    · exact h z hz
  cases i with
  | entry m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    exact ⟨env₂, rfl, rfl, h⟩
  | nop m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    exact ⟨env₂, rfl, rfl, h⟩
  | alu op d a b m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨_, rfl, ?_⟩
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz]),
      hop b (fun z hz => by simp [Instr.vars, Instr.refs, hz])]
    exact hupd d _ (by simp [Instr.vars, Instr.defs])
  | alu2 op d a m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨_, rfl, ?_⟩
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz])]
    exact hupd d _ (by simp [Instr.vars, Instr.defs])
  | ldi d a m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨_, rfl, ?_⟩
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz])]
    exact hupd d _ (by simp [Instr.vars, Instr.defs])
  | sti a b m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨env₂, ?_, rfl, h⟩
    simp only [Instr.mapLabels, Instr.exec]
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz]),
      hop b (fun z hz => by simp [Instr.vars, Instr.refs, hz])]
  | cmp c a b tt ff =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨env₂, ?_, rfl, h⟩
    simp only [Instr.mapLabels, Instr.exec]
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz]),
      hop b (fun z hz => by simp [Instr.vars, Instr.refs, hz]), apply_ite f]
  | print a m =>
    simp only [Instr.exec, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    refine ⟨env₂, ?_, rfl, h⟩
    simp only [Instr.mapLabels, Instr.exec]
    rw [hop a (fun z hz => by simp [Instr.vars, Instr.refs, hz])]
  | exit rs => simp [Instr.exec] at hi

section CSE

variable {e : Rhs V} {t : V} {targets : ι → Bool}

theorem cse_code_inl_of_ne {n : ι} (hn : ∀ x, (G.code n).assignment? ≠ some (x, e)) :
    (G.cse e t targets).code (.inl n) = (G.code n).mapLabels .inl := by
  rcases ha : (G.code n).assignment? with _ | ⟨x, e'⟩
  · simp [cse, ha]
  · obtain ⟨m, hm, -⟩ := Instr.exec_of_assignment ha (fun _ => 0) (fun _ => 0)
    have hne : e' ≠ e := fun h => hn x (h ▸ ha)
    simp [cse, ha, hm, hne]

theorem cse_code_inl_target {n m : ι} {x : V} (ha : (G.code n).assignment? = some (x, e))
    (hm : (G.code n).aluNext? = some m) (hn : targets n = true) :
    (G.cse e t targets).code (.inl n) = .alu2 .mov x (.var t) (.inl m) := by
  simp [cse, ha, hm, hn]

theorem cse_code_inl_split {n m : ι} {x : V} (ha : (G.code n).assignment? = some (x, e))
    (hm : (G.code n).aluNext? = some m) (hn : targets n = false) :
    (G.cse e t targets).code (.inl n) = Instr.ofAssignment t (.inr n) e := by
  simp [cse, ha, hm, hn]

theorem cse_code_inr {n m : ι} {x : V} (ha : (G.code n).assignment? = some (x, e))
    (hm : (G.code n).aluNext? = some m) :
    (G.cse e t targets).code (.inr n) = .alu2 .mov x (.var t) (.inl m) := by
  simp [cse, ha, hm]

/-- With no predecessors, nothing is available at the entry. -/
theorem avail_entry (hentry : G.pred G.entry = ∅) : G.avail G.entry = ∅ := by
  have h : ¬ (G.availProblem.nbrs G.entry).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]; exact hentry
  unfold avail GenKill.mustIn
  rw [ite_eq_right h]

/-- An expression available after a step was available before and not killed by
it, or is generated by it. -/
theorem avail_step {s s' : Config V ι} {o : Option ℤ} (hs : G.step s = some (o, s'))
    {e : Rhs V} (he : e ∈ G.avail s'.pc) :
    (e ∈ G.avail s.pc ∧ e ∉ (G.code s.pc).kill) ∨ e ∈ (G.code s.pc).gen := by
  have hp : s.pc ∈ G.availProblem.nbrs s'.pc := G.step_pc_mem_succs hs
  unfold avail GenKill.mustIn at he
  rw [ite_eq_left ⟨_, hp⟩] at he
  have hout : e ∈ G.availProblem.mustOut s.pc := Set.mem_iInter₂.1 he s.pc hp
  rw [GenKill.mustOut_eq] at hout
  exact hout

variable (e t) in
/-- The CSE simulation relation. -/
def cseRel (s : Config V ι) (c : Config V (ι ⊕ ι)) : Prop :=
  c.pc = .inl s.pc ∧ c.mem = s.mem ∧ (∀ z ≠ t, c.env z = s.env z) ∧
    (e ∈ G.avail s.pc → c.env t = e.eval s.env)

theorem cse_step (ht : G.Fresh t)
    (htargets : ∀ n, targets n = true → e ∈ G.avail n ∧ ∃ x, (G.code n).assignment? = some (x, e))
    {s s' : Config V ι} {c : Config V (ι ⊕ ι)} {o : Option ℤ} (hR : G.cseRel e t s c)
    (hs : G.step s = some (o, s')) :
    (∃ c', (G.cse e t targets).step c = some (o, c') ∧ G.cseRel e t s' c') ∨
      ∃ u c', (G.cse e t targets).step c = some (none, u) ∧
        (G.cse e t targets).step u = some (o, c') ∧ G.cseRel e t s' c' := by
  obtain ⟨hpc, hmem, henv, hav⟩ := hR
  by_cases hA : ∃ x, (G.code s.pc).assignment? = some (x, e)
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨m, hm, hexec, hxdef, hevars⟩ := Instr.exec_of_assignment hx s.env s.mem
    have hs2 : G.step s = some (none, ⟨m, Function.update s.env x (e.eval s.env), s.mem⟩) :=
      G.step_eq_of_exec rfl hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs2))
    have htx : t ≠ x := fun h => ht s.pc (Finset.mem_union_left _ (h ▸ hxdef))
    have hte : t ∉ e.vars := fun h => ht s.pc (Finset.mem_union_right _ (hevars h))
    have hxe : e ∈ G.avail m → x ∉ e.vars := by
      intro he'
      rcases G.avail_step hs he' with ⟨-, hk⟩ | hg
      · exact fun hv => hk ⟨x, hxdef, hv⟩
      · obtain ⟨d, hd, hde⟩ := hg
        rw [hx] at hd
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hd)
        exact hde
    have hes : e.eval c.env = e.eval s.env :=
      Rhs.eval_congr fun z hz => henv z fun hzt => hte (hzt ▸ hz)
    cases htg : targets s.pc
    · right
      refine ⟨⟨.inr s.pc, Function.update c.env t (e.eval c.env), c.mem⟩,
        ⟨.inl m, Function.update (Function.update c.env t (e.eval c.env)) x
          (Function.update c.env t (e.eval c.env) t), c.mem⟩,
        (G.cse e t targets).step_eq_of_exec (by rw [hpc, G.cse_code_inl_split hx hm htg])
          (Instr.exec_ofAssignment _ _ _ _ _),
        (G.cse e t targets).step_eq_of_exec (G.cse_code_inr hx hm) rfl, rfl, hmem, ?_, ?_⟩
      · intro z hz
        by_cases hzx : z = x <;> simp [hzx, hz, hes, henv z hz]
      · intro he'
        show _ = e.eval (Function.update s.env x (e.eval s.env))
        rw [Rhs.eval_update_of_not_mem (hxe he')]
        simp [htx, hes]
    · left
      have hct : c.env t = e.eval s.env := hav (htargets s.pc htg).1
      refine ⟨⟨.inl m, Function.update c.env x (c.env t), c.mem⟩,
        (G.cse e t targets).step_eq_of_exec (by rw [hpc, G.cse_code_inl_target hx hm htg])
          (by rfl), rfl, hmem, ?_, ?_⟩
      · intro z hz
        by_cases hzx : z = x <;> simp [hzx, hct, henv z hz]
      · intro he'
        show _ = e.eval (Function.update s.env x (e.eval s.env))
        rw [Rhs.eval_update_of_not_mem (hxe he')]
        simp [htx, hct]
  · have hn : ∀ x, (G.code s.pc).assignment? ≠ some (x, e) := fun x hx => hA ⟨x, hx⟩
    unfold step at hs
    obtain ⟨⟨n', env', mem', o'⟩, hex, heq⟩ := Option.map_eq_some_iff.1 hs
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨env₂, hex', ht', hagree⟩ :=
      Instr.exec_mapLabels_of_agree Sum.inl (ht s.pc) henv s.mem hex
    have hs' : G.step s = some (o', ⟨n', env', mem'⟩) := G.step_eq_of_exec rfl hex
    left
    refine ⟨⟨.inl n', env₂, mem'⟩,
      (G.cse e t targets).step_eq_of_exec (by rw [hpc, G.cse_code_inl_of_ne hn])
        (by rw [hmem]; exact hex'), rfl, rfl, hagree, ?_⟩
    intro he'
    rcases G.avail_step hs' he' with ⟨hin, hk⟩ | hg
    · show env₂ t = e.eval env'
      rw [ht', hav hin]
      exact (G.eval_step_of_disjoint hs' fun x hx hv => hk ⟨x, hx, hv⟩).symm
    · obtain ⟨d, hd, -⟩ := hg
      exact absurd hd (hn d)

theorem cse_halted {s : Config V ι} {c : Config V (ι ⊕ ι)} (hR : G.cseRel e t s c)
    (h : G.Halted s) : ∃ rs, G.code s.pc = .exit rs ∧
      (G.cse e t targets).code c.pc = .exit rs := by
  obtain ⟨rs, hrs⟩ := h
  have hn : ∀ x, (G.code s.pc).assignment? ≠ some (x, e) := by
    simp [hrs, Instr.assignment?]
  refine ⟨rs, hrs, ?_⟩
  rw [hR.1, G.cse_code_inl_of_ne hn, hrs, Instr.mapLabels]

theorem cse_none {s : Config V ι} {c : Config V (ι ⊕ ι)} (hR : G.cseRel e t s c)
    (hs : G.step s = none) : (G.cse e t targets).step c = none := by
  obtain ⟨rs, -, h⟩ := G.cse_halted (targets := targets) hR ((G.step_eq_none_iff s).1 hs)
  exact ((G.cse e t targets).step_eq_none_iff c).2 ⟨rs, h⟩

theorem cse_res (ht : G.Fresh t) {s : Config V ι} {c : Config V (ι ⊕ ι)}
    (hR : G.cseRel e t s c) (h : G.Halted s) :
    G.resultValues s = (G.cse e t targets).resultValues c ∧ s.mem = c.mem := by
  obtain ⟨rs, hrs, hrs'⟩ := G.cse_halted (targets := targets) hR h
  refine ⟨?_, hR.2.1.symm⟩
  unfold resultValues
  rw [hrs, hrs']
  show rs.map s.env = rs.map c.env
  refine List.map_congr_left fun z hz => (hR.2.2.1 z fun hzt => ?_).symm
  subst hzt
  exact ht s.pc (by rw [hrs]; simp [Instr.vars, Instr.refs, hz])

end CSE

/-- CSE is correct when `t` is fresh, every target computes `e` with `e`
available, and the entry has no predecessors. -/
theorem cse_correct {e : Rhs V} {t : V} {targets : ι → Bool} (ht : G.Fresh t)
    (htargets : ∀ n, targets n = true → e ∈ G.avail n ∧ ∃ x, (G.code n).assignment? = some (x, e))
    (hentry : G.pred G.entry = ∅) (env : Env V) (mem : Mem) :
    G.traces ⟨G.entry, env, mem⟩ = (G.cse e t targets).traces ⟨.inl G.entry, env, mem⟩ ∧
      G.outcomes ⟨G.entry, env, mem⟩ = (G.cse e t targets).outcomes ⟨.inl G.entry, env, mem⟩ :=
  G.traces_outcomes_eq_of_plusSim (G.cse e t targets) (G.cseRel e t)
    (fun hR hs => G.cse_step ht htargets hR hs) (fun hR hs => G.cse_none hR hs)
    (fun hR h => G.cse_res ht hR h)
    ⟨rfl, rfl, fun _ _ => rfl, fun he => by simp [G.avail_entry hentry] at he⟩

/-! ## Copy propagation (notes p. 14) -/

/-- The copy `x := y` at an instruction. -/
def copyGen (n : ι) : Set (V × V) :=
  {c | ∃ m, G.code n = .alu2 .mov c.1 (.var c.2) m ∧ c.1 ≠ c.2}

/-- Definitions of `x` or `y` kill the copy `x := y`. -/
def copyKill (n : ι) : Set (V × V) := {c | c.1 ∈ (G.code n).defs ∨ c.2 ∈ (G.code n).defs}

/-- Available copies: a forward must problem. -/
def copyProblem : GenKill ι (V × V) where
  nbrs := G.pred
  gen := G.copyGen
  kill := G.copyKill

/-- Copies known to hold on entry to `n`. -/
noncomputable def copies (n : ι) : Set (V × V) := G.copyProblem.mustIn n

/-- Copy propagation of `x := y` at the nodes `sites`. -/
def copyProp (x y : V) (sites : ι → Bool) : Flowgraph V ι where
  entry := G.entry
  code n := if sites n then (G.code n).substUses x y else G.code n

/-- A step leaves every variable it does not define unchanged. -/
theorem env_step_of_not_mem_defs {b c : Config V ι} {o : Option ℤ}
    (hs : G.step b = some (o, c)) {z : V} (hz : z ∉ (G.code b.pc).defs) : c.env z = b.env z :=
  G.eval_step_of_disjoint hs (e := .un .mov (.var z)) fun x hx hv => by
    simp only [Rhs.vars, Operand.vars, Finset.mem_singleton] at hv
    subst hv
    exact hz hx

/-- Semantic soundness of available copies: on every run from the entry, a copy
`x := y` known to hold at the current node does hold. -/
theorem copies_sound (hentry : G.pred G.entry = ∅) {env : Env V} {mem : Mem} {w : List ℤ}
    {s : Config V ι} (hrun : G.Steps ⟨G.entry, env, mem⟩ w s) :
    ∀ c ∈ G.copies s.pc, s.env c.1 = s.env c.2 := by
  refine G.steps_reach_induction (fun s => ∀ c ∈ G.copies s.pc, s.env c.1 = s.env c.2) ?_ ?_
    hrun
  · intro c hc
    have h : ¬ (G.copyProblem.nbrs G.entry).Nonempty := by
      rw [Set.not_nonempty_iff_eq_empty]; exact hentry
    unfold copies GenKill.mustIn at hc
    rw [ite_eq_right h] at hc
    simp at hc
  · intro w b o d hb ih hs c hc
    have hp : b.pc ∈ G.copyProblem.nbrs d.pc := G.step_pc_mem_succs hs
    unfold copies GenKill.mustIn at hc
    rw [ite_eq_left ⟨_, hp⟩] at hc
    have hout : c ∈ G.copyProblem.mustOut b.pc := Set.mem_iInter₂.1 hc b.pc hp
    rw [GenKill.mustOut_eq] at hout
    rcases hout with ⟨hin, hkill⟩ | hgen
    · have h₁ : c.1 ∉ (G.code b.pc).defs := fun h => hkill (Or.inl h)
      have h₂ : c.2 ∉ (G.code b.pc).defs := fun h => hkill (Or.inr h)
      rw [G.env_step_of_not_mem_defs hs h₁, G.env_step_of_not_mem_defs hs h₂]
      exact ih c hin
    · obtain ⟨m, hm, hne⟩ := hgen
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ((Flowgraph.step_alu2 hm).symm.trans hs))
      simp [Function.update_of_ne (Ne.symm hne), UnOp.eval, Operand.eval]

theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Operand.eval_subst {x y : V}
    {env : Env V} (h : env x = env y) (o : Operand V) : (o.subst x y).eval env = o.eval env := by
  cases o with
  | var z => by_cases hz : z = x <;> simp [Operand.subst, Operand.eval, hz, h]
  | imm k => rfl

theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Instr.exec_substUses {x y : V}
    {env : Env V} {mem : Mem} (h : env x = env y) (i : Instr V ι) :
    (i.substUses x y).exec env mem = i.exec env mem := by
  cases i <;> simp [Instr.substUses, Instr.exec, Operand.eval_subst h]

theorem copyProp_code {x y : V} {sites : ι → Bool} (n : ι) :
    (G.copyProp x y sites).code n = if sites n then (G.code n).substUses x y else G.code n :=
  rfl

theorem copyProp_step {x y : V} {sites : ι → Bool} {s : Config V ι}
    (h : sites s.pc = true → s.env x = s.env y) : (G.copyProp x y sites).step s = G.step s := by
  unfold step
  rw [copyProp_code]
  by_cases hs : sites s.pc = true
  · rw [ite_eq_left hs, Instr.exec_substUses (h hs)]
  · rw [ite_eq_right hs]

theorem copyProp_halted {x y : V} {sites : ι → Bool} {s : Config V ι} :
    (G.copyProp x y sites).Halted s ↔ G.Halted s := by
  unfold Halted
  rw [copyProp_code]
  by_cases hs : sites s.pc = true
  · rw [ite_eq_left hs]
    cases G.code s.pc <;> simp [Instr.substUses]
  · rw [ite_eq_right hs]

theorem copyProp_resultValues {x y : V} {sites : ι → Bool} {s : Config V ι}
    (h : sites s.pc = true → s.env x = s.env y) :
    (G.copyProp x y sites).resultValues s = G.resultValues s := by
  unfold resultValues
  rw [copyProp_code]
  by_cases hs : sites s.pc = true
  · rw [ite_eq_left hs]
    cases G.code s.pc with
    | exit rs =>
      simp only [Instr.substUses, List.map_map]
      refine List.map_congr_left fun z _ => ?_
      by_cases hz : z = x
      · simp [hz, h hs]
      · simp [hz]
    | _ => rfl
  · rw [ite_eq_right hs]

theorem copyProp_steps_iff {x y : V} {sites : ι → Bool} {start : Config V ι}
    (hR : ∀ s, (∃ w₀, G.Steps start w₀ s) → sites s.pc = true → s.env x = s.env y)
    {s : Config V ι} (hs : ∃ w₀, G.Steps start w₀ s) {w : List ℤ} {t : Config V ι} :
    G.Steps s w t ↔ (G.copyProp x y sites).Steps s w t := by
  constructor
  · intro h
    revert hs
    induction h with
    | refl => intro _; exact .refl _
    | head h₁ _ ih =>
      intro hs
      obtain ⟨w₀, h₀⟩ := hs
      exact .head ((G.copyProp_step (hR _ ⟨_, h₀⟩)).trans h₁)
        (ih ⟨_, G.steps_append_step h₀ h₁⟩)
  · intro h
    revert hs
    induction h with
    | refl => intro _; exact .refl _
    | head h₁ _ ih =>
      intro hs
      obtain ⟨w₀, h₀⟩ := hs
      have h₁' := (G.copyProp_step (hR _ ⟨_, h₀⟩)).symm.trans h₁
      exact .head h₁' (ih ⟨_, G.steps_append_step h₀ h₁'⟩)

/-- Copy propagation is correct at nodes where the copy holds. -/
theorem copyProp_correct {x y : V} {sites : ι → Bool}
    (hsites : ∀ n, sites n = true → (x, y) ∈ G.copies n)
    (hentry : G.pred G.entry = ∅) (env : Env V) (mem : Mem) :
    G.ObsEquiv (G.copyProp x y sites) ⟨G.entry, env, mem⟩ ⟨G.entry, env, mem⟩ := by
  have hR : ∀ s, (∃ w₀, G.Steps ⟨G.entry, env, mem⟩ w₀ s) → sites s.pc = true →
      s.env x = s.env y :=
    fun s ⟨_, h₀⟩ hs => G.copies_sound hentry h₀ (x, y) (hsites _ hs)
  have hiff : ∀ {w t}, G.Steps ⟨G.entry, env, mem⟩ w t ↔
      (G.copyProp x y sites).Steps ⟨G.entry, env, mem⟩ w t :=
    G.copyProp_steps_iff hR ⟨[], .refl _⟩
  unfold ObsEquiv
  refine ⟨?_, ?_⟩
  · ext w
    simp only [traces, Set.mem_ofPred_eq]
    exact ⟨fun ⟨t, h⟩ => ⟨t, hiff.1 h⟩, fun ⟨t, h⟩ => ⟨t, hiff.2 h⟩⟩
  · ext o
    simp only [outcomes, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, h, ht, hr, hm⟩
      exact ⟨t, hiff.1 h, G.copyProp_halted.2 ht,
        hr.trans (G.copyProp_resultValues (hR t ⟨_, h⟩)).symm, hm⟩
    · rintro ⟨t, h, ht, hr, hm⟩
      exact ⟨t, hiff.2 h, G.copyProp_halted.1 ht,
        hr.trans (G.copyProp_resultValues (hR t ⟨_, hiff.2 h⟩)), hm⟩

end Flowgraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
