module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Liveness
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Runs
public import Mathlib.Data.Fin.VecNotation

/-! # §4.1–4.3 Register allocation by colouring (notes pp. 10–13; slides pp. 73–78)

"If there is no 3-address instruction where two variables are both live then
the variables can share the same memory location (or, more usefully, the same
register). The justification is that when a variable is not live its value can
be corrupted arbitrarily without affecting execution" (notes p. 10).

* `clash` is the clash graph. Besides simultaneous liveness it has an edge from
  every variable defined at a node to every other variable live on exit from
  it. Without this, a dead store would overwrite a live register:
  `liveInClash_unsound` refutes the variant built from live-in sets alone (the
  notes and slides apply DCE before allocation, which removes such stores).
* `rename σ` is the allocation: every variable `x` is held in register `σ x`.
* `rename_correct`: if `σ` colours the clash graph, the allocated program
  behaves like the original.
* `chaitin` is the simplify/select heuristic of p. 11: repeatedly remove a
  node with fewer than `k` clashes, then colour in reverse order. When it does
  not need to spill, its result colours the graph (`chaitin_colours`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

namespace Operand

variable {V R : Type*}

/-- Rename the variables of an operand. -/
def rename (σ : V → R) : Operand V → Operand R
  | .var x => .var (σ x)
  | .imm k => .imm k

end Operand

namespace Instr

variable {V R ι : Type*}

/-- Rename the variables of an instruction. -/
def rename (σ : V → R) : Instr V ι → Instr R ι
  | .entry n => .entry n
  | .nop n => .nop n
  | .alu op d a b n => .alu op (σ d) (a.rename σ) (b.rename σ) n
  | .alu2 op d a n => .alu2 op (σ d) (a.rename σ) n
  | .ldi d a n => .ldi (σ d) (a.rename σ) n
  | .sti a b n => .sti (a.rename σ) (b.rename σ) n
  | .cmp c a b t f => .cmp c (a.rename σ) (b.rename σ) t f
  | .print a n => .print (a.rename σ) n
  | .exit rs => .exit (rs.map σ)

end Instr

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- The clash graph: `x` and `y` clash if they are both live at some node, or
`x` is defined at a node where `y` is live on exit. -/
def clash (x y : V) : Prop :=
  x ≠ y ∧ ((∃ n, x ∈ G.live n ∧ y ∈ G.live n) ∨
    (∃ n, x ∈ (G.code n).defs ∧ y ∈ G.outLive G.live n) ∨
    (∃ n, y ∈ (G.code n).defs ∧ x ∈ G.outLive G.live n))

theorem clash_symm {x y : V} (h : G.clash x y) : G.clash y x := by
  obtain ⟨hne, ⟨n, hx, hy⟩ | h₂ | h₃⟩ := h
  · exact ⟨hne.symm, Or.inl ⟨n, hy, hx⟩⟩
  · exact ⟨hne.symm, Or.inr (Or.inr h₂)⟩
  · exact ⟨hne.symm, Or.inr (Or.inl h₃)⟩

/-- The clash graph of the notes' literal reading: simultaneous liveness only. -/
def liveInClash (x y : V) : Prop := x ≠ y ∧ ∃ n, x ∈ G.live n ∧ y ∈ G.live n

/-- `σ` colours the clash graph: clashing variables get different registers. -/
def IsColouring {R : Type*} (σ : V → R) : Prop := ∀ x y, G.clash x y → σ x ≠ σ y

/-- The allocated program. -/
def rename {R : Type*} (σ : V → R) : Flowgraph R ι where
  entry := G.entry
  code n := (G.code n).rename σ

/-- The least liveness solution satisfies the two-stage equations. -/
theorem live_eq (n : ι) :
    G.live n = G.outLive G.live n \ ↑(G.code n).defs ∪ ↑(G.code n).refs :=
  ((Silmaril.Semantics.Dataflow.Equations.isSolution_iff _ _).1 G.liveEquations.least_isSolution n).trans
    (G.liveEquations_step_apply _ n)

theorem refs_subset_live {n : ι} {y : V} (hy : y ∈ (G.code n).refs) : y ∈ G.live n := by
  rw [G.live_eq n]
  exact Or.inr hy

theorem mem_live_of_succ {n m : ι} {y : V} (hm : m ∈ G.succ n) (hy : y ∈ G.live m)
    (hd : y ∉ (G.code n).defs) : y ∈ G.live n := by
  rw [G.live_eq n]
  exact Or.inl ⟨Set.mem_iUnion₂.2 ⟨m, hm, hy⟩, hd⟩

/-- Register allocation is correct: if `σ` colours the clash graph and the
register file initially holds the values of the variables live at the entry,
the allocated program has the same traces and outcomes. -/
theorem rename_correct {R : Type*} [DecidableEq R] {σ : V → R} (hσ : G.IsColouring σ)
    (env : Env V) (renv : Env R) (mem : Mem) (henv : ∀ x ∈ G.live G.entry, renv (σ x) = env x) :
    G.traces ⟨G.entry, env, mem⟩ = (G.rename σ).traces ⟨G.entry, renv, mem⟩ ∧
      G.outcomes ⟨G.entry, env, mem⟩ = (G.rename σ).outcomes ⟨G.entry, renv, mem⟩ := by
  have hclash : ∀ n m d y, d ∈ (G.code n).defs → m ∈ G.succ n → y ∈ G.live m → y ≠ d →
      σ y ≠ σ d := fun n m d y hd hm hy hne =>
    (hσ d y ⟨hne.symm, Or.inr (Or.inl ⟨n, hd, Set.mem_iUnion₂.2 ⟨m, hm, hy⟩⟩)⟩).symm
  let Rel : Config V ι → Config R ι → Prop := fun s t =>
    s.pc = t.pc ∧ s.mem = t.mem ∧ ∀ x ∈ G.live s.pc, t.env (σ x) = s.env x
  have hR : IsLockstep G (G.rename σ) Rel := by
    refine ⟨?_, ?_⟩
    · rintro ⟨n, env, mem⟩ ⟨n', renv, mem'⟩ s' o ⟨hn, hm, he⟩ hs
      simp only at hn hm he
      subst hn hm
      have hsucc : ∀ m, m ∈ (G.code n).succs → m ∈ G.succ n := fun m h => h
      have hkeep : (G.code n).defs = ∅ → ∀ m ∈ (G.code n).succs, ∀ y ∈ G.live m,
          renv (σ y) = env y :=
        fun hd m hm y hy => he y (G.mem_live_of_succ (hsucc m hm) hy (by simp [hd]))
      have hdef : ∀ d v, (G.code n).defs = {d} → ∀ m ∈ (G.code n).succs, ∀ y ∈ G.live m,
          Function.update renv (σ d) v (σ y) = Function.update env d v y := by
        intro d v hd m hm y hy
        by_cases hyd : y = d
        · subst hyd
          simp
        · rw [Function.update_of_ne hyd,
            Function.update_of_ne (hclash n m d y (by simp [hd]) (hsucc m hm) hy hyd)]
          exact he y (G.mem_live_of_succ (hsucc m hm) hy (by simp [hd, hyd]))
      have hrefs : ∀ a : Operand V, (∀ y ∈ a.vars, y ∈ (G.code n).refs) →
          (a.rename σ).eval renv = a.eval env := by
        intro a h
        cases a with
        | var x => exact he x (G.refs_subset_live (h x (by simp [Operand.vars])))
        | imm k => rfl
      have hc' : (G.rename σ).code n = (G.code n).rename σ := rfl
      cases hc : G.code n with
      | entry nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨⟨nx, renv, mem⟩, by simp [step, hc', hc, Instr.rename, Instr.exec], rfl, rfl, ?_⟩
        exact hkeep (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | nop nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨⟨nx, renv, mem⟩, by simp [step, hc', hc, Instr.rename, Instr.exec], rfl, rfl, ?_⟩
        exact hkeep (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | alu op d a b nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        have hb := hrefs b fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨nx, Function.update renv (σ d) (op.eval (a.eval env) (b.eval env)), mem⟩,
          by simp [step, hc', hc, Instr.rename, Instr.exec, ha, hb], rfl, rfl, ?_⟩
        exact hdef d _ (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | alu2 op d a nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨nx, Function.update renv (σ d) (op.eval (a.eval env)), mem⟩,
          by simp [step, hc', hc, Instr.rename, Instr.exec, ha], rfl, rfl, ?_⟩
        exact hdef d _ (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | ldi d a nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨nx, Function.update renv (σ d) (mem (a.eval env)), mem⟩,
          by simp [step, hc', hc, Instr.rename, Instr.exec, ha], rfl, rfl, ?_⟩
        exact hdef d _ (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | sti a b nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        have hb := hrefs b fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨nx, renv, Function.update mem (a.eval env) (b.eval env)⟩,
          by simp [step, hc', hc, Instr.rename, Instr.exec, ha, hb], rfl, rfl, ?_⟩
        exact hkeep (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | cmp c a b tt ff =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        have hb := hrefs b fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨if c.eval (a.eval env) (b.eval env) then tt else ff, renv, mem⟩,
          by simp [step, hc', hc, Instr.rename, Instr.exec, ha, hb], rfl, rfl, ?_⟩
        exact hkeep (by simp [hc, Instr.defs]) _ (by split <;> simp [hc, Instr.succs])
      | print a nx =>
        simp only [step, hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have ha := hrefs a fun y hy => by simp [hc, Instr.refs, hy]
        refine ⟨⟨nx, renv, mem⟩, by simp [step, hc', hc, Instr.rename, Instr.exec, ha], rfl, rfl,
          ?_⟩
        exact hkeep (by simp [hc, Instr.defs]) nx (by simp [hc, Instr.succs])
      | exit rs => simp [step, hc, Instr.exec] at hs
    · rintro ⟨n, env, mem⟩ ⟨n', renv, mem'⟩ ⟨hn, hm, he⟩ ⟨rs, hrs⟩
      simp only at hn hm he hrs
      subst hn hm
      refine ⟨⟨rs.map σ, by simp [rename, hrs, Instr.rename]⟩, ?_, rfl⟩
      simp only [resultValues, rename, hrs, Instr.rename, List.map_map]
      exact List.map_congr_left fun x hx =>
        (he x (G.refs_subset_live (by simp [hrs, Instr.refs, hx]))).symm
  exact hR.traces_outcomes ⟨rfl, rfl, henv⟩

/-- The program `y = 1; x = 2; print y` of `liveInClash_unsound`. -/
def deadStoreExample : Flowgraph String (Fin 4) where
  entry := 0
  code := ![.alu2 .mov "y" (.imm 1) 1, .alu2 .mov "x" (.imm 2) 2, .print (.var "y") 3, .exit []]

/-- Colouring the live-in-only clash graph is unsound: in `y = 1; x = 2; print y`
the dead store to `x` never clashes with `y` by simultaneous liveness, but
sharing a register prints `2`. -/
theorem liveInClash_unsound :
    ∃ (G : Flowgraph String (Fin 4)) (σ : String → Unit),
      (∀ x y, G.liveInClash x y → σ x ≠ σ y) ∧
        ∃ env renv mem, G.traces ⟨G.entry, env, mem⟩ ≠ (G.rename σ).traces ⟨G.entry, renv, mem⟩ := by
  have hlva : ∀ n, deadStoreExample.lva n ⊆ {"y"} := by decide
  have hlive : ∀ n, deadStoreExample.live n ⊆ {"y"} := by
    intro n x hx
    have hx' : x ∈ deadStoreExample.lva n := by
      rw [← deadStoreExample.lva_eq_live] at hx
      exact hx
    exact Finset.mem_singleton.1 (hlva n hx')
  refine ⟨deadStoreExample, fun _ => (), ?_, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  · rintro x y ⟨hne, n, hx, hy⟩
    exact absurd ((Set.mem_singleton_iff.1 (hlive n hx)).trans
      (Set.mem_singleton_iff.1 (hlive n hy)).symm) hne
  · intro heq
    have h1 : [1] ∈ deadStoreExample.traces ⟨deadStoreExample.entry, fun _ => 0, fun _ => 0⟩ := by
      rw [deadStoreExample.traces_of_silent
          (s' := ⟨1, Function.update (fun _ => 0) "y" 1, fun _ => 0⟩)
          (by simp [deadStoreExample, step, Instr.exec, Operand.eval, UnOp.eval]),
        deadStoreExample.traces_of_silent
          (s' := ⟨2, Function.update (Function.update (fun _ => 0) "y" 1) "x" 2, fun _ => 0⟩)
          (by simp [deadStoreExample, step, Instr.exec, Operand.eval, UnOp.eval]),
        deadStoreExample.traces_of_step (o := some 1)
          (s' := ⟨3, Function.update (Function.update (fun _ => 0) "y" 1) "x" 2, fun _ => 0⟩)
          (by simp [deadStoreExample, step, Instr.exec, Operand.eval]),
        deadStoreExample.traces_of_halted ⟨[], rfl⟩]
      simp
    rw [heq] at h1
    rw [(deadStoreExample.rename fun _ => ()).traces_of_silent
        (s' := ⟨1, Function.update (fun _ => 0) () 1, fun _ => 0⟩)
        (by simp [deadStoreExample, rename, Instr.rename, Operand.rename, step, Instr.exec,
          Operand.eval, UnOp.eval]),
      (deadStoreExample.rename fun _ => ()).traces_of_silent
        (s' := ⟨2, Function.update (Function.update (fun _ => 0) () 1) () 2, fun _ => 0⟩)
        (by simp [deadStoreExample, rename, Instr.rename, Operand.rename, step, Instr.exec,
          Operand.eval, UnOp.eval]),
      (deadStoreExample.rename fun _ => ()).traces_of_step (o := some 2)
        (s' := ⟨3, Function.update (Function.update (fun _ => 0) () 1) () 2, fun _ => 0⟩)
        (by simp [deadStoreExample, rename, Instr.rename, Operand.rename, step, Instr.exec,
          Operand.eval]),
      (deadStoreExample.rename fun _ => ()).traces_of_halted ⟨[], rfl⟩] at h1
    simp at h1

/-- Clash graphs need not be planar or four-colourable (notes p. 11, "this is
not generally the case for clash graphs (exercise)"): some program has five
mutually clashing variables. -/
theorem exists_five_clique : ∃ G : Flowgraph (Fin 5) (Fin 11), ∀ x y : Fin 5, x ≠ y → G.clash x y := by
  have hrefs : ∀ x : Fin 5,
      x ∈ (Instr.exit (ι := Fin 11) [0, 1, 2, 3, 4]).refs := by decide
  refine ⟨⟨0, fun n => if n = 5 then .exit [0, 1, 2, 3, 4] else .exit []⟩, fun x y hne =>
    ⟨hne, Or.inl ⟨5, Flowgraph.refs_subset_live _ (hrefs x), Flowgraph.refs_subset_live _ (hrefs y)⟩⟩⟩

end Flowgraph

/-! ## The colouring heuristic (notes p. 11) -/

section Chaitin

variable {V : Type*} [DecidableEq V]

/-- Clash degree of `v` among the remaining nodes. -/
def degreeIn (adj : V → V → Bool) (rest : List V) (v : V) : ℕ :=
  (rest.filter fun u => decide (u ≠ v) && adj v u).length

/-- The simplify phase: repeatedly remove a node with fewer than `k` clashes and
push it on the stack. Returns the stack, or `none` if every remaining node has
at least `k` clashes (a spill is needed). -/
def simplify (k : ℕ) (adj : V → V → Bool) : ℕ → List V → List V → Option (List V)
  | _, [], stack => some stack
  | 0, _ :: _, _ => none
  | fuel + 1, rest@(_ :: _), stack =>
    match rest.find? (fun v => decide (degreeIn adj rest v < k)) with
    | some v => simplify k adj fuel (rest.erase v) (v :: stack)
    | none => none

/-- The select phase (notes p. 11): pop the stack, giving each node the least
colour not used by its neighbours popped before it. `done` lists the nodes
already coloured. -/
def selectAux (k : ℕ) (adj : V → V → Bool) :
    List V → List V → (V → Option (Fin k)) → Option (V → Option (Fin k))
  | [], _, c => some c
  | v :: stack, done, c =>
    let used := done.filterMap fun u => if adj v u then c u else none
    match (List.finRange k).find? fun i => !(used.contains i) with
    | none => none
    | some col => selectAux k adj stack (v :: done) fun u => if u = v then some col else c u

/-- The select phase from an empty colouring. -/
def select (k : ℕ) (adj : V → V → Bool) (stack : List V) : Option (V → Option (Fin k)) :=
  selectAux k adj stack [] fun _ => none

/-- The heuristic: simplify then select. -/
def chaitin (k : ℕ) (adj : V → V → Bool) (vs : List V) : Option (V → Option (Fin k)) :=
  (simplify k adj vs.length vs []).bind (select k adj)

/-- The simplify phase pushes every remaining node on the stack. -/
theorem simplify_perm {k : ℕ} {adj : V → V → Bool} : ∀ (fuel : ℕ) (rest stack st : List V),
    simplify k adj fuel rest stack = some st → st.Perm (rest ++ stack)
  | _, [], stack, st, h => by
    simp only [simplify, Option.some.injEq] at h
    subst h
    exact List.Perm.refl _
  | 0, _ :: _, _, _, h => by simp [simplify] at h
  | fuel + 1, a :: l, stack, st, h => by
    simp only [simplify] at h
    split at h
    next v hv =>
      have hmem := List.mem_of_find?_eq_some hv
      exact (simplify_perm fuel _ _ _ h).trans
        (List.perm_middle.trans ((List.perm_cons_erase hmem).symm.append_right stack))
    next => simp at h

/-- The select phase extends a proper partial colouring of `done` to a proper
colouring of `stack ++ done`. -/
theorem selectAux_spec {k : ℕ} {adj : V → V → Bool} (hsymm : ∀ u v, adj u v = adj v u) :
    ∀ (stack done : List V) (c c' : V → Option (Fin k)),
    stack.Nodup → (∀ v ∈ stack, v ∉ done) → (∀ u ∈ done, (c u).isSome) →
    (∀ u ∈ done, ∀ v ∈ done, u ≠ v → adj u v = true → c u ≠ c v) →
    selectAux k adj stack done c = some c' →
    (∀ u ∈ stack ++ done, (c' u).isSome) ∧
      ∀ u ∈ stack ++ done, ∀ v ∈ stack ++ done, u ≠ v → adj u v = true → c' u ≠ c' v
  | [], done, c, c', _, _, h1, h2, h => by
    simp only [selectAux, Option.some.injEq] at h
    subst h
    exact ⟨h1, h2⟩
  | v :: stack, done, c, c', hnd, hdis, h1, h2, h => by
    simp only [selectAux] at h
    split at h
    next => simp at h
    next col hcol =>
      have hfree := List.find?_some hcol
      beta_reduce at hfree
      have hvd : v ∉ done := hdis v (List.mem_cons_self ..)
      have hne : ∀ u ∈ done, u ≠ v := fun u hu huv => hvd (huv ▸ hu)
      set c₁ : V → Option (Fin k) := fun u => if u = v then some col else c u with hc₁
      have hc₁v : c₁ v = some col := by simp [hc₁]
      have hc₁u : ∀ u ∈ done, c₁ u = c u := fun u hu => by simp [hc₁, hne u hu]
      have hcross : ∀ u ∈ done, adj v u = true → c₁ v ≠ c₁ u := by
        intro u hu hadj heq
        rw [hc₁v, hc₁u u hu] at heq
        have hused : col ∈ done.filterMap fun u => if adj v u then c u else none :=
          List.mem_filterMap.2 ⟨u, hu, by simp [hadj, ← heq]⟩
        have : (done.filterMap fun u => if adj v u then c u else none).contains col = true :=
          List.contains_iff_mem.2 hused
        rw [this] at hfree
        exact absurd hfree (by decide)
      have ih := selectAux_spec hsymm stack (v :: done) c₁ c' (List.nodup_cons.1 hnd).2
        (fun w hw hwd => by
          rcases List.mem_cons.1 hwd with rfl | hwd₁
          · exact (List.nodup_cons.1 hnd).1 hw
          · exact hdis w (List.mem_cons_of_mem _ hw) hwd₁)
        (fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu₁
          · simp [hc₁v]
          · rw [hc₁u u hu₁]; exact h1 u hu₁)
        (fun u hu w hw huw hadj => by
          rcases List.mem_cons.1 hu with rfl | hu₁ <;> rcases List.mem_cons.1 hw with rfl | hw₁
          · exact absurd rfl huw
          · exact hcross w hw₁ hadj
          · exact (hcross u hu₁ (by rw [hsymm]; exact hadj)).symm
          · rw [hc₁u u hu₁, hc₁u w hw₁]; exact h2 u hu₁ w hw₁ huw hadj)
        h
      have hmem : ∀ u, u ∈ stack ++ v :: done ↔ u ∈ (v :: stack) ++ done := fun u => by
        simp only [List.mem_append, List.mem_cons]; tauto
      exact ⟨fun u hu => ih.1 u ((hmem u).2 hu),
        fun u hu w hw => ih.2 u ((hmem u).2 hu) w ((hmem w).2 hw)⟩

/-- When the heuristic does not spill, it colours every node, and adjacent
nodes get different colours ("by construction this is always possible"). -/
theorem chaitin_colours {k : ℕ} {adj : V → V → Bool} (hsymm : ∀ u v, adj u v = adj v u)
    {vs : List V} (hvs : vs.Nodup) {c : V → Option (Fin k)} (h : chaitin k adj vs = some c) :
    (∀ v ∈ vs, (c v).isSome) ∧ ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → adj u v = true → c u ≠ c v := by
  obtain ⟨st, hst, hsel⟩ := Option.bind_eq_some_iff.1 h
  have hperm : st.Perm vs := by simpa using simplify_perm _ _ _ _ hst
  have hmem : ∀ u, u ∈ st ++ [] ↔ u ∈ vs := fun u => by simpa using hperm.mem_iff
  obtain ⟨h1, h2⟩ := selectAux_spec hsymm st [] _ c (hperm.nodup_iff.2 hvs) (by simp) (by simp)
    (by simp) hsel
  exact ⟨fun v hv => h1 v ((hmem v).2 hv),
    fun u hu v hv => h2 u ((hmem u).2 hu) v ((hmem v).2 hv)⟩

end Chaitin

end Silmaril.Courses.Cambridge.OptimisingCompilers
