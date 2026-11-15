module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.FwdEval
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# Segments of productive native runs (proofs)

Bookkeeping for the forward simulation of productive runs:

* streams: `substInf_split` (a resolved stream with a finite list in front is a resolved list
  in front of a resolved stream), `substInf_regroup` (a resolved concatenation of segments is
  resolved segment by segment, the converse of `Shape.substInf_of_segments`), `consInf_split`,
  `cons_of_concat` (consistency of the parts of a consistent stream);
* glue: `prefix_glue` (a first tree run normally, as a logged Core run to the code of the
  remaining trees, with the check carried along), `loopBack_glue` (a loop iteration branching
  back), `block_enter`, `loop_enter` (host-free entry into the body's label), `arm_glue` (an
  `if` condition, then the host-free entry into the chosen arm's label);
* `reachL_of_evalL`, `descends_unwrap`: a recorded call of a logged run is reached after the
  calls recorded before it (`ReachL`), so a descent of `wasmHOpen` is a logged reach in a Wasm
  body.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (WP Outcome funcPost frame_ends wp_vals)
open Silmaril.Wasm.Interp
open Shape (streamAppend StreamConcat SubstInf Res1 SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Streams -/

section Streams

universe u

variable {α : Type u}

theorem flatMap_range_add (L : Nat → List α) (a b : Nat) :
    (List.range (a + b)).flatMap L =
      (List.range a).flatMap L ++ (List.range b).flatMap (fun j => L (a + j)) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem flatMap_range_mono (L : Nat → List α) {m n : Nat} (h : m ≤ n) :
    ((List.range m).flatMap L).length ≤ ((List.range n).flatMap L).length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [flatMap_range_add]
  simp

theorem streamAppend_map {β : Type u} (g : α → β) (l : List α) (ω : Nat → α) :
    (fun i => g ((l ++ω ω) i)) = (l.map g) ++ω (fun i => g (ω i)) := by
  funext i
  by_cases hi : i < l.length
  · rw [Shape.streamAppend_lt hi, Shape.streamAppend_lt (by simpa using hi)]
    simp
  · rw [Shape.streamAppend_ge (by omega), Shape.streamAppend_ge (by simp; omega)]
    simp

variable {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod}

theorem substPre_of_res (l : List (Call (sh.E ⊕ₛ sh.self))) (L : Nat → List (Call sh.E))
    (h : ∀ i (hi : i < l.length), Res1 c l[i] (L i)) :
    SubstPre c l ((List.range l.length).flatMap L) := by
  induction l generalizing L with
  | nil => simpa using SubstPre.nil
  | cons x l ih =>
    have h0 : Res1 c x (L 0) := h 0 (by simp)
    have ht := ih (fun j => L (j + 1)) (fun i hi => h (i + 1) (by simp; omega))
    have e : (List.range (x :: l).length).flatMap L =
        L 0 ++ (List.range l.length).flatMap (fun j => L (j + 1)) := by
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [e]
    generalize L 0 = l0 at h0 ⊢
    cases h0 with
    | ext => exact .ext ht
    | int hm => exact .int hm ht

/-- **A resolved stream with a finite list in front** is a resolved list in front of a
resolved stream. -/
theorem substInf_split {l : List (Call (sh.E ⊕ₛ sh.self))} {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    {ω : Nat → Call sh.E} (h : SubstInf c (l ++ω ν) ω) :
    ∃ q ω', ω = q ++ω ω' ∧ SubstPre c l q ∧ SubstInf c ν ω' := by
  obtain ⟨L, hL, hc⟩ := h
  have hlen : ((List.range l.length).flatMap L).length + 0 =
      ((List.range l.length).flatMap L).length := rfl
  refine ⟨(List.range l.length).flatMap L,
    fun i => ω (((List.range l.length).flatMap L).length + i), ?_, ?_, ?_⟩
  · funext i
    by_cases hi : i < ((List.range l.length).flatMap L).length
    · rw [Shape.streamAppend_lt hi]
      exact hc.1 l.length i hi
    · rw [Shape.streamAppend_ge (by omega)]
      congr 1
      omega
  · exact substPre_of_res l L (fun i hi => by
      have := hL i
      rwa [Shape.streamAppend_lt hi] at this)
  · refine ⟨fun j => L (l.length + j), fun j => ?_, fun n i hi => ?_, fun N => ?_⟩
    · have := hL (l.length + j)
      rwa [Shape.streamAppend_ge (by omega), show l.length + j - l.length = j by omega] at this
    · have hp := hc.1 (l.length + n) (((List.range l.length).flatMap L).length + i)
        (by rw [flatMap_range_add]; simp only [List.length_append]; omega)
      dsimp only
      rw [hp]
      simp only [flatMap_range_add]
      rw [List.getElem_append_right (by omega)]
      simp
    · obtain ⟨m, hm⟩ := hc.2 (N + ((List.range l.length).flatMap L).length)
      refine ⟨m, ?_⟩
      have := flatMap_range_mono L (show m ≤ l.length + m by omega)
      rw [flatMap_range_add] at this
      simp only [List.length_append] at this
      omega

/-- **A resolved concatenation of segments is resolved segment by segment.** -/
theorem substInf_regroup {u : Nat → List (Call (sh.E ⊕ₛ sh.self))}
    {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E} (hu : StreamConcat u ν)
    (h : SubstInf c ν ω) :
    ∃ q : Nat → List (Call sh.E), (∀ n, SubstPre c (u n) (q n)) ∧ StreamConcat q ω := by
  obtain ⟨L, hL, hc⟩ := h
  let O : Nat → Nat := fun n => ((List.range n).flatMap u).length
  have hO : ∀ n, O (n + 1) = O n + (u n).length := fun n => by
    simp [O, List.range_succ]
  let q : Nat → List (Call sh.E) := fun n =>
    (List.range (u n).length).flatMap (fun j => L (O n + j))
  have hq : ∀ n, (List.range n).flatMap q = (List.range (O n)).flatMap L := by
    intro n
    induction n with
    | zero => simp [O]
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, hO, flatMap_range_add]
      simp [q]
  refine ⟨q, fun n => substPre_of_res (u n) _ (fun j hj => ?_), fun n => ?_, fun N => ?_⟩
  · have hp := hu.1 (n + 1) (O n + j) (by have := hO n; simp only [O] at this ⊢; omega)
    have := hL (O n + j)
    rw [hp] at this
    simpa [List.range_succ, List.flatMap_append, O, List.getElem_append_right] using this
  · rw [hq]
    exact hc.1 (O n)
  · obtain ⟨m, hm⟩ := hc.2 N
    obtain ⟨n, hn⟩ := hu.2 m
    exact ⟨n, by rw [hq]; exact le_trans hm (flatMap_range_mono L hn)⟩

end Streams

/-- The host answers of a stream are allowed. -/
abbrev ConsInf (host : HostSemantics H) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  ∀ n, coreHostRel host (ω n).1 (.answer (ω n).2)

theorem consInf_split {q : List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (h : ConsInf host (q ++ω ω)) : Cons host q ∧ ConsInf host ω := by
  refine ⟨fun e he => ?_, fun n => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    have := h i
    rwa [Shape.streamAppend_lt hi] at this
  · have := h (q.length + n)
    rwa [Shape.streamAppend_ge (by omega), show q.length + n - q.length = n by omega] at this

theorem cons_of_concat {q : Nat → List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hq : StreamConcat q ω) (h : ConsInf host ω) (n : Nat) : Cons host (q n) := by
  intro e he
  have hm : e ∈ (List.range (n + 1)).flatMap q :=
    List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega), he⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
  rw [← hq.1 (n + 1) i hi]
  exact h i

theorem substPre_mono {sh : Silmaril.Games.Abstract.Shape} {c c' : sh.ClosedMod} (hle : c ≤ c')
    {x : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (h : SubstPre c x q) :
    SubstPre c' x q := by
  induction h with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hm _ ih => exact .int (hle _ _ _ hm) ih

/-! ## Glue -/

theorem chkE_nil' {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {labels : List Nat}
    (o : Option Nat) : chk F mi nl ret labels o [] = some o := by
  cases o <;> rfl

section Glue

variable {s s₁ s' : Store H} {f f₁ f' : Frame} {stk stk₁ stk' : List Val}
  {es : List Binaryen.BExpr} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
  {labels : List Nat} {ret : Nat} {out : Option Nat}

/-- **A first tree run normally** is a logged Core run to the code of the remaining trees,
the check carried along. -/
theorem prefix_glue (hH : Interp.NativeHostSlice host) {e : Binaryen.BExpr}
    (h : EvalL s f stk [e] l (s', f', .normal stk'))
    (hq : SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q) (hc : Cons host q)
    (hS : StoreChk s.funcs)
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length) (e :: es) = some out) :
    EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (e :: es))⟩ q
        ⟨s', f', vals stk'.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ ∧
      StoreChk s'.funcs ∧
      chk s'.funcs f'.module f'.locals.length ret labels (some stk'.length) es = some out := by
  obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH h q (substPre_mono (close_le_goodC hH) hq) hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hchk
  have h1' : chk s.funcs f.module f.locals.length ret labels (some stk.length) [e] = some o :=
    chk_consE.mpr ⟨o, h1, chkE_nil' o⟩
  obtain ⟨hok, inv⟩ := (evalH_good (P := P) hH d).1 hS h1'
  obtain ⟨c', o', hrun, he, hm⟩ := cl hS h1'
  have hc' : c' = vals stk'.reverse := ends_normal hm he
  subst hc'
  have hok' : o = some stk'.length := hok
  subst hok'
  refine ⟨?_, storeChk_inv inv hS, chk_inv inv h2⟩
  have := evRun_append (rest := expression (Binaryen.BExpr.lowerList es)) hrun
  simpa [code_cons, expression, List.append_assoc] using this

/-- **A loop iteration branching back to the loop**, as a logged Core run to the loop again. -/
theorem loopBack_glue (hH : Interp.NativeHostSlice host) {bt : BlockType} {body : List Binaryen.BExpr}
    {np nr : Nat} {vs : List Val} (har : Binaryen.arity f bt = some (np, nr))
    (h : EvalL s f (stk.take np) body l (s₁, f₁, .brk 0 vs))
    (hq : SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q) (hc : Cons host q)
    (hS : StoreChk s.funcs)
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    EvRun P host ⟨s, f, vals stk.reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ q
        ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ ∧
      StoreChk s₁.funcs ∧
      chk s₁.funcs f₁.module f₁.locals.length ret labels (some (vs.take np ++ stk.drop np).length)
        (.loop bt body :: es) = some out := by
  obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH h q (substPre_mono (close_le_goodC hH) hq) hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
  obtain ⟨_, _, hbc, hok, inv1⟩ := body_facts hS (evalH_good (P := P) hH d).1 hb
    (take_length_of_le hp)
  obtain ⟨m, hm', hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm'
    exact hm' ▸ hle
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  refine ⟨?_, storeChk_inv inv1 hS, by rw [hlen]; exact chk_inv inv1 hchk⟩
  obtain ⟨c', o, hrun, he, hm⟩ := cl hS hbc
  rw [code_loop, code_loop]
  have enter := steps_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
  have inner := evRun_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
    (evRun_label np [.loop bt (Binaryen.BExpr.lowerList body)] hrun)
  have exit := exit_br0 (P := P) (host := NH) (s₁ := s₁) (f₁ := f₁)
    (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm hnp
    (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
  have e : vals (vs.take np ++ stk.drop np).reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: expression (Binaryen.BExpr.lowerList es) =
      vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
        expression [.loop bt (Binaryen.BExpr.lowerList body)] ++
        expression (Binaryen.BExpr.lowerList es) := by
    simp [expression]
  rw [e]
  simpa using evRun_trans (evRun_of_free enter) (evRun_trans inner (evRun_of_free exit))

/-- **Entering a block**: the body's check, and the host-free entry into its label. -/
theorem block_enter {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.block bt body :: es) = some out) :
    (∃ ob, chk s.funcs f.module f.locals.length ret (nr :: labels) (some (stk.take np).length)
      body = some ob) ∧
      Steps P NH ⟨s, f, vals stk.reverse ++
          expression (Binaryen.BExpr.lowerList (.block bt body :: es))⟩
        ⟨s, f, vals (stk.drop np).reverse ++ [.label nr [] (vals (stk.take np).reverse ++
          expression (Binaryen.BExpr.lowerList body))] ++
          expression (Binaryen.BExpr.lowerList es)⟩ := by
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hchk
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  refine ⟨⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  rw [code_block]
  exact steps_enter (P := P) (host := NH) hp (step_block har) _

/-- **Entering a loop**: the body's check, and the host-free entry into its label. -/
theorem loop_enter {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    (∃ ob, chk s.funcs f.module f.locals.length ret (np :: labels) (some (stk.take np).length)
      body = some ob) ∧
      Steps P NH ⟨s, f, vals stk.reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
        ⟨s, f, vals (stk.drop np).reverse ++ [.label np [.loop bt (Binaryen.BExpr.lowerList body)]
          (vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body))] ++
          expression (Binaryen.BExpr.lowerList es)⟩ := by
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hchk
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  refine ⟨⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  rw [code_loop]
  exact steps_enter (P := P) (host := NH) hp (step_loop har) _

/-- **An `if` condition, then the chosen arm's label**, as a logged Core run. -/
theorem arm_glue (hH : Interp.NativeHostSlice host) {bt : BlockType}
    {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {np nr : Nat}
    (h : EvalL s f stk c l (s₁, f₁, .normal (cv :: stk₁))) (hb : Binaryen.truthy cv = some b)
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (hq : SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q) (hc : Cons host q)
    (hS : StoreChk s.funcs)
    (hchk : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.if_ bt c t el :: es) = some out) :
    StoreChk s₁.funcs ∧
      (∃ ob, chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob) ∧
      EvRun P host ⟨s, f, vals stk.reverse ++
          expression (Binaryen.BExpr.lowerList (.if_ bt c t el :: es))⟩ q
        ⟨s₁, f₁, vals (stk₁.drop np).reverse ++ [.label nr [] (vals (stk₁.take np).reverse ++
          expression (Binaryen.BExpr.lowerList (if b then t else el)))] ++
          expression (Binaryen.BExpr.lowerList es)⟩ := by
  obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH h q (substPre_mono (close_le_goodC hH) hq) hc
  obtain ⟨inv1, hp, hbarm, -⟩ := arity_if_pre (b := b) hS (evalH_good (P := P) hH d).1 har hchk
  replace hbarm := chk_inv_endsAt inv1 hbarm
  obtain ⟨ob, hb', -⟩ := endsAt_eq hbarm
  refine ⟨storeChk_inv inv1 hS, ⟨ob, by rw [take_length_of_le hp]; exact hb'⟩, ?_⟩
  obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  obtain ⟨c', o', hrun, he, hm⟩ := cl hS hco
  have hc' : c' = vals (cv :: stk₁).reverse := ends_normal hm he
  subst hc'
  rw [code_if]
  have r1 := evRun_append (rest := .plain (.if_ bt (Binaryen.BExpr.lowerList t)
    (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)) hrun
  have st := step_if_armP (P := P) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t) (el := el)
    (rest := expression (Binaryen.BExpr.lowerList es)) hb
  have enter := steps_enter (P := P) (host := NH) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (step_block har)
    (expression (Binaryen.BExpr.lowerList es))
  simpa using evRun_trans r1 (evRun_of_free (Relation.ReflTransGen.head st enter))

end Glue

/-! ## Recorded calls are reached -/

theorem ocall_mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' : Store H}
    {b b' : List Val ⊕ Nat} {s₂ s₂' : Store H}
    (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' ∧ b = b' ∧ s₂ = s₂' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ocall_eq_mk (z : OCall H) : ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ := by
  match z with
  | ⟨.inr ⟨a, args, s₁⟩, (b, s₂)⟩ => exact ⟨a, args, s₁, b, s₂, rfl⟩
  | ⟨.inl m, _⟩ => exact (m : PEmpty).elim

theorem split_mid {α : Type} {a b u rest : List α} {o : α} (h : a ++ b = u ++ o :: rest) :
    (∃ r₁, a = u ++ o :: r₁) ∨ ∃ u₂, u = a ++ u₂ ∧ ∃ r₂, b = u₂ ++ o :: r₂ := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, hb⟩ | ⟨c', rfl, hc⟩
  · exact .inr ⟨a', rfl, rest, hb⟩
  · rcases c' with _ | ⟨x, c'⟩
    · exact .inr ⟨[], by simp, rest, by simpa using hc.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact .inl ⟨c', rfl⟩

/-- **A recorded call of a logged run is reached** after the calls recorded before it. -/
theorem reachL_of_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Binaryen.Flow} (h : EvalL s f stk es l r) :
    ∀ (u rest : List (OCall H)) (a : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat)
      (s₂ : Store H), l = u ++ OCall.mk a args s₁ b s₂ :: rest →
      ReachL s f stk es u ⟨a, (args, s₁)⟩ := by
  induction h with
  | nil => intro u rest _ _ _ _ _ he; simp at he
  | argsAbort _ _ ih => exact fun u rest a args s₁ b s₂ he => .args (ih u rest a args s₁ b s₂ he)
  | callRet hargs hfi hty _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .args (ih₁ u r₁ a args s₁ b s₂ h₁)
    · rcases u₂ with _ | ⟨z, u₃⟩
      · simp only [List.nil_append, List.cons.injEq] at h₂
        obtain ⟨hz, -⟩ := h₂
        obtain ⟨rfl, rfl, rfl, -, -⟩ := ocall_mk_inj hz
        rw [List.append_nil]
        exact ReachL.here hargs hfi hty
      · simp only [List.cons_append, List.cons.injEq] at h₂
        obtain ⟨rfl, h₂⟩ := h₂
        exact .callK hargs hfi hty (ih₂ u₃ r₂ a args s₁ b s₂ h₂)
  | callThrow hargs hfi hty ih =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .args (ih u r₁ a args s₁ b s₂ h₁)
    · rcases u₂ with _ | ⟨z, u₃⟩
      · simp only [List.nil_append, List.cons.injEq] at h₂
        obtain ⟨hz, -⟩ := h₂
        obtain ⟨rfl, rfl, rfl, -, -⟩ := ocall_mk_inj hz
        rw [List.append_nil]
        exact ReachL.here hargs hfi hty
      · simp at h₂
  | opOk hi hargs hflat _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .args (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .opK hi hargs hflat (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | opStop _ _ _ _ ih => exact fun u rest a args s₁ b s₂ he => .args (ih u rest a args s₁ b s₂ he)
  | blockOk har hbody hvs _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .block har (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .blockK har hbody hvs (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | blockBrk har _ ih =>
    exact fun u rest a args s₁ b s₂ he => .block har (ih u rest a args s₁ b s₂ he)
  | blockEsc har _ _ ih =>
    exact fun u rest a args s₁ b s₂ he => .block har (ih u rest a args s₁ b s₂ he)
  | loopOk har hbody _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .loop har (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .loopK har hbody (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | loopBack har hbody _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .loop har (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .loopBack har hbody (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | loopBrk har _ ih =>
    exact fun u rest a args s₁ b s₂ he => .loop har (ih u rest a args s₁ b s₂ he)
  | loopEsc har _ _ ih =>
    exact fun u rest a args s₁ b s₂ he => .loop har (ih u rest a args s₁ b s₂ he)
  | ifOk hc hb har harm hvs _ ih₁ ih₂ ih₃ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · rcases split_mid h₁ with ⟨r₁', h₁'⟩ | ⟨u₂', rfl, r₂', h₂'⟩
      · exact .cond (ih₁ u r₁' a args s₁ b s₂ h₁')
      · exact .arm hc hb har (ih₂ u₂' r₂' a args s₁ b s₂ h₂')
    · exact .ifK hc hb har harm hvs (ih₃ u₂ r₂ a args s₁ b s₂ h₂)
  | ifBrk hc hb har _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .cond (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .arm hc hb har (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | ifEsc hc hb har _ _ ih₁ ih₂ =>
    intro u rest a args s₁ b s₂ he
    rcases split_mid he with ⟨r₁, h₁⟩ | ⟨u₂, rfl, r₂, h₂⟩
    · exact .cond (ih₁ u r₁ a args s₁ b s₂ h₁)
    · exact .arm hc hb har (ih₂ u₂ r₂ a args s₁ b s₂ h₂)
  | ifAbort _ _ ih => exact fun u rest a args s₁ b s₂ he => .cond (ih u rest a args s₁ b s₂ he)

/-- **A descent of `wasmHOpen` is a logged reach in a Wasm body.** -/
theorem descends_unwrap {c : (wasmHShape H).ClosedMod} {x y : (wasmHShape H).self.Op}
    {q : List (Call (wasmHostSig H))} (h : Shape.Descends wasmHOpen c x q y) :
    ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (l : List (OCall H)),
      x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ReachL x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) l y ∧
      SubstPre c (l.map OCall.lift) q := by
  obtain ⟨z, hz, u, ans, rest, he, hq⟩ := h
  rcases hz with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, -, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, -, -, -, -, rfl⟩
  · obtain ⟨l₁, l₂, rfl, rfl, hl₂⟩ := List.map_eq_append_iff.1 he
    obtain ⟨o, l₃, rfl, ho, -⟩ := List.map_eq_cons_iff.1 hl₂
    obtain ⟨a, args, s₁, b, s₂, rfl⟩ := ocall_eq_mk o
    obtain ⟨y₁, y₂, y₃⟩ := y
    change (⟨.inr ⟨a, (args, s₁)⟩, (b, s₂)⟩ : HCall H) = ⟨.inr ⟨y₁, (y₂, y₃)⟩, ans⟩ at ho
    cases ho
    exact ⟨fi, fn, ps, rs, l₁, hfi, hc, hty,
      reachL_of_evalL hE l₁ l₃ a args s₁ b s₂ rfl, hq⟩
  · rcases u with _ | ⟨_, u⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨he, -⟩ := he
      cases he
    · have := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
