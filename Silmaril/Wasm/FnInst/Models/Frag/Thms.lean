module

public import Silmaril.Wasm.FnInst.Models.Frag.Defs
public import Silmaril.Wasm.FnInst.Models.Inst.Thms
public import Silmaril.Wasm.FnInst.Models.Version.Thms
public import Silmaril.Wasm.FnInst.Models.Entry.Thms

/-!
# The fragment: rules, transfer, and versions that distinguish more

* `bind_ret_left`, `bind_ret_right`, `bind_assoc`, `bind_congr`: the monad laws of `bind`;
* `add_zero_left`: the rule `0 + e ≐ e` holds in every environment, for every expression `e`
  over every context; `addZeroRule`/`addZeroRule_transfer`: as a sentence at the minimal
  signature (one function) it holds, translated, in every model of every signature it embeds
  into (`transfer`);
* `addZeroRule_moduleEquiv`: and replacing a body by the rewritten one is module equivalence in
  the entry logic's sense (`moduleEquiv_replace`);
* **versions**: `vg` has globals but no `mutGlobal`. The two bodies `readAfter`
  (`call 0 (0); drop; global.get`) and `readBefore` (`global.get + (call 0 (0); drop; 0)`) are
  allowed at `vg` (`readAfter_uses`, `readBefore_uses`), equivalent over the behaviours
  admissible at `vg` (`admValid_vg`) and distinguished at Wasm 1.0 (`not_admValid_v10`), whose
  callees may write the global; `not_admValid_up`: validity does not transfer up the
  `FeatureSet` lattice in the context-restricting reading. In the syntax-only reading the pair
  is not valid at any version (`not_valid_read`), consistent with conservativity
  (`valid_up_iff`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models.Frag

open Silmaril.Wasm.Models Silmaril.Inst Silmaril.Wasm

theorem bind_ret_left (v : Val) (k : Val → St → Set Res) : bind (ret v) k = k v := by
  funext s
  ext r
  simp [bind, ret]

theorem bind_ret_right (m : St → Set Res) : bind m ret = m := by
  funext s
  ext r
  constructor
  · rintro ⟨⟨o, s'⟩, hp, hr⟩
    cases o with
    | none =>
      have hr' : r = (none, s') := hr
      rw [hr']
      exact hp
    | some v =>
      have hr' : r = (some v, s') := hr
      rw [hr']
      exact hp
  · intro hr
    refine ⟨r, hr, ?_⟩
    rcases r with ⟨_ | v, s'⟩
    · rfl
    · rfl

theorem bind_assoc (m : St → Set Res) (k k' : Val → St → Set Res) :
    bind (bind m k) k' = bind m fun v => bind (k v) k' := by
  funext s
  ext r
  constructor
  · rintro ⟨p, ⟨⟨o, s1⟩, hq, hp⟩, hr⟩
    refine ⟨(o, s1), hq, ?_⟩
    cases o with
    | none =>
      have hp' : p = (none, s1) := hp
      rw [hp'] at hr
      exact hr
    | some v => exact ⟨p, hp, hr⟩
  · rintro ⟨⟨o, s1⟩, hq, hr⟩
    cases o with
    | none =>
      have hr' : r = (none, s1) := hr
      exact ⟨(none, s1), ⟨(none, s1), hq, rfl⟩, hr'⟩
    | some v =>
      obtain ⟨p, hp, hr2⟩ := hr
      exact ⟨p, ⟨(some v, s1), hq, hp⟩, hr2⟩

/-- `bind` only looks at the continuation on the values and states `m` produces. -/
theorem bind_congr (m : St → Set Res) {k k' : Val → St → Set Res} (s : St)
    (h : ∀ v s', (some v, s') ∈ m s → k v s' = k' v s') : bind m k s = bind m k' s := by
  ext r
  constructor
  · rintro ⟨⟨o, s1⟩, hq, hr⟩
    refine ⟨(o, s1), hq, ?_⟩
    cases o with
    | none => exact hr
    | some v =>
      show r ∈ k' v s1
      rw [← h v s1 hq]
      exact hr
  · rintro ⟨⟨o, s1⟩, hq, hr⟩
    refine ⟨(o, s1), hq, ?_⟩
    cases o with
    | none => exact hr
    | some v =>
      show r ∈ k v s1
      rw [h v s1 hq]
      exact hr

/-- Reading the global first. -/
theorem bind_get (k : Val → St → Set Res) (s : St) :
    bind (fun s => {(some s, s)}) k s = k s s := by
  ext r
  simp [bind]

/-! ### A rewrite rule and its transfer -/

/-- `0 + e ≐ e`, for every expression, in every environment. -/
theorem add_zero_left {n : ℕ} (e : Expr n) (env : Env sem n) :
    Sen.Holds sem env (.eq (Expr.add (.const 0) e) e) := by
  funext args
  show bind (ret 0) (fun x => bind (eval env args e) fun y => ret (x + y)) = eval env args e
  have h0 : (fun y : Val => ret (0 + y)) = ret := funext fun y => by simp
  rw [bind_ret_left, h0]
  exact bind_ret_right _

/-- The rule at the minimal signature: one unary function, the focus. -/
def addZeroRule : Sen syn (sig 1 0).n := .eq (Expr.add (.const 0) (.param 0)) (.param 0)

/-- The rule holds in every model of every signature the minimal one embeds into. -/
theorem addZeroRule_transfer {U : Sig syn} (σ : sig 1 0 ⟶ U) (M : (bodyInst sem).Mod U) :
    M ⊨[bodyInst sem] (bodyInst sem).map σ addZeroRule :=
  transfer sem σ ((sat_bot_iff sem _).2 fun env => add_zero_left _ env) M

/-- Replacing a body `0 + e` by `e` in any module is module equivalence. -/
theorem addZeroRule_moduleEquiv {T : Sig syn} (B : PBodies T.toCtx) (e : Expr T.n)
    {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ β, R β β) :
    Equiv.ModuleEquiv (entryPoints sem obs0) R
      (Closed.replace T B (Expr.add (.const 0) e)) (Closed.replace T B e) :=
  moduleEquiv_replace sem obs0 hR B _ _ fun env _ => add_zero_left e env

/-! ### Versions: a context with mutable globals distinguishes more -/

/-- Integers, globals (read only), direct calls and control. -/
def vg : FeatureSet := FeatureSet.ofList [.intNum, .globals, .directCall, .control]

theorem vg_le_v10 : vg ≤ v10 := leB_iff.mp (by decide)

theorem vg_no_mutGlobal : vg.has .mutGlobal = false := by decide

/-- Call the import, then read the global. -/
def readAfter : Expr 1 := .seq (.call 0 (.const 0)) .gget

/-- Read the global, then call the import. -/
def readBefore : Expr 1 := .add .gget (.seq (.call 0 (.const 0)) (.const 0))

theorem readAfter_uses : uses readAfter vg := by
  intro c hc
  simp only [readAfter, Expr.caps, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem readBefore_uses : uses readBefore vg := by
  intro c hc
  simp only [readBefore, Expr.caps, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide

theorem eval_readAfter (env : Fin 1 → Den) (args : List Val) :
    eval env args readAfter = bind (env 0 [0]) fun _ s => {(some s, s)} := by
  simp only [readAfter, eval, bind_ret_left]

theorem eval_readBefore (env : Fin 1 → Den) (args : List Val) (s : St) :
    eval env args readBefore s = bind (env 0 [0]) (fun _ => ret s) s := by
  have h0 : s + 0 = s := by simp
  simp only [readBefore, eval, bind_ret_left]
  rw [bind_get, bind_assoc]
  simp only [bind_ret_left]
  rw [h0]

/-- At `vg` (no callee can write the global) the two bodies are equivalent. -/
theorem admValid_vg : AdmValid sem adm vg (.eq readAfter readBefore) := by
  intro env henv
  have hpres : ∀ args s r, r ∈ env 0 args s → r.2 = s := by
    rcases henv 0 with h | h
    · exact absurd h (by rw [vg_no_mutGlobal]; decide)
    · exact h
  funext args s
  show eval env args readAfter s = eval env args readBefore s
  rw [eval_readAfter, eval_readBefore]
  refine bind_congr _ s fun v s' hmem => ?_
  have hs : s' = s := hpres [0] s (some v, s') hmem
  rw [hs]
  rfl

/-- The callee that increments the global and returns `0`. -/
def incr : Den := fun _ s => {(some 0, s + 1)}

/-- At Wasm 1.0 (mutable globals) the callee `incr` distinguishes them. -/
theorem not_admValid_v10 : ¬ AdmValid sem adm v10 (.eq readAfter readBefore) := by
  intro h
  have hadm : ∀ i, (fun _ : Fin 1 => incr) i ∈ adm v10 := fun _ => Or.inl (by decide)
  have heq : eval (fun _ => incr) [] readAfter 0 = eval (fun _ => incr) [] readBefore 0 :=
    congrFun (congrFun (h _ hadm) []) 0
  rw [eval_readAfter, eval_readBefore] at heq
  have hmem : ((some 1, 1) : Res) ∈ bind (incr [0]) (fun _ s => {(some s, s)}) 0 :=
    ⟨(some 0, 1), rfl, rfl⟩
  rw [heq] at hmem
  obtain ⟨p, hp, hr⟩ := hmem
  have hp' : p = (some 0, 1) := hp
  rw [hp'] at hr
  have hr' : ((some 1, 1) : Res) = (some 0, 1) := hr
  exact absurd hr' (by decide)

/-- Validity in the context-restricting reading does not transfer up the lattice. -/
theorem not_admValid_up : ∃ v w : FeatureSet, v ≤ w ∧
    AdmValid sem adm v (.eq readAfter readBefore) ∧
      ¬ AdmValid sem adm w (.eq readAfter readBefore) :=
  ⟨vg, v10, vg_le_v10, admValid_vg, not_admValid_v10⟩

/-- In the syntax-only reading (every environment), the pair is not valid. -/
theorem not_valid_read : ¬ ∀ env : Env sem 1, Sen.Holds sem env (.eq readAfter readBefore) :=
  fun h => not_admValid_v10 (admValid_of_valid sem adm v10 h)

end Silmaril.Wasm.FnInst.Models.Frag
