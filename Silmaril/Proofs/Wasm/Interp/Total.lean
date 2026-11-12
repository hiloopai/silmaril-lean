module

public import Silmaril.Proofs.Wasm.Interp.Progress
public import Silmaril.Proofs.Wasm.Interp.Termination
public import Mathlib.Order.WellFounded

@[expose] public section

/-!
# A Core run that terminates forces native termination (proofs)

`term_of_acc`: if a Core configuration `K` has no infinite host-free trace (deterministic
profile), then every native problem — trees `es` on a stack `stk` in store `s` and frame `f` —
whose Core code `⟨s, f, vals stk.reverse ++ lowering of es⟩` sits, in some step-preserving
context, at a configuration reachable from `K`, has a native evaluation (`Binaryen.Eval`),
provided the problem passes the arity check, its Core code is typed in context
(`Sim.ContextTyped`) and the store is native and arity-checked. The induction is on the pair
(position under `K` in the order "reached by at least one step, inside some context",
structural size of `es`): a native sub-evaluation either works on a structurally smaller
problem at a configuration reachable from the current one, or follows at least one Core step
(calls, loop iterations). Native stuckness is excluded by `evalFlat_progress` and
`truthy_progress` (`Silmaril.Proofs.Wasm.Interp.Progress`). New proofs. Used for `DivSim`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Execution.Core.Sim

variable {H : Type} {o : GrowOracle}

/-! ## Step-preserving maps and the descent order -/

/-- A map of configurations that preserves host-free steps of the deterministic profile. -/
def SP (o : GrowOracle) (g : Config H → Config H) : Prop :=
  ∀ a b, Step (profile o) Det.noHost a b → Step (profile o) Det.noHost (g a) (g b)

theorem SP.id : SP (H := H) o id := fun _ _ h => h

theorem SP.comp {g g' : Config H → Config H} (hg : SP o g) (hg' : SP o g') : SP o (g ∘ g') :=
  fun _ _ h => hg _ _ (hg' _ _ h)

theorem SP.steps {g : Config H → Config H} (hg : SP o g) {a b : Config H}
    (h : Relation.ReflTransGen (Step (profile o) Det.noHost) a b) :
    Relation.ReflTransGen (Step (profile o) Det.noHost) (g a) (g b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hg _ _ hs)

theorem SP.transGen {g : Config H → Config H} (hg : SP o g) {a b : Config H}
    (h : Relation.TransGen (Step (profile o) Det.noHost) a b) :
    Relation.TransGen (Step (profile o) Det.noHost) (g a) (g b) := by
  induction h with
  | single hs => exact .single (hg _ _ hs)
  | tail _ hs ih => exact ih.tail (hg _ _ hs)

/-- Appending code. -/
def mapSuffix (rest : List Admin) (c : Config H) : Config H := ⟨c.store, c.frame, c.code ++ rest⟩

theorem sp_suffix (rest : List Admin) : SP (H := H) o (mapSuffix rest) := by
  rintro ⟨s, f, c⟩ ⟨s', f', c'⟩ h
  exact Step.append_right h rest

/-- Inside a label below values and before code. -/
def mapLabel (pre : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) (c : Config H) :
    Config H := ⟨c.store, c.frame, vals pre ++ [.label n cont c.code] ++ rest⟩

theorem sp_label (pre : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
    SP (H := H) o (mapLabel pre n cont rest) := by
  rintro ⟨s, f, c⟩ ⟨s', f', c'⟩ h
  exact Silmaril.Wasm.Logic.Core.Step.ctx pre rest (Step.ctxtLabel h)

/-- Inside a frame below values and before code. -/
def mapFrame (pre : List Val) (n : Nat) (f₀ : Frame) (rest : List Admin) (c : Config H) :
    Config H := ⟨c.store, f₀, vals pre ++ [.frame n c.frame c.code] ++ rest⟩

theorem sp_frame (pre : List Val) (n : Nat) (f₀ : Frame) (rest : List Admin) :
    SP (H := H) o (mapFrame pre n f₀ rest) := by
  rintro ⟨s, f, c⟩ ⟨s', f', c'⟩ h
  exact Silmaril.Wasm.Logic.Core.Step.ctx pre rest (Step.ctxtFrame h)

/-- `X` occurs, in some context, at a configuration reached from `K` in at least one step. -/
def Desc (o : GrowOracle) (K X : Config H) : Prop :=
  ∃ g, SP o g ∧ Relation.TransGen (Step (profile o) Det.noHost) K (g X)

/-- An infinite chain of descents is an infinite trace. -/
theorem acc_desc {K : Config H}
    (h : ¬ Silmaril.InfiniteTrace (Step (profile o) Det.noHost) K) :
    Acc (fun X K => Desc o K X) K := by
  by_contra hacc
  apply h
  refine Silmaril.InfiniteTrace.coinduct (fun c => ∃ g X, SP o g ∧
      ¬ Acc (fun X K => Desc o K X) X ∧
      Relation.TransGen (Step (profile o) Det.noHost) c (g X)) ?_ ?_
  · rintro c ⟨g, X, hg, hX, hcX⟩
    rcases Relation.TransGen.head'_iff.mp hcX with ⟨c₁, hc₁, hrest⟩
    refine ⟨c₁, hc₁, ?_⟩
    rcases Relation.ReflTransGen.cases_head hrest with heq | ⟨c₂, h₂, h₃⟩
    · obtain ⟨Y, hY, g', hg', hXY⟩ := exists_not_acc_lt_of_not_acc hX
      exact ⟨g ∘ g', Y, hg.comp hg', hY, heq ▸ hg.transGen hXY⟩
    · exact ⟨g, X, hg, hX, Relation.TransGen.head' h₂ h₃⟩
  · obtain ⟨Y, hY, g', hg', hKY⟩ := exists_not_acc_lt_of_not_acc hacc
    exact ⟨g', Y, hg', hY, hKY⟩

/-! ## Native problems -/

/-- The Core code of a native problem. -/
def pcfg (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Config H :=
  ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩

/-- A native problem that passes the check, is typed in context and runs in a native,
checked store has a native evaluation. -/
def Term (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Prop :=
  ∀ (labels : List Nat) (ret : Nat) (out : Option Nat),
    chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    ContextTyped (pcfg s f stk es) → Binaryen.NativeFuncsOk s.funcs → StoreChk s.funcs →
    ∃ r, Binaryen.Eval s f stk es r

/-- The induction hypothesis available at a problem whose code is `P₀` and size `n`. -/
def RecFrom (o : GrowOracle) (P₀ : Config H) (n : Nat) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (g : Config H → Config H), SP o g →
    Relation.ReflTransGen (Step (profile o) Det.noHost) P₀ (g (pcfg s f stk es)) →
    (sizeOf es < n ∨ Relation.TransGen (Step (profile o) Det.noHost) P₀ (g (pcfg s f stk es))) →
    Term s f stk es

/-! ## Cases -/

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}

/-- A normal native evaluation is a Core run to its values. -/
theorem run_normal {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {xs : List Binaryen.BExpr}
    {labels : List Nat} {ret : Nat} {out : Option Nat}
    (h : Binaryen.Eval s f stk xs (s₁, f₁, .normal stk₁)) (hS : StoreChk s.funcs)
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length) xs = some out) :
    Relation.ReflTransGen (Step (profile o) Det.noHost) (pcfg s f stk xs)
      ⟨s₁, f₁, vals stk₁.reverse⟩ := by
  obtain ⟨c', o', hrun, he, hm⟩ := run_of_wp (wp_of_eval (P := profile o) (host := Det.noHost) h hS hc)
  have hc' : c' = vals stk₁.reverse := ends_normal hm he
  rw [← hc']
  exact hrun

theorem size_args {i : Instr} {args : List Binaryen.BExpr} :
    sizeOf args < sizeOf (Binaryen.BExpr.op i args :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.op.sizeOf_spec]
  omega

theorem size_tail {e : Binaryen.BExpr} : sizeOf es < sizeOf (e :: es) := by
  simp only [List.cons.sizeOf_spec]
  omega

theorem pcfg_op (i : Instr) (args : List Binaryen.BExpr) :
    pcfg s f stk (.op i args :: es) =
      mapSuffix (.plain i :: expression (Binaryen.BExpr.lowerList es)) (pcfg s f stk args) := by
  simp [pcfg, mapSuffix, expression]

/-- The flat-instruction case after the arguments. -/
theorem term_flat {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {i : Instr}
    {args : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat}
    {o₁ : Option Nat} (hi : ∀ x, i ≠ .call x)
    (rec : RecFrom o (pcfg s f stk (.op i args :: es)) (sizeOf (Binaryen.BExpr.op i args :: es)))
    (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hrun : Relation.ReflTransGen (Step (profile o) Det.noHost) (pcfg s f stk (.op i args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es)⟩)
    (hf : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o₁)
    (inv1 : EvalInv s f (s₁, f₁, .normal stk₁))
    (h2 : chk s.funcs f.module f.locals.length ret labels o₁ es = some out)
    (ht : ContextTyped (pcfg s f stk (.op i args :: es))) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) : ∃ r, Binaryen.Eval s f stk (.op i args :: es) r := by
  have hF₁ : Binaryen.NativeFuncsOk s₁.funcs := inv1.1 ▸ hF
  have ht₁ := ContextTyped.steps ht hrun
  obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progress hf hi ht₁ hF₁
  by_cases hn : fl₂.IsNormal
  · rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨ho, inv2⟩ := flat_normal hflat hf
    have inv12 : EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have hst := steps_flat_normal (P := profile o) (host := Det.noHost) hi hf hflat
      (expression (Binaryen.BExpr.lowerList es))
    have hrun₂ : Relation.ReflTransGen (Step (profile o) Det.noHost)
        (pcfg s f stk (.op i args :: es)) (pcfg s₂ f₂ stk₂ es) := hrun.trans hst
    have h2' : chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [chk_inv inv12, ← ho]
      exact h2
    obtain ⟨r, hk⟩ := rec s₂ f₂ stk₂ es id SP.id hrun₂ (.inl size_tail) labels ret out h2'
      (ContextTyped.steps ht hrun₂) (inv12.1 ▸ hF) (storeChk_inv inv12 hS)
    exact ⟨r, .opOk hi hargs hflat hk⟩
  · exact ⟨_, .opStop hi hargs hflat hn⟩

/-- **Operators other than calls.** -/
theorem term_op {i : Instr} {args : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (rec : RecFrom o (pcfg s f stk (.op i args :: es)) (sizeOf (Binaryen.BExpr.op i args :: es))) :
    Term s f stk (.op i args :: es) := by
  intro labels ret out hc ht hF hS
  obtain ⟨o₁, h1, h2⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  have hta : ContextTyped (pcfg s f stk args) := by
    rw [pcfg_op] at ht
    exact ContextTyped.suffix ht
  obtain ⟨⟨s₁, f₁, fl⟩, hargs⟩ := rec s f stk args _ (sp_suffix _) (by rw [pcfg_op])
    (.inl size_args) labels ret oa ha hta hF hS
  by_cases hn : fl.IsNormal
  · rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨hf, inv1⟩ := arity_args hS (flowOk_of_eval hargs) h1
    have hrun : Relation.ReflTransGen (Step (profile o) Det.noHost)
        (pcfg s f stk (.op i args :: es))
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [pcfg_op]
      exact (sp_suffix _).steps (run_normal hargs hS ha)
    exact term_flat hi rec hargs hrun hf inv1 h2 ht hF hS
  · exact ⟨_, .argsAbort hargs hn⟩

/-! ### Calls -/

theorem callArity_func? {f₁ : Frame} {s₁ : Store H} {x : FuncIdx} {p q : Nat}
    (h : callArity s₁.funcs f₁.module x = some (p, q)) :
    ∃ a fi ps rs, s₁.func? f₁ x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ p = ps.length ∧ q = rs.length := by
  unfold callArity at h
  split at h
  · rename_i fi hfi
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hfi
    obtain ⟨a, ha, hfa⟩ := hfi
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ps, rs⟩, hty, rfl, rfl⟩ := h
    exact ⟨a, fi, ps, rs, by simp [Store.func?, ha, hfa], hty, rfl, rfl⟩
  · cases h

/-- The callee problem of a call, in its frame and label. -/
theorem pcfg_callee {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} :
    (⟨s₁, f₁, vals (stk₁.drop ps.length).reverse ++
        [.frame rs.length (calleeFrame fi fn stk₁ ps.length)
          [.label rs.length [] (expression fn.body)]] ++
        expression (Binaryen.BExpr.lowerList es)⟩ : Config H) =
      (mapFrame (stk₁.drop ps.length).reverse rs.length f₁ (expression (Binaryen.BExpr.lowerList es)) ∘
        mapLabel [] rs.length [] [])
        (pcfg s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)) := by
  simp [mapFrame, mapLabel, pcfg, vals, Binaryen.lowerList_liftInstrs]

/-- The callee's native evaluation, from the induction hypothesis. -/
theorem term_callee {i : Instr} {args : List Binaryen.BExpr} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType}
    (rec : RecFrom o (pcfg s f stk (.op i args :: es)) (sizeOf (Binaryen.BExpr.op i args :: es)))
    (hrun : Relation.ReflTransGen (Step (profile o) Det.noHost) (pcfg s f stk (.op i args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (ht : ContextTyped (pcfg s f stk (.op i args :: es)))
    (hF₁ : Binaryen.NativeFuncsOk s₁.funcs) (hS₁ : StoreChk s₁.funcs) :
    ∃ r, Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body) r := by
  have enter := steps_call_enter (P := profile o) (host := Det.noHost) hfi hcode hty hp
    (expression (Binaryen.BExpr.lowerList es))
  rw [pcfg_callee] at enter
  have hmap : SP o (mapFrame (stk₁.drop ps.length).reverse rs.length f₁
      (expression (Binaryen.BExpr.lowerList es)) ∘ mapLabel [] rs.length [] []) :=
    SP.comp (sp_frame (H := H) (o := o) _ _ _ _) (sp_label (H := H) (o := o) [] rs.length [] [])
  have htg := Relation.TransGen.trans_right hrun enter
  have hct : ContextTyped (pcfg s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)) :=
    ContextTyped.label (ContextTyped.frame (ContextTyped.steps ht htg.to_reflTransGen))
  obtain ⟨ob, -, hb'⟩ := callee_chk hS₁ hfi hcode hty hp
  exact rec _ _ _ _ _ hmap htg.to_reflTransGen (.inr htg) _ _ _ hb' hct hF₁ hS₁

/-- After the callee: return to the caller and continue. -/
theorem term_call_ret {args : List Binaryen.BExpr} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    {stk₁ vs : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {flb : Binaryen.Flow} {labels : List Nat} {ret : Nat}
    {out : Option Nat}
    (rec : RecFrom o (pcfg s f stk (.op (.call x) args :: es))
      (sizeOf (Binaryen.BExpr.op (.call x) args :: es)))
    (hrun : Relation.ReflTransGen (Step (profile o) Det.noHost)
      (pcfg s f stk (.op (.call x) args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hbody : Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, flb)) (hvs : flb.retVals = some vs)
    (inv1 : EvalInv s f (s₁, f₁, .normal stk₁))
    (h2 : chk s.funcs f.module f.locals.length ret labels
      (some (stk₁.length - ps.length + rs.length)) es = some out)
    (ht : ContextTyped (pcfg s f stk (.op (.call x) args :: es)))
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) :
    ∃ r, Binaryen.Eval s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r := by
  have hS₁ : StoreChk s₁.funcs := storeChk_inv inv1 hS
  obtain ⟨ob, hob, hb'⟩ := callee_chk hS₁ hfi hcode hty hp
  obtain ⟨hok, hinvb⟩ := flowOk_of_eval hbody hS₁ hb'
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have hnorm : ∀ ws, flb = .normal ws → ws.length = rs.length := by
    rintro ws rfl
    exact length_of_ends hok hob
  obtain ⟨c', o', hrunb, he, hm⟩ :=
    run_of_wp (wp_of_eval (P := profile o) (host := Det.noHost) hbody hS₁ hb')
  have hrunb' : Relation.ReflTransGen (Step (profile o) Det.noHost)
      ⟨s₁, calleeFrame fi fn stk₁ ps.length, expression fn.body⟩ ⟨s₂, f₂, c'⟩ := by
    simpa [vals, Binaryen.lowerList_liftInstrs] using hrunb
  have htg := Relation.TransGen.trans_right hrun
    (tg_call_ok hfi hcode hty hp hrunb' he hm hvs hrs hnorm)
  have inv2 : EvalInv s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨hinvb.1.trans inv1.1, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chk s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [chk_inv inv2, hlen]
    exact h2
  exact rec s₂ f₁ _ es id SP.id htg.to_reflTransGen (.inl size_tail) labels ret out h2'
    (ContextTyped.steps ht htg.to_reflTransGen) (inv2.1 ▸ hF) (storeChk_inv inv2 hS)

/-- A callee flow is a return, a trap or a throw (never a branch out of the body). -/
theorem callee_flow {flb : Binaryen.Flow} {n : Nat} {ob : Option Nat}
    (hok : FlowOk [n] n ob flb) :
    (∃ vs, flb.retVals = some vs) ∨ flb = .trap ∨ ∃ t, flb = .throw t := by
  rcases flb with vs | ⟨_ | k, vs⟩ | vs | _ | t
  · exact .inl ⟨vs, rfl⟩
  · exact .inl ⟨vs, rfl⟩
  · obtain ⟨m, hm, -⟩ := hok
    simp at hm
  · exact .inl ⟨vs, rfl⟩
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨t, rfl⟩)

/-- **Direct calls.** -/
theorem term_call {x : FuncIdx} {args : List Binaryen.BExpr}
    (rec : RecFrom o (pcfg s f stk (.op (.call x) args :: es))
      (sizeOf (Binaryen.BExpr.op (.call x) args :: es))) :
    Term s f stk (.op (.call x) args :: es) := by
  intro labels ret out hc ht hF hS
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  have hta : ContextTyped (pcfg s f stk args) := by
    rw [pcfg_op] at ht
    exact ContextTyped.suffix ht
  obtain ⟨⟨s₁, f₁, fl⟩, hargs⟩ := rec s f stk args _ (sp_suffix _) (by rw [pcfg_op])
    (.inl size_args) labels ret oa ha hta hF hS
  by_cases hn : fl.IsNormal
  · show ∃ r, Binaryen.Eval s f stk (.op (.call x) args :: es) r
    rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨hf, inv1⟩ := arity_args hS (flowOk_of_eval hargs) h1
    obtain ⟨p, q, hpq, -, -⟩ := flatChk_call hf
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
    obtain ⟨-, hp, h2⟩ := arity_call_pre hS (flowOk_of_eval hargs) hfi hty hc
    have hF₁ : Binaryen.NativeFuncsOk s₁.funcs := inv1.1 ▸ hF
    have hS₁ : StoreChk s₁.funcs := storeChk_inv inv1 hS
    obtain ⟨fn, hcode, -⟩ := hF₁ fi (List.mem_of_getElem? (funcs_of_func? hfi))
    have hrun : Relation.ReflTransGen (Step (profile o) Det.noHost)
        (pcfg s f stk (.op (.call x) args :: es))
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
          expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [pcfg_op]
      exact (sp_suffix _).steps (run_normal hargs hS ha)
    obtain ⟨⟨s₂, f₂, flb⟩, hbody⟩ := term_callee rec hrun hfi hcode hty hp ht hF₁ hS₁
    obtain ⟨ob, hob, hb'⟩ := callee_chk hS₁ hfi hcode hty hp
    obtain ⟨hok, -⟩ := flowOk_of_eval hbody hS₁ hb'
    rcases callee_flow hok with
      ⟨vs, hvs⟩ | rfl | ⟨t, rfl⟩
    · obtain ⟨r, hk⟩ := term_call_ret rec hrun hfi hcode hty hp hbody hvs inv1 h2 ht hF hS
      exact ⟨r, .callOk hargs hfi hcode hty hbody hvs hk⟩
    · exact ⟨_, .callTrap hargs hfi hcode hty hbody⟩
    · exact ⟨_, .callThrow hargs hfi hcode hty hbody⟩
  · exact ⟨_, .argsAbort hargs hn⟩

/-! ### Blocks, conditionals and loops -/

/-- A flow handed to a block's continuation, leaving to an outer label, or escaping. -/
theorem flow_cases (fl : Binaryen.Flow) :
    (∃ vs, fl.blockVals = some vs) ∨ (∃ k vs, fl = .brk (k + 1) vs) ∨ fl.Escapes := by
  rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
  · exact .inl ⟨vs, rfl⟩
  · exact .inl ⟨vs, rfl⟩
  · exact .inr (.inl ⟨k, vs, rfl⟩)
  all_goals exact .inr (.inr trivial)

/-- The parts of a block: its body's evaluation, and its continuation's when the body hands
on values. -/
theorem block_parts {P₀ : Config H} {n : Nat} (rec : RecFrom o P₀ n) {bt : BlockType}
    {body : List Binaryen.BExpr} {np nr : Nat} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hrun : Relation.ReflTransGen (Step (profile o) Det.noHost) P₀
      ⟨s, f, vals stk.reverse ++ .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩)
    (hsz : sizeOf body < n) (hszes : sizeOf es < n)
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : endsAt (chk s.funcs f.module f.locals.length ret (nr :: labels) (some np) body) nr = true)
    (h2 : chk s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
      some out)
    (ht : ContextTyped P₀) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) :
    ∃ r, Binaryen.Eval s f (stk.take np) body r ∧
      ∀ vs, r.2.2.blockVals = some vs →
        ∃ r', Binaryen.Eval r.1 r.2.1 (vs.take nr ++ stk.drop np) es r' := by
  have enter := step_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har) (expression (Binaryen.BExpr.lowerList es))
  have hrun₁ : Relation.ReflTransGen (Step (profile o) Det.noHost) P₀
      (mapLabel (stk.drop np).reverse nr [] (expression (Binaryen.BExpr.lowerList es))
        (pcfg s f (stk.take np) body)) := hrun.tail enter
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hbc : chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]
    exact hb'
  have ht₁ : ContextTyped (pcfg s f (stk.take np) body) :=
    ContextTyped.label (ContextTyped.steps ht hrun₁)
  obtain ⟨⟨s₁, f₁, fl⟩, hbody⟩ := rec s f (stk.take np) body _ (sp_label _ _ _ _) hrun₁
    (.inl hsz) (nr :: labels) ret ob hbc ht₁ hF hS
  refine ⟨_, hbody, fun vs hvs => ?_⟩
  obtain ⟨hok, inv1⟩ := flowOk_of_eval hbody hS hbc
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  obtain ⟨c', o', hr, he, hm⟩ :=
    run_of_wp (wp_of_eval (P := profile o) (host := Det.noHost) hbody hS hbc)
  have htg := tg_block_vals (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm
    hvs hnr hnorm
  have hrun₂ : Relation.ReflTransGen (Step (profile o) Det.noHost) P₀
      (pcfg s₁ f₁ (vs.take nr ++ stk.drop np) es) := hrun.trans htg.to_reflTransGen
  exact rec s₁ f₁ _ es id SP.id hrun₂ (.inl hszes) labels ret out (chk_after inv1 hp hnr h2)
    (ContextTyped.steps ht hrun₂) (inv1.1 ▸ hF) (storeChk_inv inv1 hS)

theorem size_block {bt : BlockType} {body : List Binaryen.BExpr} :
    sizeOf body < sizeOf (Binaryen.BExpr.block bt body :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.block.sizeOf_spec]
  omega

theorem pcfg_block (bt : BlockType) (body : List Binaryen.BExpr) :
    pcfg s f stk (.block bt body :: es) = ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
  simp [pcfg, expression, Binaryen.BExpr.lower]

/-- **Blocks.** -/
theorem term_block {bt : BlockType} {body : List Binaryen.BExpr}
    (rec : RecFrom o (pcfg s f stk (.block bt body :: es))
      (sizeOf (Binaryen.BExpr.block bt body :: es))) :
    Term s f stk (.block bt body :: es) := by
  intro labels ret out hc ht hF hS
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_block h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨⟨s₁, f₁, fl⟩, hbody, hk⟩ := block_parts rec (by rw [pcfg_block]) size_block size_tail
    har hp hb h2 ht hF hS
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · obtain ⟨r, hr⟩ := hk vs hvs
    exact ⟨r, .blockOk har hbody hvs hr⟩
  · exact ⟨_, .blockBrk har hbody⟩
  · exact ⟨_, .blockEsc har hbody hesc⟩

/-- An `if` steps to the block of its chosen arm. -/
theorem step_if_arm {bt : BlockType} {t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {rest : List Admin} (hb : Binaryen.truthy cv = some b) :
    Step (profile o) Det.noHost
      ⟨s, f, vals (cv :: stk).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩
      ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

theorem size_cond {bt : BlockType} {c t el : List Binaryen.BExpr} :
    sizeOf c < sizeOf (Binaryen.BExpr.if_ bt c t el :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.if_.sizeOf_spec]
  omega

theorem size_arm {bt : BlockType} {c t el : List Binaryen.BExpr} (b : Bool) :
    sizeOf (if b then t else el) < sizeOf (Binaryen.BExpr.if_ bt c t el :: es) := by
  cases b <;> simp only [List.cons.sizeOf_spec, Binaryen.BExpr.if_.sizeOf_spec,
    Bool.false_eq_true, ↓reduceIte] <;> omega

theorem pcfg_if (bt : BlockType) (c t el : List Binaryen.BExpr) :
    pcfg s f stk (.if_ bt c t el :: es) =
      mapSuffix (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es)) (pcfg s f stk c) := by
  simp [pcfg, mapSuffix, expression, Binaryen.BExpr.lower]

/-- The arm of an `if` whose condition ran normally. -/
theorem term_if_arm {bt : BlockType} {c t el : List Binaryen.BExpr} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {cv : Val} {b : Bool} {np nr : Nat} {labels : List Nat} {ret : Nat}
    {out : Option Nat}
    (rec : RecFrom o (pcfg s f stk (.if_ bt c t el :: es))
      (sizeOf (Binaryen.BExpr.if_ bt c t el :: es)))
    (hcond : Binaryen.Eval s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hrun : Relation.ReflTransGen (Step (profile o) Det.noHost) (pcfg s f stk (.if_ bt c t el :: es))
      ⟨s₁, f₁, vals (cv :: stk₁).reverse ++ .plain (.if_ bt (Binaryen.BExpr.lowerList t)
        (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)⟩)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.if_ bt c t el :: es) = some out)
    (ht : ContextTyped (pcfg s f stk (.if_ bt c t el :: es)))
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) :
    ∃ r, Binaryen.Eval s f stk (.if_ bt c t el :: es) r := by
  obtain ⟨inv1, hp, hbarm, h2⟩ := arity_if_pre (b := b) hS (flowOk_of_eval hcond) har hc
  rw [← chk_inv inv1] at hbarm h2
  have hrun₂ := hrun.tail (step_if_arm (rest := expression (Binaryen.BExpr.lowerList es)) hb)
  obtain ⟨⟨s₂, f₂, fl⟩, harm, hk⟩ := block_parts rec hrun₂ (size_arm b) size_tail har hp hbarm
    h2 ht (inv1.1 ▸ hF) (storeChk_inv inv1 hS)
  rcases flow_cases fl with ⟨vs, hvs⟩ | ⟨k, vs, rfl⟩ | hesc
  · obtain ⟨r, hr⟩ := hk vs hvs
    exact ⟨r, .ifOk hcond hb har harm hvs hr⟩
  · exact ⟨_, .ifBrk hcond hb har harm⟩
  · exact ⟨_, .ifEsc hcond hb har harm hesc⟩

/-- **Conditionals.** -/
theorem term_if {bt : BlockType} {c t el : List Binaryen.BExpr}
    (rec : RecFrom o (pcfg s f stk (.if_ bt c t el :: es))
      (sizeOf (Binaryen.BExpr.if_ bt c t el :: es))) :
    Term s f stk (.if_ bt c t el :: es) := by
  intro labels ret out hc ht hF hS
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_if h1
  have htc : ContextTyped (pcfg s f stk c) := by
    rw [pcfg_if] at ht
    exact ContextTyped.suffix ht
  obtain ⟨⟨s₁, f₁, fl⟩, hcond⟩ := rec s f stk c _ (sp_suffix _) (by rw [pcfg_if])
    (.inl size_cond) labels ret oc hco htc hF hS
  by_cases hn : fl.IsNormal
  · show ∃ r, Binaryen.Eval s f stk (.if_ bt c t el :: es) r
    rcases fl with stk₁' | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨hoc, inv1⟩ := flowOk_of_eval hcond hS hco
    obtain ⟨np, nr, ha, -, -, -, -⟩ := hk1 _ hoc
    have hrun₁ : Relation.ReflTransGen (Step (profile o) Det.noHost)
        (pcfg s f stk (.if_ bt c t el :: es))
        ⟨s₁, f₁, vals stk₁'.reverse ++ .plain (.if_ bt (Binaryen.BExpr.lowerList t)
          (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
      rw [pcfg_if]
      exact (sp_suffix _).steps (run_normal hcond hS hco)
    obtain ⟨cv, stk₁, b, rfl, hb⟩ := truthy_progress (ContextTyped.steps ht hrun₁)
      (inv1.1 ▸ hF)
    have har : Binaryen.arity f₁ bt = some (np, nr) := by
      rw [arity_eq, inv1.2.1]
      exact ha
    exact term_if_arm rec hcond hrun₁ hb har hc ht hF hS
  · exact ⟨_, .ifAbort hcond hn⟩

theorem size_loop {bt : BlockType} {body : List Binaryen.BExpr} :
    sizeOf body < sizeOf (Binaryen.BExpr.loop bt body :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.loop.sizeOf_spec]
  omega

theorem pcfg_loop (bt : BlockType) (body : List Binaryen.BExpr) :
    pcfg s f stk (.loop bt body :: es) = ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
  simp [pcfg, expression, Binaryen.BExpr.lower]

/-- A loop body that branched back: the next iteration. -/
theorem term_loop_back {bt : BlockType} {body : List Binaryen.BExpr} {s₁ : Store H} {f₁ : Frame}
    {vs : List Val} {np nr : Nat} {labels : List Nat} {ret : Nat} {out : Option Nat}
    {c' : List Admin} {o' : Logic.Core.Outcome}
    (rec : RecFrom o (pcfg s f stk (.loop bt body :: es))
      (sizeOf (Binaryen.BExpr.loop bt body :: es)))
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hr : Relation.ReflTransGen (Step (profile o) Det.noHost)
      ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩
      ⟨s₁, f₁, c'⟩) (he : o'.Ends c') (hm : FlowMatch (.brk 0 vs) o') (hnp : np ≤ vs.length)
    (inv1 : EvalInv s f (s₁, f₁, .brk 0 vs))
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out)
    (ht : ContextTyped (pcfg s f stk (.loop bt body :: es)))
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) :
    ∃ r, Binaryen.Eval s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r := by
  have htg := tg_loop_back (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm hnp
  rw [← pcfg_loop] at htg
  rw [← pcfg_loop] at htg
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hc' : chk s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
    rw [chk_inv inv1, hlen]
    exact hc
  exact rec s₁ f₁ _ _ id SP.id htg.to_reflTransGen (.inr htg) labels ret out hc'
    (ContextTyped.steps ht htg.to_reflTransGen) (inv1.1 ▸ hF) (storeChk_inv inv1 hS)

/-- **Loops.** -/
theorem term_loop {bt : BlockType} {body : List Binaryen.BExpr}
    (rec : RecFrom o (pcfg s f stk (.loop bt body :: es))
      (sizeOf (Binaryen.BExpr.loop bt body :: es))) :
    Term s f stk (.loop bt body :: es) := by
  intro labels ret out hc ht hF hS
  obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
  obtain ⟨np, nr, ha, -, -, -⟩ := chk1_loop h1
  have har : Binaryen.arity f bt = some (np, nr) := (arity_eq f bt).trans ha
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  have enter := step_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) (expression (Binaryen.BExpr.lowerList es))
  have hrun₁ : Relation.ReflTransGen (Step (profile o) Det.noHost)
      (pcfg s f stk (.loop bt body :: es))
      (mapLabel (stk.drop np).reverse np [.loop bt (Binaryen.BExpr.lowerList body)]
        (expression (Binaryen.BExpr.lowerList es)) (pcfg s f (stk.take np) body)) := by
    rw [pcfg_loop]
    exact .single enter
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hbc : chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]
    exact hb'
  obtain ⟨⟨s₁, f₁, fl⟩, hbody⟩ := rec s f (stk.take np) body _ (sp_label _ _ _ _) hrun₁
    (.inl size_loop) (np :: labels) ret ob hbc (ContextTyped.label (ContextTyped.steps ht hrun₁))
    hF hS
  obtain ⟨hok, inv1⟩ := flowOk_of_eval hbody hS hbc
  obtain ⟨c', o', hr, he, hm⟩ :=
    run_of_wp (wp_of_eval (P := profile o) (host := Det.noHost) hbody hS hbc)
  rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t
  · have hlen : vs.length = nr := length_of_ends hok hob
    have htg := tg_loop_normal (rest := expression (Binaryen.BExpr.lowerList es)) har hp hr he hm
      hlen
    rw [← pcfg_loop] at htg
    obtain ⟨r, hk⟩ := rec s₁ f₁ _ es id SP.id htg.to_reflTransGen (.inl size_tail) labels ret out
      (chk_after inv1 hp hlen.ge h2) (ContextTyped.steps ht htg.to_reflTransGen) (inv1.1 ▸ hF)
      (storeChk_inv inv1 hS)
    exact ⟨r, .loopOk har hbody hk⟩
  · obtain ⟨m, hm', hle⟩ := hok
    have hnp : np ≤ vs.length := by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm'
      exact hm' ▸ hle
    obtain ⟨r, hk⟩ := term_loop_back rec har hp hr he hm hnp inv1 hc ht hF hS
    exact ⟨r, .loopBack har hbody hk⟩
  · exact ⟨_, .loopBrk har hbody⟩
  · exact ⟨_, .loopEsc har hbody trivial⟩
  · exact ⟨_, .loopEsc har hbody trivial⟩
  · exact ⟨_, .loopEsc har hbody trivial⟩

/-- **One problem, given the induction hypothesis.** -/
theorem term_step (rec : RecFrom o (pcfg s f stk es) (sizeOf es)) : Term s f stk es := by
  rcases es with _ | ⟨e, es⟩
  · exact fun _ _ _ _ _ _ _ => ⟨_, .nil⟩
  · cases e with
    | op i args =>
      by_cases hi : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hi
        exact term_call rec
      · exact term_op (fun x hx => hi ⟨x, hx⟩) rec
    | block bt body => exact term_block rec
    | loop bt body => exact term_loop rec
    | if_ bt c t el => exact term_if rec
    | tryTable bt cs body =>
      intro labels ret out hc
      obtain ⟨o₁, h1, -⟩ := chk_cons.mp hc
      simp [chk1] at h1

end Cases

/-- **A Core configuration without infinite traces makes every native problem reachable from
it terminate.** -/
theorem term_of_acc {K : Config H} (hacc : Acc (fun X K => Desc o K X) K) :
    ∀ (n : Nat) (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
      (g : Config H → Config H), SP o g → sizeOf es = n →
      Relation.ReflTransGen (Step (profile o) Det.noHost) K (g (pcfg s f stk es)) →
      Term s f stk es := by
  induction hacc with
  | intro K _ ihO =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihI =>
  intro s f stk es g hg hn hK
  apply term_step
  intro s' f' stk' es' g' hg' hst hsz
  rcases hsz with hlt | htr
  · exact ihI (sizeOf es') (hn ▸ hlt) s' f' stk' es' (g ∘ g') (hg.comp hg') rfl
      (hK.trans (hg.steps hst))
  · have hdesc : Desc o K (pcfg s' f' stk' es') :=
      ⟨g ∘ g', hg.comp hg', Relation.TransGen.trans_right hK (hg.transGen htr)⟩
    exact ihO _ hdesc (sizeOf es') s' f' stk' es' id SP.id rfl .refl

end Silmaril.Wasm.Interp
