module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Fwd

/-!
# The logged forward simulation of `EvalL` and of the closure (proofs)

* `coreL_*`: the cases of `Interp.wp_of_eval`/`evalO_goodE` with logs, from the logged
  combinators of `Fwd`; the arity facts of the native run come from `Interp.evalH_good` on the
  `EvalH` run that the logged run, its calls answered consistently, is;
* `evalL_fwd`: a logged run whose calls `GoodC` resolves to a consistent `q` is an `EvalH` run
  and a logged Core run with exactly the events `q`;
* `close_le_goodC`: every closed behaviour is in `GoodC`;
* `close_ret_evRun`, `wasmEvFun_evRun`: **a returning closed behaviour with a consistent log is
  a Core run of the call (of the invocation) with exactly that log**, every profile.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (WP Outcome funcPost frame_ends wp_vals)
open Silmaril.Wasm.Interp

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

section Cases

variable {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × Binaryen.Flow} {q₁ q₂ q₃ : List (Call (wasmHostSig H))}

theorem coreL_nil : CoreL P host s f stk [] (s, f, .normal stk) [] := by
  intro labels ret out _ _
  simpa using (runL_of_wp (host := host) (wp_vals (P := P) (host := NH) (s := s) (f := f)
    (vs := stk.reverse) (Q := Match (s, f, .normal stk)) ⟨rfl, rfl, rfl⟩))

theorem coreL_argsAbort (iha : CoreL P host s f stk args (s₁, f₁, fl) q₁) (hfl : ¬ fl.IsNormal) :
    CoreL P host s f stk (.op i args :: es) (s₁, f₁, fl) q₁ := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  exact runL_append_abrupt (iha hS ha) hfl

theorem coreL_opOk (hargs : ArityGood s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreL P host s f stk args (s₁, f₁, .normal stk₁) q₁) (hi : ∀ x, i ≠ .call x)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : CoreL P host s₂ f₂ stk₂ es r q₂) :
    CoreL P host s f stk (.op i args :: es) r (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS hargs h1
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  replace hf := flatChk_of_evalFlat hflat hf
  obtain ⟨ho, inv2⟩ := flat_normal (ext := noExt) hflat hf
  have inv12 : EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
  have h2' : chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
      some out := by
    rw [← ho]
    exact chk_inv inv12 h2
  have st := steps_flat_normal (P := P) (host := NH) hi hf hflat
    (expression (Binaryen.BExpr.lowerList es))
  rw [code_op]
  exact runL_append_normal (iha hS ha) (runL_free st (ihk (storeChk_inv inv12 hS) h2'))

theorem coreL_opStop (hargs : ArityGood s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreL P host s f stk args (s₁, f₁, .normal stk₁) q₁)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
    CoreL P host s f stk (.op i args :: es) (s₂, f₂, fl) q₁ := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS hargs h1
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  replace hf := flatChk_of_evalFlat hflat hf
  rw [code_op]
  simpa using runL_append_normal (iha hS ha)
    (runL_of_wp (host := host) (wp_flat_abrupt (P := P) (host := NH) hf hflat hfl _))

section CallCases

variable {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}

/-- A call answered by a logged callee run `qc`, the callee handing back `ws`. -/
theorem coreL_callOk (hH : NativeHostSlice host)
    (aha : ArityGood s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreL P host s f stk args (s₁, f₁, .normal stk₁) q₁)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    {bfl : Binaryen.Flow} {w ws : List Val} {qc : List (Call (wasmHostSig H))}
    (hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, bfl))
    (hvs : bfl.retVals = some w) (hws : ws.reverse = w.take rs.length)
    (hrun : StoreChk s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      EvRun P host ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++
        [.ref (.func a), .callRefType fi.type]⟩ qc ⟨s₂, f₁, vals ws⟩)
    (ihk : CoreL P host s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es r q₂) :
    CoreL P host s f stk (.op (.call x) args :: es) r (q₁ ++ (qc ++ q₂)) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
    oracle_at (hostCall_sound (P := P) hH) hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ w.length := retVals_length hok hob hvs
  have inv2 : EvalInv s f (s₂, f₁, .normal (ws.reverse ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (ws.reverse ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    rw [hws]
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chk s₂.funcs f₁.module f₁.locals.length ret labels
      (some (ws.reverse ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have st := evRun_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi
    (hrun (storeChk_inv inv1 hS) (take_rev_length hp))
  rw [code_op]
  refine runL_append_normal (iha hS ha) (runL_evRun st ?_)
  simpa [vals, List.reverse_append, List.append_assoc] using hk

/-- A call whose callee throws: impossible for a checked store and the native host slice. -/
theorem coreL_callThrow (hH : NativeHostSlice host) {t : Nat}
    (aha : ArityGood s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, .throw t))
    (q : List (Call (wasmHostSig H))) :
    CoreL P host s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t) q := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨⟨_, _, hok, _⟩, -, -⟩ :=
    oracle_at (hostCall_sound (P := P) hH) hS inv1 hfi hty hp hcall f₁
  exact absurd hok id

end CallCases

section BlockCases

variable {bt : BlockType} {np nr : Nat}

theorem coreL_blockOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGood s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreL P host s f (stk.take np) body (s₁, f₁, fl) q₁) (hvs : fl.blockVals = some vs)
    (ihk : CoreL P host s₁ f₁ (vs.take nr ++ stk.drop np) es r q₂) :
    CoreL P host s f stk (.block bt body :: es) r (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
  rw [code_block]
  exact runL_block_vals har hp (ihb hS hbc) hvs hnr hnorm hk

theorem coreL_blockAbrupt {fl' : Binaryen.Flow} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGood s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreL P host s f (stk.take np) body (s₁, f₁, fl) q₁)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreL P host s f stk (.block bt body :: es) (s₁, f₁, fl') q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_block]
  exact runL_block_abrupt har hp (ihb hS hbc) hfl

theorem coreL_loopOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGood s f (stk.take np) body (s₁, f₁, .normal vs))
    (ihb : CoreL P host s f (stk.take np) body (s₁, f₁, .normal vs) q₁)
    (ihk : CoreL P host s₁ f₁ (vs.take nr ++ stk.drop np) es r q₂) :
    CoreL P host s f stk (.loop bt body :: es) r (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hlen : vs.length = nr := length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hlen.ge h2)
  rw [code_loop]
  exact runL_loop_normal har hp (ihb hS hbc) hlen hk

theorem coreL_loopBack (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGood s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ihb : CoreL P host s f (stk.take np) body (s₁, f₁, .brk 0 vs) q₁)
    (ihk : CoreL P host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r q₂) :
    CoreL P host s f stk (.loop bt body :: es) r (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  obtain ⟨m, hm, hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hc' : chk s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
    rw [hlen]
    exact chk_inv inv1 hc
  have hk := ihk (storeChk_inv inv1 hS) hc'
  rw [code_loop] at hk ⊢
  exact runL_loop_back har hp (ihb hS hbc) hnp hk

theorem coreL_loopAbrupt {fl' : Binaryen.Flow} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGood s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreL P host s f (stk.take np) body (s₁, f₁, fl) q₁)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreL P host s f stk (.loop bt body :: es) (s₁, f₁, fl') q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_loop]
  exact runL_loop_abrupt har hp (ihb hS hbc) hfl

theorem coreL_ifOk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGood s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ihc : CoreL P host s f stk c (s₁, f₁, .normal (cv :: stk₁)) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : ArityGood s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (iharm : CoreL P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) q₂)
    (hvs : fl.blockVals = some vs)
    (ihk : CoreL P host s₂ f₂ (vs.take nr ++ stk₁.drop np) es r q₃) :
    CoreL P host s f stk (.if_ bt c t el :: es) r (q₁ ++ q₂ ++ q₃) := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, hob, hok, inv1, inv2, hp, h2⟩ := if_facts hS hcond har harm hc
  have hS1 : StoreChk s₁.funcs := storeChk_inv inv1 hS
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv2 hS1) (chk_after inv2 hp hnr h2)
  have hwb := runL_block_vals har hp (iharm hS1 hbc) hvs hnr hnorm hk
  rw [code_if, show q₁ ++ q₂ ++ q₃ = q₁ ++ (q₂ ++ q₃) from List.append_assoc _ _ _]
  exact runL_append_normal (ihc hS hco) (runL_if_arm hb hwb)

theorem coreL_ifAbrupt {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {fl' : Binaryen.Flow}
    (hcond : ArityGood s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ihc : CoreL P host s f stk c (s₁, f₁, .normal (cv :: stk₁)) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : ArityGood s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (iharm : CoreL P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) q₂)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreL P host s f stk (.if_ bt c t el :: es) (s₂, f₂, fl') (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, -, -, inv1, -, hp, -⟩ := if_facts hS hcond har harm hc
  have hwb := runL_block_abrupt (rest := expression (Binaryen.BExpr.lowerList es)) har hp
    (iharm (storeChk_inv inv1 hS) hbc) hfl
  rw [code_if]
  exact runL_append_normal (ihc hS hco) (runL_if_arm hb hwb)

theorem coreL_ifAbort {bt : BlockType} {c t el : List Binaryen.BExpr}
    (ihc : CoreL P host s f stk c (s₁, f₁, fl) q₁) (hfl : ¬ fl.IsNormal) :
    CoreL P host s f stk (.if_ bt c t el :: es) (s₁, f₁, fl) q₁ := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if]
  exact runL_append_abrupt (ihc hS hco) hfl

end BlockCases

end Cases

/-! ## The simulation -/

/-- **The logged forward simulation of `EvalL`**, every profile: a logged run whose calls
`GoodC` resolves to a consistent `q` is an `EvalH` run, and a Core run with exactly the host
events `q`. -/
theorem evalL_fwd (hH : NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {l : List (OCall H)} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalL s f stk es l r) :
    ∀ q, Shape.SubstPre (GoodC P host) (l.map OCall.lift) q → Cons host q →
      EvalH host s f stk es r ∧ CoreL P host s f stk es r q := by
  induction h with
  | nil =>
    intro q hq _
    cases hq
    exact ⟨.nil, coreL_nil⟩
  | argsAbort _ hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.argsAbort d hfl, coreL_argsAbort c hfl⟩
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ r hargs hfi hty _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append, List.map_cons] at hq
    obtain ⟨q₁, q₂', rfl, h₁, h₂⟩ := substPre_append.1 hq
    obtain ⟨c₁, q₂, rfl, hm, h₃⟩ := substPre_mk h₂
    rw [cons_append, cons_append] at hc
    obtain ⟨bfl, w, hC, hvs, hws, hrun⟩ :=
      goodC_inl hm hc.2.1 (Silmaril.Wasm.Interp.funcs_of_func? hfi) hty
    obtain ⟨d₁, c₁'⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂'⟩ := ih₂ q₂ h₃ hc.2.2
    refine ⟨.callOk d₁ hfi hty hC hvs (hws ▸ d₂), ?_⟩
    exact coreL_callOk hH (evalH_good (P := P) hH d₁).1 c₁' hfi hty hC hvs hws
      (fun hS hn => hrun hS hn f₁) c₂'
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t l₁ hargs hfi hty ih =>
    intro q hq hc
    rw [List.map_append, List.map_cons, List.map_nil] at hq
    obtain ⟨q₁, q₂', rfl, h₁, h₂⟩ := substPre_append.1 hq
    obtain ⟨c₁, q₂, rfl, hm, h₃⟩ := substPre_mk h₂
    rw [cons_append, cons_append] at hc
    have hC := goodC_inr hm hc.2.1
    obtain ⟨d₁, -⟩ := ih q₁ h₁ hc.1
    exact ⟨.callThrow d₁ hfi hty hC, coreL_callThrow hH (evalH_good (P := P) hH d₁).1 hfi hty hC _⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.opOk hi d₁ hflat d₂, coreL_opOk (evalH_good (P := P) hH d₁).1 c₁ hi hflat c₂⟩
  | opStop hi _ hflat hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.opStop hi d hflat hfl, coreL_opStop (evalH_good (P := P) hH d).1 c hflat hfl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.blockOk har d₁ hvs d₂, coreL_blockOk har (evalH_good (P := P) hH d₁).1 c₁ hvs c₂⟩
  | blockBrk har _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.blockBrk har d, coreL_blockAbrupt har (evalH_good (P := P) hH d).1 c (.inl ⟨_, _, rfl, rfl⟩)⟩
  | blockEsc har _ hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.blockEsc har d hfl, coreL_blockAbrupt har (evalH_good (P := P) hH d).1 c (.inr ⟨hfl, rfl⟩)⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.loopOk har d₁ d₂, coreL_loopOk har (evalH_good (P := P) hH d₁).1 c₁ c₂⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.loopBack har d₁ d₂, coreL_loopBack har (evalH_good (P := P) hH d₁).1 c₁ c₂⟩
  | loopBrk har _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.loopBrk har d, coreL_loopAbrupt har (evalH_good (P := P) hH d).1 c (.inl ⟨_, _, rfl, rfl⟩)⟩
  | loopEsc har _ hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.loopEsc har d hfl, coreL_loopAbrupt har (evalH_good (P := P) hH d).1 c (.inr ⟨hfl, rfl⟩)⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro q hq hc
    rw [List.map_append, List.map_append] at hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := substPre_append.1 hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 h₁₂
    rw [cons_append, cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.1.2
    obtain ⟨d₃, c₃⟩ := ih₃ q₃ h₃ hc.2
    exact ⟨.ifOk d₁ hb har d₂ hvs d₃,
      coreL_ifOk (evalH_good (P := P) hH d₁).1 c₁ hb har (evalH_good (P := P) hH d₂).1 c₂ hvs c₃⟩
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.ifBrk d₁ hb har d₂, coreL_ifAbrupt (evalH_good (P := P) hH d₁).1 c₁ hb har
      (evalH_good (P := P) hH d₂).1 c₂ (.inl ⟨_, _, rfl, rfl⟩)⟩
  | ifEsc _ hb har _ hfl ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    exact ⟨.ifEsc d₁ hb har d₂ hfl, coreL_ifAbrupt (evalH_good (P := P) hH d₁).1 c₁ hb har
      (evalH_good (P := P) hH d₂).1 c₂ (.inr ⟨hfl, rfl⟩)⟩
  | ifAbort _ hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.ifAbort d hfl, coreL_ifAbort c hfl⟩

/-! ## The closure -/

/-- **Every closed behaviour is in `GoodC`**: least-fixpoint induction. -/
theorem close_le_goodC (hH : NativeHostSlice host) :
    Shape.close (wasmHOpen (H := H)) ≤ GoodC P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩ b s'' hy hq
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩
  · obtain ⟨hpre, he⟩ := subst_ret hS hy
    have hs'' : s'' = s' := by
      rw [hy] at he
      rcases fl <;> simp_all [endOfFlow]
    subst hs''
    obtain ⟨d, cl⟩ := evalL_fwd hH hE y.1 hpre hq
    have hcall : hostCall host s a us (s'', bfl) := by
      rw [hostCall_fixpoint]
      exact .inl ⟨fi, fn, ps, rs, _, hfi, hc, hty, d⟩
    refine ⟨fi, ps, rs, bfl, fl, hfi, hty, hcall, hxf, by rw [← hy, he], ?_⟩
    intro hSt hn ws hfl g
    subst hfl
    have hrun := evRun_callRef_of_good hSt hn hfi hc hty (evalH_good (P := P) hH d).1 cl g
    rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t <;>
      simp only [exitFlow, Option.some.injEq, reduceCtorEq, Binaryen.Flow.normal.injEq] at hxf
    all_goals subst hxf
    all_goals exact hrun w rfl
  · cases hS with
    | ext h =>
      cases h
      have hm : host hh s us (.returned s' r) := hq _ List.mem_cons_self
      have hs'' : s'' = s' := by
        rcases fl <;> simp_all [endOfFlow]
      subst hs''
      refine ⟨fi, ps, rs, resFlow r, fl, hfi, hty, ?_, hxf, hy, ?_⟩
      · rw [hostCall_fixpoint]
        exact .inr ⟨fi, hh, r, hfi, hc, hm, rfl⟩
      · intro _ hn ws hfl g
        subst hfl
        obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
        rcases r with w | t | _ <;> simp only [resFlow, exitFlow, Option.some.injEq,
          reduceCtorEq, Binaryen.Flow.normal.injEq] at hxf
        have hw := hH.arity s a fi hh ps rs us w s'' hfi hc hty hm
        have hwr : (w.reverse.take rs.length).reverse = w := by
          rw [List.take_of_length_le (by simp [hw])]
          simp
        rw [← hxf, hwr]
        exact .event (hEvStep_host_call hfi he' (hn.trans hpl.symm) hc hm) (.refl _)

/-- **A returning closed behaviour with a consistent log is a Core run of the call** with
exactly that log, in any frame, every profile. -/
theorem close_ret_evRun (hH : NativeHostSlice host) {a : Nat} {s s₂ : Store H} {us ws : List Val}
    {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, .ret (.inl ws) s₂) ∈ Shape.close wasmHOpen a s us) (hc : Cons host c₁)
    (hS : StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (f : Frame) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ c₁ ⟨s₂, f, vals ws⟩ := by
  obtain ⟨_, _, -, -, -, hrun⟩ := goodC_inl (close_le_goodC (P := P) hH a s us hm) hc hfi hty
  exact hrun hS hn f

/-- **A returning behaviour of an invocation with a consistent log is a Core run of the
invocation with exactly that log**, every profile. -/
theorem wasmEvFun_evRun (hH : NativeHostSlice host) {s s₂ : Store H} {a : Nat}
    {vs ws : List Val} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s₂) ∈ wasmEvFun s (a, vs))
    (hc : Cons host cs) : EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ := by
  obtain ⟨fi, ps, rs, hfi, hty⟩ : ∃ fi ps rs, s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
    obtain ⟨fi', ps', rs', -, -, hfi', hty', -⟩ :=
      close_le_goodC (P := P) hH a s vs h _ _ rfl hc
    exact ⟨fi', ps', rs', hfi', hty'⟩
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv]
  exact close_ret_evRun hH h hc hS hfi hty (args_length hok hfi hty) {}

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
