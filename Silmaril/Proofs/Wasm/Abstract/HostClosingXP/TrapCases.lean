module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Calls

/-!
# Logged runs cut at a trapping callee (proofs)

A run whose `k`-th call's callee traps is, in Core, the logged run up to that call, the callee's
logged run to a trap, and the trap leaving every context (`trap` in a sequence, `trap-label`,
`trap-handler`, `trap-frame`). `CoreLT` is the invariant (postcondition `TrapPost`); the cases
here are the positions of the trapping call: in the arguments, a body, a condition or an arm
(the trap propagates out), or at the call itself (`coreLT_call`, `coreLT_ir`). A trapping call in
a continuation is the generalised continuation cases of `Cases` and `Calls` at `TrapPost`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **A logged run of a callee to a trap** in any caller frame, from any `call_ref` form, with
the host events `qc`, in some store. -/
def CalleeTrap (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (a : Nat) (us : List Val) (qc : List (Call (wasmHostSig H))) : Prop :=
  ∀ (f : Frame) (c : Admin), c.IsCallRef →
    ∃ s', EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ qc ⟨s', f, [.trap]⟩

section Trap

variable {s s₁ : Store H} {f f₁ : Frame} {q q₁ q₂ : List (Call (wasmHostSig H))}

theorem trap_of_ends {c' : List Admin} {o : Outcome} (he : o.Ends c') (ho : o = .trap) :
    c' = [.trap] := by
  subst ho
  exact he

/-- A trap is a final form for `TrapPost`, in a value prefix and before code. -/
theorem wp_trapPost (pre : List Val) (rest : List Admin) :
    WP P NH s f (vals pre ++ [.trap] ++ rest) TrapPost := by
  simpa using wp_trap (P := P) (host := NH) (s := s) (f := f) (vs := pre) (rest := rest)
    (Q := TrapPost) rfl

/-- **A trap leaves a sequence context.** -/
theorem wpl_trap_seq {c : List Admin} (pre : List Val) (rest : List Admin)
    (h : WPL P host ⟨s, f, c⟩ q TrapPost) :
    WPL P host ⟨s, f, vals pre ++ c ++ rest⟩ q TrapPost :=
  wpl_wrap (Wseq pre rest) (hW_seq pre rest) h fun _ _ _ _ he ho => by
    rw [trap_of_ends he ho]
    exact wp_trapPost pre rest

/-- **A trap leaves a label entered host-free.** -/
theorem wpl_trap_label {code body : List Admin} {pre : List Val} {rest : List Admin} {n : Nat}
    {cont : List Instr}
    (enter : Steps P NH ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.label n cont body] ++ rest⟩)
    (hb : WPL P host ⟨s, f, body⟩ q TrapPost) : WPL P host ⟨s, f, code⟩ q TrapPost :=
  wpl_free enter (wpl_wrap (Wlab pre rest n cont) (hW_lab pre rest n cont) hb
    fun s' f' _ _ he ho => by
      rw [trap_of_ends he ho]
      exact WP.steps (Steps.ctx (P := P) (host := NH) pre rest (.single Step.trapLabel))
        (wp_trapPost pre rest))

/-- **A trap leaves a `try_table`'s label and handler entered host-free.** -/
theorem wpl_trap_try {code body : List Admin} {pre : List Val} {rest : List Admin} {n : Nat}
    {cs : List Catch}
    (enter : Steps P NH ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.handler n cs [.label n [] body]] ++ rest⟩)
    (hb : WPL P host ⟨s, f, body⟩ q TrapPost) : WPL P host ⟨s, f, code⟩ q TrapPost :=
  wpl_free enter (wpl_wrap (Wtry pre rest n cs) (hW_try pre rest n cs) hb
    fun s' f' _ _ he ho => by
      rw [trap_of_ends he ho]
      have hout : Steps P NH ⟨s', f', [.handler n cs [.label n [] [.trap]]]⟩ ⟨s', f', [.trap]⟩ :=
        (Steps.handler (Relation.ReflTransGen.single Step.trapLabel)).tail Step.trapHandler
      exact WP.steps (Steps.ctx (P := P) (host := NH) pre rest hout) (wp_trapPost pre rest))

/-- **A trap leaves a callee's label and frame.** -/
theorem steps_trap_frame {n : Nat} {F : Frame} :
    Steps P NH ⟨s, f, [.frame n F [.label n [] [.trap]]]⟩ ⟨s, f, [.trap]⟩ :=
  (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame

end Trap

section Cases

variable {tags : List TagInst} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
  {stk stk₁ vs : List Val} {es args body : List Binaryen.BExpr} {i : Instr}
  {q q₁ q₂ qc : List (Call (wasmHostSig H))} {bt : BlockType} {cs : List Catch} {np nr : Nat}

theorem coreLT_args (iha : CoreLT tags P host s f stk args q) :
    CoreLT tags P host s f stk (.op i args :: es) q := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  simpa using wpl_trap_seq [] (.plain i :: expression (Binaryen.BExpr.lowerList es)) (iha hS ha)

theorem coreLT_block (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLT tags P host s f (stk.take np) body q) :
    CoreLT tags P host s f stk (.block bt body :: es) q := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_block]
  exact wpl_trap_label (steps_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har) _) (ihb hS hbc)

theorem coreLT_loop (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLT tags P host s f (stk.take np) body q) :
    CoreLT tags P host s f stk (.loop bt body :: es) q := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_loop]
  exact wpl_trap_label (steps_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) _) (ihb hS hbc)

theorem coreLT_ifCond {c t el : List Binaryen.BExpr} (ihc : CoreLT tags P host s f stk c q) :
    CoreLT tags P host s f stk (.if_ bt c t el :: es) q := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if]
  simpa using wpl_trap_seq [] _ (ihc hS hco)

theorem coreLT_ifArm {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE (ehExt tags) s f stk c (s₁, f₁, .normal (cv :: stk₁)) true)
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : CoreLT tags P host s₁ f₁ (stk₁.take np) (if b then t else el) q₂) :
    CoreLT tags P host s f stk (.if_ bt c t el :: es) (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hbarm, -⟩ := arity_if_pre (b := b) hS hcond har hc
  replace hbarm := chk_inv_endsAt inv1 hbarm
  obtain ⟨ob, hb', -⟩ := endsAt_eq hbarm
  have hbc : chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [take_length_of_le hp]; exact hb'
  obtain ⟨o'', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  have hwb := wpl_trap_label (steps_enter (P := P) (host := NH) hp (step_block har)
    (expression (Binaryen.BExpr.lowerList es))) (iharm (storeChk_inv inv1 hS) hbc)
  rw [code_if]
  exact wpl_append_normal (ihc hS hco) (wpl_if_arm hb hwb)

theorem coreLT_try (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLT tags P host s f (stk.take np) body q) :
    CoreLT tags P host s f stk (.tryTable bt cs body :: es) q := by
  intro labels ret out hS hc
  obtain ⟨hp, ob, hbc⟩ := try_body_chk har hc
  rw [code_tryTable]
  exact wpl_trap_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp _)
    (ihb hS hbc)

variable {x : FuncIdx} {a fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
  {y : TypeIdx}

/-- **A call whose callee traps.** -/
theorem coreLT_call (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeTrap P host s₁ a (stk₁.take ps.length).reverse qc) :
    CoreLT tags P host s f stk (.op (.call x) args :: es) (q₁ ++ qc) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨s', hst⟩ := hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.callRefType fi.type) trivial
  have st := evRun_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi hst
  rw [code_op, show q₁ ++ qc = q₁ ++ (qc ++ []) by simp]
  exact wpl_append_normal (iha hS ha) (wpl_evRun st (wpl_of_wp (wp_trapPost _ _)))

/-- **An indirect or reference call whose callee traps.** -/
theorem coreLT_ir {top : Val} (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (top :: stk₁))) q₁)
    (hpre : Steps P NH ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeTrap P host s₁ fa (stk₁.take ps.length).reverse qc) :
    CoreLT tags P host s f stk (.op i args :: es) (q₁ ++ qc) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preP hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := NH) stk₁.reverse E hpre
  obtain ⟨s', hst⟩ := hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.plain (.callRef y))
    trivial
  have st₂ := evRun_callRef (rest := E) hst
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op, show q₁ ++ qc = q₁ ++ (qc ++ []) by simp]
  refine wpl_append_normal (iha hS ha) ?_
  rw [e]
  exact wpl_free st₁ (wpl_evRun st₂ (wpl_of_wp (wp_trapPost _ _)))

end Cases

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
