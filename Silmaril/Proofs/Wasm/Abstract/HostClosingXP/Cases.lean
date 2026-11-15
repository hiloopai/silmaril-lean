module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Struct

/-!
# The cases of the logged canonical simulation (proofs)

`CoreLP` for each rule of `EvalLXPh`: the corresponding case of `PendSim.evalOXP_goodP`, its
sub-runs logged, its glue host-free. A call is answered by a logged run of the callee
(`EvRun`, a hypothesis here), in the caller's frame; the arity facts of the answer come from
the canonical host oracle (`hostP`), as in `PendSim`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

section Cases

variable {tags : List TagInst} {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
  {stk stk₁ stk₂ vs : List Val} {es args body : List Binaryen.BExpr} {i : Instr}
  {fl : Binaryen.Flow} {r : Store H × Frame × POut} {o : POut}
  {q q₁ q₂ q₃ : List (Call (wasmHostSig H))} {bt : BlockType} {cs : List Catch} {np nr : Nat}
  {Q : Post H}

theorem coreLP_nil : CoreLP tags P host s f stk [] (s, f, .flow (.normal stk)) [] := by
  intro labels ret out _ _
  refine wpl_matchP (wpl_of_wp ?_)
  simpa using wp_vals (P := P) (host := NH) (s := s) (f := f) (vs := stk.reverse)
    (Q := Match (s, f, .normal stk)) ⟨rfl, rfl, rfl⟩

theorem coreLP_argsAbort (iha : CoreLP tags P host s f stk args (s₁, f₁, o) q)
    (ho : ¬ o.IsNormal) : CoreLP tags P host s f stk (.op i args :: es) (s₁, f₁, o) q := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  exact wpl_append_abruptP (iha hS ha) ho

theorem coreLP_opOk (hargs : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hi : ∀ x, i ≠ .call x)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : CoreLQ tags P host s₂ f₂ stk₂ es Q q₂) :
    CoreLQ tags P host s f stk (.op i args :: es) Q (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS hargs h1
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  replace hf := flatChk_of_evalFlat hflat hf
  obtain ⟨ho, inv2⟩ := flat_normal (ext := ehExt tags) hflat hf
  have inv12 : EvalInvE (ehExt tags) s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
  have h2' : chkE (ehExt tags) s₂.funcs f₂.module f₂.locals.length ret labels
      (some stk₂.length) es = some out := by
    rw [← ho]
    exact chk_inv inv12 h2
  have st := steps_flat_normal (P := P) (host := NH) hi hf hflat
    (expression (Binaryen.BExpr.lowerList es))
  rw [code_op]
  exact wpl_append_normal (iha hS ha) (wpl_free st (ihk (storeChk_inv inv12 hS) h2'))

theorem coreLP_opStop (hargs : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
    CoreLP tags P host s f stk (.op i args :: es) (s₂, f₂, .flow fl) q₁ := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS hargs h1
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  replace hf := flatChk_of_evalFlat hflat hf
  rw [code_op, ← List.append_nil q₁]
  exact wpl_append_normal (iha hS ha)
    (wpl_matchP (wpl_of_wp (wp_flat_abrupt (P := P) (host := NH) hf hflat hfl _)))

/-! ### Blocks, loops, conditionals -/

theorem coreLP_blockOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) true)
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow fl) q₁)
    (hvs : fl.blockVals = some vs)
    (ihk : CoreLQ tags P host s₁ f₁ (vs.take nr ++ stk.drop np) es Q q₂) :
    CoreLQ tags P host s f stk (.block bt body :: es) Q (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
  rw [code_block]
  exact wpl_block_vals har hp (ihb hS hbc) hvs hnr hnorm hk

theorem coreLP_blockBrk {k : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs)) q₁) :
    CoreLP tags P host s f stk (.block bt body :: es) (s₁, f₁, .flow (.brk k vs)) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_block]
  exact wpl_block_brk har hp (ihb hS hbc)

theorem coreLP_blockEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, o) q₁) (ho : o.Escapes) :
    CoreLP tags P host s f stk (.block bt body :: es) (s₁, f₁, o) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_block]
  exact wpl_label_esc (steps_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_block har) _) (ihb hS hbc) ho

theorem coreLP_loopOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .normal vs) true)
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.normal vs)) q₁)
    (ihk : CoreLQ tags P host s₁ f₁ (vs.take nr ++ stk.drop np) es Q q₂) :
    CoreLQ tags P host s f stk (.loop bt body :: es) Q (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hlen : vs.length = nr := length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hlen.ge h2)
  rw [code_loop]
  exact wpl_loop_normal har hp (ihb hS hbc) hlen hk

theorem coreLP_loopBack (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .brk 0 vs) true)
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.brk 0 vs)) q₁)
    (ihk : CoreLQ tags P host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) Q q₂) :
    CoreLQ tags P host s f stk (.loop bt body :: es) Q (q₁ ++ q₂) := by
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
  have hc' : chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
    rw [hlen]
    exact chk_inv inv1 hc
  have hk := ihk (storeChk_inv inv1 hS) hc'
  rw [code_loop] at hk ⊢
  exact wpl_loop_back har hp (ihb hS hbc) hnp hk

theorem coreLP_loopBrk {k : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs)) q₁) :
    CoreLP tags P host s f stk (.loop bt body :: es) (s₁, f₁, .flow (.brk k vs)) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_loop]
  exact wpl_loop_brk har hp (ihb hS hbc)

theorem coreLP_loopEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, o) q₁) (ho : o.Escapes) :
    CoreLP tags P host s f stk (.loop bt body :: es) (s₁, f₁, o) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  have hbc : chkE (ehExt tags) s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [take_length_of_le hp]; exact hb'
  rw [code_loop]
  exact wpl_label_esc (steps_enter (P := P) (host := NH) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (step_loop har) _) (ihb hS hbc) ho

theorem coreLP_ifOk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE (ehExt tags) s f stk c (s₁, f₁, .normal (cv :: stk₁)) true)
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : ArityGoodE (ehExt tags) s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) true)
    (iharm : CoreLP tags P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .flow fl) q₂)
    (hvs : fl.blockVals = some vs)
    (ihk : CoreLQ tags P host s₂ f₂ (vs.take nr ++ stk₁.drop np) es Q q₃) :
    CoreLQ tags P host s f stk (.if_ bt c t el :: es) Q (q₁ ++ q₂ ++ q₃) := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, hob, hok, inv1, inv2, hp, h2⟩ := if_facts hS hcond har harm hc
  have hS1 : StoreChkE (ehExt tags) s₁.funcs := storeChk_inv inv1 hS
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv2 hS1) (chk_after inv2 hp hnr h2)
  have hwb := wpl_block_vals har hp (iharm hS1 hbc) hvs hnr hnorm hk
  rw [code_if, show q₁ ++ q₂ ++ q₃ = q₁ ++ (q₂ ++ q₃) from List.append_assoc _ _ _]
  exact wpl_append_normal (ihc hS hco) (wpl_if_arm hb hwb)

/-- The arm of an `if` left by a branch, a return, a trap, a throw or a pending tail call. -/
theorem coreLP_ifAbrupt {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {o' : POut}
    (hcond : ArityGoodE (ehExt tags) s f stk c (s₁, f₁, .normal (cv :: stk₁)) true)
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : CoreLP tags P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o) q₂)
    (hblk : ∀ {rest : List Admin}, np ≤ stk₁.length →
      WPL P host ⟨s₁, f₁, vals (stk₁.take np).reverse ++
        expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ q₂ (MatchP (s₂, f₂, o)) →
      WPL P host ⟨s₁, f₁, vals stk₁.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ q₂
        (MatchP (s₂, f₂, o'))) :
    CoreLP tags P host s f stk (.if_ bt c t el :: es) (s₂, f₂, o') (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hbarm, -⟩ := arity_if_pre (b := b) hS hcond har hc
  replace hbarm := chk_inv_endsAt inv1 hbarm
  obtain ⟨ob, hb', -⟩ := endsAt_eq hbarm
  have hbc : chkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [take_length_of_le hp]; exact hb'
  obtain ⟨o'', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  have hwb := hblk (rest := expression (Binaryen.BExpr.lowerList es)) hp
    (iharm (storeChk_inv inv1 hS) hbc)
  rw [code_if]
  exact wpl_append_normal (ihc hS hco) (wpl_if_arm hb hwb)

theorem coreLP_ifBrk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {k : Nat}
    (hcond : ArityGoodE (ehExt tags) s f stk c (s₁, f₁, .normal (cv :: stk₁)) true)
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : CoreLP tags P host s₁ f₁ (stk₁.take np) (if b then t else el)
      (s₂, f₂, .flow (.brk (k + 1) vs)) q₂) :
    CoreLP tags P host s f stk (.if_ bt c t el :: es) (s₂, f₂, .flow (.brk k vs)) (q₁ ++ q₂) :=
  coreLP_ifAbrupt hcond ihc hb har iharm fun hp h => wpl_block_brk har hp h

theorem coreLP_ifEsc {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : ArityGoodE (ehExt tags) s f stk c (s₁, f₁, .normal (cv :: stk₁)) true)
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) q₁)
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : CoreLP tags P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o) q₂)
    (ho : o.Escapes) :
    CoreLP tags P host s f stk (.if_ bt c t el :: es) (s₂, f₂, o) (q₁ ++ q₂) :=
  coreLP_ifAbrupt hcond ihc hb har iharm fun hp h =>
    wpl_label_esc (steps_enter (P := P) (host := NH) hp (step_block har) _) h ho

theorem coreLP_ifAbort {c t el : List Binaryen.BExpr}
    (ihc : CoreLP tags P host s f stk c (s₁, f₁, o) q₁) (ho : ¬ o.IsNormal) :
    CoreLP tags P host s f stk (.if_ bt c t el :: es) (s₁, f₁, o) q₁ := by
  intro labels ret out hS hc
  obtain ⟨o', h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  rw [code_if]
  exact wpl_append_abruptP (ihc hS hco) ho

/-! ### `try_table` -/

/-- The body of a checked `try_table`, checked. -/
theorem try_body_chk {labels : List Nat} {ret : Nat} {out : Option Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.tryTable bt cs body :: es) = some out) :
    np ≤ stk.length ∧ ∃ ob, chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨ob, hb', -⟩ := endsAt_eq hb
  exact ⟨hp, ob, by rw [take_length_of_le hp]; exact hb'⟩

theorem coreLP_tryOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) true)
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow fl) q₁)
    (hvs : fl.blockVals = some vs)
    (ihk : CoreLQ tags P host s₁ f₁ (vs.take nr ++ stk.drop np) es Q q₂) :
    CoreLQ tags P host s f stk (.tryTable bt cs body :: es) Q (q₁ ++ q₂) := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, h2⟩ := arity_try_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
  rw [code_tryTable]
  exact wpl_try_vals har hp (ihb hS hbc) hvs hnr hnorm hk

theorem coreLP_tryBrk {k : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.brk (k + 1) vs)) q₁) :
    CoreLP tags P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, .flow (.brk k vs)) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, ob, hbc⟩ := try_body_chk har hc
  rw [code_tryTable]
  exact wpl_try_brk har hp (ihb hS hbc)

theorem coreLP_tryEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, o) q₁) (ho : o.Escapes)
    (hnt : o.NotThrow) :
    CoreLP tags P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, o) q₁ := by
  intro labels ret out hS hc
  obtain ⟨hp, ob, hbc⟩ := try_body_chk har hc
  rw [code_tryTable]
  exact wpl_try_esc har hp (ihb hS hbc) ho hnt

theorem coreLP_tryCatch {a : Nat} {us : List Val} {l : LabelIdx}
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.throw a)) q₁)
    (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
    CoreLP tags P host s f stk (.tryTable bt cs body :: es)
      (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np))) q₁ := by
  intro labels ret out hS hck
  obtain ⟨hp, ob, hbc⟩ := try_body_chk har hck
  rw [code_tryTable]
  exact wpl_try_catch har hp (ihb hS hbc) hc

theorem coreLP_tryRethrow {a : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : CoreLP tags P host s f (stk.take np) body (s₁, f₁, .flow (.throw a)) q₁)
    (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
    CoreLP tags P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, .flow (.throw a)) q₁ := by
  intro labels ret out hS hck
  obtain ⟨hp, ob, hbc⟩ := try_body_chk har hck
  rw [code_tryTable]
  exact wpl_try_rethrow har hp (ihb hS hbc) hc

/-! ### Operators ending the run after their arguments -/

/-- An operator whose arguments complete normally, then a host-free run. -/
theorem coreLP_after_args {stk' : List Val} {r' : Store H × Frame × POut}
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk')) q₁)
    (hk : ∀ {labels : List Nat} {ret : Nat} {out : Option Nat},
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
        (.op i args :: es) = some out →
      WP P NH s₁ f₁ (vals stk'.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es))
        (MatchP r')) :
    CoreLP tags P host s f stk (.op i args :: es) r' q₁ := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op, ← List.append_nil q₁]
  exact wpl_append_normal (iha hS ha) (wpl_of_wp (hk hc))

theorem coreLP_throw {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
    (hn : ts.length ≤ stk₁.length) :
    CoreLP tags P host s f stk (.op (.throw x) args :: es)
      (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .flow (.throw s₁.exns.length)) q₁ :=
  coreLP_after_args iha fun _ => by
    rw [rev_take_drop stk₁ ts.length]
    exact wpP_of_wp (wp_throw ht he (by simp only [List.length_reverse, List.length_take]; omega)
      ⟨rfl, rfl, rfl⟩)

theorem coreLP_throwRefNull
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (.ref .null :: stk₁))) q₁) :
    CoreLP tags P host s f stk (.op .throwRef args :: es) (s₁, f₁, .flow .trap) q₁ :=
  coreLP_after_args iha fun _ => wpP_of_wp (by
    simpa using wp_throwRef_null (P := P) (host := NH) (s := s₁) (f := f₁) (vs := stk₁.reverse)
      (rest := expression (Binaryen.BExpr.lowerList es)) (Q := Match (s₁, f₁, .trap))
      ⟨rfl, rfl, trivial⟩)

theorem coreLP_throwRefExn {a : Nat}
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (.ref (.exn a) :: stk₁))) q₁) :
    CoreLP tags P host s f stk (.op .throwRef args :: es) (s₁, f₁, .flow (.throw a)) q₁ :=
  coreLP_after_args iha fun _ => by
    have e : vals (Val.ref (.exn a) :: stk₁).reverse ++
        .plain .throwRef :: expression (Binaryen.BExpr.lowerList es) =
        vals stk₁.reverse ++ throwing a ++ expression (Binaryen.BExpr.lowerList es) := by
      simp [vals, Val.toAdmin]
    rw [e]
    exact wpP_of_wp (wp_throwing ⟨rfl, rfl, rfl⟩)

/-- An indirect or reference call that traps before any call. -/
theorem coreLP_irTrap {top : Val}
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (top :: stk₁))) q₁)
    (hpre : Steps P NH ⟨s₁, f₁, vals [top] ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
    CoreLP tags P host s f stk (.op i args :: es) (s₁, f₁, .flow .trap) q₁ :=
  coreLP_after_args iha fun _ => by
    let E := expression (Binaryen.BExpr.lowerList es)
    have st₁ := Steps.ctx (P := P) (host := NH) stk₁.reverse E hpre
    have e : vals (top :: stk₁).reverse ++ .plain i :: E =
        vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
    rw [e]
    refine wpP_of_wp ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
    simpa using steps_trap (P := P) (host := NH) s₁ f₁ stk₁.reverse E

/-- **A resolved tail call ends the body in Core's pending tail call.** -/
theorem coreLP_tail {fa n m : Nat}
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk₁.drop (tailPop i)))) :
    CoreLP tags P host s f stk (.op i args :: es)
      (s₁, f₁, .tail fa ((stk₁.drop (tailPop i)).take n).reverse m) q₁ :=
  coreLP_after_args iha fun _ => by
    obtain ⟨c, hcr, -, hpre⟩ := tailRes_steps (P := P) (host := NH) hres
    let E := expression (Binaryen.BExpr.lowerList es)
    have st := Steps.ctx (P := P) (host := NH) (stk₁.drop (tailPop i)).reverse E hpre
    have e : vals stk₁.reverse ++ .plain i :: E = vals (stk₁.drop (tailPop i)).reverse ++
        (vals (stk₁.take (tailPop i)).reverse ++ [.plain i]) ++ E := by
      rw [rev_take_drop stk₁ (tailPop i)]; simp [vals]
    rw [e]
    refine WP.steps st ?_
    have hw := wp_tailP (P := P) (host := NH) (s₁ := s₁) (f₁ := f₁) (a := fa) (n := m)
      (vs₁ := ((stk₁.drop (tailPop i)).drop n).reverse)
      (args := ((stk₁.drop (tailPop i)).take n).reverse) hcr [] [] E
    rw [← rev_take_drop] at hw
    simpa using hw

/-- **An unresolved tail call traps.** -/
theorem coreLP_tailRes
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hres : TailRes s₁ f₁ i stk₁ none) :
    CoreLP tags P host s f stk (.op i args :: es) (s₁, f₁, .flow .trap) q₁ :=
  coreLP_after_args iha fun _ => by
    let E := expression (Binaryen.BExpr.lowerList es)
    cases hres with
    | @indirectTrap x y ad j stk hres' =>
      have e : vals (Val.num ⟨.int ad.intType, j⟩ :: stk).reverse ++
          .plain (.returnCallIndirect x y) :: E =
          vals stk.reverse ++ [aconst ad j, .plain (.returnCallIndirect x y)] ++ E := by
        rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]
        simp
      rw [e]
      rcases Silmaril.Wasm.Abstract.CallRes.steps_returnCallIndirect_trap (P := P) (host := NH)
        hres' with st | st
      · have st₁ := Steps.ctx (P := P) (host := NH) stk.reverse E st
        refine wpP_of_wp ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
        simpa using steps_trap (P := P) (host := NH) s₁ f₁ stk.reverse E
      · have st₁ := Steps.ctx (P := P) (host := NH) stk.reverse E st
        refine WP.steps st₁ ?_
        have hw := wp_tailNullP (P := P) (host := NH) (s₁ := s₁) (f₁ := f₁) (vs := stk.reverse)
          (c := .plain (.returnCallRef y)) trivial [] E []
        simpa [vals] using hw
    | @refNull y stk =>
      have hw := wp_tailNullP (P := P) (host := NH) (s₁ := s₁) (f₁ := f₁) (vs := stk.reverse)
        (c := .plain (.returnCallRef y)) trivial [] E []
      simpa [vals, Val.toAdmin] using hw

end Cases

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
