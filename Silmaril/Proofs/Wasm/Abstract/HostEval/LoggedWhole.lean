module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedCall
public import Silmaril.Proofs.Wasm.Abstract.HostEval.Invoke

/-!
# The logged whole-run backward simulation, and exact pending agreement (proofs)

`back_wholeL`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers (`HostTyped`) in the native host slice (`Interp.NativeHostSlice`), every labelled Core
run (`EvRunN`, with its exact log `cs`) of lowered, arity-checked, typed trees to an end with
no host-free step satisfies `BackOutL`: it is the end of an `EvalH` run that, unless it traps,
is a logged run whose calls resolve to exactly `cs`; or it is at a host call pending after
exactly `cs` (`PendT`). The induction (`BackGoalL`) and the discharge of the hypotheses are
those of `back_whole` (`Whole`), with the logged cases.

`invoke_pendL`, `evRun_pend`: a finite labelled Core run of a typed invocation, with its exact
host-event log `cs`, to a configuration at a host call `(hh, c.store, us)` (`decompose?`) is a
pending host call of the logged closed semantics after exactly that log: `(cs, (hh, c.store,
us)) ∈ wasmEvPend s (a, vs)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- The statement of the logged backward simulation for `n` steps of the trees `es`. -/
def BackGoalL (o : GrowOracle) (host : HostSemantics H) (n : Nat) (es : List Binaryen.BExpr) :
    Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat) (ret : Nat) (out : Option Nat)
    (c : Config H) (cs : List (Call (wasmHostSig H))), Interp.StoreChk s.funcs →
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
    EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs c →
    (∀ c', ¬ Step (profile o) Det.noHost c c') → BackOutL host s f stk es cs c

variable {o : GrowOracle}

/-- **The operator case** other than a call, logged. -/
theorem case_op_flatL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {i : Instr} {args es : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op i args :: es) →
      BackGoalL o host m es') :
    BackGoalL o host n (.op i args :: es) := by
  intro s f stk labels ret out c cs hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hta : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  have htyped : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk₁ hev
    have hr := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain i :: expression (Binaryen.BExpr.lowerList es))
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  refine back_op_flatL hi hrun hend ?_ ?_ ?_
  · intro m hm c₁ cs₁ h₁ hs₁
    exact ihle m hm args Interp.size_args s f stk labels ret oa c₁ cs₁ hS ha hta h₁ hs₁
  · intro s₁ f₁ stk₁ hev
    obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    exact ⟨Interp.evalFlat_progressH hf hi (htyped s₁ f₁ stk₁ hev),
      _, _, _, _, _, _, hf⟩
  · intro s₁ f₁ stk₁ s₂ f₂ stk₂ m cs' hm hev hfl hrun₂
    obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := host) hi hf hfl
      (expression (Binaryen.BExpr.lowerList es))
    have ht₂ : Sim.ContextTyped ⟨s₂, f₂, vals stk₂.reverse ++
        expression (Binaryen.BExpr.lowerList es)⟩ :=
      ContextTyped.steps_typed hT (htyped s₁ f₁ stk₁ hev) hst
    exact ihle m hm es Interp.size_tail s₂ f₂ stk₂ labels ret out c cs'
      (Interp.storeChk_inv inv12 hS) h2' ht₂ hrun₂ hend

/-- **The block case**, logged. -/
theorem case_blockL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.block bt body :: es) →
      BackGoalL o host m es') :
    BackGoalL o host n (.block bt body :: es) := by
  intro s f stk labels ret out c cs hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_block (body := body) stk bt es
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := by
    have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    exact Sim.ContextTyped.label (Sim.ContextTyped.steps (hcode ▸ ht) henter)
  refine back_block_treeL har hp hrun hend ?_ ?_ ?_
  · intro m hm cb cs₁ h hs
    exact ihle m hm body Interp.size_block s f (stk.take np) (nr :: labels) ret ob cb cs₁ hS hb'
      htb h hs
  · intro r hev vs hvs
    obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    exact ⟨Interp.blockVals_length hok hob hvs, fun ws hws => by
      rw [hws] at hok; exact Interp.length_of_ends hok hob⟩
  · intro s₁ f₁ fl vs m cs' hm hev hvs hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) inv1 hp hnr h2
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hb')
    have htg := Interp.tg_block_vals (P := profile o) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    have ht₁ := ContextTyped.steps_typed hT (hcode ▸ ht) htg.to_reflTransGen
    exact ihle m hm es Interp.size_tail s₁ f₁ _ labels ret out c cs'
      (Interp.storeChk_inv inv1 hS) h2' ht₁ hk hend

/-- **The loop case**, logged. -/
theorem case_loopL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ihlt : ∀ m < n, ∀ es', BackGoalL o host m es')
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.loop bt body :: es) →
      BackGoalL o host m es') :
    BackGoalL o host n (.loop bt body :: es) := by
  intro s f stk labels ret out c cs hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_loop (body := body) stk bt es
  have henter := Interp.steps_enter (P := profile o) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har)
    (expression (Binaryen.BExpr.lowerList es))
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ :=
    Sim.ContextTyped.label (ContextTyped.steps_typed hT (hcode ▸ ht) henter)
  have hinner : ∀ s₁ f₁ fl, EvalH host s f (stk.take np) body (s₁, f₁, fl) →
      ∃ c' o', Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
          (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
        ⟨s₁, f₁, vals (stk.drop np).reverse ++
          [.label np [.loop bt (Binaryen.BExpr.lowerList body)] c'] ++
          expression (Binaryen.BExpr.lowerList es)⟩ ∧ o'.Ends c' ∧ Interp.FlowMatch fl o' := by
    intro s₁ f₁ fl hev
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hb')
    refine ⟨c', o', ?_, he, hm'⟩
    rw [hcode]
    exact henter.trans (Silmaril.Wasm.Logic.Core.Steps.ctx _ _
      (Silmaril.Wasm.Logic.Core.Steps.label np _ hbr))
  refine back_loop_treeL har hp hrun hend ?_ ?_ ?_ ?_
  · intro m hm cb cs₁ h hs
    exact ihle m hm.le body Interp.size_loop s f (stk.take np) (np :: labels) ret ob cb cs₁ hS hb'
      htb h hs
  · intro r hev
    obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    refine ⟨fun ws hws => ?_, fun vs hvs => ?_⟩
    · rw [hws] at hok; exact Interp.length_of_ends hok hob
    · rw [hvs] at hok
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
  · intro s₁ f₁ vs m cs' hm hev hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hlen : vs.length = nr := Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) (vs := vs) inv1 hp hlen.ge h2
    obtain ⟨c', o', hst, he, hm'⟩ := hinner s₁ f₁ _ hev
    have hx := Interp.exit_normal (P := profile o) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    have htake : vs.take nr = vs := List.take_of_length_le hlen.le
    have ht₁ : Sim.ContextTyped ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList es)⟩ := by
      have := ContextTyped.steps_typed hT ht (hst.trans hx)
      rw [htake]
      simpa [List.reverse_append, List.append_assoc] using this
    exact ihle m hm.le es Interp.size_tail s₁ f₁ _ labels ret out c cs'
      (Interp.storeChk_inv inv1 hS) h2' ht₁ hk hend
  · intro s₁ f₁ vs m cs' hm hev hk
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    obtain ⟨c', o', hst, he, hm'⟩ := hinner s₁ f₁ _ hev
    have hx := Interp.exit_br0 (P := profile o) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' hnp (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    have ht₁ : Sim.ContextTyped ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
        expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ := by
      have := ContextTyped.steps_typed hT ht (hst.trans hx)
      rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression] using this
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact Interp.chk_inv inv1 hc
    exact ihlt m hm _ s₁ f₁ _ labels ret out c cs' (Interp.storeChk_inv inv1 hS) hc' ht₁ hk hend

/-- **The `if` case**, logged. -/
theorem case_ifL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.if_ bt cnd t el :: es) →
      BackGoalL o host m es') :
    BackGoalL o host n (.if_ bt cnd t el :: es) := by
  intro s f stk labels ret out c cs hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt cnd t el es
  have htc : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      expression (Binaryen.BExpr.lowerList cnd)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  have hafter : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
          (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
        ⟨s₁, f₁, vals stk'.reverse ++
          .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
          expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk' hev
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS hco)
  have harity : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      ∃ np nr, Binaryen.arity f₁ bt = some (np, nr) := by
    intro s₁ f₁ stk' hev
    obtain ⟨hoc, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hco
    obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
    exact ⟨np, nr, by rw [Interp.arity_eq, inv1.2.1]; exact ha⟩
  have hinfo : ∀ s₁ f₁ cv stk₁ b np nr, EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) →
      Binaryen.truthy cv = some b → Binaryen.arity f₁ bt = some (np, nr) →
      Interp.EvalInv s f (s₁, f₁, .normal (cv :: stk₁)) ∧ np ≤ stk₁.length ∧
      (∃ ob, (ob = none ∨ ob = some nr) ∧
        Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
          (some (stk₁.take np).length) (if b then t else el) = some ob) ∧
      Interp.chk s₁.funcs f₁.module f₁.locals.length ret labels
        (some (stk₁.length - np + nr)) es = some out ∧
      Sim.ContextTyped ⟨s₁, f₁, vals (stk₁.take np).reverse ++
        expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ := by
    intro s₁ f₁ cv stk₁ b np nr hev hb har
    obtain ⟨inv1, hp, hendArm, h2'⟩ :=
      Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := profile o) hH hev).1 har hc
    obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
    have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb'
    have ht₁ := ContextTyped.steps_typed hT ht (hafter _ _ _ hev)
    have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s₁) (f := f₁)
      (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    refine ⟨inv1, hp, ⟨ob, hob, hb''⟩, Interp.chk_inv inv1 h2', ?_⟩
    exact Sim.ContextTyped.label (Sim.ContextTyped.steps (Sim.ContextTyped.step ht₁ hif) henter)
  refine back_if_treeL hrun hend ?_ ?_ ?_ ?_
  · intro m hm c₁ cs₁ h hs
    exact ihle m hm cnd Interp.size_cond s f stk labels ret oc c₁ cs₁ hS hco htc h hs
  · intro s₁ f₁ stk' hev
    obtain ⟨np, nr, har⟩ := harity s₁ f₁ stk' hev
    obtain ⟨cv, stk₁, b, rfl, hb⟩ :=
      Interp.truthy_progressH (ContextTyped.steps_typed hT ht (hafter _ _ _ hev))
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, -, -⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    refine ⟨cv, stk₁, b, np, nr, rfl, hb, har, hp, fun r hevb vs hvs => ?_⟩
    obtain ⟨hok, -⟩ :=
      (Interp.evalH_good (P := profile o) hH hevb).1 (Interp.storeChk_inv inv1 hS) hb'
    exact ⟨Interp.blockVals_length hok hob hvs, fun ws hws => by
      rw [hws] at hok; exact Interp.length_of_ends hok hob⟩
  · intro s₁ f₁ cv stk₁ b np nr m hm hev hb har cb cs₁ h hs
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, -, htarm⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    exact ihle m hm _ (Interp.size_arm b) s₁ f₁ (stk₁.take np) (nr :: labels) ret ob cb cs₁
      (Interp.storeChk_inv inv1 hS) hb' htarm h hs
  · intro s₁ f₁ cv stk₁ b np nr s₂ f₂ fl vs m cs' hm hev hb har hevb hvs hk
    obtain ⟨inv1, hp, ⟨ob, hob, hb'⟩, h2₁, -⟩ := hinfo s₁ f₁ cv stk₁ b np nr hev hb har
    have hS₁ := Interp.storeChk_inv inv1 hS
    obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hb'
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    have h2₂ := Interp.chk_after (ext := Interp.noExt) inv2 hp hnr h2₁
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hevb).2 hS₁ hb')
    have htg := Interp.tg_block_vals (P := profile o) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    have hrun₂ := (hafter _ _ _ hev).trans
      ((Relation.ReflTransGen.single (Step.of_noHost host hif)).trans htg.to_reflTransGen)
    exact ihle m hm es Interp.size_tail s₂ f₂ _ labels ret out c cs'
      (Interp.storeChk_inv (inv1.trans inv2) hS) h2₂ (ContextTyped.steps_typed hT ht hrun₂) hk
      hend

/-- **The call case**, logged. -/
theorem case_callL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {x : FuncIdx} {args es : List Binaryen.BExpr}
    (ihlt : ∀ m < n, ∀ es', BackGoalL o host m es')
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op (.call x) args :: es) →
      BackGoalL o host m es') :
    BackGoalL o host n (.op (.call x) args :: es) := by
  intro s f stk labels ret out c cs hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk (.call x) args es
  have hta : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  have hargrun : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
          (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
          expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk₁ hev
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS ha)
  have hinfo : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      ∃ a fi ps rs, s₁.func? f₁ x = some (a, fi) ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        Interp.EvalInv s f (s₁, f₁, .normal stk₁) ∧ ps.length ≤ stk₁.length ∧
        Interp.chk s.funcs f.module f.locals.length ret labels
          (some (stk₁.length - ps.length + rs.length)) es = some out := by
    intro s₁ f₁ stk₁ hev
    obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    obtain ⟨p, q, hpq, -, -⟩ := Interp.flatChk_call (Interp.flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := Interp.callArity_func? hpq
    obtain ⟨inv1, hp, h2'⟩ :=
      Interp.arity_call_pre hS (Interp.evalH_good (P := profile o) hH hev).1 hfi hty hc
    exact ⟨a, fi, ps, rs, hfi, hty, inv1, hp, h2'⟩
  refine back_op_callL hrun hend ?_ ?_ ?_
  · intro m hm c₁ cs₁ h₁ hs₁
    exact ihle m hm args Interp.size_args s f stk labels ret oa c₁ cs₁ hS ha hta h₁ hs₁
  · intro s₁ f₁ stk₁ m cs' hm hev hrun₁
    obtain ⟨a, fi, ps, rs, hfi, hty, inv1, hp, -⟩ := hinfo s₁ f₁ stk₁ hev
    refine ⟨a, fi, ps, rs, hfi, hty, ?_⟩
    have hS₁ := Interp.storeChk_inv inv1 hS
    have hfa := Interp.funcs_of_func? hfi
    cases hcd : fi.code with
    | host hh =>
      exact back_call_hostL hfi hcd hty hp
        (fun s' ws h => hH.arity s₁ a fi hh ps rs _ ws s' hfa hcd hty h)
        (fun s' t h => hH.noThrow hh s₁ _ s' t h) hrun₁ hend
    | wasm fn =>
      obtain ⟨ob, hob, hcb⟩ := Interp.callee_chk (ext := Interp.noExt) hS₁ hfi hcd hty hp
      have htc : Sim.ContextTyped ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
        have hent := Interp.steps_call_enter (P := profile o) (host := Det.noHost) hfi hcd hty hp
          (expression (Binaryen.BExpr.lowerList es))
        have h₀ := Sim.ContextTyped.steps (ContextTyped.steps_typed hT ht (hargrun _ _ _ hev))
          hent.to_reflTransGen
        have h₁ := Sim.ContextTyped.frame h₀
        have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
        simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
      exact back_call_wasmL hfi hcd hty hp hrun₁ hend
          (fun m' hm' cb cs₁ h hs => ihlt m' (by omega) _ s₁ _ [] [rs.length] rs.length ob cb cs₁
            hS₁ hcb htc h hs)
          (fun r hevb => by
            obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hcb
            refine ⟨fun vs hvs => ⟨Interp.retVals_length hok hob hvs, fun ws hws => by
              rw [hws] at hok; exact Interp.length_of_ends hok hob⟩, fun hn => ?_⟩
            rcases hfl : r.2.2 with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok hn <;>
              simp_all [Binaryen.Flow.retVals, Interp.FlowOk])
  · intro s₁ f₁ stk₁ a fi ps rs s₂ fl vs m cs' hm hev hfi hty hcall hvs hk
    obtain ⟨a', fi', ps', rs', hfi', hty', inv1, hp, h2'⟩ := hinfo s₁ f₁ stk₁ hev
    rw [hfi] at hfi'
    simp only [Option.some.injEq, Prod.mk.injEq] at hfi'
    obtain ⟨rfl, rfl⟩ := hfi'
    rw [hty] at hty'
    simp only [Option.some.injEq, Prod.mk.injEq] at hty'
    obtain ⟨rfl, rfl⟩ := hty'
    have hS₁ := Interp.storeChk_inv inv1 hS
    have hn : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨⟨ob, hob, hok, hfuncs⟩, hrunv, -⟩ :=
      Interp.hostCall_sound (P := profile o) hH s₁ s₂ f₁ a fi ps rs _ fl hS₁
        (Interp.funcs_of_func? hfi) hty hn hcall
    have hrs := Interp.retVals_length hok hob hvs
    have inv2 : Interp.EvalInv s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have h2'' : Interp.chk s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]
      have := Interp.chk_inv inv2 h2'
      simpa using this
    obtain ⟨hx, hfx⟩ := Interp.func?_inv hfi
    have hcallstep : Steps (profile o) host
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
          expression (Binaryen.BExpr.lowerList es)⟩
        ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ := by
      have h₁ : Step (profile o) host
          ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
            expression (Binaryen.BExpr.lowerList es)⟩
          ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++
            expression (Binaryen.BExpr.lowerList es))⟩ := by
        simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := host)
          stk₁.reverse (expression (Binaryen.BExpr.lowerList es)) (Step.call hx hfx)
      have h₂ := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o) (host := host)
        (stk₁.drop ps.length).reverse (expression (Binaryen.BExpr.lowerList es)) (hrunv vs hvs)
      rw [code_call_split stk₁ ps.length] at h₁
      refine (Relation.ReflTransGen.single h₁).trans ?_
      simpa [List.reverse_append, List.append_assoc] using h₂
    have ht₂ := ContextTyped.steps_typed hT ht ((hargrun _ _ _ hev).trans hcallstep)
    exact ihle m hm es Interp.size_tail s₂ f₁ _ labels ret out c cs'
      (Interp.storeChk_inv inv2 hS) h2'' ht₂ hk hend

/-- **The logged whole-run backward simulation with host calls**, deterministic profile
`profile o`. Well-founded induction on the run length, then the tree size. -/
theorem back_wholeL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) :
    ∀ n es, BackGoalL o host n es := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro es
  induction hsz : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ k ihk =>
  have ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf es → BackGoalL o host m es' := by
    intro m hm es' hes'
    rcases Nat.lt_or_eq_of_le hm with hlt | rfl
    · exact ihn m hlt es'
    · exact ihk _ (hsz ▸ hes') es' rfl
  rcases es with _ | ⟨e, es⟩
  · intro s f stk labels ret out c cs _ _ _ hrun _
    exact back_nilL hrun
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, cnd, t, el⟩ | ⟨bt, cs, body⟩
    · by_cases hcall : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hcall
        exact case_callL hT hH ihn ihle
      · exact case_op_flatL hT hH (fun x hx => hcall ⟨x, hx⟩) ihle
    · exact case_blockL hT hH ihle
    · exact case_loopL hT hH ihn ihle
    · exact case_ifL hT hH ihle
    · intro s f stk labels ret out c cs _ hc
      obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
      simp [Interp.chk1E, Interp.noExt] at h1

/-! ## Invocations -/

theorem atHost_unique {c : Config H} {m m' : (wasmHostSig H).Op} (h : AtHost c m)
    (h' : AtHost c m') : m = m' := by
  obtain ⟨E, a, hd, hs⟩ := h
  obtain ⟨E', a', hd', hs'⟩ := h'
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨-, -, h1, h2⟩ := hd'
  rcases m with ⟨x, y, z⟩
  rcases m' with ⟨x', y', z'⟩
  dsimp only at h1 h2 hs hs'
  subst h1 h2 hs hs'
  rfl

/-- **Exact pending agreement for an invocation** (deterministic profile): a labelled Core run
of a typed invocation, with its log `cs`, to a configuration at the host call `m` is a pending
host call of the invocation after exactly `cs`. -/
theorem invoke_pendL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {s : Store H} {a : Nat} {vs : List Val} {c : Config H} {cs : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hrun : EvRunN (profile o) host n (invoke s a vs) cs c)
    (hat : AtHost c m) : PendL s a vs cs m := by
  have hend : ∀ c', ¬ Step (profile o) Det.noHost c c' := by
    obtain ⟨E, a', hd, -⟩ := hat
    exact fun c' => noFree_of_decompose hd
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have hcode₀ : (invoke s a vs).code =
      vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ []) := by
    simp [invoke, hfi]
  have hrun' : EvRunN (profile o) host n
      ⟨s, {}, vals vs.reverse.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ [])⟩ cs c := by
    rw [← hcode₀]; exact hrun
  cases hcd : fi.code with
  | host hh =>
    have hrun'' : EvRunN (profile o) host n
        ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ cs c := by
      simpa using hrun'
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    rcases evRunN_host_call hfi hcd he hn hrun'' with ⟨rfl, rfl⟩ |
        ⟨s', r, m', cs', -, rfl, hhost, hk⟩
    · obtain rfl := atHost_unique hat (atHost_call (ws := []) (rest := []) hfi hcd he hn)
      exact .self hfi hcd
    · exfalso
      rcases r with ws | t | _
      · obtain ⟨rfl, -⟩ := evRunN_of_stuck (fun c' => Sim.Step.not_vals (vs := ws))
          (by simpa [Result.toAdmin] using hk)
        exact atHost_ne_vals hat ws rfl
      · exact hH.noThrow hh s vs s' t hhost
      · obtain ⟨rfl, -⟩ := evRunN_of_stuck (fun c' => Step.trap_stuck)
          (by simpa [Result.toAdmin] using hk)
        exact atHost_ne_trap hat rfl
  | wasm fn =>
    have hp : ps'.toList.length ≤ vs.reverse.length := by simp [hlen]
    have htake : (vs.reverse.take ps'.toList.length).reverse = vs := by
      rw [List.take_of_length_le (by simp [hlen])]; simp
    have hdrop : vs.reverse.drop ps'.toList.length = [] := by simp [hlen]
    have hframe : Interp.calleeFrame fi fn vs.reverse ps'.toList.length =
        Frame.forCall fi.module vs fn.locals := by
      simp [Interp.calleeFrame, htake]
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs (Frame.forCall fi.module vs fn.locals).module
        (Frame.forCall fi.module vs fn.locals).locals.length rs'.toList.length [rs'.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [Interp.forCall_length _ _ hlen]; exact hb
    have hct : Sim.ContextTyped ⟨s, Frame.forCall fi.module vs fn.locals,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have enter := Interp.steps_invoke_enter (P := profile o) (host := Det.noHost) hfi hcd hty
        hlen
      have h₁ := Sim.ContextTyped.frame (vs := []) (rest := [])
        (by simpa [vals] using Sim.ContextTyped.steps (Sim.ContextTyped.of_configOk hcok) enter)
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    rcases back_callRef_wasmL (o := o) hfi hcd hty hp hrun' hend
        (fun m _ cb cs₁ h hsb => by
          rw [hframe] at h ⊢
          exact back_wholeL hT hH m _ s _ [] [rs'.toList.length] rs'.toList.length ob cb cs₁ hS
            hbc hct h hsb)
        (fun r hev => by
          rw [hframe] at hev
          obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hbc
          refine ⟨fun ws hws => ⟨Interp.retVals_length hok' hob hws, fun ws' hws' => by
            rw [hws'] at hok'; exact Interp.length_of_ends hok' hob⟩, fun hn => ?_⟩
          rcases hfl : r.2.2 with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hn <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOk]) with ⟨mm, hat', hpl⟩ |
      ⟨s₂, fl, q, cs', -, -, -, ⟨ws, m', -, hws, hk⟩ | ⟨rfl, hends, -⟩⟩
    · rw [htake] at hpl
      obtain rfl := atHost_unique hat hat'
      exact hpl
    · exfalso
      rw [hdrop] at hk
      obtain ⟨rfl, -⟩ := evRunN_of_stuck (fun c' => Sim.Step.not_vals) (by simpa using hk)
      exact atHost_ne_vals hat _ rfl
    · exfalso
      obtain ⟨oc, he', hst, hfr, hm⟩ := hends
      rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
      exact atHost_ne_trap hat he'

/-- **Exact same-log pending agreement** (deterministic profile): a finite Core run of a typed
invocation with its exact host-event log `cs`, to a configuration at a host call, is a pending
host call of the logged closed semantics after exactly `cs`. -/
theorem evRun_pend (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} {cs : List (Call (wasmHostSig H))}
    {E : SingleThreaded.Ctx} {a' : Nat} {hh : H} {us : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs c)
    (hd : SingleThreaded.decompose? c.store c.code = some (E, a', hh, us)) :
    (cs, (hh, c.store, us)) ∈ wasmEvPend s (a, vs) := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  exact invoke_pendL hT hH hs hS hok hn ⟨E, a', hd, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
