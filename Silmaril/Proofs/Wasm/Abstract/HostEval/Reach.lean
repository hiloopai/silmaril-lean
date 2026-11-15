module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Obs

/-!
# Forward reachability of pending calls (proofs)

`reach_atCall`: in **every** profile, a reach of the call `y` after answered calls
(`ReachO (hostCall host)`) of arity-checked trees, for a host in the native host
slice, is a Core run to a configuration at that call (`AtCall`), in the call's
store. With a host function there, `atCall_pending` (no host outcome) and
`atCall_pendingDiv` (the host may diverge) turn it into the `blocked` and
`hostDiv` observations in Core.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **At a host call with no outcome, Core is blocked.** -/
theorem atCall_pending {s : Store H} {a : Nat} {us : List Val} {es : List Admin}
    {fi : FuncInst H} {hh : H} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hno : ∀ o, ¬ host hh s us o) (h : AtCall s a us es) : Pending host s es := by
  induction h with
  | here hf' =>
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    exact Pending.call hf hcode he hn hno
  | label _ ih => exact Pending.label ih
  | frame _ ih => exact Pending.frame ih

/-- **At a host call the host may diverge on, Core diverges.** -/
theorem atCall_pendingDiv {s : Store H} {a : Nat} {us : List Val} {es : List Admin}
    {fi : FuncInst H} {hh : H} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hdiv : host hh s us .diverged) (h : AtCall s a us es) : PendingDiv host s es := by
  induction h with
  | here hf' =>
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    exact PendingDiv.call hf hcode he hn hdiv
  | label _ ih => exact PendingDiv.label ih
  | frame _ ih => exact PendingDiv.frame ih

/-- A normal native run of checked trees is a Core run to its values, any profile. -/
theorem run_of_evalH' (hH : Interp.NativeHostSlice host) {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} {xs : List Binaryen.BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hev : EvalH host s f stk xs (s₁, f₁, .normal stk₁))
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) xs = some out) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)⟩
      ⟨s₁, f₁, vals stk₁.reverse⟩ := by
  obtain ⟨c', o', hrun, he, hm⟩ :=
    Interp.run_of_wp ((Interp.evalH_good (P := P) hH hev).2 hS hc)
  rw [← Interp.ends_normal hm he]
  exact hrun

/-- The `if` step to the chosen arm's block, any profile and host. -/
theorem step_if_arm' {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {rest : List Admin}
    (hb : Binaryen.truthy cv = some b) :
    Step P host
      ⟨s, f, vals (cv :: stk).reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩
      ⟨s, f, vals stk.reverse ++
        .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ := by
  obtain ⟨c₀, rfl, rfl⟩ := Interp.truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) (s := s) (f := f)
      stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) (s := s) (f := f)
      stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

/-- What is known at a reached call: the store passes the check, and the callee
has a function type whose parameters the arguments match in number. -/
def CallFacts (y : (wasmOShape H).self.Op) : Prop :=
  Interp.StoreChk y.2.2.funcs ∧ ∃ (fi : FuncInst H) (ps rs : List Validation.CValType),
    y.2.2.funcs[y.1]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    y.2.1.length = ps.length

/-- The conclusion of `reach_atCall`. -/
def ReachCore (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (f' : Frame) (c : List Admin),
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ ⟨y.2.2, f', c⟩ ∧
      AtCall y.2.2 y.1 y.2.1 c ∧ CallFacts y

/-- **Forward reachability of a call**, every profile: a reach of `y` after
answered calls, of arity-checked trees in a checked store, is a Core run to a
configuration at the call `y`. -/
theorem reach_atCall (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {y : (wasmOShape H).self.Op}
    (hr : ReachO (hostCall host) s f stk es y) :
    ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, Interp.StoreChk s.funcs →
      Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      ReachCore P host s f stk es y := by
  induction hr with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
    obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
    have h₁ := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain (.call x) :: expression (Binaryen.BExpr.lowerList es)) (run_of_evalH' (P := P) hH hargs hS ha)
    have h₂ : Step P host
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++
          expression (Binaryen.BExpr.lowerList es))⟩ := by
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) stk₁.reverse
        (expression (Binaryen.BExpr.lowerList es)) (Step.call hx hf)
    rw [code_call_split stk₁ ps.length] at h₂
    obtain ⟨inv1, hp, -⟩ :=
      Interp.arity_call_pre hS (Interp.evalH_good (P := P) hH hargs).1 hfi hty hc
    have hfacts : CallFacts (H := H) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ :=
      ⟨Interp.storeChk_inv inv1 hS, fi, ps, rs, hf, hty, by
        simp only [List.length_reverse, List.length_take]; omega⟩
    refine ⟨f₁, vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse ++
      .ref (.func a) :: .callRefType fi.type :: expression (Binaryen.BExpr.lowerList es), ?_,
      AtCall.here hf, hfacts⟩
    rw [Interp.code_op]
    exact h₁.tail h₂
  | @args s f stk i args es y _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
    obtain ⟨f', c, hr, hat, hcf⟩ := ih hS ha
    refine ⟨f', _, ?_, atCall_append hat (.plain i :: expression (Binaryen.BExpr.lowerList es)), hcf⟩
    rw [Interp.code_op]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ hr
  | @callK s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl y hargs hfi hty hcall hvs _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
    obtain ⟨inv1, hp, h2'⟩ :=
      Interp.arity_call_pre hS (Interp.evalH_good (P := P) hH hargs).1 hfi hty hc
    have hS₁ := Interp.storeChk_inv inv1 hS
    have hn : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨⟨ob, hob, hok, hfuncs⟩, hrunv, -⟩ :=
      Interp.hostCall_sound (P := P) hH s₁ s₂ f₁ a fi ps rs _ fl hS₁
        (Interp.funcs_of_func? hfi) hty hn hcall
    have hrs := Interp.retVals_length hok hob hvs
    have inv2 : Interp.EvalInv s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
      ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
    have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
        stk₁.length - ps.length + rs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have h2'' : Interp.chk s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
      rw [hlen]; simpa using Interp.chk_inv inv2 h2'
    obtain ⟨f', c, hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv2 hS) h2''
    obtain ⟨hx, hfx⟩ := Interp.func?_inv hfi
    have h₁ := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain (.call x) :: expression (Binaryen.BExpr.lowerList es)) (run_of_evalH' (P := P) hH hargs hS ha)
    have h₂ : Step P host
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++
          expression (Binaryen.BExpr.lowerList es))⟩ := by
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) stk₁.reverse
        (expression (Binaryen.BExpr.lowerList es)) (Step.call hx hfx)
    rw [code_call_split stk₁ ps.length] at h₂
    have h₃ := Silmaril.Wasm.Logic.Core.Steps.ctx (P := P) (host := host)
      (stk₁.drop ps.length).reverse (expression (Binaryen.BExpr.lowerList es)) (hrunv vs hvs)
    refine ⟨f', c, ?_, hat, hcf⟩
    rw [Interp.code_op]
    refine (h₁.tail h₂).trans (Relation.ReflTransGen.trans ?_ hr)
    simpa [List.reverse_append, List.append_assoc] using h₃
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es y hi hargs hflat _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
    obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := P) hH hargs).1 h1
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hflat hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    obtain ⟨f', c, hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv12 hS) h2'
    have h₁ := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain i :: expression (Binaryen.BExpr.lowerList es)) (run_of_evalH' (P := P) hH hargs hS ha)
    have h₂ := Interp.steps_flat_normal (P := P) (host := host) hi hf hflat
      (expression (Binaryen.BExpr.lowerList es))
    refine ⟨f', c, ?_, hat, hcf⟩
    rw [Interp.code_op]
    exact (h₁.trans h₂).trans hr
  | @block s f stk bt body es np nr y har _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨np', nr', hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
    rw [← Interp.arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq hbody
    have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
        (some (stk.take np).length) body = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb
    obtain ⟨f', c, hr, hat, hcf⟩ := ih hS hb'
    have henter := Interp.steps_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    have hat' := AtCall.label (ws := (stk.drop np).reverse) (n := nr) (cont := [])
      (rest := expression (Binaryen.BExpr.lowerList es)) hat
    refine ⟨f', _, ?_, hat', hcf⟩
    rw [Interp.code_block]
    have hctx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := P) (host := host)
      (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (Silmaril.Wasm.Logic.Core.Steps.label nr [] hr)
    exact henter.trans (by simpa using hctx)
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
    obtain ⟨np', nr', hba, hp, hbd, rfl⟩ := Interp.chk1_blockE h1
    rw [← Interp.arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbd
    have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
        (some (stk.take np).length) body = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := P) hH hbody).1 hS hb'
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    obtain ⟨f', c, hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv1 hS)
      (Interp.chk_after (ext := Interp.noExt) inv1 hp hnr h2)
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := P) hH hbody).2 hS hb')
    have htg := Interp.tg_block_vals (P := P) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    refine ⟨f', c, ?_, hat, hcf⟩
    rw [Interp.code_block]
    exact htg.to_reflTransGen.trans hr
  | @loop s f stk bt body es np nr y har _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨np', nr', hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
    rw [← Interp.arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq hbody
    have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
        (some (stk.take np).length) body = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb
    obtain ⟨f', c, hr, hat, hcf⟩ := ih hS hb'
    have henter := Interp.steps_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har)
      (expression (Binaryen.BExpr.lowerList es))
    have hat' := AtCall.label (ws := (stk.drop np).reverse) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
      (rest := expression (Binaryen.BExpr.lowerList es)) hat
    refine ⟨f', _, ?_, hat', hcf⟩
    rw [Interp.code_loop]
    have hctx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := P) (host := host)
      (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (Silmaril.Wasm.Logic.Core.Steps.label np [.loop bt (Binaryen.BExpr.lowerList body)] hr)
    exact henter.trans (by simpa using hctx)
  | @loopK s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
    obtain ⟨np', nr', hba, hp, hbd, rfl⟩ := Interp.chk1_loopE h1
    rw [← Interp.arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbd
    have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
        (some (stk.take np).length) body = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := P) hH hbody).1 hS hb'
    have hlen : vs.length = nr := Interp.length_of_ends hok hob
    obtain ⟨f', c, hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv1 hS)
      (Interp.chk_after (ext := Interp.noExt) (vs := vs) inv1 hp hlen.ge h2)
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := P) hH hbody).2 hS hb')
    have henter := Interp.steps_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har)
      (expression (Binaryen.BExpr.lowerList es))
    have hx := Interp.exit_normal (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    have htake : vs.take nr = vs := List.take_of_length_le hlen.le
    refine ⟨f', c, ?_, hat, hcf⟩
    rw [Interp.code_loop]
    refine (henter.trans (Silmaril.Wasm.Logic.Core.Steps.ctx _ _
      (Silmaril.Wasm.Logic.Core.Steps.label np _ hbr))).trans ((hx.trans ?_))
    rw [htake] at hr
    simpa [List.reverse_append, List.append_assoc] using hr
  | @loopBack s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
    obtain ⟨np', nr', hba, hp, hbd, rfl⟩ := Interp.chk1_loopE h1
    rw [← Interp.arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbd
    have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
        (some (stk.take np).length) body = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb
    obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := P) hH hbody).1 hS hb'
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    obtain ⟨f', c, hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv1 hS)
      (by rw [hlen]; exact Interp.chk_inv inv1 hc)
    obtain ⟨c', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := P) hH hbody).2 hS hb')
    have henter := Interp.steps_enter (P := P) (host := host) (s := s) (f := f)
      (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har)
      (expression (Binaryen.BExpr.lowerList es))
    have hx := Interp.exit_br0 (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (n := np)
      (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm' hnp (stk.drop np).reverse
      (expression (Binaryen.BExpr.lowerList es))
    refine ⟨f', c, ?_, hat, hcf⟩
    rw [Interp.code_loop]
    refine (henter.trans (Silmaril.Wasm.Logic.Core.Steps.ctx _ _
      (Silmaril.Wasm.Logic.Core.Steps.label np _ hbr))).trans ((hx.trans ?_))
    rw [Interp.code_loop] at hr
    simpa [List.reverse_append, List.append_assoc, expression] using hr
  | @cond s f stk bt c t el es y _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oc, hco, -⟩ := Interp.chk1_ifE h1
    obtain ⟨f', c', hr, hat, hcf⟩ := ih hS hco
    refine ⟨f', _, ?_, atCall_append hat
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es)), hcf⟩
    rw [Interp.code_if]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ hr
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr y hcd hb har _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oc, hco, -⟩ := Interp.chk1_ifE h1
    obtain ⟨inv1, hp, hendArm, -⟩ :=
      Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := P) hH hcd).1 har hc
    obtain ⟨ob, hb', -⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
    have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb'
    obtain ⟨f', c', hr, hat, hcf⟩ := ih (Interp.storeChk_inv inv1 hS) hb''
    have h₁ := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es)) (run_of_evalH' (P := P) hH hcd hS hco)
    have h₂ := step_if_arm' (P := P) (host := host) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt)
      (t := t) (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    have henter := Interp.steps_enter (P := P) (host := host) (s := s₁) (f := f₁)
      (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har)
      (expression (Binaryen.BExpr.lowerList es))
    have hat' := AtCall.label (ws := (stk₁.drop np).reverse) (n := nr) (cont := [])
      (rest := expression (Binaryen.BExpr.lowerList es)) hat
    refine ⟨f', _, ?_, hat', hcf⟩
    rw [Interp.code_if]
    have hctx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := P) (host := host)
      (stk₁.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (Silmaril.Wasm.Logic.Core.Steps.label nr [] hr)
    exact ((h₁.tail h₂).trans henter).trans (by simpa using hctx)
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hcd hb har harm hvs _ ih =>
    intro labels ret out hS hc
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨oc, hco, -⟩ := Interp.chk1_ifE h1
    obtain ⟨inv1, hp, hendArm, h2'⟩ :=
      Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := P) hH hcd).1 har hc
    obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
    have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
        (some (stk₁.take np).length) (if b then t else el) = some ob := by
      rw [Interp.take_length_of_le hp]; exact hb'
    have hS₁ := Interp.storeChk_inv inv1 hS
    obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := P) hH harm).1 hS₁ hb''
    have hnr := Interp.blockVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
      rintro ws rfl; exact Interp.length_of_ends hok hob
    obtain ⟨f', c', hr, hat, hcf⟩ := ih (Interp.storeChk_inv (inv1.trans inv2) hS)
      (Interp.chk_after (ext := Interp.noExt) inv2 hp hnr (Interp.chk_inv inv1 h2'))
    have h₁ := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
        expression (Binaryen.BExpr.lowerList es)) (run_of_evalH' (P := P) hH hcd hS hco)
    have h₂ := step_if_arm' (P := P) (host := host) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt)
      (t := t) (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    obtain ⟨c'', o', hbr, he, hm'⟩ :=
      Interp.run_of_wp ((Interp.evalH_good (P := P) hH harm).2 hS₁ hb'')
    have htg := Interp.tg_block_vals (P := P) (host := host)
      (rest := expression (Binaryen.BExpr.lowerList es)) har hp hbr he hm' hvs hnr hnorm
    refine ⟨f', c', ?_, hat, hcf⟩
    rw [Interp.code_if]
    exact ((h₁.tail h₂).trans htg.to_reflTransGen).trans hr

end Silmaril.Proofs.Wasm.Abstract.HostEval
