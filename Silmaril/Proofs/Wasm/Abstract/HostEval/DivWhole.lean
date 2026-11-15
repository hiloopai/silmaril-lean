module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Whole
public import Silmaril.Wasm.Abstract.DivO.Thms

/-!
# Divergent runs with host calls (proofs)

`div_whole`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers (`HostTyped`) in the native host slice (`Interp.NativeHostSlice`), a divergent Core
run of lowered, arity-checked, typed trees reaches a host call the host may diverge on
(`HostDivReach`), or the open native semantics with host calls diverges coinductively
(`EvalDivO (hostCall host)`). The coinductive counterpart of `back_whole`.

The proof is by coinduction (`evalDivO_of_coind`) on `DivHyp`: the hypotheses of `back_whole`
for the trees, divergence of their Core run, and no reach of a host call the host may diverge
on. At each tree, the divergent run is split (`HostCall.diverges_seq_split`,
`diverges_label_seq_split`, `diverges_frame_seq_split`, `diverges_host_call`): a part that
diverges is the next coinductive problem; a part that runs to a stuck end is read by
`back_whole` as a native run; host-free steps are passed through
(`HostCall.diverges_through_steps`), and abrupt ends, being stuck, do not diverge. The
invariant `¬ HostDivReach` passes to every subproblem along the `ReachO` constructors.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H} {o : GrowOracle}

/-- The coinductive invariant: the hypotheses of `back_whole` for the trees, divergence of
their Core run, and no reach of a host call the host may diverge on. -/
def DivHyp (o : GrowOracle) (host : HostSemantics H) : Interp.Problem H := fun s f stk es =>
  (∃ (labels : List Nat) (ret : Nat) (out : Option Nat), Interp.StoreChk s.funcs ∧
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩) ∧
  Diverges (profile o) host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ ∧
  ¬ HostDivReach host s f stk es

/-! ## Helpers -/

theorem not_div_stuck {P : Silmaril.Wasm.Numerics.Profile} {c : Config H}
    (hs : ∀ c', ¬ Step P host c c') (hd : Diverges P host c) : False := by
  obtain ⟨b, hb, -⟩ := hd.unfold
  exact hs b hb

/-- `HostDivReach` is closed under every `ReachO` constructor. -/
theorem hdr_lift {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr}
    (hl : ∀ z, ReachO (hostCall host) s' f' stk' es' z → ReachO (hostCall host) s f stk es z)
    (h : HostDivReach host s' f' stk' es') : HostDivReach host s f stk es := by
  obtain ⟨y, fi, hh, hr, h1, h2, h3⟩ := h
  exact ⟨y, fi, hh, reachP_lift hl hr, h1, h2, h3⟩

/-- A finite run of checked, typed trees to values is a normal native run. -/
theorem evalH_of_vals (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {labels : List Nat}
    {ret : Nat} {out : Option Nat} {c₁ : Config H} {ws : List Val}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (hrun : Steps (profile o) host
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c₁)
    (hw : c₁.code = vals ws) :
    ∃ stk₁, EvalH host s f stk es (c₁.store, c₁.frame, .normal stk₁) ∧ ws = stk₁.reverse := by
  have hend : ∀ c', ¬ Step (profile o) host c₁ c' := by
    intro c' h
    rcases c₁ with ⟨_, _, _⟩
    dsimp only at hw
    subst hw
    exact Sim.Step.not_vals h
  obtain ⟨n, hn⟩ := stepsN_of_steps hrun
  rcases back_whole hT hH n es s f stk labels ret out c₁ hS hc ht hn hend with
      ⟨⟨s₁, f₁, fl⟩, hev, oc, he, hst, hfr, hm⟩ | ⟨hp, -⟩
  · rw [hw] at he
    obtain rfl := ends_vals he
    dsimp only at hst hfr hm
    subst hst hfr
    rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
    exact ⟨stk₁, hev, hm⟩
  · exact (pending_ne_vals hp ws hw).elim

/-- A finite run of a body to a stuck end, with the label around that end diverging, is a
native run of the body to that end. -/
theorem body_end_label (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {body : List Binaryen.BExpr} {labels : List Nat}
    {ret : Nat} {out : Option Nat} {cb : Config H} {pre : List Val} {n : Nat}
    {cont : List Instr} {rest : List Admin}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) body = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList body)⟩)
    (hrun : Steps (profile o) host
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb)
    (hsb : ∀ c', ¬ Step (profile o) host cb c')
    (hd : Diverges (profile o) host
      ⟨cb.store, cb.frame, vals pre ++ [.label n cont cb.code] ++ rest⟩) :
    ∃ (fl : Binaryen.Flow) (oc : Outcome), EvalH host s f stk body (cb.store, cb.frame, fl) ∧
      oc.Ends cb.code ∧ Interp.FlowMatch fl oc := by
  obtain ⟨m, hm⟩ := stepsN_of_steps hrun
  rcases back_whole hT hH m body s f stk labels ret out cb hS hc ht hm hsb with
      ⟨⟨s₁, f₁, fl⟩, hev, oc, he, hst, hfr, hfm⟩ | ⟨hp, -⟩
  · dsimp only at hst hfr hfm
    subst hst hfr
    exact ⟨fl, oc, hev, he, hfm⟩
  · obtain ⟨hstk, -⟩ := pending_label (P := profile o) (ws := pre) (n := n) (cont := cont)
      (rest := rest) (f := cb.frame) hp hsb
    exact (not_div_stuck hstk hd).elim

/-- The same for a callee body, in its frame and label. -/
theorem body_end_frame (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {F : Frame} {stk : List Val} {body : List Binaryen.BExpr} {labels : List Nat}
    {ret : Nat} {out : Option Nat} {cb : Config H} {f : Frame} {pre : List Val} {n : Nat}
    {rest : List Admin}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs F.module F.locals.length ret labels (some stk.length) body = some out)
    (ht : Sim.ContextTyped ⟨s, F, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList body)⟩)
    (hrun : Steps (profile o) host
      ⟨s, F, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb)
    (hsb : ∀ c', ¬ Step (profile o) host cb c')
    (hd : Diverges (profile o) host
      ⟨cb.store, f, vals pre ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩) :
    ∃ (fl : Binaryen.Flow) (oc : Outcome), EvalH host s F stk body (cb.store, cb.frame, fl) ∧
      oc.Ends cb.code ∧ Interp.FlowMatch fl oc := by
  obtain ⟨m, hm⟩ := stepsN_of_steps hrun
  rcases back_whole hT hH m body s F stk labels ret out cb hS hc ht hm hsb with
      ⟨⟨s₁, f₁, fl⟩, hev, oc, he, hst, hfr, hfm⟩ | ⟨hp, -⟩
  · dsimp only at hst hfr hfm
    subst hst hfr
    exact ⟨fl, oc, hev, he, hfm⟩
  · obtain ⟨hstk, -⟩ := pending_frame (P := profile o) (f := f) (ws := pre) (n := n)
      (rest := rest) hp hsb
    exact (not_div_stuck hstk hd).elim

/-- Typing of a label in place, along a run of its body. -/
theorem typed_label_steps (hT : HostTyped host) {s : Store H} {f : Frame} {pre : List Val}
    {n : Nat} {cont : List Instr} {b rest : List Admin} {cb : Config H}
    (ht : Sim.ContextTyped ⟨s, f, vals pre ++ [.label n cont b] ++ rest⟩)
    (h : Steps (profile o) host ⟨s, f, b⟩ cb) :
    Sim.ContextTyped ⟨cb.store, cb.frame, vals pre ++ [.label n cont cb.code] ++ rest⟩ :=
  ContextTyped.steps_typed hT ht
    (Silmaril.Wasm.Logic.Core.Steps.ctx pre rest (Silmaril.Wasm.Logic.Core.Steps.label n cont h))

/-- Typing of a call frame in place, along a run of its body. -/
theorem typed_frame_steps (hT : HostTyped host) {s : Store H} {f F : Frame} {pre : List Val}
    {n : Nat} {b rest : List Admin} {cb : Config H}
    (ht : Sim.ContextTyped ⟨s, f, vals pre ++ [.frame n F [.label n [] b]] ++ rest⟩)
    (h : Steps (profile o) host ⟨s, F, b⟩ cb) :
    Sim.ContextTyped ⟨cb.store, f, vals pre ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ :=
  ContextTyped.steps_typed hT ht
    (Silmaril.Wasm.Logic.Core.Steps.ctx pre rest
      (Silmaril.Wasm.Logic.Core.Steps.frame n (Silmaril.Wasm.Logic.Core.Steps.label n [] h)))

/-- **An abrupt exit from a label does not diverge**: it ends in a stuck form. -/
theorem div_label_abrupt {s₁ : Store H} {f₁ : Frame} {pre : List Val} {code rest : List Admin}
    {n : Nat} {cont : List Instr} {oc : Outcome} {fl fl' : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl))
    (hn : ¬ fl'.IsNormal)
    (ht : Sim.ContextTyped ⟨s₁, f₁, vals pre ++ [.label n cont code] ++ rest⟩)
    (hd : Diverges (profile o) host ⟨s₁, f₁, vals pre ++ [.label n cont code] ++ rest⟩) : False := by
  have hw := Interp.exit_abrupt (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
    (n := n) (cont := cont) (fl' := fl') he hm hfl pre rest
  obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
  exact not_div_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₁) (f := f₁)
    he'' hm'' hn) (diverges_through_steps hst' ht hd)

/-- **Leaving a block's label in a divergent run**: the body's flow hands values on, and the
run after the block diverges. A branch out, a return or a trap ends in a stuck form. -/
theorem div_block_exit {s₁ : Store H} {f₁ : Frame} {pre : List Val} {code rest : List Admin}
    {nr : Nat} {oc : Outcome} {fl : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hnr : ∀ vs, fl.blockVals = some vs → nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (ht : Sim.ContextTyped ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩)
    (hd : Diverges (profile o) host ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩) :
    ∃ vs, fl.blockVals = some vs ∧
      Sim.ContextTyped ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ ∧
      Diverges (profile o) host ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ := by
  cases hvs : fl.blockVals with
  | some vs =>
    have hx := Interp.exit_blockVals (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
      (pre := pre) (rest := rest) he hm hvs (hnr vs hvs) hnorm
    exact ⟨vs, rfl, ht.steps hx, diverges_through_steps hx ht hd⟩
  | none =>
    exfalso
    have hfl : (∃ k vs, fl = Binaryen.Flow.brk (k + 1) vs) ∨ fl.Escapes := by
      rcases fl with _ | ⟨_ | k, vs⟩ | _ | _ | _ <;>
        simp_all [Binaryen.Flow.blockVals, Binaryen.Flow.Escapes]
    rcases hfl with ⟨k, vs, rfl⟩ | hesc
    · exact div_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id ht hd
    · exact div_label_abrupt he hm (.inr ⟨hesc, rfl⟩) (by
        rcases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]) ht hd

/-! ## Operator trees -/

/-- **The operator case** other than a call. -/
theorem div_op_flat (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List Binaryen.BExpr}
    (hi : ∀ x, i ≠ .call x) (h : DivHyp o host s f stk (.op i args :: es)) :
    DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk (.op i args :: es) := by
  obtain ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hnr⟩ := h
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hta : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  rw [hcode] at hd
  rcases diverges_seq_split hd with hda | ⟨⟨s₁, f₁, k₁⟩, ws, hrun₁, hw, hd₁⟩
  · exact .args ⟨⟨labels, ret, oa, hS, ha, hta⟩, hda,
      fun h => hnr (hdr_lift (fun _ => ReachO.args) h)⟩
  dsimp only at hw hd₁
  obtain ⟨stk₁, hev, rfl⟩ := evalH_of_vals hT hH hS ha hta hrun₁ hw
  dsimp only at hev
  have htyped : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
      expression (Binaryen.BExpr.lowerList es)⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain i :: expression (Binaryen.BExpr.lowerList es)) (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
  obtain ⟨⟨s₂, f₂, fl⟩, hfl⟩ := Interp.evalFlat_progressH hf hi htyped
  by_cases hn : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := Det.noHost) hi hf hfl
      (expression (Binaryen.BExpr.lowerList es))
    exact .opK hi hev hfl ⟨⟨labels, ret, out, Interp.storeChk_inv inv12 hS, h2', htyped.steps hst⟩,
      diverges_through_steps hst htyped hd₁,
      fun h => hnr (hdr_lift (fun _ => ReachO.opK hi hev hfl) h)⟩
  · exfalso
    have hw := Interp.wp_flat_abrupt (P := profile o) (host := Det.noHost) hf hfl hn
      (expression (Binaryen.BExpr.lowerList es))
    obtain ⟨c', o', hst, he, hm⟩ := Interp.run_of_wp hw
    exact not_div_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₂) (f := f₂)
      he hm hn) (diverges_through_steps hst htyped hd₁)

/-! ## Calls -/

/-- The callee facts after the arguments of a call. -/
theorem call_info (o : GrowOracle) (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out)
    {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    (hev : EvalH host s f stk args (s₁, f₁, .normal stk₁)) :
    ∃ a fi ps rs, s₁.func? f₁ x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      Interp.EvalInv s f (s₁, f₁, .normal stk₁) ∧ ps.length ≤ stk₁.length ∧
      Interp.chk s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
  obtain ⟨p, q, hpq, -, -⟩ := Interp.flatChk_call (Interp.flatChkE_call hf)
  obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := Interp.callArity_func? hpq
  obtain ⟨inv1, hp, h2'⟩ :=
    Interp.arity_call_pre hS (Interp.evalH_good (P := profile o) hH hev).1 hfi hty hc
  exact ⟨a, fi, ps, rs, hfi, hty, inv1, hp, h2'⟩

/-- The hypotheses of the trees after an answered call. -/
theorem after_call (o : GrowOracle) (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr}
    {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩)
    {s₁ s₂ : Store H} {f₁ : Frame} {stk₁ vs : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {fl : Binaryen.Flow}
    (hev : EvalH host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl))
    (hvs : fl.retVals = some vs) :
    ∃ (labels : List Nat) (ret : Nat) (out : Option Nat), Interp.StoreChk s₂.funcs ∧
      Interp.chk s₂.funcs f₁.module f₁.locals.length ret labels
        (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out ∧
      Sim.ContextTyped ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
        expression (Binaryen.BExpr.lowerList es)⟩ := by
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  obtain ⟨a', fi', ps', rs', hfi', hty', inv1, hp, h2'⟩ := call_info o hH hS hc hev
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
  have hargrun : Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
        (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩ := by
    rw [Interp.code_op]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS ha)
  obtain ⟨hx, hfx⟩ := Interp.func?_inv hfi
  have hcallstep : Steps (profile o) host
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩
      ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    have h₁ : Step (profile o) host
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++
          expression (Binaryen.BExpr.lowerList es))⟩ := by
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := host)
        stk₁.reverse (expression (Binaryen.BExpr.lowerList es)) (Step.call hx hfx)
    have h₂ := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o) (host := host)
      (stk₁.drop ps.length).reverse (expression (Binaryen.BExpr.lowerList es)) (hrunv vs hvs)
    rw [code_call_split stk₁ ps.length] at h₁
    refine (Relation.ReflTransGen.single h₁).trans ?_
    simpa [List.reverse_append, List.append_assoc] using h₂
  exact ⟨labels, ret, out, Interp.storeChk_inv inv2 hS, h2'',
    ContextTyped.steps_typed hT ht (hargrun.trans hcallstep)⟩


/-- **The call case.** -/
theorem div_call (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr}
    (h : DivHyp o host s f stk (.op (.call x) args :: es)) :
    DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk
      (.op (.call x) args :: es) := by
  obtain ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hnr⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk (.call x) args es
  have hta : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  rw [hcode] at hd
  rcases diverges_seq_split hd with hda | ⟨⟨s₁, f₁, k₁⟩, ws, hrun₁, hw, hd₁⟩
  · exact .args ⟨⟨labels, ret, oa, hS, ha, hta⟩, hda,
      fun h => hnr (hdr_lift (fun _ => ReachO.args) h)⟩
  dsimp only at hw hd₁
  obtain ⟨stk₁, hev, rfl⟩ := evalH_of_vals hT hH hS ha hta hrun₁ hw
  dsimp only at hev
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  obtain ⟨a, fi, ps, rs, hfi, hty, inv1, hp, -⟩ := call_info o hH hS hc hev
  have hS₁ := Interp.storeChk_inv inv1 hS
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  -- typing after the arguments, and after `call x`
  have htK₀ : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append (.plain (.call x) :: rest)
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  have hs₁ : Step (profile o) host
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := host)
      stk₁.reverse rest (Step.call hx hf)
  have htK₁ := ContextTyped.steps_typed hT htK₀ (.single hs₁)
  -- `call x` is the only step
  obtain ⟨c', hc', hd₂⟩ := hd₁.unfold
  obtain rfl := call_step_unique hfi hc'
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  have e : stk₁.reverse = (stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  cases hcd : fi.code with
  | host hh =>
    have hd₃ : Diverges (profile o) host
        ⟨s₁, f₁, vals stk₁.reverse ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ := by
      simpa [Diverges] using hd₂
    obtain ⟨vs₁, vs₂, ps'', rs'', hsplit, he, hn, hdiv | ⟨s', res, hhost, hd₄⟩⟩ :=
      diverges_host_call (r := .callRefType fi.type) trivial hf hcd hd₃
    all_goals
      have heq := (Validation.Expand.iff.1 he).symm.trans (Validation.Expand.iff.1 hex)
      simp only [Option.some.injEq, Validation.Ty.func.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [e] at hsplit
      have hlen : vs₂.length = (stk₁.take ps.length).reverse.length := by
        simp only [List.length_reverse, List.length_take]; omega
      obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit.symm hlen
    · exact (hnr ⟨⟨a, ((stk₁.take ps.length).reverse, s₁)⟩, fi, hh, .inl (.here hev hfi hty),
        hf, hcd, hdiv⟩).elim
    · have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s', resFlow res) := by
        rw [hostCall_fixpoint]
        exact .inr ⟨fi, hh, res, hf, hcd, hhost, rfl⟩
      rcases res with ws | t | _
      · have hl := hH.arity s₁ a fi hh ps rs _ ws s' (Interp.funcs_of_func? hfi) hcd hty hhost
        have hvs : (resFlow (.values ws)).retVals = some ws.reverse := rfl
        refine .callRet hev hfi hty hcall hvs
          ⟨after_call o hT hH hS hc ht hev hfi hty hcall hvs, ?_,
            fun h => hnr (hdr_lift (fun _ => ReachO.callK hev hfi hty hcall hvs) h)⟩
        have htake : ws.reverse.take rs.length = ws.reverse :=
          List.take_of_length_le (by simp [hl])
        rw [htake]
        simpa [Result.toAdmin, List.reverse_append, List.append_assoc] using hd₄
      · exact (hH.noThrow hh s₁ _ s' t hhost).elim
      · exact (trap_not_diverges (by simpa [Result.toAdmin] using hd₄)).elim
  | wasm fn =>
    have hp' : ps'.length ≤ stk₁.length := by omega
    have hs₂ : Step (profile o) host
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩
        ⟨s₁, f₁, vals (stk₁.drop ps'.length).reverse ++
          [.frame rs'.length (Frame.forCall fi.module (stk₁.take ps'.length).reverse fn.locals)
            [.label rs'.length [] (expression fn.body)]] ++ rest⟩ := by
      rw [code_call_split stk₁ ps'.length]
      have hn : (stk₁.take ps'.length).reverse.length = ps'.length := by
        simp only [List.length_reverse, List.length_take]; omega
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := host)
        (stk₁.drop ps'.length).reverse rest
        (Step.callRefFunc (c := .callRefType fi.type) trivial hf hex hn hcd)
    have htK₂ := ContextTyped.steps_typed hT htK₁ (.single hs₂)
    obtain ⟨c'', hc'', hd₃⟩ := hd₂.unfold
    obtain rfl := callRef_wasm_step_unique hf hcd hex hp' hc''
    rw [hpl, hrl] at hd₃ htK₂
    obtain ⟨ob, hob, hcb⟩ := Interp.callee_chk (ext := Interp.noExt) hS₁ hfi hcd hty hp
    have htc : Sim.ContextTyped ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htK₂
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    rcases diverges_frame_seq_split hd₃ with hdb | ⟨⟨rcs, rcf, rcc⟩, hb, hsb, hd₄⟩
    · refine .callee hev hfi hcd hty ⟨⟨[rs.length], rs.length, ob, hS₁, hcb, htc⟩,
        by simpa [Binaryen.lowerList_liftInstrs, vals] using hdb, fun h => ?_⟩
      obtain ⟨y, fi', hh', hr, h1, h2, h3⟩ := h
      exact hnr ⟨y, fi', hh', reachP_call hev hfi hty
        (.inr (pendO_of_body (x := ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩) hf hcd hr)),
        h1, h2, h3⟩
    · dsimp only at hsb hd₄
      have hb' : Steps (profile o) host
          ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length, vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hb
      obtain ⟨fl, oc, hevb, he, hm⟩ := body_end_frame hT hH hS₁ hcb htc hb' hsb hd₄
      dsimp only at hevb he
      have htyF := typed_frame_steps hT htK₂ hb
      dsimp only at htyF
      have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (rcs, fl) := by
        rw [hostCall_fixpoint]
        exact .inl ⟨fi, fn, ps, rs, rcf, hf, hcd, hty, hevb⟩
      obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hcb
      cases hvs : fl.retVals with
      | some vs =>
        have hrs := Interp.retVals_length hok hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
          intro ws hws; rw [hws] at hok; exact Interp.length_of_ends hok hob
        obtain ⟨s', res, hret', hK⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := f₁) he
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
        obtain ⟨rfl, rfl⟩ := hK
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) (stk₁.drop ps.length).reverse rest hret'
        have hd₅ := diverges_through_steps hx htyF hd₄
        refine .callRet hev hfi hty hcall hvs
          ⟨after_call o hT hH hS hc ht hev hfi hty hcall hvs, ?_,
            fun h => hnr (hdr_lift (fun _ => ReachO.callK hev hfi hty hcall hvs) h)⟩
        simpa [Interp.stack_after] using hd₅
      | none =>
        exfalso
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOk]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
          exact he
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++
              [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ rest⟩
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++ rest⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact trap_not_diverges (by simpa using diverges_through_steps hout htyF hd₄)


/-! ## Structured trees -/

/-- **The block case.** -/
theorem div_block (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr}
    (h : DivHyp o host s f stk (.block bt body :: es)) :
    DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk (.block bt body :: es) := by
  obtain ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hnr⟩ := h
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_block (body := body) stk bt es
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hcode ▸ ht
  have htK := ht₀.steps henter
  have hdK := diverges_through_steps henter ht₀ (hcode ▸ hd)
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := Sim.ContextTyped.label htK
  rcases diverges_label_seq_split hdK with hdb | ⟨⟨rcs, rcf, rcc⟩, hbr, hsb, hd₁⟩
  · exact .block har ⟨⟨nr :: labels, ret, ob, hS, hb', htb⟩, hdb,
      fun h => hnr (hdr_lift (fun _ => ReachO.block har) h)⟩
  dsimp only at hsb hd₁
  obtain ⟨fl, oc, hev, he, hm⟩ := body_end_label hT hH hS hb' htb hbr hsb hd₁
  dsimp only at hev he
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK hbr
  obtain ⟨vs, hvs, ht₂, hd₂⟩ :=
    div_block_exit he hm (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm htL hd₁
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2' := Interp.chk_after (ext := Interp.noExt) inv1 hp hnr' h2
  refine .blockK har hev hvs ⟨⟨labels, ret, out, Interp.storeChk_inv inv1 hS, h2', ?_⟩, ?_,
    fun h => hnr (hdr_lift (fun _ => ReachO.blockK har hev hvs) h)⟩
  · rwa [Interp.stack_after]
  · rwa [Interp.stack_after]

/-- **The loop case.** -/
theorem div_loop (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr}
    (h : DivHyp o host s f stk (.loop bt body :: es)) :
    DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk (.loop bt body :: es) := by
  obtain ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hnr⟩ := h
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_loop (body := body) stk bt es
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hcode ▸ ht
  have htK := ht₀.steps henter
  have hdK := diverges_through_steps henter ht₀ (hcode ▸ hd)
  have htb : Sim.ContextTyped ⟨s, f, vals (stk.take np).reverse ++
      expression (Binaryen.BExpr.lowerList body)⟩ := Sim.ContextTyped.label htK
  rcases diverges_label_seq_split hdK with hdb | ⟨⟨rcs, rcf, rcc⟩, hbr, hsb, hd₁⟩
  · exact .loop har ⟨⟨np :: labels, ret, ob, hS, hb', htb⟩, hdb,
      fun h => hnr (hdr_lift (fun _ => ReachO.loop har) h)⟩
  dsimp only at hsb hd₁
  obtain ⟨fl, oc, hev, he, hm⟩ := body_end_label hT hH hS hb' htb hbr hsb hd₁
  dsimp only at hev he
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have htL := typed_label_steps hT htK hbr
  dsimp only at htL
  rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
  · -- falls through
    have hlen : ws.length = nr := Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) (vs := ws) inv1 hp hlen.ge h2
    have hx := Interp.exit_normal (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (stk.drop np).reverse
      rest
    have htake : ws.take nr = ws := List.take_of_length_le hlen.le
    refine .loopK har hev ⟨⟨labels, ret, out, Interp.storeChk_inv inv1 hS, h2', ?_⟩, ?_,
      fun h => hnr (hdr_lift (fun _ => ReachO.loopK har hev) h)⟩
    · rw [htake]
      simpa [List.reverse_append] using htL.steps hx
    · rw [htake]
      simpa [List.reverse_append] using diverges_through_steps hx htL hd₁
  · -- branches back to the loop
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    have hx := Interp.exit_br0 (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm hnp
      (stk.drop np).reverse rest
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : Interp.chk rcs.funcs rcf.module rcf.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact Interp.chk_inv inv1 hc
    refine .loopBack har hev ⟨⟨labels, ret, out, Interp.storeChk_inv inv1 hS, hc', ?_⟩, ?_,
      fun h => hnr (hdr_lift (fun _ => ReachO.loopBack har hev) h)⟩
    · rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression, hrest] using htL.steps hx
    · rw [Interp.code_loop]
      simpa [List.reverse_append, List.append_assoc, expression, hrest] using
        diverges_through_steps hx htL hd₁
  · exact (div_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id htL hd₁).elim
  · exact (div_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) htL hd₁).elim
  · exact (div_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) htL hd₁).elim
  · rcases oc <;> simp only [Interp.FlowMatch] at hm

/-- **The `if` case.** -/
theorem div_if (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (h : DivHyp o host s f stk (.if_ bt cnd t el :: es)) :
    DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk (.if_ bt cnd t el :: es) := by
  obtain ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hnr⟩ := h
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt cnd t el es
  have htc : Sim.ContextTyped
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  rw [hcode] at hd
  rcases diverges_seq_split hd with hdc | ⟨⟨s₁, f₁, k₁⟩, ws, hrun₁, hw, hd₁⟩
  · exact .cond ⟨⟨labels, ret, oc, hS, hco, htc⟩, hdc,
      fun h => hnr (hdr_lift (fun _ => ReachO.cond) h)⟩
  dsimp only at hw hd₁
  obtain ⟨stk', hev, rfl⟩ := evalH_of_vals hT hH hS hco htc hrun₁ hw
  dsimp only at hev
  have hafter : Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
        (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
      ⟨s₁, f₁, vals stk'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩ := by
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS hco)
  have ht₁ := ContextTyped.steps_typed hT ht hafter
  obtain ⟨hoc, inv0⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hco
  obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [Interp.arity_eq, inv0.2.1]; exact ha
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := Interp.truthy_progressH ht₁
  obtain ⟨inv1, hp, hendArm, h2'⟩ :=
    Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := profile o) hH hev).1 har hc
  obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
  have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb'
  have hS₁ := Interp.storeChk_inv inv1 hS
  have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
    (el := el) (rest := rest) hb
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har) rest
  have hpre := (Relation.ReflTransGen.single hif).trans henter
  have htK := ht₁.steps hpre
  have hdK := diverges_through_steps hpre ht₁ hd₁
  have htarm : Sim.ContextTyped ⟨s₁, f₁, vals (stk₁.take np).reverse ++
      expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ := Sim.ContextTyped.label htK
  rcases diverges_label_seq_split hdK with hda | ⟨⟨rcs, rcf, rcc⟩, hbr, hsb, hd₂⟩
  · exact .arm hev hb har ⟨⟨nr :: labels, ret, ob, hS₁, hb'', htarm⟩, hda,
      fun h => hnr (hdr_lift (fun _ => ReachO.arm hev hb har) h)⟩
  dsimp only at hsb hd₂
  obtain ⟨fl, oc', hevb, he, hm⟩ := body_end_label hT hH hS₁ hb'' htarm hbr hsb hd₂
  dsimp only at hevb he
  obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hb''
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK hbr
  obtain ⟨vs, hvs, ht₂, hd₃⟩ :=
    div_block_exit he hm (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm htL hd₂
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2₂ := Interp.chk_after (ext := Interp.noExt) inv2 hp hnr' (Interp.chk_inv inv1 h2')
  refine .ifK hev hb har hevb hvs
    ⟨⟨labels, ret, out, Interp.storeChk_inv (inv1.trans inv2) hS, h2₂, ?_⟩, ?_,
      fun h => hnr (hdr_lift (fun _ => ReachO.ifK hev hb har hevb hvs) h)⟩
  · rwa [Interp.stack_after]
  · rwa [Interp.stack_after]

/-! ## The whole run -/

/-- One unfolding of divergence, at every tree list satisfying the invariant. -/
theorem div_step (hT : HostTyped host) (hH : Interp.NativeHostSlice host) :
    ∀ s f stk es, DivHyp o host s f stk es →
      DivStepO (hostCall host) (DivHyp o host) (DivHyp o host) s f stk es := by
  intro s f stk es h
  rcases es with _ | ⟨e, es⟩
  · exfalso
    obtain ⟨-, hd, -⟩ := h
    obtain ⟨b, hb, -⟩ := hd.unfold
    exact Sim.Step.not_vals (by simpa [expression] using hb)
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, cnd, t, el⟩ | ⟨bt, cs, body⟩
    · by_cases hcall : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hcall
        exact div_call hT hH h
      · exact div_op_flat hT hH (fun x hx => hcall ⟨x, hx⟩) h
    · exact div_block hT hH h
    · exact div_loop hT hH h
    · exact div_if hT hH h
    · exfalso
      obtain ⟨⟨labels, ret, out, -, hc, -⟩, -⟩ := h
      obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
      simp [Interp.chk1E] at h1

/-- **Divergent runs with host calls**, deterministic profile `profile o`, for a host with
typed answers (`HostTyped`) in the native host slice: a divergent Core run of arity-checked,
typed trees reaches a host call the host may diverge on (`HostDivReach`), or the open native
semantics with host calls diverges coinductively (`EvalDivO (hostCall host)`). -/
theorem div_whole {o : GrowOracle} (hT : HostTyped host) (hH : Interp.NativeHostSlice host) :
    ∀ s f stk es labels ret out, Interp.StoreChk s.funcs →
      Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
      Diverges (profile o) host
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
      HostDivReach host s f stk es ∨ EvalDivO (hostCall host) s f stk es := by
  intro s f stk es labels ret out hS hc ht hd
  by_cases hr : HostDivReach host s f stk es
  · exact .inl hr
  · exact .inr (evalDivO_of_coind (div_step (o := o) hT hH) s f stk es
      ⟨⟨labels, ret, out, hS, hc, ht⟩, hd, hr⟩)

end Silmaril.Proofs.Wasm.Abstract.HostEval
