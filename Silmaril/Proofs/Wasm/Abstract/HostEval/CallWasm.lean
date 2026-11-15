module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Backward
public import Silmaril.Wasm.SingleThreaded.HeadInversion

/-!
# The backward case of a call of a Wasm function (proofs)

The two steps into a Wasm callee are its only steps: `call x` resolves the
function (`call_step_unique`), and `call_ref` of Wasm code enters its frame on
exactly the top `ps.length` values (`callRef_wasm_step_unique`). So the callee
body's run is strictly shorter than the whole run, and is given by the case of
the callee body on that shorter run; the frame and label of the call are left by
host-free steps, as the native call returns.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

local macro "not_family" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

theorem head_call' {s : Store H} {f : Frame} {args : List Val} {x : FuncIdx} {c₀ : Config H}
    (h : Det.Head P s f args (.plain (.call x)) c₀) : args = [] ∧ ∃ a fi,
      f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c₀ = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  cases h with
  | call hx hf => exact ⟨rfl, _, _, hx, hf, rfl⟩
  | _ => not_family

/-- **`call x` under values has one step**: it resolves the function. -/
theorem call_step_unique {s : Store H} {f : Frame} {stk : List Val} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} {rest : List Admin} {c₁ : Config H}
    (hfi : s.func? f x = some (a, fi))
    (h : Step P host ⟨s, f, vals stk.reverse ++ .plain (.call x) :: rest⟩ c₁) :
    c₁ = ⟨s, f, vals stk.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  have h' := Interp.noHost_of_plain rfl rfl h
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) h'
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_call' hh
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  simp only [List.append_nil] at hW
  subst hW
  simp

theorem head_callRef' {s : Store H} {f : Frame} {args : List Val} {c : Admin} {c₀ : Config H}
    (hc : c.IsCallRef) (h : Det.Head P s f args c c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Validation.Ty (.list .val)) (code : Func),
      args = vs ++ [.ref (.func a)] ∧ s.funcs[a]? = some fi ∧ Validation.Expand fi.type (.func ps rs) ∧
      vs.length = ps.length ∧ fi.code = .wasm code ∧
      c₀ = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  rcases Det.IsCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> cases h with
  | callRefNull _ => exact .inl ⟨rfl, rfl⟩
  | callRefFunc ha _ hf he hn hcode => exact .inr ⟨_, _, _, _, _, _, ha, hf, he, hn, hcode, rfl⟩
  | _ => not_family

/-- **`call_ref` of a Wasm function has one step**: it enters the callee's frame on
exactly the top `ps.length` values. -/
theorem callRef_wasm_step_unique {s : Store H} {f : Frame} {stk : List Val} {a : Nat}
    {fi : FuncInst H} {fn : Func} {ps rs : Validation.Ty (.list .val)} {rest : List Admin}
    {c₁ : Config H} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (he : Validation.Expand fi.type (.func ps rs)) (hp : ps.length ≤ stk.length)
    (h : Step P host ⟨s, f, vals stk.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ c₁) :
    c₁ = ⟨s, f, vals (stk.drop ps.length).reverse ++
      [.frame rs.length (Frame.forCall fi.module (stk.take ps.length).reverse fn.locals)
        [.label rs.length [] (expression fn.body)]] ++ rest⟩ := by
  have hcode' : vals stk.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest) =
      vals (stk.reverse ++ [.ref (.func a)]) ++ .callRefType fi.type :: rest := by
    simp [vals, Val.toAdmin]
  rw [hcode'] at h
  have hd : decompose? s (vals (stk.reverse ++ [.ref (.func a)]) ++ .callRefType fi.type :: rest) =
      none := by
    rw [decompose?_of_split (splitVals_vals_cons rfl rest), decompHead_of_IsCallRef (d := .callRefType fi.type) trivial]
    simp [topRedex, hostArity?, hf, hcode]
  have h' : Step P Det.noHost ⟨s, f, vals (stk.reverse ++ [.ref (.func a)]) ++
      .callRefType fi.type :: rest⟩ c₁ := by
    rcases Step.split_host h with h | ⟨E, a', hh, args, hdc, -⟩
    · exact h
    · rw [hd] at hdc; cases hdc
  obtain ⟨vs₀, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) h'
  rcases head_callRef' (c := .callRefType fi.type) trivial hh with ⟨rfl, -⟩ | ⟨vs, a', fi', ps', rs', code, rfl, hf', he', hn, hc', rfl⟩
  · have := congrArg List.getLast? hW
    simp at this
  · rw [← List.append_assoc] at hW
    obtain ⟨hW', hl⟩ := List.append_inj' hW rfl
    simp only [List.cons.injEq, Val.ref.injEq, Ref.func.injEq, and_true] at hl
    subst hl
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    rw [hcode] at hc'
    obtain rfl := FuncCode.wasm.inj hc'
    have := (Validation.Expand.iff.1 he).symm.trans (Validation.Expand.iff.1 he')
    simp only [Option.some.injEq, Validation.Ty.func.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    have e : stk.reverse = (stk.drop ps.length).reverse ++ (stk.take ps.length).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e] at hW'
    have hlen : vs.length = (stk.take ps.length).reverse.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨rfl, rfl⟩ := List.append_inj' hW'.symm hlen
    simp

/-- A call frame and label around a stuck pending call are stuck, and pending. -/
theorem pending_frame {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} (hp : Pending host s b) (hb : ∀ c', ¬ Step P host ⟨s, F, b⟩ c') :
    (∀ c', ¬ Step P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ c') ∧
      Pending host s (vals ws ++ [.frame n F [.label n [] b]] ++ rest) := by
  have hpl : Pending host s (vals [] ++ .label n [] b :: []) := Pending.label hp
  have hpe : Pending host s (vals ws ++ [.frame n F [.label n [] b]] ++ rest) := by
    simpa using Pending.frame (ws := ws) (n := n) (F := F) (rest := rest) (by simpa using hpl)
  refine ⟨fun c' h => ?_, hpe⟩
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial (by simpa using h)
  rcases Step.frame_inv h₀ with ⟨s', F', is', hin, -⟩ | ⟨out, hex, -⟩
  · rcases Step.label_inv hin with ⟨s'', F'', b', hin', -⟩ | ⟨out, hex, -⟩
    · exact hb _ hin'
    · exact pending_not_labelExit hp hex
  · exact frameExit_label hex rfl

/-- A call reached in a callee body is reached under the callee's frame and label. -/
theorem atCall_frame_label {s : Store H} {a : Nat} {us ws : List Val} {n : Nat} {F : Frame}
    {b rest : List Admin} (h : AtCall s a us b) :
    AtCall s a us (vals ws ++ [.frame n F [.label n [] b]] ++ rest) := by
  have hl : AtCall s a us (vals [] ++ .label n [] b :: []) := AtCall.label h
  simpa using AtCall.frame (ws := ws) (n := n) (F := F) (rest := rest) (by simpa using hl)

/-- **The backward case of `call_ref` of a Wasm function** on the top `ps.length`
values, deterministic profile. `call_ref` is the only step into the callee, so its
body runs strictly shorter than the whole run, in its frame and label
(`stepsN_frame_seq_split`), as `ihbody` says. A blocked body blocks the call;
otherwise the body ran natively (`bodyCall`, hence `hostCall`), and the frame is
left by host-free steps: with the callee's results, or by a trap. The callee's
result arity and that it returns or traps are the hypothesis `hret`. -/
theorem back_callRef_wasm {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    (hf : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hrun₁ : StepsN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body) cb)
    (hret : ∀ r, EvalH host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
        (Binaryen.liftInstrs fn.body) r →
      (∀ vs, r.2.2.retVals = some vs →
        rs.length ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = rs.length) ∧
      (r.2.2.retVals = none → r.2.2 = .trap)) :
    (Pending host c.store c.code ∧
        ∃ y, PendO (hostCall host) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ y ∧
          BlockedAt host c y) ∨
      ∃ s₂ fl, hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ c) ∨
          (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)) := by
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  -- `call_ref`, the only step, enters the frame
  have hp' : ps'.length ≤ stk₁.length := by omega
  have hs₂ : Step (SingleThreaded.profile o) host
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩
      ⟨s₁, f₁, vals (stk₁.drop ps'.length).reverse ++
        [.frame rs'.length (Frame.forCall fi.module (stk₁.take ps'.length).reverse fn.locals)
          [.label rs'.length [] (expression fn.body)]] ++ rest⟩ := by
    rw [code_call_split stk₁ ps'.length]
    have hn : (stk₁.take ps'.length).reverse.length = ps'.length := by
      simp only [List.length_reverse, List.length_take]; omega
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := SingleThreaded.profile o) (host := host)
      (stk₁.drop ps'.length).reverse rest
      (Step.callRefFunc (c := .callRefType fi.type) trivial hf hex hn hcode)
  obtain ⟨n₂, rfl, hrun₂⟩ :=
    stepsN_unique (fun c₁ h => callRef_wasm_step_unique hf hcode hex hp' h) hs₂ hrun₁ hend
  rw [hpl, hrl] at hrun₂
  -- the body in its frame
  obtain ⟨cb, N₁, hN₁, hb, hsb, hk⟩ := stepsN_frame_seq_split hrun₂ hend
  have hb' : StepsN (SingleThreaded.profile o) host N₁
      ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cb := by
    simpa [Binaryen.lowerList_liftInstrs, vals] using hb
  rcases ihbody N₁ (by omega) cb hb' hsb with ⟨⟨s₂, f₂, fl⟩, hev, oc, he, hst, hfr, hm⟩ |
      ⟨hpend, y, hy, hbl⟩
  · right
    dsimp only at hst hfr hm
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (rcs, fl) := by
      rw [hostCall_fixpoint]
      exact .inl ⟨fi, fn, ps, rs, rcf, hf, hcode, hty, hev⟩
    refine ⟨rcs, fl, hcall, ?_⟩
    obtain ⟨hvals, htrap⟩ := hret _ hev
    cases hvs : fl.retVals with
    | some vs =>
      obtain ⟨hrs, hnorm⟩ := hvals vs hvs
      obtain ⟨s', res, hret', hK⟩ := Silmaril.Wasm.Logic.Core.frame_ends (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (f := f₁) he
        (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
      obtain ⟨rfl, rfl⟩ := hK
      have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (stk₁.drop ps.length).reverse rest hret'
      obtain ⟨m, hm', h⟩ := stepsN_through_steps hx hk hend
      refine .inl ⟨vs, m, by omega, rfl, ?_⟩
      simpa [Interp.stack_after] using h
    | none =>
      have hfl := htrap hvs
      subst hfl
      have hc' : rcc = [.trap] := by
        rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
        exact he
      subst hc'
      have hout : Steps (SingleThreaded.profile o) SingleThreaded.Det.noHost
          ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++
            [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ rest⟩
          ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++ rest⟩ :=
        Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
          ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
      obtain ⟨m, -, h⟩ := stepsN_through_steps hout hk hend
      have hc := steps_trap_head (by simpa using stepsN_steps h) hend
      subst hc
      exact .inr ⟨rfl, .trap, rfl, rfl, rfl, trivial⟩
  · left
    obtain ⟨hstk, hpe⟩ := pending_frame (P := SingleThreaded.profile o) (f := f₁)
      (ws := (stk₁.drop ps.length).reverse) (n := rs.length) (rest := rest) hpend hsb
    have := stepsN_of_stuck hstk hk
    subst this
    exact ⟨hpe, y, pendO_of_body (x := ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩) hf hcode hy,
      blockedAt_mono hbl rfl atCall_frame_label⟩


/-- **The backward case of a direct call of a Wasm function**, deterministic
profile: `call x` is the only step, then `back_callRef_wasm`. -/
theorem back_call_wasm {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body) cb)
    (hret : ∀ r, EvalH host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
        (Binaryen.liftInstrs fn.body) r →
      (∀ vs, r.2.2.retVals = some vs →
        rs.length ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = rs.length) ∧
      (r.2.2.retVals = none → r.2.2 = .trap)) :
    (Pending host c.store c.code ∧
        ∃ y, PendO (hostCall host) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ y ∧
          BlockedAt host c y) ∨
      ∃ s₂ fl, hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ c) ∨
          (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)) := by
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  have hs₁ : Step (SingleThreaded.profile o) host
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := SingleThreaded.profile o) (host := host)
      stk₁.reverse rest (Step.call hx hf)
  obtain ⟨n₁, rfl, hrun₁⟩ := stepsN_unique (fun c₁ h => call_step_unique hfi h) hs₁ hrun hend
  rcases back_callRef_wasm hf hcode hty hp hrun₁ hend
      (fun m hm cb h hs => ihbody m (by omega) cb h hs) hret with hp' |
    ⟨s₂, fl, hcall, ⟨vs, m, hm, hvs, hk⟩ | htr⟩
  · exact .inl hp'
  · exact .inr ⟨s₂, fl, hcall, .inl ⟨vs, m, by omega, hvs, hk⟩⟩
  · exact .inr ⟨s₂, fl, hcall, .inr htr⟩

/-- **A direct call, as a tree**, for any callee: the arguments by `back_op_args`,
the call by `hcase` (`back_call_host` for a host function, `back_call_wasm` for a
Wasm function), the following trees by `ihes`. -/
theorem back_op_call {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hcase : ∀ s₁ f₁ stk₁ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩ c →
      (Pending host c.store c.code ∧
        ∃ (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
          (y : (wasmOShape H).self.Op), s₁.func? f₁ x = some (a, fi) ∧
          Validation.DefType.funcType? fi.type = some (ps, rs) ∧
          (y = ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ ∨
            PendO (hostCall host) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ y) ∧
          BlockedAt host c y) ∨
        ∃ (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H)
          (fl : Binaryen.Flow), s₁.func? f₁ x = some (a, fi) ∧
          Validation.DefType.funcType? fi.type = some (ps, rs) ∧
          hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
          ((∃ vs m', m' ≤ n ∧ fl.retVals = some vs ∧
              StepsN (SingleThreaded.profile o) host m'
                ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
                  expression (Binaryen.BExpr.lowerList es)⟩ c) ∨
            (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)))
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) (a : Nat) (fi : FuncInst H)
      (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow) (vs : List Val)
      (m : Nat), m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      s₁.func? f₁ x = some (a, fi) → Validation.DefType.funcType? fi.type = some (ps, rs) →
      hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) → fl.retVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es c) :
    BackOut host s f stk (.op (.call x) args :: es) c := by
  refine back_op_args hrun hend ihargs fun s₁ f₁ stk₁ m hm hev hrun₁ => ?_
  rcases hcase s₁ f₁ stk₁ m hm hev hrun₁ with ⟨hpend, a, fi, ps, rs, y, hfi, hty, hy, hb⟩ |
      ⟨a, fi, ps, rs, s₂, fl, hfi, hty, hcall, ⟨vs, m', hm', hvs, hk⟩ | ⟨rfl, hends⟩⟩
  · exact .inr ⟨hpend, y, reachP_call hev hfi hty hy, hb⟩
  · rcases ihes s₁ f₁ stk₁ a fi ps rs s₂ fl vs m' hm' hev hfi hty hcall hvs hk with
        ⟨r, hev', hr⟩ | ⟨hp', y, hy, hb⟩
    · exact .inl ⟨r, .callOk hev hfi hty hcall hvs hev', hr⟩
    · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.callK hev hfi hty hcall hvs) hy, hb⟩
  · exact .inl ⟨_, .callTrap hev hfi hty hcall, hends⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
