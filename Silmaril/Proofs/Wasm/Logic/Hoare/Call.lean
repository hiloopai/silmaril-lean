module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Frame

/-!
# The every-run logic: instructions, calls and recursion

* `Safe.head`: the generic rule for a plain instruction that cannot call the
  host (every Core 3.0 instruction except `call_ref`, its type-annotated form and
  `throw_ref`): the code is safe if some head step exists and every head step
  (`Silmaril.Wasm.SingleThreaded.Det.Head`, which every step at such a head is, by
  `Silmaril.Wasm.SingleThreaded.inert_head_inv`) leads to safe code.
* Function specifications: `FSpecAt.of_body` proves a specification of a Wasm
  function from its body (one step to enter the frame, then `Safe.frame` and
  `Safe.label`); `Safe.call` uses one at a call site; `Ctx.valid_of_step` is the
  rule for **mutual recursion**: if every specification of a context holds for
  `n + 1` steps whenever all hold for `n` steps, all hold (Löb induction on the
  step index).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## The generic rule for a plain instruction -/

/-- A plain instruction that cannot select a host call. -/
def Inert (i : Instr) : Prop :=
  (Admin.plain i).val? = none ∧ i ≠ .throwRef ∧ (Admin.plain i).isCallRef = false

/-- **The head rule.** A plain inert instruction under the values `W` is safe for
`n + 1` steps if it has a head step and every head step leads to code safe for
`n` steps. -/
theorem Safe.head {n : Nat} {s : Store H} {f : Frame} {W : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H} (hi : Inert i)
    (hp : ∃ vs args c₀, W = vs ++ args ∧ Head P s f args (.plain i) c₀)
    (hs : ∀ vs args c₀, W = vs ++ args → Head P s f args (.plain i) c₀ →
      Safe P host Q n ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩) :
    Safe P host Q (n + 1) ⟨s, f, vals W ++ .plain i :: rest⟩ := by
  obtain ⟨vs, args, ⟨s₀, f₀, c₀⟩, rfl, hh⟩ := hp
  have h₁ : Step P host ⟨s, f, vals args ++ [.plain i]⟩ ⟨s₀, f₀, c₀⟩ :=
    Step.of_noHost host hh.toStep
  have h₂ : Step P host ⟨s, f, vals (vs ++ args) ++ .plain i :: rest⟩
      ⟨s₀, f₀, vals vs ++ c₀ ++ rest⟩ := by
    simpa using Sim.Step.append_right (Sim.Step.vals_left h₁ vs) rest
  refine Safe.of_step ⟨_, h₂⟩ fun c' hst => ?_
  obtain ⟨vs', args', c₁, hW, hh', rfl⟩ := SingleThreaded.inert_head_inv hi.1 hi.2.1 hi.2.2 hst
  exact hs vs' args' c₁ hW hh'

/-- The head rule for every-run weakest preconditions. -/
theorem HWP.head {s : Store H} {f : Frame} {W : List Val} {i : Instr} {rest : List Admin}
    {Q : Post H} (hi : Inert i)
    (hp : ∃ vs args c₀, W = vs ++ args ∧ Head P s f args (.plain i) c₀)
    (hs : ∀ vs args c₀, W = vs ++ args → Head P s f args (.plain i) c₀ →
      HWP P host c₀.store c₀.frame (vals vs ++ c₀.code ++ rest) Q) :
    HWP P host s f (vals W ++ .plain i :: rest) Q
  | 0 => trivial
  | n + 1 => Safe.head hi hp fun vs args c₀ hW hh => hs vs args c₀ hW hh n

/-! ## Head steps of calls -/

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

/-- The head step of `call x`. -/
theorem head_call {s : Store H} {f : Frame} {args : List Val} {x : FuncIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.call x)) c₀) : args = [] ∧ ∃ a fi,
      f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c₀ = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  cases h with
  | call hx hf => exact ⟨rfl, _, _, hx, hf, rfl⟩
  | _ => head_absurd

/-- The head step of `return_call x`. -/
theorem head_returnCall {s : Store H} {f : Frame} {args : List Val} {x : FuncIdx}
    {c₀ : Config H} (h : Head P s f args (.plain (.returnCall x)) c₀) : args = [] ∧ ∃ a fi,
      f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c₀ = ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ := by
  cases h with
  | returnCall hx hf => exact ⟨rfl, _, _, hx, hf, rfl⟩
  | _ => head_absurd

/-- The head steps of a `CALL_REF` form. -/
theorem head_callRef {s : Store H} {f : Frame} {args : List Val} {c : Admin} {c₀ : Config H}
    (hc : c.IsCallRef) (h : Head P s f args c c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ (vs : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)) (code : Func),
      args = vs ++ [.ref (.func a)] ∧ s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
      vs.length = ps.length ∧ fi.code = .wasm code ∧
      c₀ = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  rcases SingleThreaded.Det.IsCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> cases h with
  | callRefNull _ => exact .inl ⟨rfl, rfl⟩
  | callRefFunc ha _ hf he hn hcode => exact .inr ⟨_, _, _, _, _, _, ha, hf, he, hn, hcode, rfl⟩
  | _ => head_absurd

/-! ## Entering a Wasm function -/

/-- A call of a Wasm function has no host-call redex. -/
theorem decompose?_call_wasm {s : Store H} {W : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst H} {code : Func} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) : decompose? s (vals W ++ [.ref (.func a), c]) = none := by
  have hw : SingleThreaded.splitVals (vals W ++ [.ref (.func a), c]) =
      (W ++ [.ref (.func a)], [c]) := by
    rw [show vals W ++ [.ref (.func a), c] = vals (W ++ [.ref (.func a)]) ++ c :: [] by
      simp [vals, Val.toAdmin], SingleThreaded.splitVals_vals_cons (Admin.val?_of_IsCallRef hc)]
  rw [SingleThreaded.decompose?_of_split hw, SingleThreaded.decompHead_of_IsCallRef hc]
  unfold SingleThreaded.topRedex
  simp [SingleThreaded.hostArity?_none_of_wasm hf hcode]

/-- The configuration a call of a Wasm function enters. -/
def callFrame (fi : FuncInst H) (code : Func) (rs : Ty (.list .val)) (args : List Val) : Admin :=
  .frame rs.length (Frame.forCall fi.module args code.locals)
    [.label rs.length [] (expression code.body)]

/-- The only step of a call of a Wasm function: it enters the function's frame. -/
theorem call_step_inv {s : Store H} {f : Frame} {vs₀ args : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} {c' : Config H}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hst : Step P host ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩ c') :
    c' = ⟨s, f, vals vs₀ ++ [callFrame fi code rs args]⟩ := by
  have e : vals vs₀ ++ vals args ++ [.ref (.func a), c] =
      vals (vs₀ ++ args ++ [.ref (.func a)]) ++ c :: [] := by simp [vals, Val.toAdmin]
  have e' : vals vs₀ ++ vals args ++ [.ref (.func a), c] =
      vals (vs₀ ++ args) ++ [.ref (.func a), c] := by simp
  have hd : decompose? s (vals vs₀ ++ vals args ++ [.ref (.func a), c]) = none :=
    e' ▸ decompose?_call_wasm hc hf hcode
  have hst' := step_noHost hd hst
  obtain ⟨vs, args', c₀, hW, hh, rfl⟩ := SingleThreaded.hostFree_head_inv
    (Admin.val?_of_IsCallRef hc) (by rintro rfl; exact hc) (by rintro rfl; exact hc) (e ▸ hst')
  rcases head_callRef hc hh with ⟨rfl, -⟩ | ⟨vs', a', fi', ps', rs', code', rfl, hf', he', hn', hc', rfl⟩
  · have := congrArg List.getLast? hW
    simp at this
  · exact call_frame_eq hf hcode he hn hW hf' he' hn' hc'
where
  call_frame_eq {vs vs' : List Val} {a' : Nat} {fi' : FuncInst H} {ps' rs' : Ty (.list .val)}
      {code' : Func} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
      (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
      (hW : vs₀ ++ args ++ [.ref (.func a)] = vs ++ (vs' ++ [.ref (.func a')]))
      (hf' : s.funcs[a']? = some fi') (he' : Expand fi'.type (.func ps' rs'))
      (hn' : vs'.length = ps'.length) (hc' : fi'.code = .wasm code') :
      (⟨s, f, vals vs ++ [Admin.frame rs'.length (Frame.forCall fi'.module vs' code'.locals)
        [.label rs'.length [] (expression code'.body)]] ++ []⟩ : Config H) =
        ⟨s, f, vals vs₀ ++ [callFrame fi code rs args]⟩ := by
    have hW' : (vs₀ ++ args) ++ [Val.ref (.func a)] = (vs ++ vs') ++ [.ref (.func a')] := by simpa using hW
    obtain ⟨hW₁, ha⟩ := SingleThreaded.Det.append_singleton_inj.mp hW'
    obtain rfl : a' = a := by injection ha with h; injection h with h; exact h.symm
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    have hE : (Ty.func ps' rs' : CCompType) = Ty.func ps rs := SingleThreaded.Det.Expand.det he' he
    injection hE with hps hrs
    subst hps hrs
    have hl : (vs₀ ++ args).length = (vs ++ vs').length := congrArg List.length hW₁
    rw [List.length_append, List.length_append] at hl
    obtain ⟨rfl, rfl⟩ := List.append_inj hW₁ (by omega)
    obtain rfl : code' = code := by rw [hcode] at hc'; injection hc' with h; exact h.symm
    simp [callFrame]

/-! ## Function specifications -/

/-- **A specification from the body** (Wasm Logic's `[call]`): one step enters the
frame, after which the body must be safe for `n` steps. -/
theorem FSpecAt.of_body {n a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    {S : FSpec H} (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hbody : ∀ s args, S.pre s args → ∀ (f : Frame) (vs₀ : List Val),
      Safe P host (bodyPostK P host rs.length f vs₀ (callPost f vs₀ (S.post s args)) n) n
        ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩) :
    FSpecAt P host (n + 1) a S := by
  intro s args hpre f vs₀ c hc
  have hf : s.funcs[a]? = some fi := hfi s args hpre
  have hn : args.length = ps.length := hlen s args hpre
  have hstep : Step P host ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs₀ ++ [callFrame fi code rs args]⟩ := by
    simpa [callFrame] using Sim.Step.vals_left (Step.callRefFunc hc hf he hn hcode) vs₀
  refine Safe.of_step ⟨_, hstep⟩ fun c' hst => ?_
  rw [call_step_inv hc hf hcode he hn hst]
  exact Safe.frame (k := n) (by omega) (Safe.label (us := []) (k := n) (by omega) (hbody s args hpre f vs₀))

/-- **The call rule.** A specification that holds for `n` steps gives the safety of
a call followed by `rest`, if every outcome the specification allows makes the
continuation safe. -/
theorem Safe.call {n a : Nat} {S : FSpec H} {s : Store H} {f : Frame} {vs₀ args : List Val}
    {c : Admin} {rest : List Admin} {Q : Post H} (hS : FSpecAt P host n a S) (hpre : S.pre s args)
    (hc : c.IsCallRef)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPostK P host rest Q n s' f o) :
    Safe P host Q n ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c] ++ rest⟩ := by
  refine Safe.seq le_rfl ((hS s args hpre f vs₀ c hc).post_mono fun s' f' o h => ?_)
  have hf' : f' = f := h.1
  subst hf'
  exact hpost s' o h

/-- **The call rule for `call x`.** -/
theorem Safe.callIdx {n a : Nat} {S : FSpec H} {s : Store H} {f : Frame} {vs₀ args : List Val}
    {x : FuncIdx} {fi : FuncInst H} {rest : List Admin} {Q : Post H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : FSpecAt P host n a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPostK P host rest Q n s' f o) :
    Safe P host Q (n + 1) ⟨s, f, vals (vs₀ ++ args) ++ .plain (.call x) :: rest⟩ := by
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨vs₀ ++ args, [], _, by simp, .call hx hf⟩ ?_
  intro vs args' c₀ hW hh
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_call hh
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hvs : vs = vs₀ ++ args := by simpa using hW.symm
  subst hvs
  simpa using Safe.call (vs₀ := vs₀) (rest := rest) hS hpre
    (show Admin.IsCallRef (.callRefType fi'.type) from trivial) hpost

/-- The `CALL_REF` a tail call turns into when it leaves its frame. -/
theorem isCallRef_retToCallIn {c : Admin} (m : ModuleInst) (h : c.IsReturnCallRef) :
    (c.retToCallIn m).IsCallRef := by
  rcases SingleThreaded.Det.IsReturnCallRef.cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · show (match m.types[y.toNat]? with
      | some d => Admin.callRefType d
      | none => Admin.plain (.callRef y)).IsCallRef
    split <;> trivial
  · trivial

/-- **The tail-call rule.** A tail call of a function with a specification that
holds for `k` steps is an allowed outcome of a body, if every outcome of the callee
is one the caller's postcondition allows. -/
theorem framePostK_tail {k m a : Nat} {f F : Frame} {us vs₁ args : List Val} {Q : Post H}
    {s : Store H} {c : Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} {S : FSpec H}
    (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : args.length = ps.length) (hS : FSpecAt P host k a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f us (S.post s args) s' f o → Q s' f o) :
    framePostK P host m f us Q k s F (.tail (vs₁ ++ args) a c) := by
  refine ⟨vs₁, args, fn, ps, rs, rfl, hf, he, hn, ?_⟩
  refine (hS s args hpre f us _ (isCallRef_retToCallIn F.module hc)).post_mono fun s' f' o h => ?_
  have hf' : f' = f := h.1
  subst hf'
  exact hpost s' o h

/-- `return_call x` exits the body with a tail call. -/
theorem Safe.returnCallIdx {n a : Nat} {s : Store H} {F : Frame} {vs : List Val} {x : FuncIdx}
    {fi : FuncInst H} {rest : List Admin} {Q : Post H}
    (hx : F.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hq : Q s F (.tail vs a (.returnCallRefType fi.type))) :
    Safe P host Q (n + 1) ⟨s, F, vals vs ++ .plain (.returnCall x) :: rest⟩ := by
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨vs, [], _, by simp, .returnCall hx hf⟩ ?_
  intro vs' args' c₀ hW hh
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_returnCall hh
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hvs : vs' = vs := by simpa using hW.symm
  subst hvs
  exact Safe.of_exits (o := .tail vs' _ (.returnCallRefType fi'.type)) ⟨trivial, rest, by simp⟩ hq

theorem HWP.returnCallIdx {a : Nat} {s : Store H} {F : Frame} {vs : List Val} {x : FuncIdx}
    {fi : FuncInst H} {rest : List Admin} {Q : Post H}
    (hx : F.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hq : Q s F (.tail vs a (.returnCallRefType fi.type))) :
    HWP P host s F (vals vs ++ .plain (.returnCall x) :: rest) Q
  | 0 => trivial
  | _ + 1 => Safe.returnCallIdx hx hf hq

/-! ## Mutual recursion -/

/-- **Mutual recursion** (Löb induction on the step index): if all specifications
of the context hold for `n + 1` steps whenever all hold for `n` steps, all hold. -/
theorem Ctx.valid_of_step {Γ : Ctx H} (h : ∀ n, Ctx.ValidAt P host n Γ → Ctx.ValidAt P host (n + 1) Γ) :
    Ctx.Valid P host Γ := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ _ _ _ => trivial
  | succ n ih => exact h n ih

theorem Ctx.ValidAt.mono {Γ : Ctx H} {n m : Nat} (hmn : m ≤ n) (h : Ctx.ValidAt P host n Γ) :
    Ctx.ValidAt P host m Γ :=
  fun a S hS s args hpre f vs₀ c hc => (h a S hS s args hpre f vs₀ c hc).mono hmn

end Silmaril.Wasm.Logic.Hoare
