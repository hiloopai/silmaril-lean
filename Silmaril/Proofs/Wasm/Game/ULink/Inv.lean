module

public import Silmaril.Proofs.Wasm.Game.ULink.Threads
public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.Binaryen.DirectizeRel

/-!
# Provider code inside the consumer's context: inversion

In the linked module a provider call runs *inside* the consumer's callout context `E`; in the
composite it is a separate thread at top level. `ProvCode s Y` describes the provider's
top-level code: a frame, a call with its arguments (`vals vs ++ [ref.func a, c]`, arity of the
function at `a`), a call on `null`, or a result.

* `step_fill_inv`: **a linked step of `E.fill Y`, for live provider code `Y`, is a provider step
  of `Y` in the hole of `E`**, with the same frame, and the provider code stays `ProvCode`
  (`Det.Step.decomp`: a step is a head step at the first non-value or a bubble; the first
  non-value of `E.fill Y` is the frame or call of `Y`, or a label, handler or frame of `E`,
  none of which bubbles).
* `decompose_fill`: the callouts of `E.fill Y` are those of `Y` in the context `E`.
* `fill_ne_result`: `E.fill Y` is not a result.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Proofs.Wasm.Game.Linking.Split

/-! ### Provider code -/

/-- Live top-level provider code. -/
def ProvLive (s : Store Nat) (Y : List Admin) : Prop :=
  (∃ n F B, Y = [.frame n F B]) ∨
  (∃ (vs : List Val) (a : Nat) (c : Admin) (fi : FuncInst Nat) (ps rs : Ty (.list .val)),
    Y = vals vs ++ [.ref (.func a), c] ∧ c.IsCallRef ∧ s.funcs[a]? = some fi ∧
    Expand fi.type (.func ps rs) ∧ vs.length = ps.length) ∨
  (∃ c, Y = [.ref .null, c] ∧ c.IsCallRef)

/-- Top-level provider code: live, or a result. -/
def ProvCode (s : Store Nat) (Y : List Admin) : Prop := ProvLive s Y ∨ ∃ r : Result, Y = r.toAdmin

/-- The first non-value of live code. -/
def LiveTop (x : Admin) : Prop :=
  (∃ n F B, x = .frame n F B) ∨ (∃ n c B, x = .label n c B) ∨ (∃ n cs B, x = .handler n cs B) ∨
    x.IsCallRef

/-- Code whose first non-value is live. -/
def LiveBody (B : List Admin) : Prop := ∃ W x R, fnv B = (W, x :: R) ∧ LiveTop x

theorem fnv_at {l : List Admin} {W : List Val} {x : Admin} {R : List Admin}
    (h : l = vals W ++ x :: R) (hx : x.val? = none) : fnv l = (W, x :: R) := by
  rw [h, fnv_vals_append, fnv_cons_of_none hx]
  simp

theorem LiveTop.val_none {x : Admin} (h : LiveTop x) : x.val? = none := by
  rcases h with ⟨n, F, B, rfl⟩ | ⟨n, c, B, rfl⟩ | ⟨n, cs, B, rfl⟩ | h
  · rfl
  · rfl
  · rfl
  · exact IsCallRef.val_none h

/-- The first non-value of live code is not one of `x`. -/
theorem live_ne {B : List Admin} (hB : LiveBody B) {W : List Val} {x : Admin} {R : List Admin}
    (h : B = vals W ++ x :: R) (hx : x.val? = none) (hn : ¬ LiveTop x) : False := by
  obtain ⟨W', x', R', hf, hl⟩ := hB
  have heq : (W, x :: R) = (W', x' :: R') := (fnv_at h hx).symm.trans hf
  obtain ⟨-, rfl, -⟩ : W = W' ∧ x = x' ∧ R = R' := by simpa using heq
  exact hn hl

theorem live_ne_vals {B : List Admin} (hB : LiveBody B) {vs : List Val} (h : B = vals vs) : False := by
  obtain ⟨W, x, R, hf, -⟩ := hB
  rw [h, fnv_vals] at hf
  cases hf

theorem notLive_br (l : LabelIdx) : ¬ LiveTop (.plain (.br l)) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | h) <;> cases h

theorem notLive_return : ¬ LiveTop (.plain .return_) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | h) <;> cases h

theorem notLive_trap : ¬ LiveTop .trap := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | h) <;> cases h

theorem notLive_throwRef : ¬ LiveTop (.plain .throwRef) := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | h) <;> cases h

theorem notLive_ret {c : Admin} (hc : c.IsReturnCallRef) : ¬ LiveTop c := by
  rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;>
    rintro (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | h) <;> cases h

theorem ret_val_none {c : Admin} (hc : c.IsReturnCallRef) : c.val? = none := by
  rcases IsReturnCallRef.cases hc with ⟨x, rfl⟩ | ⟨d, rfl⟩ <;> rfl

theorem exn_live {a : Nat} (hB : LiveBody [.ref (.exn a), .plain .throwRef]) : False :=
  live_ne hB (W := [Val.ref (.exn a)]) (R := []) rfl rfl notLive_throwRef

/-! ### Steps at a single non-value -/

/-- **A step of code whose first non-value is `x`** (neither a trap nor `THROW_REF`) is a head
step at `x`. -/
theorem step_single_inv {P : Profile} {s : Store Nat} {f : Frame} {pre : List Val} {x : Admin}
    {rest : List Admin} {d : Config Nat}
    (h : Execution.Core.Step P Det.noHost ⟨s, f, vals pre ++ [x] ++ rest⟩ d) (hx : x.val? = none)
    (ht : x ≠ .trap) (hr : x ≠ .plain .throwRef) :
    ∃ vs args c₀, pre = vs ++ args ∧ Head P s f args x c₀ ∧
      d = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  have hf : fnv (vals pre ++ [x] ++ rest) = (pre, x :: rest) := fnv_at (by simp) hx
  rcases Step.decomp h with ⟨vs, args, e, rest', c₀, hcode, hhead, hd⟩ | hb
  · have he : e.val? = none := (Head.good hhead).val_none
    have hf' : fnv (vals pre ++ [x] ++ rest) = (vs ++ args, e :: rest') :=
      fnv_at (by simpa [vals_append] using hcode) he
    obtain ⟨h1, rfl, rfl⟩ : pre = vs ++ args ∧ x = e ∧ rest = rest' := by
      simpa using hf.symm.trans hf'
    exact ⟨vs, args, c₀, h1, hhead, hd⟩
  · obtain ⟨p, q, u, r, -, ⟨hf', -, -⟩ | ⟨a, hf', -, -⟩⟩ := fnv_bubble hb
    · have h2 := congrArg Prod.snd (hf.symm.trans hf')
      simp only [List.cons.injEq] at h2
      exact (ht h2.1).elim
    · have h2 := congrArg Prod.snd (hf.symm.trans hf')
      simp only [List.cons.injEq] at h2
      exact (hr h2.1).elim

/-- A family head step does not happen at a control instruction. -/
theorem fam_control {k : Fam} {args : List Val} {e : Admin} (h : FamShape k (vals args ++ [e]))
    (hk : k ≠ .control) (he : famOf e = .control) : False :=
  hk ((famOf_of_shape h).2.symm.trans he)

/-! ### Head steps at frames, labels, handlers and calls -/

/-- A head step at a frame is a step under any outer frame; its result is provider code. -/
theorem head_frame {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {n : Nat}
    {F : Frame} {B : List Admin} {c₀ : Config Nat} (h : Head P s f args (.frame n F B) c₀) :
    args = [] ∧ c₀.frame = f ∧ ProvCode c₀.store c₀.code ∧
      ∀ g, Execution.Core.Step P Det.noHost ⟨s, g, [.frame n F B]⟩ ⟨c₀.store, g, c₀.code⟩ := by
  cases h with
  | parametric h => exact (fam_control (ParametricStep.shape h) (by decide) rfl).elim
  | numeric h => exact (fam_control (NumericStep.shape h) (by decide) rfl).elim
  | vector h => exact (fam_control (VectorStep.shape h) (by decide) rfl).elim
  | «variable» h => exact (fam_control (VariableStep.shape h) (by decide) rfl).elim
  | table h => exact (fam_control (TableStep.shape h) (by decide) rfl).elim
  | memory h => exact (fam_control (MemoryStep.shape h) (by decide) rfl).elim
  | reference h => exact (fam_control (RefStep.shape h) (by decide) rfl).elim
  | aggregate h => exact (fam_control (AggregateStep.shape h) (by decide) rfl).elim
  | callRefNull hc => exact hc.elim
  | callRefFunc _ hc => exact hc.elim
  | ctxtFrame h' => exact ⟨rfl, rfl, .inl (.inl ⟨_, _, _, rfl⟩), fun g => Step.ctxtFrame h'⟩
  | frameVals hb hn =>
    exact ⟨rfl, rfl, .inr ⟨.values _, rfl⟩, fun g => by rw [hb]; exact Step.frameVals hn⟩
  | returnFrame hb hn =>
    exact ⟨rfl, rfl, .inr ⟨.values _, rfl⟩, fun g => by rw [hb]; exact Step.returnFrame hn⟩
  | returnCallRefFrameNull hb hc =>
    exact ⟨rfl, rfl, .inr ⟨.trap, rfl⟩, fun g => by rw [hb]; exact Step.returnCallRefFrameNull hc⟩
  | returnCallRefFrameAddr hb hc hf he hn =>
    exact ⟨rfl, rfl, .inl (.inr (.inl ⟨_, _, _, _, _, _, rfl,
      Silmaril.Wasm.Binaryen.DirSim.isCallRef_retToCallIn hc _, hf, he, hn⟩)),
      fun g => by rw [hb]; exact Step.returnCallRefFrameAddr hc hf he hn⟩
  | throwRefFrame => exact ⟨rfl, rfl, .inr ⟨.throw _, rfl⟩, fun g => Step.throwRefFrame⟩
  | trapFrame => exact ⟨rfl, rfl, .inr ⟨.trap, rfl⟩, fun g => Step.trapFrame⟩

/-- A head step at a frame with a live body is a step of the body. -/
theorem head_frame_live {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {n : Nat}
    {F : Frame} {B : List Admin} {c₀ : Config Nat} (h : Head P s f args (.frame n F B) c₀)
    (hB : LiveBody B) :
    args = [] ∧ ∃ s' F' B', Execution.Core.Step P Det.noHost ⟨s, F, B⟩ ⟨s', F', B'⟩ ∧
      c₀ = ⟨s', f, [.frame n F' B']⟩ := by
  cases h with
  | parametric h => exact (fam_control (ParametricStep.shape h) (by decide) rfl).elim
  | numeric h => exact (fam_control (NumericStep.shape h) (by decide) rfl).elim
  | vector h => exact (fam_control (VectorStep.shape h) (by decide) rfl).elim
  | «variable» h => exact (fam_control (VariableStep.shape h) (by decide) rfl).elim
  | table h => exact (fam_control (TableStep.shape h) (by decide) rfl).elim
  | memory h => exact (fam_control (MemoryStep.shape h) (by decide) rfl).elim
  | reference h => exact (fam_control (RefStep.shape h) (by decide) rfl).elim
  | aggregate h => exact (fam_control (AggregateStep.shape h) (by decide) rfl).elim
  | callRefNull hc => exact hc.elim
  | callRefFunc _ hc => exact hc.elim
  | ctxtFrame h' => exact ⟨rfl, _, _, _, h', rfl⟩
  | frameVals hb => exact (live_ne_vals hB hb).elim
  | @returnFrame _ _ _ _ vs' vs rest hb _ =>
    exact (live_ne hB (W := vs' ++ vs) (R := rest) (by rw [hb]; simp [vals_append]) rfl
      notLive_return).elim
  | @returnCallRefFrameNull _ _ _ _ vs c rest hb hc =>
    exact (live_ne hB (W := vs ++ [Val.ref .null]) (R := rest)
      (by rw [hb]; simp [vals_append]; rfl)
      (ret_val_none hc) (notLive_ret hc)).elim
  | @returnCallRefFrameAddr _ _ _ _ vs' vs a c rest _ _ _ hb hc _ _ _ =>
    exact (live_ne hB (W := vs' ++ vs ++ [Val.ref (.func a)]) (R := rest)
      (by rw [hb]; simp [vals_append]; rfl) (ret_val_none hc) (notLive_ret hc)).elim
  | @throwRefFrame _ _ _ a =>
    exact (live_ne hB (W := [Val.ref (.exn a)]) (R := []) rfl rfl
      notLive_throwRef).elim
  | trapFrame => exact (live_ne hB (W := []) (R := []) (by simp) rfl notLive_trap).elim

/-- A head step at a label with a live body is a step of the body. -/
theorem head_label_live {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {n : Nat}
    {cont : List Instr} {B : List Admin} {c₀ : Config Nat}
    (h : Head P s f args (.label n cont B) c₀) (hB : LiveBody B) :
    args = [] ∧ ∃ s' f' B', Execution.Core.Step P Det.noHost ⟨s, f, B⟩ ⟨s', f', B'⟩ ∧
      c₀ = ⟨s', f', [.label n cont B']⟩ := by
  cases h with
  | parametric h => exact (fam_control (ParametricStep.shape h) (by decide) rfl).elim
  | numeric h => exact (fam_control (NumericStep.shape h) (by decide) rfl).elim
  | vector h => exact (fam_control (VectorStep.shape h) (by decide) rfl).elim
  | «variable» h => exact (fam_control (VariableStep.shape h) (by decide) rfl).elim
  | table h => exact (fam_control (TableStep.shape h) (by decide) rfl).elim
  | memory h => exact (fam_control (MemoryStep.shape h) (by decide) rfl).elim
  | reference h => exact (fam_control (RefStep.shape h) (by decide) rfl).elim
  | aggregate h => exact (fam_control (AggregateStep.shape h) (by decide) rfl).elim
  | callRefNull hc => exact hc.elim
  | callRefFunc _ hc => exact hc.elim
  | ctxtLabel h' => exact ⟨rfl, _, _, _, h', rfl⟩
  | labelVals hb => exact (live_ne_vals hB hb).elim
  | @brLabelZero _ _ _ _ vs' vs l rest hb _ _ =>
    exact (live_ne hB (W := vs' ++ vs) (R := rest) (by rw [hb]; simp [vals_append]) rfl
      (notLive_br l)).elim
  | @brLabelSucc _ _ _ _ vs l rest hb _ =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) rfl (notLive_br l)).elim
  | @returnCallRefLabel _ _ _ _ vs c rest hb hc =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) (ret_val_none hc)
      (notLive_ret hc)).elim
  | @returnLabel _ _ _ _ vs rest hb =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) rfl notLive_return).elim
  | @throwRefLabel _ _ _ a =>
    exact (live_ne hB (W := [Val.ref (.exn a)]) (R := []) rfl rfl
      notLive_throwRef).elim
  | trapLabel => exact (live_ne hB (W := []) (R := []) (by simp) rfl notLive_trap).elim

/-- A head step at a handler with a live body is a step of the body. -/
theorem head_handler_live {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {n : Nat}
    {cs : List Catch} {B : List Admin} {c₀ : Config Nat}
    (h : Head P s f args (.handler n cs B) c₀) (hB : LiveBody B) :
    args = [] ∧ ∃ s' f' B', Execution.Core.Step P Det.noHost ⟨s, f, B⟩ ⟨s', f', B'⟩ ∧
      c₀ = ⟨s', f', [.handler n cs B']⟩ := by
  cases h with
  | parametric h => exact (fam_control (ParametricStep.shape h) (by decide) rfl).elim
  | numeric h => exact (fam_control (NumericStep.shape h) (by decide) rfl).elim
  | vector h => exact (fam_control (VectorStep.shape h) (by decide) rfl).elim
  | «variable» h => exact (fam_control (VariableStep.shape h) (by decide) rfl).elim
  | table h => exact (fam_control (TableStep.shape h) (by decide) rfl).elim
  | memory h => exact (fam_control (MemoryStep.shape h) (by decide) rfl).elim
  | reference h => exact (fam_control (RefStep.shape h) (by decide) rfl).elim
  | aggregate h => exact (fam_control (AggregateStep.shape h) (by decide) rfl).elim
  | callRefNull hc => exact hc.elim
  | callRefFunc _ hc => exact hc.elim
  | ctxtHandler h' => exact ⟨rfl, _, _, _, h', rfl⟩
  | handlerVals hb => exact (live_ne_vals hB hb).elim
  | @brHandler _ _ _ _ vs l rest hb =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) rfl (notLive_br l)).elim
  | @returnCallRefHandler _ _ _ _ vs c rest hb hc =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) (ret_val_none hc)
      (notLive_ret hc)).elim
  | @returnHandler _ _ _ _ vs rest hb =>
    exact (live_ne hB (W := vs) (R := rest) (by rw [hb]; simp) rfl notLive_return).elim
  | @throwRefHandlerEmpty _ _ a => exact (exn_live hB).elim
  | @throwRefHandlerCatch _ _ _ _ _ a _ _ _ => exact (exn_live hB).elim
  | @throwRefHandlerCatchRef _ _ _ _ _ a _ _ _ => exact (exn_live hB).elim
  | @throwRefHandlerCatchAll _ _ _ _ a => exact (exn_live hB).elim
  | @throwRefHandlerCatchAllRef _ _ _ _ a => exact (exn_live hB).elim
  | @throwRefHandlerNext _ _ _ _ a _ => exact (exn_live hB).elim
  | trapHandler => exact (live_ne hB (W := []) (R := []) (by simp) rfl notLive_trap).elim

/-- A head step at a call annotation: a call on `null`, or into a Wasm function. -/
theorem head_call {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {c : Admin}
    {c₀ : Config Nat} (hc : c.IsCallRef) (h : Head P s f args c c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
      ∃ (vs : List Val) (a : Nat) (fi : FuncInst Nat) (ps rs : Ty (.list .val)) (code : Func),
        args = vs ++ [.ref (.func a)] ∧ s.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
        vs.length = ps.length ∧ fi.code = .wasm code ∧ c₀ = ⟨s, f, callCode fi rs code vs⟩ := by
  rcases Det.IsCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  all_goals
    cases h with
    | parametric h => exact (fam_control (ParametricStep.shape h) (by decide) rfl).elim
    | numeric h => exact (fam_control (NumericStep.shape h) (by decide) rfl).elim
    | vector h => exact (fam_control (VectorStep.shape h) (by decide) rfl).elim
    | «variable» h => exact (fam_control (VariableStep.shape h) (by decide) rfl).elim
    | table h => exact (fam_control (TableStep.shape h) (by decide) rfl).elim
    | memory h => exact (fam_control (MemoryStep.shape h) (by decide) rfl).elim
    | reference h => exact (fam_control (RefStep.shape h) (by decide) rfl).elim
    | aggregate h => exact (fam_control (AggregateStep.shape h) (by decide) rfl).elim
    | callRefNull _ => exact .inl ⟨rfl, rfl⟩
    | callRefFunc ha _ hf he hn hcode => exact .inr ⟨_, _, _, _, _, _, ha, hf, he, hn, hcode, rfl⟩

end Silmaril.Proofs.Wasm.Game.ULink
