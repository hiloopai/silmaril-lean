module

public import Silmaril.Proofs.Wasm.Logic.Total.Label

/-!
# Total correctness: blocks, loops, calls and recursion

* `TWP.block`, `TWP.if_`, `TWP.brIf`: structured control;
* `TWP.loop` (**the loop rule with a variant**): an invariant on the loop
  parameters and a natural-number variant that every branch back to the loop
  decreases;
* `TFSpecAt.of_body` (a total specification from the body), `TSafe.call`,
  `TSafe.callIdx` (**the total call rule**), `TSafe.returnCallIdx` (tail calls);
* `TCtx.valid_of_measure` (**total recursion**): a context of specifications
  each proved for calls of measure below `n + 1`, assuming all of them for calls
  of measure below `n`, is totally correct; `TCtxSat.valid`, `TCtxSat.link`
  (**the total module rule**, also for mutually recursive contexts sharing a
  measure);
* adequacy: `TFSpecAt.valid` (total implies partial), `TFSpecAt.invoke_terminates`
  (no infinite run of `$invoke`), `TFSpecAt.invoke_vals`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Structured control -/

/-- **`block`** for total correctness. -/
theorem TWP.block {s : Store H} {f : Frame} {us vs : List Val} {bt : BlockType}
    {body : List Instr} {rest : List Admin} {Q : Post H} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hn : vs.length = t₁.length)
    (h : TWP P host s f (vals vs ++ expression body)
      (labelPostT P host t₂.length [] us (seqPostT P host rest Q))) :
    TWP P host s f (vals (us ++ vs) ++ .plain (.block bt body) :: rest) Q := by
  refine TSafe.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .block hbt hn⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := SingleThreaded.head_block hh
  obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ t₂' = t₂ := by simpa [hbt] using hbt'.symm
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  exact TSafe.seq (TSafe.label h)

/-- **`if`** for total correctness. -/
theorem TWP.if_ {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h : TWP P host s f (vals us ++ .plain (.block bt (if c ≠ 0 then b₁ else b₂)) :: rest) Q) :
    TWP P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [Val.i32 c] = vs ++ args ∧
      Head P s f args (.plain (.if_ bt b₁ b₂)) c₀ := by
    by_cases hc : c = 0
    · exact ⟨us, _, _, rfl, .ifFalse hc⟩
    · exact ⟨us, _, _, rfl, .ifTrue hc⟩
  refine TSafe.head ⟨rfl, by simp, rfl⟩ hp fun vs args c₀ hW hh => ?_
  obtain ⟨c', rfl, hres⟩ := head_if hh
  obtain ⟨rfl, hv⟩ := split_one hW
  obtain rfl := i32_inj hv.symm
  rcases hres with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · have hb : (if c' ≠ 0 then b₁ else b₂) = b₁ := ite_eq_left_of_eq_true _ _ (eq_true hc)
    rw [hb] at h
    simpa [TWP] using h
  · have hb : (if c' ≠ 0 then b₁ else b₂) = b₂ :=
      ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr hc))
    rw [hb] at h
    simpa [TWP] using h

/-- **`br_if`** for total correctness. -/
theorem TWP.brIf {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32} {l : LabelIdx}
    {rest : List Admin} {Q : Post H}
    (htrue : c ≠ 0 → Q s f (.br l.toNat us))
    (hfalse : c = 0 → TWP P host s f (vals us ++ rest) Q) :
    TWP P host s f (vals (us ++ [.i32 c]) ++ .plain (.brIf l) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [Val.i32 c] = vs ++ args ∧
      Head P s f args (.plain (.brIf l)) c₀ := by
    by_cases hc : c = 0
    · exact ⟨us, _, _, rfl, .brIfFalse hc⟩
    · exact ⟨us, _, _, rfl, .brIfTrue hc⟩
  refine TSafe.head ⟨rfl, by simp, rfl⟩ hp fun vs args c₀ hW hh => ?_
  obtain ⟨c', rfl, hres⟩ := head_brIf hh
  obtain ⟨rfl, hv⟩ := split_one hW
  obtain rfl := i32_inj hv.symm
  rcases hres with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · exact .exit (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩ (htrue hc)
  · simpa [TWP] using hfalse hc

/-! ## Loops with a variant -/

section Loop

variable {us : List Val} {Inv : Store H → Frame → List Val → Prop}
  {V : Store H → Frame → List Val → Nat} {Q : Post H} {bt : BlockType} {body : List Instr}
  {t₁ t₂ : List CValType}

theorem loopPostT.toT {m v : Nat}
    (ih : ∀ s f vs, Inv s f vs → V s f vs < v →
      TSafe P host Q ⟨s, f, vals (us ++ vs) ++ [.plain (.loop bt body)]⟩)
    {s : Store H} {f : Frame} {o : Outcome} (h : loopPostT m us Inv V v Q s f o) :
    labelPostT P host m [.loop bt body] us Q s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact h
  · obtain ⟨vs₁, vs₂, he, hn, hi, hv⟩ := h
    exact ⟨vs₁, vs₂, he, hn, by simpa [expression] using ih s f vs₂ hi hv⟩
  all_goals exact h

/-- One unfolding of a loop, given the loop for every smaller variant. -/
theorem tloop_below (hbt : ∀ s f vs, Inv s f vs → f.module.blockType? bt = some (t₁, t₂))
    (hn : ∀ s f vs, Inv s f vs → vs.length = t₁.length)
    (hbody : ∀ s f vs, Inv s f vs →
      TWP P host s f (vals vs ++ expression body) (loopPostT t₁.length us Inv V (V s f vs) Q)) :
    ∀ (v : Nat) (s : Store H) (f : Frame) (vs : List Val), Inv s f vs → V s f vs < v →
      TSafe P host Q ⟨s, f, vals (us ++ vs) ++ [.plain (.loop bt body)]⟩ := by
  intro v
  induction v with
  | zero => exact fun _ _ _ _ hv => absurd hv (Nat.not_lt_zero _)
  | succ v ih =>
    intro s f vs hi hv
    refine TSafe.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .loop (hbt s f vs hi) (hn s f vs hi)⟩ ?_
    intro us' args c₀ hW hh
    obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
    obtain ⟨rfl, rfl⟩ : t₁' = t₁ ∧ t₂' = t₂ := by simpa [hbt s f vs hi] using hbt'.symm
    obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans (hn s f vs hi).symm)
    have hb : TSafe P host (labelPostT P host t₁'.length [.loop bt body] us' Q)
        ⟨s, f, vals args ++ expression body⟩ :=
      (hbody s f args hi).post_mono fun _ _ _ =>
        loopPostT.toT fun s' f' vs' hi' hv' => ih s' f' vs' hi' (by omega)
    simpa using TSafe.label hb

/-- **`loop`** (total correctness): an invariant on the loop's parameters and a
variant that decreases at every branch back to the loop. -/
theorem TWP.loop (hbt : ∀ s f vs, Inv s f vs → f.module.blockType? bt = some (t₁, t₂))
    (hn : ∀ s f vs, Inv s f vs → vs.length = t₁.length)
    (hbody : ∀ s f vs, Inv s f vs →
      TWP P host s f (vals vs ++ expression body) (loopPostT t₁.length us Inv V (V s f vs) Q))
    {s : Store H} {f : Frame} {vs : List Val} (hi : Inv s f vs) :
    TWP P host s f (vals (us ++ vs) ++ [.plain (.loop bt body)]) Q :=
  tloop_below hbt hn hbody (V s f vs + 1) s f vs hi (Nat.lt_succ_self _)

end Loop

/-! ## Calls -/

/-- **A total specification from the body**: one step enters the frame, after
which the body must be totally correct. -/
theorem TFSpecAt.of_body {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    {S : FSpec H} (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hbody : ∀ s args, S.pre s args → ∀ (f : Frame) (vs₀ : List Val),
      TSafe P host (bodyPostT P host rs.length f vs₀ (callPost f vs₀ (S.post s args)))
        ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩) :
    TFSpecAt P host a S := by
  intro s args hpre f vs₀ c hc
  have hf : s.funcs[a]? = some fi := hfi s args hpre
  have hn : args.length = ps.length := hlen s args hpre
  have hstep : Step P host ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs₀ ++ [callFrame fi code rs args]⟩ := by
    simpa [callFrame] using Sim.Step.vals_left (Step.callRefFunc hc hf he hn hcode) vs₀
  refine .step ⟨_, hstep⟩ fun c' hst => ?_
  rw [call_step_inv hc hf hcode he hn hst]
  exact TSafe.frame (TSafe.label (us := []) (hbody s args hpre f vs₀))

/-- **The total call rule.** -/
theorem TSafe.call {a : Nat} {S : FSpec H} {s : Store H} {f : Frame} {vs₀ args : List Val}
    {c : Admin} {rest : List Admin} {Q : Post H} (hS : TFSpecAt P host a S) (hpre : S.pre s args)
    (hc : c.IsCallRef)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPostT P host rest Q s' f o) :
    TSafe P host Q ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c] ++ rest⟩ := by
  refine TSafe.seq ((hS s args hpre f vs₀ c hc).post_mono fun s' f' o h => ?_)
  have hf' : f' = f := h.1
  subst hf'
  exact hpost s' o h

/-- **The total call rule for `call x`.** -/
theorem TSafe.callIdx {a : Nat} {S : FSpec H} {s : Store H} {f : Frame} {vs₀ args : List Val}
    {x : FuncIdx} {fi : FuncInst H} {rest : List Admin} {Q : Post H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPostT P host rest Q s' f o) :
    TSafe P host Q ⟨s, f, vals (vs₀ ++ args) ++ .plain (.call x) :: rest⟩ := by
  refine TSafe.head ⟨rfl, by simp, rfl⟩ ⟨vs₀ ++ args, [], _, by simp, .call hx hf⟩ ?_
  intro vs args' c₀ hW hh
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_call hh
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hvs : vs = vs₀ ++ args := by simpa using hW.symm
  subst hvs
  simpa using TSafe.call (vs₀ := vs₀) (rest := rest) hS hpre
    (show Admin.IsCallRef (.callRefType fi'.type) from trivial) hpost

/-- A tail call leaving a function body, for total correctness: the body exits
with outcome `tail`, and `framePostT` asks the call it makes to be totally correct. -/
theorem framePostT_tail {m a : Nat} {f F : Frame} {us vs₁ args : List Val} {Q : Post H}
    {s : Store H} {fn : FuncInst H} {ps rs : Ty (.list .val)} {S : FSpec H} {c : Admin}
    (hr : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : args.length = ps.length) (hS : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f us (S.post s args) s' f o → Q s' f o) :
    framePostT P host m f us Q s F (.tail (vs₁ ++ args) a c) := by
  refine ⟨vs₁, args, fn, ps, rs, rfl, hf, he, hn, ?_⟩
  have h₁ := hS s args hpre f us _ (isCallRef_retToCallIn F.module hr)
  exact h₁.post_mono fun s' f' o h => by
    have hf' : f' = f := h.1
    subst hf'
    exact hpost s' o h

/-! ## Total recursion and the total module rule -/

/-- **Total recursion**: a context whose specifications, restricted to calls of
measure below `n + 1`, follow from all of them restricted to calls of measure
below `n`, is totally correct. -/
theorem TCtx.valid_of_measure {Γ : Ctx H} (μ : Nat → Store H → List Val → Nat)
    (h : ∀ n, TCtx.ValidBelow P host Γ μ n → TCtx.ValidBelow P host Γ μ (n + 1)) :
    TCtx.Valid P host Γ := by
  have hall : ∀ n, TCtx.ValidBelow P host Γ μ n := by
    intro n
    induction n with
    | zero => exact fun a S _ s args hpre => absurd hpre.2 (Nat.not_lt_zero _)
    | succ n ih => exact h n ih
  intro a S hS s args hpre
  exact hall (μ a s args + 1) a S hS s args ⟨hpre, Nat.lt_succ_self _⟩

/-- Valid imports give valid exports (the total module rule). -/
theorem TCtxSat.valid {Γi Γe : Ctx H} {μ : Nat → Store H → List Val → Nat}
    (hm : TCtxSat P host Γi Γe μ) (hi : TCtx.Valid P host Γi) : TCtx.Valid P host Γe :=
  TCtx.valid_of_measure μ fun n h => hm n hi h

theorem TCtx.ValidBelow.union {Γ Γ' : Ctx H} {μ : Nat → Store H → List Val → Nat} {n : Nat}
    (h : TCtx.ValidBelow P host Γ μ n) (h' : TCtx.ValidBelow P host Γ' μ n) :
    TCtx.ValidBelow P host (Ctx.union Γ Γ') μ n := fun a S hS =>
  (Ctx.union_some hS).elim (h a S) (h' a S)

theorem TCtx.ValidBelow.union_left {Γ Γ' : Ctx H} {μ : Nat → Store H → List Val → Nat} {n : Nat}
    (h : TCtx.ValidBelow P host (Ctx.union Γ Γ') μ n) : TCtx.ValidBelow P host Γ μ n :=
  fun a S hS => h a S (by simp [Ctx.union, hS])

theorem TCtx.ValidBelow.union_right {Γ Γ' : Ctx H} {μ : Nat → Store H → List Val → Nat} {n : Nat}
    (hd : ∀ a, Γ a = none ∨ Γ' a = none) (h : TCtx.ValidBelow P host (Ctx.union Γ Γ') μ n) :
    TCtx.ValidBelow P host Γ' μ n := fun a S hS => by
  rcases hd a with hn | hn
  · exact h a S (by simp [Ctx.union, hn, hS])
  · rw [hn] at hS; cases hS

/-- **Linking total contexts**: two contexts that may call each other, with a
common measure that every cross call decreases, give their joint exports. -/
theorem TCtxSat.link {Γi Γe₁ Γe₂ : Ctx H} {μ : Nat → Store H → List Val → Nat}
    (hd : ∀ a, Γe₁ a = none ∨ Γe₂ a = none)
    (h₁ : ∀ n, TCtx.Valid P host Γi → TCtx.ValidBelow P host Γe₁ μ n →
      TCtx.ValidBelow P host Γe₂ μ n → TCtx.ValidBelow P host Γe₁ μ (n + 1))
    (h₂ : ∀ n, TCtx.Valid P host Γi → TCtx.ValidBelow P host Γe₁ μ n →
      TCtx.ValidBelow P host Γe₂ μ n → TCtx.ValidBelow P host Γe₂ μ (n + 1)) :
    TCtxSat P host Γi (Ctx.union Γe₁ Γe₂) μ := by
  intro n hi he
  have he₁ : TCtx.ValidBelow P host Γe₁ μ n := he.union_left
  have he₂ : TCtx.ValidBelow P host Γe₂ μ n := he.union_right hd
  exact (h₁ n hi he₁ he₂).union (h₂ n hi he₁ he₂)

/-! ## Adequacy -/

/-- A total specification is a valid (partial) specification. -/
theorem TFSpecAt.valid {a : Nat} {S : FSpec H} (h : TFSpecAt P host a S) :
    FSpecValid P host a S := fun n s args hpre f vs₀ c hc =>
  TSafe.safe (h s args hpre f vs₀ c hc) n

/-- **Termination of `$invoke`**: no run of a function with a total specification
diverges. -/
theorem TFSpecAt.invoke_terminates {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args) : ¬ Diverges P host (invoke s a args) := by
  rw [invoke_code]
  exact TSafe.not_diverges (h s args hpre {} [] _ trivial)

/-- Every run of `$invoke` of a function with a total specification that returns
values satisfies the postcondition. -/
theorem TFSpecAt.invoke_vals {a : Nat} {S : FSpec H} {s s' : Store H} {f' : Frame}
    {args res : List Val} (h : TFSpecAt P host a S) (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) ⟨s', f', vals res⟩) : S.post s args s' (.normal res) :=
  h.valid.invoke_vals hpre hs

end Silmaril.Wasm.Logic.Hoare
