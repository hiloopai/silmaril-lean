module

public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Proofs.Wasm.Abstract.HostEval.Basic

/-!
# The whole-run backward simulation with host calls (proofs, first cases)

A Core run of lowered native trees to a stuck configuration either ends as a
native run with host calls (`EvalH host`) does, or is blocked at a host call
with no outcome (`Pending`): `BackOut`. The proof is an induction on the length
of the Core run (`StepsN`) and on the trees. This file has the first cases:

* `Pending` facts: closed under appending code (`Pending.append`); a pending
  call is not values, not a trap and not a thrown exception;
* `back_nil`: the empty tree list;
* `back_op_args`: an operator tree `op i args :: es`. The run of the arguments
  is split off (`stepsN_seq_split`); an abrupt or blocked end of the arguments
  is the end of the whole run (`EvalO.argsAbort`), and a normal end hands the
  remaining run, from `vals stk₁ ++ i :: es`, to the instruction's own case.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Pending host calls -/

theorem pending_append {s : Store H} {es : List Admin} (h : Pending host s es) (rest' : List Admin) :
    Pending host s (es ++ rest') := by
  cases h with
  | call hf hcode he hn hno => simpa using Pending.call (rest := _ ++ rest') hf hcode he hn hno
  | label h => simpa using Pending.label (rest := _ ++ rest') h
  | frame h => simpa using Pending.frame (rest := _ ++ rest') h

theorem not_mem_vals_of_val? {a : Admin} (ha : a.val? = none) {ws : List Val} : a ∉ vals ws := by
  intro hm
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hm
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.val?] at ha

/-- A pending call contains a non-value that is neither a trap nor `throw_ref`. -/
theorem pending_exists_nonval {s : Store H} {es : List Admin} (h : Pending host s es) :
    ∃ a ∈ es, a.val? = none ∧ a ≠ .trap ∧ a ≠ .plain .throwRef := by
  cases h with
  | @call ws us a fi hh ps rs rest => exact ⟨.callRefType fi.type, by simp, rfl, by simp, by simp⟩
  | @label ws n cont es rest => exact ⟨.label n cont es, by simp, rfl, by simp, by simp⟩
  | @frame ws n F es rest => exact ⟨.frame n F es, by simp, rfl, by simp, by simp⟩

/-- A pending call is not values. -/
theorem pending_ne_vals {s : Store H} {es : List Admin} (h : Pending host s es) (ws : List Val) :
    es ≠ vals ws := by
  rintro rfl
  obtain ⟨a, ha, hv, -, -⟩ := pending_exists_nonval h
  exact not_mem_vals_of_val? hv ha

/-- A pending call is not a trap. -/
theorem pending_ne_trap {s : Store H} {es : List Admin} (h : Pending host s es) : es ≠ [.trap] := by
  rintro rfl
  obtain ⟨a, ha, -, ht, -⟩ := pending_exists_nonval h
  simp_all

/-- A pending call is not a thrown exception. -/
theorem pending_ne_throwing {s : Store H} {es : List Admin} (h : Pending host s es) (x : Nat) :
    es ≠ throwing x := by
  rintro rfl
  obtain ⟨a, ha, hv, -, htr⟩ := pending_exists_nonval h
  simp only [throwing, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · simp [Admin.val?] at hv
  · exact htr rfl

/-- The only outcome ending in values is falling through with them. -/
theorem ends_vals {o : Outcome} {ws : List Val} (h : o.Ends (vals ws)) : o = .normal ws := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩ | ⟨vs, r⟩
  · exact congrArg Outcome.normal (Sim.vals_injective h.symm)
  · obtain ⟨x, rest, -, h⟩ := h
    have : Admin.plain (.br x) ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals_of_val? rfl this).elim
  · obtain ⟨rest, h⟩ := h
    have : Admin.plain .return_ ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals_of_val? rfl this).elim
  · have : Admin.trap ∈ vals ws := by rw [show vals ws = [Admin.trap] from h]; simp
    exact (not_mem_vals_of_val? rfl this).elim
  · have : Admin.plain .throwRef ∈ vals ws := by
      rw [show vals ws = throwing a from h]; simp [throwing]
    exact (not_mem_vals_of_val? rfl this).elim
  · obtain ⟨hr, rest, h⟩ := h
    have : r ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals_of_val? (Admin.val?_of_isReturnCallRef hr) this).elim
  · obtain ⟨hr, rest, h⟩ := h
    have : r ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals_of_val? (Admin.val?_of_isReturnCallRef hr) this).elim

/-! ## The empty tree list -/

/-- **The empty tree list**: the run is empty, and ends as the native `nil`. -/
theorem back_nil {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
    (hrun : StepsN P host n ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList [])⟩ c) :
    BackOut host s f stk [] c := by
  have hrun' : StepsN P host n ⟨s, f, vals stk.reverse⟩ c := by simpa [expression] using hrun
  cases hrun' with
  | refl => exact .inl ⟨(s, f, .normal stk), .nil, .normal stk.reverse, rfl, rfl, rfl, rfl⟩
  | head h _ => exact (Sim.Step.not_vals h).elim

/-! ## Operator trees: the arguments -/

theorem code_op_split (stk : List Val) (i : Instr) (args es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es)) =
      (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)) ++
        (.plain i :: expression (Binaryen.BExpr.lowerList es)) := by
  simp [expression, Binaryen.BExpr.lower]

/-- **An operator tree, through its arguments.** The arguments' run ends the
whole run when it ends abruptly or blocks; when they complete normally on
`stk₁`, the remaining run from `vals stk₁ ++ i :: es` is the instruction's case
`hk`. -/
theorem back_op_args {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN P host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ c)
    (hend : ∀ c', ¬ Step P host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN P host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step P host c₁ c') → BackOut host s f stk args c₁)
    (hk : ∀ s₁ f₁ stk₁ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      StepsN P host m ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s f stk (.op i args :: es) c) :
    BackOut host s f stk (.op i args :: es) c := by
  rw [code_op_split] at hrun
  obtain ⟨c₁, n₁, h₁, hn₁, hs₁, hk₁⟩ := stepsN_seq_split hrun hend
  rcases ihargs n₁ hn₁ c₁ h₁ hs₁ with ⟨r₁, hev, o, he, hm⟩ | hp
  · obtain ⟨hst, hfr, hfm⟩ := hm
    -- the arguments' result decides
    rcases r₁ with ⟨s₁, f₁, fl⟩
    dsimp only at hst hfr hfm
    subst hst hfr
    by_cases hnorm : fl.IsNormal
    · -- normal: the arguments end in values `stk₁`
      rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hnorm
      rcases o with ws | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hfm
      subst hfm
      have hcode : c₁.code = vals stk₁.reverse := he
      rcases hk₁ with ⟨ws', hw, hrest⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | rfl
      · rw [hcode] at hw
        obtain rfl : ws' = stk₁.reverse := (Sim.vals_injective hw).symm
        exact hk c₁.store c₁.frame stk₁ (n - n₁) (Nat.sub_le _ _) hev hrest
      · rw [hcode] at htr
        exact absurd (htr ▸ (by simp : Admin.trap ∈ [Admin.trap]))
          (not_mem_vals_of_val? (a := .trap) rfl)
      · rw [hcode] at hth
        exact absurd (hth ▸ (by simp [throwing] : Admin.plain .throwRef ∈ throwing x))
          (not_mem_vals_of_val? (a := .plain .throwRef) rfl)
      · refine hk c₁.store c₁.frame stk₁ 0 (Nat.zero_le _) hev ?_
        rw [hcode]
        exact .refl _
    · -- abrupt: the arguments' end is the whole run's end
      have hev' : EvalH host s f stk (.op i args :: es) (c₁.store, c₁.frame, fl) :=
        .argsAbort hev hnorm
      refine .inl ⟨_, hev', ?_⟩
      rcases hk₁ with ⟨ws', hw, -⟩ | ⟨-, rfl⟩ | ⟨x, -, rfl⟩ | rfl
      · rw [hw] at he
        obtain rfl := ends_vals he
        rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
      · exact ⟨o, he, rfl, rfl, hfm⟩
      · exact ⟨o, he, rfl, rfl, hfm⟩
      · refine ⟨o, ?_, rfl, rfl, hfm⟩
        rcases o with _ | ⟨l, vs⟩ | vs | _ | _ | ⟨vs, a, r⟩ | ⟨vs, r⟩
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · obtain ⟨x, rest, hx, he⟩ := he
          exact ⟨x, rest ++ (.plain i :: expression (Binaryen.BExpr.lowerList es)), hx, by
            rw [he]; simp⟩
        · obtain ⟨rest, he⟩ := he
          exact ⟨rest ++ (.plain i :: expression (Binaryen.BExpr.lowerList es)), by rw [he]; simp⟩
        · -- a trap before more code is not stuck
          have he' : c₁.code = [.trap] := he
          exfalso
          apply hend ⟨c₁.store, c₁.frame, [.trap]⟩
          rw [he']
          simpa using Step.trapInstrs (P := P) (host := host) (s := c₁.store) (f := c₁.frame)
            (vs := []) (rest := .plain i :: expression (Binaryen.BExpr.lowerList es)) (.inr (by simp))
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
  · -- blocked in the arguments
    refine .inr ?_
    rcases hk₁ with ⟨ws', hw, -⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | rfl
    · exact (pending_ne_vals hp ws' hw).elim
    · exact (pending_ne_trap hp htr).elim
    · exact (pending_ne_throwing hp x hth).elim
    · exact pending_append hp _

/-! ## Flat instructions -/

/-- An abrupt matched final form (a branch, a return or a trap) has no step. -/
theorem ends_abrupt_stuck {s : Store H} {f : Frame} {o : Outcome} {fl : Binaryen.Flow}
    {c' : List Admin} (he : o.Ends c') (hm : Interp.FlowMatch fl o) (hn : ¬ fl.IsNormal)
    (c : Config H) : ¬ Step P host ⟨s, f, c'⟩ c := by
  intro hst
  rcases c with ⟨s', f', es'⟩
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩ | ⟨vs, r⟩
  · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
  · obtain ⟨x, rest, -, rfl⟩ := he
    rcases Sim.Step.split_head (a := .plain (.br x)) rfl hst with ⟨ws, us, is', -, h, -⟩ |
        ⟨h, -⟩ | ⟨h, -⟩
    · exact Step.br_vals_stuck h
    · cases h
    · cases h
  · obtain ⟨rest, rfl⟩ := he
    rcases Sim.Step.split_head (a := .plain .return_) rfl hst with ⟨ws, us, is', -, h, -⟩ |
        ⟨h, -⟩ | ⟨h, -⟩
    · exact Step.return_vals_stuck h
    · cases h
    · cases h
  · have hc : c' = [.trap] := he
    subst hc
    exact Step.trap_stuck hst
  · rcases fl <;> simp_all [Interp.FlowMatch]
  · rcases fl <;> simp_all [Interp.FlowMatch]
  · rcases fl <;> simp_all [Interp.FlowMatch]

/-- A run of `m` steps from a stuck configuration is empty. -/
theorem stepsN_of_stuck {m : Nat} {X c : Config H} (hX : ∀ c', ¬ Step P host X c')
    (h : StepsN P host m X c) : c = X := by
  cases h with
  | refl => rfl
  | head h _ => exact (hX _ h).elim

/-- **The backward case of a flat instruction**, in the deterministic profile and
with any host. Let the native instruction `i` (not a call, passing the check)
step `stk₁` to `(s₂, f₂, fl)`. Then a Core run of `vals stk₁ ++ i :: rest` to a
stuck end either continues, after `i`, from `vals stk₂ ++ rest` in at most as many
steps (`fl = normal stk₂`), or ends as the native abrupt result. -/
theorem back_flat {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    {stk₁ : List Val} {i : Instr} {fl : Binaryen.Flow} {rest : List Admin} {c : Config H}
    {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat} {h₀ : Nat}
    {o₁ : Option Nat} (hi : ∀ x, i ≠ .call x)
    (hc : Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl))
    (hrun : StepsN (SingleThreaded.profile o) host n ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    (∀ stk₂, fl = .normal stk₂ →
        ∃ m ≤ n, StepsN (SingleThreaded.profile o) host m ⟨s₂, f₂, vals stk₂.reverse ++ rest⟩ c) ∧
      (¬ fl.IsNormal → EndsAs (s₂, f₂, fl) c) := by
  refine ⟨fun stk₂ hfl => ?_, fun hn => ?_⟩
  · subst hfl
    have hst := Interp.steps_flat_normal (P := SingleThreaded.profile o)
      (host := SingleThreaded.Det.noHost) hi hc hflat rest
    exact stepsN_through_steps hst hrun hend
  · have hw := Interp.wp_flat_abrupt (P := SingleThreaded.profile o)
      (host := SingleThreaded.Det.noHost) hc hflat hn rest
    obtain ⟨c', o', hst, he, hm⟩ := Interp.run_of_wp hw
    obtain ⟨m, -, h⟩ := stepsN_through_steps hst hrun hend
    have hc' := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
      (s := s₂) (f := f₂) he hm hn) h
    subst hc'
    exact ⟨o', he, rfl, rfl, hm⟩

/-- **An operator tree other than a call**, in the deterministic profile, any host:
the arguments by `back_op_args`, the instruction by `back_flat`, the following
trees by `ihes`. After the arguments complete normally, the native step and its
check are given by `hflat` (from typing, `Interp.evalFlat_progressH`, and the
forward arity invariants). -/
theorem back_op_flat {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {i : Instr} {args es : List Binaryen.BExpr} {c : Config H}
    (hi : ∀ x, i ≠ .call x)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hflat : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      (∃ r, Binaryen.evalFlat s₁ f₁ stk₁ i = some r) ∧
      ∃ (F : List (FuncInst H)) (mi : ModuleInst) (ret : Nat) (labels : List Nat) (h₀ : Nat)
        (o₁ : Option Nat), Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (ihes : ∀ s₁ f₁ stk₁ s₂ f₂ stk₂ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₂ stk₂ es c) :
    BackOut host s f stk (.op i args :: es) c := by
  refine back_op_args hrun hend ihargs fun s₁ f₁ stk₁ m hm hev hrun₁ => ?_
  obtain ⟨⟨⟨s₂, f₂, fl⟩, hfl⟩, F, mi, ret, labels, h₀, o₁, hc⟩ := hflat s₁ f₁ stk₁ hev
  obtain ⟨hnorm, habr⟩ := back_flat hi hc hfl hrun₁ hend
  by_cases hn : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨m', hm', hrun₂⟩ := hnorm stk₂ rfl
    rcases ihes s₁ f₁ stk₁ s₂ f₂ stk₂ m' (by omega) hev hfl hrun₂ with ⟨r, hk, hr⟩ | hp
    · exact .inl ⟨r, .opOk hi hev hfl hk, hr⟩
    · exact .inr hp
  · exact .inl ⟨_, .opStop hi hev hfl hn, habr hn⟩

/-! ## Calls of host functions -/

theorem code_call_split (stk : List Val) (n : Nat) (a : Nat) (d : Validation.DefType)
    (rest : List Admin) :
    vals stk.reverse ++ ([.ref (.func a), .callRefType d] ++ rest) =
      vals (stk.drop n).reverse ++ vals (stk.take n).reverse ++
        .ref (.func a) :: .callRefType d :: rest := by
  have e : stk.reverse = (stk.drop n).reverse ++ (stk.take n).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [e, vals_append]
  simp

/-- **The backward case of a direct call of a host function**, in the deterministic
profile. After `call x` (a host-free step) the run is at the host call on the top
`ps.length` values `us`. Either it is blocked there (`Pending`), or the host gave
an answer the native semantics takes (`hostCall`): values (the run continues, in
fewer steps, from the native continuation stack) or a trap (the run ends as the
native trap). The host-slice facts give the result arity and exclude exceptions. -/
theorem back_call_host {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .host hh)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (harity : ∀ s' ws, host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.values ws)) →
      ws.length = rs.length)
    (hnothrow : ∀ s' t, ¬ host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.throw t)))
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ s₂ fl, hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ c) ∨
          (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)) := by
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  -- `call x` is a host-free step
  have hd : SingleThreaded.Det.DStep o ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    have := Silmaril.Wasm.Logic.Core.Step.ctx (P := SingleThreaded.profile o)
      (host := SingleThreaded.Det.noHost) stk₁.reverse rest (Step.call hx hf)
    have h2 : Step (SingleThreaded.profile o) SingleThreaded.Det.noHost
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
      simpa using this
    exact h2
  obtain ⟨m₁, hm₁, hrun₁⟩ := stepsN_through hrun hend hd
  rw [code_call_split stk₁ ps.length] at hrun₁
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  have hn : (stk₁.take ps.length).reverse.length = ps'.length := by
    simp only [List.length_reverse, List.length_take]; omega
  rcases host_call_runN_seq hf hcode hex hn hrun₁ hend with ⟨rfl, hno⟩ | ⟨s₂, r, m, hm, hhost, hk⟩
  · exact .inl (Pending.call hf hcode hex hn hno)
  · right
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, resFlow r) := by
      rw [hostCall_fixpoint]
      exact .inr ⟨fi, hh, r, hf, hcode, hhost, rfl⟩
    refine ⟨s₂, resFlow r, hcall, ?_⟩
    rcases r with ws | t | _
    · left
      refine ⟨ws.reverse, m, by omega, rfl, ?_⟩
      have hl := harity s₂ ws hhost
      have htake : ws.reverse.take rs.length = ws.reverse :=
        List.take_of_length_le (by simp [hl])
      rw [htake]
      simpa [Result.toAdmin] using hk
    · exact (hnothrow s₂ t hhost).elim
    · right
      refine ⟨rfl, ?_⟩
      have hc := steps_trap_head (ws := (stk₁.drop ps.length).reverse) (r := rest)
        (by simpa [Result.toAdmin] using stepsN_steps hk) hend
      subst hc
      exact ⟨.trap, rfl, rfl, rfl, trivial⟩

/-- **A direct call of a host function, as a tree** (deterministic profile): the
arguments by `back_op_args`, the call by `back_call_host`, the following trees by
`ihes`. The callee facts after the arguments (a host function with the declared
type, its result arity and no exceptions) are the hypothesis `hcallee`. -/
theorem back_op_call_host {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hcallee : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      ∃ (a : Nat) (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType),
        s₁.func? f₁ x = some (a, fi) ∧ fi.code = .host hh ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ps.length ≤ stk₁.length ∧
        (∀ s' ws, host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.values ws)) →
          ws.length = rs.length) ∧
        ∀ s' t, ¬ host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.throw t)))
    (ihes : ∀ s₂ f₁ stk₂ m, m ≤ n →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₁, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₁ stk₂ es c) :
    BackOut host s f stk (.op (.call x) args :: es) c := by
  refine back_op_args hrun hend ihargs fun s₁ f₁ stk₁ m hm hev hrun₁ => ?_
  obtain ⟨a, fi, hh, ps, rs, hfi, hcode, hty, hp, har, hnt⟩ := hcallee s₁ f₁ stk₁ hev
  rcases back_call_host hfi hcode hty hp har hnt hrun₁ hend with hpend |
      ⟨s₂, fl, hcall, ⟨vs, m', hm', hvs, hk⟩ | ⟨rfl, hends⟩⟩
  · exact .inr hpend
  · rcases ihes s₂ f₁ _ m' (by omega) hk with ⟨r, hev', hr⟩ | hp'
    · exact .inl ⟨r, .callOk hev hfi hty hcall hvs hev', hr⟩
    · exact .inr hp'
  · exact .inl ⟨_, .callTrap hev hfi hty hcall, hends⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
