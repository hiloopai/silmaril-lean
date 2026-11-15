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
with no outcome (`Pending`), reached from the trees (`ReachP`) and with the end at
that call (`BlockedAt`): `BackOut`. The proof is an induction on the length
of the Core run (`StepsN`) and on the trees. This file has the first cases:

* `Pending` facts: closed under appending code (`Pending.append`); a pending
  call is not values, not a trap and not a thrown exception;
* reach evidence: `ReachP` is closed under the `ReachO` constructors
  (`reachP_lift`, `reachP_call`), a reach in a Wasm callee body is a `PendO`
  (`pendO_of_body`), and `BlockedAt` follows the call under appended code and
  labels (`blockedAt_mono`, `atCall_append`, `atCall_label`);
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

/-! ## Reach evidence -/

theorem atCall_append {s : Store H} {a : Nat} {us : List Val} {es : List Admin}
    (h : AtCall s a us es) (rest' : List Admin) : AtCall s a us (es ++ rest') := by
  cases h with
  | here hf => simpa using AtCall.here (rest := _ ++ rest') hf
  | label h => simpa using AtCall.label (rest := _ ++ rest') h
  | frame h => simpa using AtCall.frame (rest := _ ++ rest') h

/-- A call reached under a label. -/
theorem atCall_label {s : Store H} {a : Nat} {us ws : List Val} {n : Nat} {cont : List Instr}
    {b rest : List Admin} (h : AtCall s a us b) :
    AtCall s a us (vals ws ++ [.label n cont b] ++ rest) := by
  simpa using AtCall.label (ws := ws) (n := n) (cont := cont) (rest := rest) h

/-- `BlockedAt` depends only on the store and on the call in the code. -/
theorem blockedAt_mono {c c' : Config H} {y : (wasmOShape H).self.Op} (h : BlockedAt host c y)
    (hs : c'.store = c.store)
    (hat : AtCall c.store y.1 y.2.1 c.code → AtCall c.store y.1 y.2.1 c'.code) :
    BlockedAt host c' y := by
  obtain ⟨fi, hh, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fi, hh, ?_, ?_, h3, ?_, ?_⟩ <;> rw [hs]
  · exact h1
  · exact h2
  · exact h4
  · exact hat h5

/-- `ReachP` is closed under every `ReachO` constructor with the same reached call. -/
theorem reachP_lift {C : CallRel H} {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {y : (wasmOShape H).self.Op}
    (hl : ∀ z, ReachO C s' f' stk' es' z → ReachO C s f stk es z)
    (h : ReachP C s' f' stk' es' y) : ReachP C s f stk es y := by
  rcases h with h | ⟨z, hz, hp⟩
  · exact .inl (hl _ h)
  · exact .inr ⟨z, hl _ hz, hp⟩

/-- A direct call reaches its callee `z`, and every pending call of `z`. -/
theorem reachP_call {C : CallRel H} {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
    {x : FuncIdx} {args es : List Binaryen.BExpr} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {y : (wasmOShape H).self.Op}
    (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : y = ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ ∨
      PendO C ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ y) :
    ReachP C s f stk (.op (.call x) args :: es) y := by
  rcases hy with rfl | hp
  · exact .inl (.here hargs hfi hty)
  · exact .inr ⟨_, .here hargs hfi hty, hp⟩

/-- A call reached in the body of a Wasm callee `x` is a pending call of `x`. -/
theorem pendO_of_body {C : CallRel H} {x y : (wasmOShape H).self.Op} {fi : FuncInst H}
    {fn : Func} (hf : x.2.2.funcs[x.1]? = some fi) (hcode : fi.code = .wasm fn)
    (h : ReachP C x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body)
      y) :
    PendO C x y := by
  rcases h with h | ⟨z, hz, hp⟩
  · exact .body hf hcode h
  · exact .desc hf hcode hz hp

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
    obtain ⟨hp, y, hr, hb⟩ := hp
    rcases hk₁ with ⟨ws', hw, -⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | rfl
    · exact (pending_ne_vals hp ws' hw).elim
    · exact (pending_ne_trap hp htr).elim
    · exact (pending_ne_throwing hp x hth).elim
    · exact .inr ⟨pending_append hp _, y, reachP_lift (fun _ => ReachO.args) hr,
        blockedAt_mono hb rfl (fun h => atCall_append h _)⟩

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
    rcases ihes s₁ f₁ stk₁ s₂ f₂ stk₂ m' (by omega) hev hfl hrun₂ with ⟨r, hk, hr⟩ |
        ⟨hp, y, hy, hb⟩
    · exact .inl ⟨r, .opOk hi hev hfl hk, hr⟩
    · exact .inr ⟨hp, y, reachP_lift (fun _ => ReachO.opK hi hev hfl) hy, hb⟩
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
    (Pending host c.store c.code ∧ BlockedAt host c ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩) ∨
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
  · exact .inl ⟨Pending.call hf hcode hex hn hno, fi, hh, rfl, hf, hcode, hno, AtCall.here hf⟩
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
  rcases back_call_host hfi hcode hty hp har hnt hrun₁ hend with ⟨hpend, hb⟩ |
      ⟨s₂, fl, hcall, ⟨vs, m', hm', hvs, hk⟩ | ⟨rfl, hends⟩⟩
  · exact .inr ⟨hpend, _, reachP_call hev hfi hty (.inl rfl), hb⟩
  · rcases ihes s₂ f₁ _ m' (by omega) hk with ⟨r, hev', hr⟩ | ⟨hp', y, hy, hb⟩
    · exact .inl ⟨r, .callOk hev hfi hty hcall hvs hev', hr⟩
    · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.callK hev hfi hty hcall hvs) hy, hb⟩
  · exact .inl ⟨_, .callTrap hev hfi hty hcall, hends⟩

/-! ## Blocks -/

/-- The first non-value of a pending call is the call itself, a label or a frame. -/
theorem pending_head {s : Store H} {es : List Admin} (h : Pending host s es) :
    ∃ (vs : List Val) (a : Admin) (r : List Admin), es = vals vs ++ a :: r ∧ a.val? = none ∧
      ((∃ d, a = .callRefType d) ∨ (∃ n cont b, a = .label n cont b) ∨
        ∃ n F b, a = .frame n F b) := by
  cases h with
  | @call ws us a fi hh ps rs rest =>
    exact ⟨ws ++ us ++ [.ref (.func a)], .callRefType fi.type, rest,
      by simp [vals, Val.toAdmin], rfl, .inl ⟨_, rfl⟩⟩
  | @label ws n cont es rest => exact ⟨ws, _, rest, rfl, rfl, .inr (.inl ⟨_, _, _, rfl⟩)⟩
  | @frame ws n F es rest => exact ⟨ws, _, rest, rfl, rfl, .inr (.inr ⟨_, _, _, rfl⟩)⟩

/-- **A pending call is not a label exit form.** -/
theorem pending_not_labelExit {s : Store H} {es out : List Admin} {n : Nat} {cont : List Instr}
    (hp : Pending host s es) (hx : LabelExit n cont es out) : False := by
  obtain ⟨vs, a, r, hes, ha, hk⟩ := pending_head hp
  have key : ∀ (ws : List Val) (b : Admin) (r' : List Admin), b.val? = none →
      es = vals ws ++ b :: r' → a = b := fun ws b r' hb he =>
    (Sim.vals_append_cons_inj ha hb (hes.symm.trans he)).2.1
  have nk : ∀ b, (b = .plain .return_ ∨ (∃ l, b = .plain (.br l)) ∨ b.IsReturnCallRef) → a ≠ b := by
    rintro b hb rfl
    rcases hk with ⟨d, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      rcases hb with h | ⟨l, h⟩ | h <;> cases h
  cases hx with
  | vals ws => exact pending_ne_vals hp ws rfl
  | @brZero vs' ws l rest' _ _ =>
    exact nk _ (.inr (.inl ⟨l, rfl⟩)) (key (vs' ++ ws) _ rest' rfl (by simp))
  | @brSucc ws l rest' _ =>
    exact nk _ (.inr (.inl ⟨l, rfl⟩)) (key ws _ rest' rfl (by simp))
  | @ret ws rest' =>
    exact nk _ (.inl rfl) (key ws _ rest' rfl (by simp))
  | @returnCall ws c' rest' hc =>
    exact nk _ (.inr (.inr hc)) (key ws c' rest' (Admin.val?_of_isReturnCallRef hc) (by simp))
  | throw x => exact pending_ne_throwing hp x rfl
  | trap => exact pending_ne_trap hp rfl

/-- A label around a stuck pending call is stuck, and pending. -/
theorem pending_label {s : Store H} {f : Frame} {ws : List Val} {n : Nat} {cont : List Instr}
    {b rest : List Admin} (hp : Pending host s b) (hb : ∀ c', ¬ Step P host ⟨s, f, b⟩ c') :
    (∀ c', ¬ Step P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ c') ∧
      Pending host s (vals ws ++ [.label n cont b] ++ rest) := by
  have hpe : Pending host s (vals ws ++ [.label n cont b] ++ rest) := by
    simpa using Pending.label (ws := ws) (n := n) (cont := cont) (rest := rest) hp
  refine ⟨fun c' h => ?_, hpe⟩
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .label n cont b) trivial (by simpa using h)
  rcases Step.label_inv h₀ with ⟨s', f', b', hin, -⟩ | ⟨out, hex, -⟩
  · exact hb _ hin
  · exact pending_not_labelExit hp hex

/-- **The backward case of a block**, deterministic profile. Entering the block is
host-free; the body runs in its label to a stuck end (`stepsN_label_seq_split`),
given by the body's case `ihbody` on a no longer run; a blocked body blocks the
block; otherwise the label is left by host-free steps, as the native block is
left. The block arity facts of the body's results are the hypothesis `hblk`. -/
theorem back_block {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    {rest : List Admin} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ .plain (.block bt (Binaryen.BExpr.lowerList body)) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m ≤ n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hblk : ∀ r, EvalH host s f (stk.take np) body r → ∀ vs, r.2.2.blockVals = some vs →
      nr ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = nr) :
    (Pending host c.store c.code ∧
        ∃ y, ReachP (hostCall host) s f (stk.take np) body y ∧ BlockedAt host c y) ∨
      ∃ s₁ f₁ fl, EvalH host s f (stk.take np) body (s₁, f₁, fl) ∧
        ((∃ vs m, m ≤ n ∧ fl.blockVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ c) ∨
          (∃ k vs, fl = .brk (k + 1) vs ∧ EndsAs (s₁, f₁, .brk k vs) c) ∨
          (fl.Escapes ∧ EndsAs (s₁, f₁, fl) c)) := by
  -- entering the block is host-free
  have henter := Interp.steps_enter (P := SingleThreaded.profile o)
    (host := SingleThreaded.Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har) rest
  obtain ⟨m₁, hm₁, hrun₁⟩ := stepsN_through_steps henter hrun hend
  obtain ⟨cb, N₁, hN₁, hb, hsb, hk⟩ := stepsN_label_seq_split hrun₁ hend
  rcases ihbody N₁ (by omega) cb hb hsb with ⟨⟨s₁, f₁, fl⟩, hev, oc, he, hst, hfr, hm⟩ |
      ⟨hpend, y, hy, hbl⟩
  · right
    dsimp only at hst hfr hm
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    refine ⟨rcs, rcf, fl, hev, ?_⟩
    cases hvs : fl.blockVals with
    | some vs =>
      obtain ⟨hnr, hnorm⟩ := hblk _ hev vs hvs
      have hx := Interp.exit_blockVals (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf)
        (pre := (stk.drop np).reverse) (rest := rest) he hm hvs hnr hnorm
      obtain ⟨m, hm', h⟩ := stepsN_through_steps hx hk hend
      refine .inl ⟨vs, m, by omega, rfl, ?_⟩
      rwa [Interp.stack_after]
    | none =>
      have hfl : (∃ k vs, fl = Binaryen.Flow.brk (k + 1) vs) ∨ fl.Escapes := by
        rcases fl with _ | ⟨_ | k, vs⟩ | _ | _ | _ <;>
          simp_all [Binaryen.Flow.blockVals, Binaryen.Flow.Escapes]
      rcases hfl with ⟨k, vs, rfl⟩ | hesc
      · have hw := Interp.exit_abrupt (P := SingleThreaded.profile o)
          (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := nr) (cont := [])
          (fl' := .brk k vs) he hm (.inl ⟨k, vs, rfl, rfl⟩) (stk.drop np).reverse rest
        obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
        obtain ⟨m, -, h⟩ := stepsN_through_steps hst' hk hend
        have := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
          (s := rcs) (f := rcf) he'' hm'' id) h
        subst this
        exact .inr (.inl ⟨k, vs, rfl, o'', he'', rfl, rfl, hm''⟩)
      · have hw := Interp.exit_abrupt (P := SingleThreaded.profile o)
          (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := nr) (cont := [])
          (fl' := fl) he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
        obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
        obtain ⟨m, -, h⟩ := stepsN_through_steps hst' hk hend
        have hn : ¬ fl.IsNormal := by
          rcases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
        have := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
          (s := rcs) (f := rcf) he'' hm'' hn) h
        subst this
        exact .inr (.inr ⟨hesc, o'', he'', rfl, rfl, hm''⟩)
  · left
    obtain ⟨hstk, hpe⟩ := pending_label (P := SingleThreaded.profile o) (ws := (stk.drop np).reverse)
      (n := nr) (cont := []) (rest := rest) (f := cb.frame) hpend hsb
    have := stepsN_of_stuck hstk hk
    subst this
    exact ⟨hpe, y, hy, blockedAt_mono hbl rfl atCall_label⟩

/-- **A block tree** (deterministic profile): `back_block`, then the following
trees by `ihes`. -/
theorem back_block_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.block bt body :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m ≤ n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hblk : ∀ r, EvalH host s f (stk.take np) body r → ∀ vs, r.2.2.blockVals = some vs →
      nr ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = nr)
    (ihes : ∀ s₁ f₁ fl vs m, m ≤ n → EvalH host s f (stk.take np) body (s₁, f₁, fl) →
      fl.blockVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₁ f₁ (vs.take nr ++ stk.drop np) es c) :
    BackOut host s f stk (.block bt body :: es) c := by
  rw [Interp.code_block] at hrun
  rcases back_block har hp hrun hend ihbody hblk with ⟨hpend, y, hy, hb⟩ |
      ⟨s₁, f₁, fl, hev, ⟨vs, m, hm, hvs, hk⟩ | ⟨k, vs, rfl, hends⟩ | ⟨hesc, hends⟩⟩
  · exact .inr ⟨hpend, y, reachP_lift (fun _ => ReachO.block har) hy, hb⟩
  · rcases ihes s₁ f₁ fl vs m hm hev hvs hk with ⟨r, hev', hr⟩ | ⟨hp', y, hy, hb⟩
    · exact .inl ⟨r, .blockOk har hev hvs hev', hr⟩
    · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.blockK har hev hvs) hy, hb⟩
  · exact .inl ⟨_, .blockBrk har hev, hends⟩
  · exact .inl ⟨_, .blockEsc har hev hesc, hends⟩

/-! ## Loops -/

/-- A run from a configuration whose only step is to `d` goes through `d`, one step
shorter. -/
theorem stepsN_unique {n : Nat} {K d c : Config H}
    (huniq : ∀ c₁, Step P host K c₁ → c₁ = d) (hK : Step P host K d)
    (hrun : StepsN P host n K c) (hend : ∀ c', ¬ Step P host c c') :
    ∃ m, n = m + 1 ∧ StepsN P host m d c := by
  cases hrun with
  | refl => exact (hend d hK).elim
  | @head m _ c₁ _ h hrest =>
    obtain rfl := huniq c₁ h
    exact ⟨m, rfl, hrest⟩

/-- **Entering a loop is the only step of a loop under values.** -/
theorem loop_step_unique {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {B : List Instr} {np nr : Nat} {rest : List Admin} {c₁ : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (h : Step P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ c₁) :
    c₁ = ⟨s, f, vals (stk.drop np).reverse ++
      [.label np [.loop bt B] (vals (stk.take np).reverse ++ expression B)] ++ rest⟩ := by
  rcases c₁ with ⟨s', f', es'⟩
  rcases Sim.Step.split_head (a := .plain (.loop bt B)) rfl h with
      ⟨ws, us, is', hsplit, hst, rfl⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · obtain ⟨ws', vs, t₁, t₂, rfl, hbt, hvl, hc⟩ := Step.loop_vals_inv hst
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := Interp.blockType_of_arity har
    rw [hbt] at hbt'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbt'
    obtain ⟨rfl, rfl⟩ := hbt'
    have e : stk.reverse = (stk.drop np).reverse ++ (stk.take np).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e, ← List.append_assoc] at hsplit
    have hlen : vs.length = (stk.take np).reverse.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨h₁, rfl⟩ := List.append_inj' hsplit hlen.symm
    rw [hl₁, h₁]
    simp
  · cases hx
  · cases hx

/-- **The backward case of a loop**, deterministic profile. Entering is the loop's
only step; the body runs in its label to a stuck end, given by `ihbody`; a
blocked body blocks the loop. Otherwise the label is left by host-free steps:
falling through continues after the loop, a branch to the loop re-enters it with
a strictly shorter run, an outer branch, a return or a trap leaves it. The loop's
arity facts on the body's results are the hypothesis `hlp`. -/
theorem back_loop {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    {rest : List Admin} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hlp : ∀ r, EvalH host s f (stk.take np) body r →
      (∀ ws, r.2.2 = .normal ws → ws.length = nr) ∧ ∀ vs, r.2.2 = .brk 0 vs → np ≤ vs.length) :
    (Pending host c.store c.code ∧
        ∃ y, ReachP (hostCall host) s f (stk.take np) body y ∧ BlockedAt host c y) ∨
      ∃ s₁ f₁ fl, EvalH host s f (stk.take np) body (s₁, f₁, fl) ∧
        ((∃ vs m, m < n ∧ fl = .normal vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ c) ∨
          (∃ vs m, m < n ∧ fl = .brk 0 vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
                .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ c) ∨
          (∃ k vs, fl = .brk (k + 1) vs ∧ EndsAs (s₁, f₁, .brk k vs) c) ∨
          (fl.Escapes ∧ EndsAs (s₁, f₁, fl) c)) := by
  have hstep := Interp.step_enter (P := SingleThreaded.profile o) (host := host) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har) rest
  obtain ⟨m₀, rfl, hrun₁⟩ := stepsN_unique (fun c₁ h => loop_step_unique har hp h) hstep hrun hend
  obtain ⟨cb, N₁, hN₁, hb, hsb, hk⟩ := stepsN_label_seq_split hrun₁ hend
  rcases ihbody N₁ (by omega) cb hb hsb with ⟨⟨s₁, f₁, fl⟩, hev, oc, he, hst, hfr, hm⟩ |
      ⟨hpend, y, hy, hbl⟩
  · right
    dsimp only at hst hfr hm
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    refine ⟨rcs, rcf, fl, hev, ?_⟩
    obtain ⟨hnorm, hbr0⟩ := hlp _ hev
    rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
    · -- falls through
      have hx := Interp.exit_normal (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (stk.drop np).reverse rest
      obtain ⟨m, hm', h⟩ := stepsN_through_steps hx hk hend
      refine .inl ⟨ws, m, by omega, rfl, ?_⟩
      have htake : ws.take nr = ws := List.take_of_length_le (hnorm ws rfl).le
      rw [htake]
      simpa [Interp.stack_after] using h
    · -- branches back to the loop
      have hx := Interp.exit_br0 (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (hbr0 vs rfl)
        (stk.drop np).reverse rest
      obtain ⟨m, hm', h⟩ := stepsN_through_steps hx hk hend
      refine .inr (.inl ⟨vs, m, by omega, rfl, ?_⟩)
      simpa [Interp.stack_after, expression] using h
    · -- an outer branch
      have hw := Interp.exit_abrupt (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        (fl' := .brk k vs) he hm (.inl ⟨k, vs, rfl, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := stepsN_through_steps hst' hk hend
      have := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' id) h
      subst this
      exact .inr (.inr (.inl ⟨k, vs, rfl, o'', he'', rfl, rfl, hm''⟩))
    · -- returns
      have hesc : (Binaryen.Flow.ret ws).Escapes := by simp [Binaryen.Flow.Escapes]
      have hw := Interp.exit_abrupt (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := stepsN_through_steps hst' hk hend
      have := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' (by simp [Binaryen.Flow.IsNormal])) h
      subst this
      exact .inr (.inr (.inr ⟨hesc, o'', he'', rfl, rfl, hm''⟩))
    · -- traps
      have hesc : (Binaryen.Flow.trap).Escapes := by simp [Binaryen.Flow.Escapes]
      have hw := Interp.exit_abrupt (P := SingleThreaded.profile o)
        (host := SingleThreaded.Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := stepsN_through_steps hst' hk hend
      have := stepsN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' (by simp [Binaryen.Flow.IsNormal])) h
      subst this
      exact .inr (.inr (.inr ⟨hesc, o'', he'', rfl, rfl, hm''⟩))
    · rcases oc <;> simp_all [Interp.FlowMatch]
  · left
    obtain ⟨hstk, hpe⟩ := pending_label (P := SingleThreaded.profile o) (ws := (stk.drop np).reverse)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) (rest := rest)
      (f := cb.frame) hpend hsb
    have := stepsN_of_stuck hstk hk
    subst this
    exact ⟨hpe, y, hy, blockedAt_mono hbl rfl atCall_label⟩

/-- **A loop tree** (deterministic profile): `back_loop`, then the following trees
by `ihes`, and a re-entry by `ihloop` on a strictly shorter run. -/
theorem back_loop_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hlp : ∀ r, EvalH host s f (stk.take np) body r →
      (∀ ws, r.2.2 = .normal ws → ws.length = nr) ∧ ∀ vs, r.2.2 = .brk 0 vs → np ≤ vs.length)
    (ihes : ∀ s₁ f₁ vs m, m < n → EvalH host s f (stk.take np) body (s₁, f₁, .normal vs) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₁ f₁ (vs.take nr ++ stk.drop np) es c)
    (ihloop : ∀ s₁ f₁ vs m, m < n → EvalH host s f (stk.take np) body (s₁, f₁, .brk 0 vs) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ c →
      BackOut host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) c) :
    BackOut host s f stk (.loop bt body :: es) c := by
  rw [Interp.code_loop] at hrun
  rcases back_loop har hp hrun hend ihbody hlp with ⟨hpend, y, hy, hb⟩ |
      ⟨s₁, f₁, fl, hev, ⟨vs, m, hm, rfl, hk⟩ | ⟨vs, m, hm, rfl, hk⟩ | ⟨k, vs, rfl, hends⟩ |
        ⟨hesc, hends⟩⟩
  · exact .inr ⟨hpend, y, reachP_lift (fun _ => ReachO.loop har) hy, hb⟩
  · rcases ihes s₁ f₁ vs m hm hev hk with ⟨r, hev', hr⟩ | ⟨hp', y, hy, hb⟩
    · exact .inl ⟨r, .loopOk har hev hev', hr⟩
    · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.loopK har hev) hy, hb⟩
  · rcases ihloop s₁ f₁ vs m hm hev (by rw [Interp.code_loop]; exact hk) with ⟨r, hev', hr⟩ |
        ⟨hp', y, hy, hb⟩
    · exact .inl ⟨r, .loopBack har hev hev', hr⟩
    · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.loopBack har hev) hy, hb⟩
  · exact .inl ⟨_, .loopBrk har hev, hends⟩
  · exact .inl ⟨_, .loopEsc har hev hesc, hends⟩

/-! ## `if` -/

/-- **A run of trees followed by more code**: the trees' run blocks, or ends
abruptly (and the whole run ends there), or completes normally on `stk₁`, and the
rest of the run continues from `vals stk₁ ++ K` in no more steps. -/
theorem back_prefix {n : Nat} {s : Store H} {f : Frame} {stk : List Val}
    {xs : List Binaryen.BExpr} {K : List Admin} {c : Config H} (hK : K ≠ [])
    (hrun : StepsN P host n
      ⟨s, f, (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)) ++ K⟩ c)
    (hend : ∀ c', ¬ Step P host c c')
    (ihxs : ∀ m ≤ n, ∀ c₁, StepsN P host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)⟩ c₁ →
      (∀ c', ¬ Step P host c₁ c') → BackOut host s f stk xs c₁) :
    (Pending host c.store c.code ∧
        ∃ y, ReachP (hostCall host) s f stk xs y ∧ BlockedAt host c y) ∨
      (∃ r₁, EvalH host s f stk xs r₁ ∧ ¬ r₁.2.2.IsNormal ∧ EndsAs r₁ c) ∨
      ∃ s₁ f₁ stk₁ m, m ≤ n ∧ EvalH host s f stk xs (s₁, f₁, .normal stk₁) ∧
        StepsN P host m ⟨s₁, f₁, vals stk₁.reverse ++ K⟩ c := by
  obtain ⟨c₁, n₁, h₁, hn₁, hs₁, hk₁⟩ := stepsN_seq_split hrun hend
  rcases ihxs n₁ hn₁ c₁ h₁ hs₁ with ⟨⟨s₁, f₁, fl⟩, hev, o, he, hst, hfr, hfm⟩ | ⟨hp, y, hy, hb⟩
  · dsimp only at hst hfr hfm
    subst hst hfr
    by_cases hnorm : fl.IsNormal
    · rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hnorm
      rcases o with ws | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hfm
      subst hfm
      have hcode : c₁.code = vals stk₁.reverse := he
      right; right
      rcases hk₁ with ⟨ws', hw, hrest⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | rfl
      · rw [hcode] at hw
        obtain rfl : ws' = stk₁.reverse := (Sim.vals_injective hw).symm
        exact ⟨_, _, stk₁, n - n₁, Nat.sub_le _ _, hev, hrest⟩
      · rw [hcode] at htr
        exact absurd (htr ▸ (by simp : Admin.trap ∈ [Admin.trap]))
          (not_mem_vals_of_val? (a := .trap) rfl)
      · rw [hcode] at hth
        exact absurd (hth ▸ (by simp [throwing] : Admin.plain .throwRef ∈ throwing x))
          (not_mem_vals_of_val? (a := .plain .throwRef) rfl)
      · refine ⟨_, _, stk₁, 0, Nat.zero_le _, hev, ?_⟩
        rw [hcode]
        exact .refl _
    · right; left
      refine ⟨_, hev, hnorm, ?_⟩
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
          exact ⟨x, rest ++ K, hx, by rw [he]; simp⟩
        · obtain ⟨rest, he⟩ := he
          exact ⟨rest ++ K, by rw [he]; simp⟩
        · have he' : c₁.code = [.trap] := he
          exfalso
          apply hend ⟨c₁.store, c₁.frame, [.trap]⟩
          rw [he']
          obtain ⟨k₀, K', rfl⟩ := List.exists_cons_of_ne_nil hK
          simpa using Step.trapInstrs (P := P) (host := host) (s := c₁.store) (f := c₁.frame)
            (vs := []) (rest := k₀ :: K') (.inr (by simp))
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
  · left
    rcases hk₁ with ⟨ws', hw, -⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | rfl
    · exact (pending_ne_vals hp ws' hw).elim
    · exact (pending_ne_trap hp htr).elim
    · exact (pending_ne_throwing hp x hth).elim
    · exact ⟨pending_append hp _, y, hy, blockedAt_mono hb rfl (fun h => atCall_append h _)⟩

/-- **An `if` tree** (deterministic profile): the condition by `back_prefix`, the
host-free `if` step to the block of the chosen arm (`Interp.step_if_arm`), the arm
by `back_block`, the following trees by `ihes`. The condition's result being an
`i32` with the arm's block arity, and the arm's block arity facts, are the
hypotheses `hcond` and `hblk`. -/
theorem back_if_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {cnd t el es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihcond : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk cnd c₁)
    (hcond : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      ∃ cv stk₁ b np nr, stk' = cv :: stk₁ ∧ Binaryen.truthy cv = some b ∧
        Binaryen.arity f₁ bt = some (np, nr) ∧ np ≤ stk₁.length ∧
        (∀ r, EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) r →
          ∀ vs, r.2.2.blockVals = some vs → nr ≤ vs.length ∧
            ∀ ws, r.2.2 = .normal ws → ws.length = nr))
    (iharm : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (m : Nat), m ≤ n → EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) →
      Binaryen.truthy cv = some b → Binaryen.arity f₁ bt = some (np, nr) → ∀ cb,
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (stk₁.take np).reverse ++
          expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s₁ f₁ (stk₁.take np) (if b then t else el) cb)
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (s₂ : Store H) (f₂ : Frame) (fl : Binaryen.Flow) (vs : List Val) (m : Nat), m ≤ n →
      EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) → Binaryen.truthy cv = some b →
      Binaryen.arity f₁ bt = some (np, nr) →
      EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) →
      fl.blockVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₂, vals (vs.take nr ++ stk₁.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₂ (vs.take nr ++ stk₁.drop np) es c) :
    BackOut host s f stk (.if_ bt cnd t el :: es) c := by
  rw [Interp.code_if] at hrun
  rcases back_prefix (by simp) hrun hend ihcond with ⟨hpend, y, hy, hb⟩ |
      ⟨r₁, hev, hn, hends⟩ | ⟨s₁, f₁, stk', m, hm, hev, hrun₁⟩
  · exact .inr ⟨hpend, y, reachP_lift (fun _ => ReachO.cond) hy, hb⟩
  · rcases r₁ with ⟨s₁, f₁, fl⟩
    exact .inl ⟨_, .ifAbort hev hn, hends⟩
  · obtain ⟨cv, stk₁, b, np, nr, rfl, hb, har, hp, hblk⟩ := hcond s₁ f₁ stk' hev
    have hd := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    obtain ⟨m₁, hm₁, hrun₂⟩ := stepsN_through hrun₁ hend hd
    rcases back_block har hp hrun₂ hend
        (fun m' hm' cb h hs => iharm s₁ f₁ cv stk₁ b np nr m' (by omega) hev hb har cb h hs) hblk with
      ⟨hpend, y, hy, hbl⟩ |
      ⟨s₂, f₂, fl, hevb, ⟨vs, m', hm', hvs, hk⟩ | ⟨k, vs, rfl, hends⟩ | ⟨hesc, hends⟩⟩
    · exact .inr ⟨hpend, y, reachP_lift (fun _ => ReachO.arm hev hb har) hy, hbl⟩
    · rcases ihes s₁ f₁ cv stk₁ b np nr s₂ f₂ fl vs m' (by omega) hev hb har hevb hvs hk with
          ⟨r, hev', hr⟩ | ⟨hp', y, hy, hbl⟩
      · exact .inl ⟨r, .ifOk hev hb har hevb hvs hev', hr⟩
      · exact .inr ⟨hp', y, reachP_lift (fun _ => ReachO.ifK hev hb har hevb hvs) hy, hbl⟩
    · exact .inl ⟨_, .ifBrk hev hb har hevb, hends⟩
    · exact .inl ⟨_, .ifEsc hev hb har hevb hesc, hends⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
