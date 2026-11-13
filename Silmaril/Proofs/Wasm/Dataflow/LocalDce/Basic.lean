module

public import Silmaril.Wasm.Dataflow.LocalDce.Defs
public import Silmaril.Wasm.Dataflow.Liveness.Thms
public import Silmaril.Wasm.Dataflow.Fragment.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

/-!
# an earlier step of the two-pass DCE: structural lemmas

The transform is a homomorphism for `++` (`localDceAdminSeq_append`), agrees with the
source transform on source code (`localDceAdminSeq_expression`) and fixes values, results
and pending returns. `LCode` is closed under value/suffix contexts (`LCode.ctx`) and is the
transform on code whose first non-value is neither a pending store nor a label.

`LMatched` is the one-step obligation of the pass-1 simulation, and `LMatched.lock` is its
lock-step case.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-! ## The transform -/

/-- The administrative transform is a homomorphism for `++`: the left part is transformed
with the live set of the right part as its live-out set. -/
theorem localDceAdminSeq_append (env : List LiveSet) (out : LiveSet) (as bs : List Admin) :
    localDceAdminSeq env out (as ++ bs) =
      localDceAdminSeq env (liveAdminSeq env out bs) as ++ localDceAdminSeq env out bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, liveAdminSeq_append]

theorem localDceSeq_append (env : List LiveSet) (out : LiveSet) (is js : List Instr) :
    localDceSeq env out (is ++ js) =
      localDceSeq env (liveSeq env out js) is ++ localDceSeq env out js := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih, Backward.seq_append]

/-- On source code the administrative transform is the source transform. -/
theorem localDceAdminSeq_expression (env : List LiveSet) (out : LiveSet) (e : List Instr) :
    localDceAdminSeq env out (expression e) = expression (localDceSeq env out e) := by
  induction e with
  | nil => simp [expression]
  | cons i e ih =>
      rw [show expression (i :: e) = .plain i :: expression e from rfl, localDceAdminSeq_cons,
        ih, liveAdminSeq_expression, localDceSeq_cons]
      simp [localDceAdmin, expression]

/-- A value is unchanged. -/
theorem localDceAdmin_toAdmin (env : List LiveSet) (out : LiveSet) (v : Val) :
    localDceAdmin env out v.toAdmin = [v.toAdmin] := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, localDceAdmin, localDceInstr]

/-- A sequence of values is unchanged. -/
theorem localDceAdminSeq_vals (env : List LiveSet) (out : LiveSet) (vs : List Val) :
    localDceAdminSeq env out (vals vs) = vals vs := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih =>
      simp only [vals, List.map_cons, localDceAdminSeq_cons] at ih ⊢
      rw [ih, localDceAdmin_toAdmin]
      rfl

/-- A result is unchanged. -/
theorem localDceAdminSeq_result (env : List LiveSet) (out : LiveSet) (r : Result) :
    localDceAdminSeq env out r.toAdmin = r.toAdmin := by
  cases r with
  | values vs => exact localDceAdminSeq_vals env out vs
  | throw a => simp [Result.toAdmin, localDceAdmin, localDceInstr]
  | trap => simp [Result.toAdmin, localDceAdmin]

/-- A pending `return` with its values is unchanged. -/
theorem localDceAdminSeq_returning (env : List LiveSet) (out : LiveSet) (vs : List Val) :
    localDceAdminSeq env out (vals vs ++ [.plain .return_]) = vals vs ++ [.plain .return_] := by
  rw [localDceAdminSeq_append, localDceAdminSeq_vals]
  simp [localDceAdmin, localDceInstr]

/-- The transform of code in a value/suffix context. -/
theorem localDceAdminSeq_ctx (env : List LiveSet) (out : LiveSet) (vs : List Val)
    (is rest : List Admin) :
    localDceAdminSeq env out (vals vs ++ is ++ rest) =
      vals vs ++ localDceAdminSeq env (liveAdminSeq env out rest) is ++
        localDceAdminSeq env out rest := by
  simp only [List.append_assoc, localDceAdminSeq_append, localDceAdminSeq_vals]

/-! ## The target relation on code -/

variable {H : Type}

/-- `LCode` is closed under a value prefix and a suffix (`Step/ctxt-instrs`). -/
theorem LCode.ctx {env : List LiveSet} {out : LiveSet} {a b : List Admin} (vs : List Val)
    (rest : List Admin) (h : LCode env (liveAdminSeq env out rest) a b) :
    LCode env out (vals vs ++ a ++ rest) (vals vs ++ b ++ localDceAdminSeq env out rest) := by
  cases h with
  | clean =>
    have := LCode.clean (env := env) (out := out) (vals vs ++ a ++ rest)
    simpa only [List.append_assoc, localDceAdminSeq_append, localDceAdminSeq_vals] using this
  | pend us w x r hx =>
    have hx' : (liveAdminSeq env out (r ++ rest)).mem x.toNat = false := by
      rwa [liveAdminSeq_append]
    have := LCode.pend (env := env) (out := out) (vs ++ us) w x (r ++ rest) hx'
    simpa only [vals_append, List.append_assoc, List.cons_append, localDceAdminSeq_append]
      using this
  | label us n cont r hb =>
    rw [← liveAdminSeq_append] at hb
    have := LCode.label (env := env) (out := out) (vs ++ us) n cont (r ++ rest) hb
    simpa only [vals_append, List.append_assoc, List.cons_append, localDceAdminSeq_append,
      liveAdminSeq_append] using this

/-- Code whose first non-value is neither a `local.set` nor a label is related by `LCode`
only to its transform. -/
theorem LCode.clean_of_head {env : List LiveSet} {out : LiveSet} {us : List Val} {e : Admin}
    {r d : List Admin} (h : LCode env out (vals us ++ e :: r) d) (he : e.val? = none)
    (hset : ∀ x, e ≠ .plain (.localSet x)) (hlab : ∀ n cont b, e ≠ .label n cont b) :
    d = localDceAdminSeq env out (vals us ++ e :: r) := by
  generalize hc : vals us ++ e :: r = c at h
  cases h with
  | clean => rfl
  | pend vs w x rest hx =>
    have hc' : vals us ++ e :: r = vals (vs ++ [w]) ++ Admin.plain (.localSet x) :: rest := by
      rw [hc]; simp [vals]
    exact absurd (SingleThreaded.Det.vals_append_cons_inj hc' he rfl).2.1 (hset x)
  | label vs n cont rest hb =>
    exact absurd (SingleThreaded.Det.vals_append_cons_inj hc he rfl).2.1 (hlab n cont _)

theorem LCode.clean_of_head₂ {env : List LiveSet} {out : LiveSet} {us : List Val} {e : Admin}
    {r d : List Admin} (h : LCode env out (vals us ++ [e] ++ r) d) (he : e.val? = none)
    (hset : ∀ x, e ≠ .plain (.localSet x)) (hlab : ∀ n cont b, e ≠ .label n cont b) :
    d = localDceAdminSeq env out (vals us ++ [e] ++ r) := by
  simpa using LCode.clean_of_head (us := us) (e := e) (r := r) (by simpa using h) he hset hlab

theorem inert_result (r : Result) : Inert r.toAdmin := by
  intro a ha
  cases r with
  | values vs => exact .inl (SingleThreaded.Det.mem_vals ha)
  | throw x =>
      simp only [Result.toAdmin, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inl (by simp [Admin.val?])
      · exact .inr (.inl rfl)
  | trap =>
      simp only [Result.toAdmin, List.mem_singleton] at ha
      exact .inr (.inr (.inr ha))

theorem inert_returning (vs : List Val) : Inert (vals vs ++ [.plain .return_]) := by
  intro a ha
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact .inl (SingleThreaded.Det.mem_vals ha)
  · exact .inr (.inr (.inl rfl))

theorem inert_vals (vs : List Val) : Inert (vals vs) :=
  fun _ ha => .inl (SingleThreaded.Det.mem_vals ha)

theorem inert_trap : Inert [.trap] := by
  intro a ha
  exact .inr (.inr (.inr (List.mem_singleton.mp ha)))

/-- On inert code `LCode` is the transform. -/
theorem LCode.eq_of_inert {env : List LiveSet} {out : LiveSet} {c d : List Admin}
    (h : LCode env out c d) (hc : Inert c) : d = localDceAdminSeq env out c := by
  cases h with
  | clean => rfl
  | pend vs w x rest hx =>
      exfalso
      rcases hc _ (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))) with
        h | h | h | h <;> simp [Admin.val?] at h
  | label vs n cont rest hb =>
      exfalso
      rcases hc _ (List.mem_append_right _ (List.Mem.head _)) with h | h | h | h <;>
        simp [Admin.val?] at h

/-- `LCode` relates a result only to itself. -/
theorem LCode.result {env : List LiveSet} {out : LiveSet} {r : Result} {d : List Admin}
    (h : LCode env out r.toAdmin d) : d = r.toAdmin :=
  (h.eq_of_inert (inert_result r)).trans (localDceAdminSeq_result env out r)

/-- `LCode` relates a pending `return` only to itself. -/
theorem LCode.returning {env : List LiveSet} {out : LiveSet} {vs : List Val} {d : List Admin}
    (h : LCode env out (vals vs ++ [.plain .return_]) d) : d = vals vs ++ [.plain .return_] :=
  (h.eq_of_inert (inert_returning vs)).trans (localDceAdminSeq_returning env out vs)

/-! ## The one-step obligation -/

/-- The obligation of one source step `c₁ ⟶ c₂` against the target `d₁`: a related target
`d₂`, reached in at least one step or, with `codeSize` decreasing, in none. -/
def LMatched (P : Profile) (host : HostSemantics H) (env : List LiveSet) (out : LiveSet)
    (c₁ c₂ d₁ : Config H) : Prop :=
  ∃ d₂, LRel env out c₂ d₂ ∧
    (Relation.TransGen (Step P host) d₁ d₂ ∨ (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code))

/-- A lock-step source step on clean code. -/
theorem LMatched.lock {P : Profile} {host : HostSemantics H} {env : List LiveSet}
    {out : LiveSet} {s s' : Store H} {f f' fd fd' : Frame} {c c' : List Admin}
    (hstep : Step P host ⟨s, fd, localDceAdminSeq env out c⟩
      ⟨s', fd', localDceAdminSeq env out c'⟩)
    (hfr : FrameRel (liveAdminSeq env out c') f' fd') (hfrag : fragAdminSeq c' = true) :
    LMatched P host env out ⟨s, f, c⟩ ⟨s', f', c'⟩ ⟨s, fd, localDceAdminSeq env out c⟩ :=
  ⟨⟨s', fd', localDceAdminSeq env out c'⟩, ⟨rfl, hfr, hfrag, .clean _⟩, .inl (.single hstep)⟩

/-- A stutter: the target stays put and the source measure decreases. -/
theorem LMatched.stutter {P : Profile} {host : HostSemantics H} {env : List LiveSet}
    {out : LiveSet} {c₁ c₂ d : Config H} (hr : LRel env out c₂ d)
    (hlt : codeSize c₂.code < codeSize c₁.code) : LMatched P host env out c₁ c₂ d :=
  ⟨d, hr, .inr ⟨rfl, hlt⟩⟩

/-- Lift a match through a value prefix and a transformed suffix. -/
theorem LMatched.ctx {P : Profile} {host : HostSemantics H} {env : List LiveSet}
    {out : LiveSet} {s s' : Store H} {f f' df : Frame} {is is' dc : List Admin}
    (vs : List Val) (rest : List Admin)
    (hm : LMatched P host env (liveAdminSeq env out rest) ⟨s, f, is⟩ ⟨s', f', is'⟩ ⟨s, df, dc⟩)
    (hfrag : fragAdminSeq (vals vs ++ is' ++ rest) = true) :
    LMatched P host env out ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
      ⟨s, df, vals vs ++ dc ++ localDceAdminSeq env out rest⟩ := by
  obtain ⟨⟨ds', df', dc'⟩, hr', hp⟩ := hm
  have hfr : FrameRel (liveAdminSeq env out (vals vs ++ is' ++ rest)) f' df' := by
    simpa [liveAdminSeq_append, liveAdminSeq_vals] using hr'.frame
  refine ⟨⟨ds', df', vals vs ++ dc' ++ localDceAdminSeq env out rest⟩,
    ⟨hr'.store, hfr, hfrag, LCode.ctx vs rest hr'.code⟩, ?_⟩
  rcases hp with ht | ⟨he, hlt⟩
  · exact .inl (Sim.Closure.transGen_ctx ht vs _)
  · have he' : ds' = s ∧ df' = df ∧ dc' = dc := by simpa using he
    have hlt' : codeSize is' < codeSize is := hlt
    refine .inr ⟨by rw [he'.1, he'.2.1, he'.2.2], ?_⟩
    show codeSize (vals vs ++ is' ++ rest) < codeSize (vals vs ++ is ++ rest)
    simp only [codeSize_append]
    omega

/-- Lift a match of a label body through the label. -/
theorem LMatched.label {P : Profile} {host : HostSemantics H} {env : List LiveSet}
    {out : LiveSet} {s s' : Store H} {f f' df : Frame} {n : Nat} {cont : List Instr}
    (vs : List Val) (rest : List Admin) {body body' bd : List Admin}
    (hm : LMatched P host (liveSeq env (liveAdminSeq env out rest) cont :: env)
      (liveAdminSeq env out rest) ⟨s, f, body⟩ ⟨s', f', body'⟩ ⟨s, df, bd⟩)
    (hfrag : fragAdminSeq (vals vs ++ .label n cont body' :: rest) = true) :
    LMatched P host env out ⟨s, f, vals vs ++ .label n cont body :: rest⟩
      ⟨s', f', vals vs ++ .label n cont body' :: rest⟩
      ⟨s, df, vals vs ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) bd ::
        localDceAdminSeq env out rest⟩ := by
  obtain ⟨⟨ds', df', dc'⟩, hr', hp⟩ := hm
  have hfr : FrameRel (liveAdminSeq env out (vals vs ++ .label n cont body' :: rest)) f' df' := by
    simpa [liveAdminSeq_append, liveAdminSeq_vals, liveAdmin] using hr'.frame
  refine ⟨⟨ds', df', vals vs ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) dc' ::
      localDceAdminSeq env out rest⟩, ⟨hr'.store, hfr, hfrag, LCode.label vs n cont rest hr'.code⟩,
    ?_⟩
  rcases hp with ht | ⟨he, hlt⟩
  · left
    simpa using Sim.Closure.transGen_ctx
      (Sim.Closure.transGen_label ht n (localDceSeq env (liveAdminSeq env out rest) cont)) vs
      (localDceAdminSeq env out rest)
  · have he' : ds' = s ∧ df' = df ∧ dc' = bd := by simpa using he
    have hlt' : codeSize body' < codeSize body := hlt
    refine .inr ⟨by rw [he'.1, he'.2.1, he'.2.2], ?_⟩
    show codeSize (vals vs ++ .label n cont body' :: rest) <
      codeSize (vals vs ++ .label n cont body :: rest)
    simp only [codeSize_append, codeSize_cons, adminSize]
    omega

theorem Store.global?_congr {s : Store H} {f f' : Frame} (hm : f.module = f'.module)
    (x : GlobalIdx) : s.global? f x = s.global? f' x := by
  simp [Store.global?, hm]

end Silmaril.Wasm.Dataflow
