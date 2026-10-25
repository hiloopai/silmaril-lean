module

public import Silmaril.Wasm.SingleThreaded.Profile

@[expose] public section

/-! # Store-free threads, status, callouts and resumption

A `Thread` is a store-free description of a Core configuration: either a
*pending* invocation `$invoke(s, a, args)` (whose `CALL_REF` annotation is read
from the store when the thread is loaded, so no store is needed to create it), or
an *active* frame and administrative code. `Thread.config s t` is the Core
configuration it denotes.

A host call is not a step. `decompose?` finds the host-call redex
`val^n (REF.FUNC_ADDR a) (CALL_REF yy)` (with `a` a host function of arity `n`)
under the evaluation contexts `val* [_] instr*`, `LABEL_`, `HANDLER_`, `FRAME_`,
and returns the context, the host code and the arguments. `resume` plugs the
host's result into that context (the spec's `$lift_result`).

`status` classifies a thread: `returned` for a value result, for a trap, and —
exceptions at the boundary are traps — for an uncaught `THROW_REF`; `callout`
for a host-call redex; `running` when an internal (host-free) step exists; else
`stuck`. `status` is noncomputable only in its last case (existence of a step);
`Exec` for a computable step function is later work.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

inductive Thread where
  | pending (a : Nat) (args : List Val)
  | active (frame : Frame) (code : List Admin)

/-- The Core configuration denoted by a thread. -/
def Thread.config (s : Store H) : Thread → Config H
  | .pending a args => invoke s a args
  | .active f code => ⟨s, f, code⟩

/-- `Thread.invoke a args`, the component interface's store-free invocation. -/
def Thread.invoke (a : Nat) (args : List Val) : Thread := .pending a args

/-- Results crossing the boundary: values or a trap (exceptions become traps). -/
inductive CallResult where
  | values (vs : List Val)
  | trap
  deriving DecidableEq, Repr

def CallResult.toAdmin : CallResult → List Admin
  | .values vs => vals vs
  | .trap => [.trap]

inductive Status (H : Type) where
  | running
  | returned (r : CallResult)
  | callout (h : H) (args : List Val)
  | stuck

/-- Evaluation contexts around a host-call redex. -/
inductive Ctx where
  | top (pre : List Val) (rest : List Admin)
  | label (pre : List Val) (n : Nat) (cont : List Instr) (inner : Ctx) (rest : List Admin)
  | handler (pre : List Val) (n : Nat) (cs : List Catch) (inner : Ctx) (rest : List Admin)
  | frame (pre : List Val) (n : Nat) (f : Frame) (inner : Ctx) (rest : List Admin)

def Ctx.fill : Ctx → List Admin → List Admin
  | .top pre rest, xs => vals pre ++ xs ++ rest
  | .label pre n cont E rest, xs => vals pre ++ [.label n cont (E.fill xs)] ++ rest
  | .handler pre n cs E rest, xs => vals pre ++ [.handler n cs (E.fill xs)] ++ rest
  | .frame pre n f E rest, xs => vals pre ++ [.frame n f (E.fill xs)] ++ rest

def _root_.Silmaril.Wasm.Execution.Core.Admin.isCallRef : Admin → Bool
  | .plain (.callRef _) => true
  | .callRefType _ => true
  | _ => false

/-- The maximal prefix of value instructions. -/
def splitVals : List Admin → List Val × List Admin
  | [] => ([], [])
  | a :: as =>
    match a.val? with
    | some v => ((splitVals as).1.cons v, (splitVals as).2)
    | none => ([], a :: as)

theorem splitVals_snd_sizeOf (l : List Admin) : sizeOf (splitVals l).2 ≤ sizeOf l := by
  induction l with
  | nil => simp [splitVals]
  | cons a as ih =>
    unfold splitVals
    (cases a.val? <;> simp); omega

/-- The host code and arity of the function at address `a`, if it is a host function. -/
def hostArity? (s : Store H) (a : Nat) : Option (H × Nat) :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code, fi.type.funcType? with
    | .host h, some (ps, _) => some (h, ps.length)
    | _, _ => none
  | none => none

/-- Locate a host-call redex: the context, the callee address, its host code and
the arguments. -/
def decompose? (s : Store H) (code : List Admin) : Option (Ctx × Nat × H × List Val) :=
  match _hs : splitVals code with
  | (vs, .label n cont body :: rest) =>
    (decompose? s body).map fun (E, a, h, args) => (.label vs n cont E rest, a, h, args)
  | (vs, .handler n cs body :: rest) =>
    (decompose? s body).map fun (E, a, h, args) => (.handler vs n cs E rest, a, h, args)
  | (vs, .frame n f body :: rest) =>
    (decompose? s body).map fun (E, a, h, args) => (.frame vs n f E rest, a, h, args)
  | (vs, c :: rest) =>
    if c.isCallRef then
      match vs.getLast? with
      | some (.ref (.func a)) =>
        match hostArity? s a with
        | some (h, n) =>
          let pre := vs.dropLast
          if n ≤ pre.length then
            some (.top (pre.take (pre.length - n)) rest, a, h, pre.drop (pre.length - n))
          else none
        | none => none
      | _ => none
    else none
  | (_, []) => none
termination_by sizeOf code
decreasing_by
  all_goals
    have h := splitVals_snd_sizeOf code
    rw [_hs] at h
    simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec, Admin.handler.sizeOf_spec,
      Admin.frame.sizeOf_spec] at h
    omega

/-- A thread with no store-independent redex other than a host call, in terms of
its code (a pending thread is loaded first). -/
def Thread.code (s : Store H) (t : Thread) : List Admin := (t.config s).code

/-- The internal (host-free) step of the single-threaded machine: a Core step in
the deterministic profile with the empty host relation. The result is active. -/
def Internal (o : GrowOracle) : Store H × Thread → Store H × Thread → Prop
  | (s, t), (s', t') => ∃ f' code', t' = .active f' code' ∧
      Step (profile o) (fun _ _ _ _ => False) (t.config s) ⟨s', f', code'⟩

open Classical in
/-- The status of a thread. -/
noncomputable def status (o : GrowOracle) (s : Store H) (t : Thread) : Status H :=
  let c := t.config s
  if h : ∃ vs, c.code = vals vs then .returned (.values h.choose)
  else if c.code = [.trap] then .returned .trap
  else if ∃ a, c.code = throwing a then .returned .trap
  else match decompose? s c.code with
    | some (_, _, h, args) => .callout h args
    | none => if ∃ y, Internal o (s, t) y then .running else .stuck

/-- Plug a host result into the callout context. -/
def resume (s : Store H) (t : Thread) (r : CallResult) : Thread :=
  let c := t.config s
  match decompose? s c.code with
  | some (E, _, _, _) => .active c.frame (E.fill r.toAdmin)
  | none => t

/-- Resumption with a full Core host result (exceptions are propagated inside the
thread, as `$lift_result` does). -/
def resumeResult (s : Store H) (t : Thread) (r : Result) : Thread :=
  let c := t.config s
  match decompose? s c.code with
  | some (E, _, _, _) => .active c.frame (E.fill r.toAdmin)
  | none => t

/-! ## Helper lemmas: values, `splitVals`, `Ctx.fill` -/

theorem _root_.Silmaril.Wasm.Execution.Core.Admin.eq_toAdmin_of_val? {a : Admin} {v : Val}
    (h : a.val? = some v) : a = v.toAdmin := by
  unfold Admin.val? at h
  split at h <;> first | (cases h; rfl) | simp at h

theorem _root_.Silmaril.Wasm.Execution.Core.Admin.IsCallRef_of_isCallRef {a : Admin}
    (h : a.isCallRef = true) : a.IsCallRef := by
  unfold Admin.isCallRef at h
  split at h <;> trivial

theorem _root_.Silmaril.Wasm.Execution.Core.Admin.isCallRef_of_IsCallRef {a : Admin}
    (h : a.IsCallRef) : a.isCallRef = true := by
  unfold Admin.IsCallRef at h
  split at h <;> first | rfl | exact h.elim

theorem _root_.Silmaril.Wasm.Execution.Core.Admin.val?_of_IsCallRef {a : Admin}
    (h : a.IsCallRef) : a.val? = none := by
  unfold Admin.IsCallRef at h
  split at h <;> first | rfl | exact h.elim

@[simp] theorem vals_nil : vals [] = [] := rfl
@[simp] theorem vals_cons (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs := rfl

theorem splitVals_cons_val {a : Admin} {v : Val} (h : a.val? = some v) (as : List Admin) :
    splitVals (a :: as) = (v :: (splitVals as).1, (splitVals as).2) := by
  rw [splitVals, h]

theorem splitVals_cons_nonval {a : Admin} (h : a.val? = none) (as : List Admin) :
    splitVals (a :: as) = ([], a :: as) := by
  rw [splitVals, h]

theorem splitVals_vals_append (vs : List Val) (l : List Admin) :
    splitVals (vals vs ++ l) = (vs ++ (splitVals l).1, (splitVals l).2) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [vals_cons, List.cons_append, splitVals_cons_val (Admin.val?_toAdmin v), ih]
    rfl

theorem splitVals_vals (vs : List Val) : splitVals (vals vs) = (vs, []) := by
  simpa [splitVals] using splitVals_vals_append vs []

theorem splitVals_vals_cons {vs : List Val} {d : Admin} (hd : d.val? = none) (r : List Admin) :
    splitVals (vals vs ++ d :: r) = (vs, d :: r) := by
  rw [splitVals_vals_append, splitVals_cons_nonval hd]; simp

theorem splitVals_spec (l : List Admin) : l = vals (splitVals l).1 ++ (splitVals l).2 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases h : a.val? with
    | none => rw [splitVals_cons_nonval h]; rfl
    | some v =>
      rw [splitVals_cons_val h]
      simp only [vals_cons, List.cons_append]
      rw [← Admin.eq_toAdmin_of_val? h, ← ih]

theorem splitVals_head {l : List Admin} {d : Admin} {r : List Admin}
    (h : (splitVals l).2 = d :: r) : d.val? = none := by
  induction l with
  | nil => simp [splitVals] at h
  | cons a as ih =>
    cases ha : a.val? with
    | none =>
      rw [splitVals_cons_nonval ha] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ha
    | some v =>
      rw [splitVals_cons_val ha] at h
      exact ih h

theorem splitVals_eq {l : List Admin} {vs : List Val} {d : Admin} {r : List Admin}
    (h : splitVals l = (vs, d :: r)) : l = vals vs ++ d :: r ∧ d.val? = none := by
  refine ⟨?_, splitVals_head (l := l) (by rw [h])⟩
  have := splitVals_spec l
  rw [h] at this
  exact this

theorem vals_injective {xs ys : List Val} (h : vals xs = vals ys) : xs = ys := by
  have := congrArg splitVals h
  rw [splitVals_vals, splitVals_vals] at this
  simpa using this

/-- Uniqueness of the split of a list into a value prefix and a non-value head. -/
theorem vals_append_cons_inj {vs ws : List Val} {d e : Admin} {r t : List Admin}
    (hd : d.val? = none) (he : e.val? = none) (h : vals vs ++ d :: r = vals ws ++ e :: t) :
    vs = ws ∧ d = e ∧ r = t := by
  have := congrArg splitVals h
  rw [splitVals_vals_cons hd, splitVals_vals_cons he] at this
  simp only [Prod.mk.injEq, List.cons.injEq] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- The value prefix and rest of a context's outermost layer, extended. -/
def Ctx.wrap (vs : List Val) (rest : List Admin) : Ctx → Ctx
  | .top pre r => .top (vs ++ pre) (r ++ rest)
  | .label pre n cont E r => .label (vs ++ pre) n cont E (r ++ rest)
  | .handler pre n cs E r => .handler (vs ++ pre) n cs E (r ++ rest)
  | .frame pre n f E r => .frame (vs ++ pre) n f E (r ++ rest)

theorem Ctx.fill_wrap (E : Ctx) (vs : List Val) (rest xs : List Admin) :
    (E.wrap vs rest).fill xs = vals vs ++ E.fill xs ++ rest := by
  cases E <;> simp [Ctx.wrap, Ctx.fill]

/-- The top-level host-call redex search of `decompose?`. -/
def topRedex (s : Store H) (vs : List Val) (rest : List Admin) :
    Option (Ctx × Nat × H × List Val) :=
  match vs.getLast? with
  | some (.ref (.func a)) =>
    match hostArity? s a with
    | some (h, n) =>
      let pre := vs.dropLast
      if n ≤ pre.length then
        some (.top (pre.take (pre.length - n)) rest, a, h, pre.drop (pre.length - n))
      else none
    | none => none
  | _ => none

/-- One layer of `decompose?`, given the split. -/
def decompHead (s : Store H) (vs : List Val) (d : Admin) (rest : List Admin) :
    Option (Ctx × Nat × H × List Val) :=
  match d with
  | .label n cont body =>
    (decompose? s body).map fun (E, a, h, args) => (.label vs n cont E rest, a, h, args)
  | .handler n cs body =>
    (decompose? s body).map fun (E, a, h, args) => (.handler vs n cs E rest, a, h, args)
  | .frame n f body =>
    (decompose? s body).map fun (E, a, h, args) => (.frame vs n f E rest, a, h, args)
  | c => if c.isCallRef then topRedex s vs rest else none

theorem decompose?_of_split {s : Store H} {code : List Admin} {vs : List Val} {d : Admin}
    {rest : List Admin} (hs : splitVals code = (vs, d :: rest)) :
    decompose? s code = decompHead s vs d rest := by
  rw [decompose?]
  split <;> rename_i heq <;> rw [hs] at heq <;>
    simp only [Prod.mk.injEq, List.cons.injEq, reduceCtorEq, and_false] at heq <;>
    obtain ⟨rfl, rfl, rfl⟩ := heq <;>
    first | rfl | (cases d <;> first | rfl | simp_all)

theorem decompose?_of_split_nil {s : Store H} {code : List Admin} {vs : List Val}
    (hs : splitVals code = (vs, [])) : decompose? s code = none := by
  rw [decompose?]
  split <;> simp_all

theorem hostArity?_eq_some {s : Store H} {a : Nat} {h : H} {n : Nat}
    (hh : hostArity? s a = some (h, n)) :
    ∃ fi ps rs, s.funcs[a]? = some fi ∧ fi.code = .host h ∧ Expand fi.type (.func ps rs) ∧
      n = ps.length := by
  unfold hostArity? at hh
  split at hh
  · rename_i fi hfi
    split at hh
    · rename_i h' ps' rs' hc hft
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      unfold DefType.funcType? at hft
      split at hft
      · rename_i ps rs hex
        simp only [Option.some.injEq, Prod.mk.injEq] at hft
        obtain ⟨rfl, rfl⟩ := hft
        exact ⟨fi, ps, rs, hfi, hc, Expand.iff.mpr hex, rfl⟩
      · cases hft
    · cases hh
  · cases hh

theorem hostArity?_of {s : Store H} {a : Nat} {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hc : fi.code = .host h) (he : Expand fi.type (.func ps rs)) :
    hostArity? s a = some (h, ps.length) := by
  have hft : fi.type.funcType? = some (ps.toList, rs.toList) := by
    unfold DefType.funcType?; rw [Expand.iff.mp he]
  unfold hostArity?
  rw [hf]
  simp only [hc, hft]
  rfl

theorem topRedex_sound {s : Store H} {vs : List Val} {rest : List Admin} {E : Ctx} {a : Nat}
    {h : H} {args : List Val} (ht : topRedex s vs rest = some (E, a, h, args)) :
    ∃ fi ps rs, s.funcs[a]? = some fi ∧ fi.code = .host h ∧ Expand fi.type (.func ps rs) ∧
      args.length = ps.length ∧
      ∀ yy, vals vs ++ yy :: rest = E.fill (vals args ++ [.ref (.func a), yy]) := by
  unfold topRedex at ht
  split at ht
  · rename_i a' hl
    split at ht
    · rename_i h' n hh
      dsimp only at ht
      split at ht
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
        obtain ⟨fi, ps, rs, hf, hc, he, rfl⟩ := hostArity?_eq_some hh
        refine ⟨fi, ps, rs, hf, hc, he, ?_, ?_⟩
        · simp only [List.length_drop]; omega
        · intro yy
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
          simp only [List.dropLast_concat, Ctx.fill, vals_append, List.append_assoc]
          rw [← List.append_assoc (vals (List.take _ ys)), ← vals_append, List.take_append_drop]
          rfl
      · cases ht
    · cases ht
  · cases ht

/-- `decompose?` on the result of `splitVals`. -/
def decompTop (s : Store H) : List Val × List Admin → Option (Ctx × Nat × H × List Val)
  | (vs, d :: rest) => decompHead s vs d rest
  | (_, []) => none

theorem decompose?_eq (s : Store H) (code : List Admin) :
    decompose? s code = decompTop s (splitVals code) := by
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · exact decompose?_of_split_nil hsp
  · exact decompose?_of_split hsp

theorem decompHead_of_IsCallRef {s : Store H} {vs : List Val} {d : Admin} {rest : List Admin}
    (hd : d.IsCallRef) : decompHead s vs d rest = topRedex s vs rest := by
  have h' := Admin.isCallRef_of_IsCallRef hd
  cases d <;> first | exact (hd : False).elim | exact ite_eq_left h'

theorem topRedex_some {s : Store H} {vs : List Val} {rest : List Admin} {x}
    (ht : topRedex s vs rest = some x) :
    ∃ a h n, vs.getLast? = some (.ref (.func a)) ∧ hostArity? s a = some (h, n) := by
  unfold topRedex at ht
  split at ht
  · rename_i a' hl
    split at ht
    · rename_i h' n hh
      exact ⟨a', h', n, hl, hh⟩
    · cases ht
  · cases ht

/-- Soundness of `decompose?`. (Strengthened from the skeleton: the callee address
is returned, and its type expands to a function type whose arity is the number
of arguments; `step_iff`, `callout_no_internal` and `resume_progress` need it.) -/
theorem decompose?_sound {s : Store H} {code : List Admin} {E : Ctx} {a : Nat} {h : H}
    {args : List Val} (hd : decompose? s code = some (E, a, h, args)) :
    ∃ fi yy ps rs, s.funcs[a]? = some fi ∧ fi.code = .host h ∧ yy.IsCallRef ∧
      Expand fi.type (.func ps rs) ∧ args.length = ps.length ∧
      code = E.fill (vals args ++ [.ref (.func a), yy]) := by
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rw [decompose?_of_split_nil hsp] at hd; cases hd
  · obtain ⟨hcode, _⟩ := splitVals_eq hsp
    have hsz : sizeOf (d :: rest) ≤ sizeOf code := by
      have := splitVals_snd_sizeOf code; rw [hsp] at this; exact this
    rw [decompose?_of_split hsp] at hd
    cases d with
    | label n cont body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E', a', h', args'⟩, hb, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      have : sizeOf body < sizeOf code := by
        simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec] at hsz; omega
      obtain ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, hbody⟩ := decompose?_sound hb
      exact ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, by rw [hcode, hbody]; simp [Ctx.fill]⟩
    | handler n cs body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E', a', h', args'⟩, hb, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      have : sizeOf body < sizeOf code := by
        simp only [List.cons.sizeOf_spec, Admin.handler.sizeOf_spec] at hsz; omega
      obtain ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, hbody⟩ := decompose?_sound hb
      exact ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, by rw [hcode, hbody]; simp [Ctx.fill]⟩
    | frame n f body =>
      simp only [decompHead, Option.map_eq_some_iff] at hd
      obtain ⟨⟨E', a', h', args'⟩, hb, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      have : sizeOf body < sizeOf code := by
        simp only [List.cons.sizeOf_spec, Admin.frame.sizeOf_spec] at hsz; omega
      obtain ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, hbody⟩ := decompose?_sound hb
      exact ⟨fi, yy, ps, rs, h1, h2, h3, h4, h5, by rw [hcode, hbody]; simp [Ctx.fill]⟩
    | _ =>
      simp only [decompHead] at hd
      split at hd
      · rename_i hc
        obtain ⟨fi, ps, rs, h1, h2, h3, h4, hfill⟩ := topRedex_sound hd
        exact ⟨fi, _, ps, rs, h1, h2, Admin.IsCallRef_of_isCallRef hc, h3, h4,
          by rw [hcode]; exact hfill _⟩
      · cases hd
termination_by sizeOf code

end Silmaril.Wasm.SingleThreaded
