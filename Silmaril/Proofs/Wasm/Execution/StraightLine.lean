module

public import Silmaril.Wasm.Execution.StraightLine.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Foundations.InfiniteTrace

/-!
# Proofs: every run of a straight-line numeric function, at any profile

The invocation of a straight-line numeric function (`StraightLine.Fn`) goes through the stages

* `invoke s a args` (`$invoke`), then by `call_ref` the frame
  `FRAME_1{F} (LABEL_1{} (local.get 0 … local.get (k-1) op))`;
* `j` `local.get`s later, the label holds `vals (args.take j) ++ (local.get j … op)`;
* the numeric step: the label holds `is'`, any result of `NumericStep P (vals args ++ [op])`;
* the label and then the frame are left (`label-vals`/`trap-label`, `frame-vals`/`trap-frame`),
  ending at `⟨s, {}, is'⟩`.

`Inv` is that list of stages, with a rank that every step decreases (`inv_step`). Every step from
a stage is inverted through the head decomposition `Det.Step.decomp`, which holds at every
profile: only the numeric step depends on `P`, and its results are kept as the relation
`NumericStep P`. Hence every normal form is a final stage (`nf`), every result of the numeric
step is reached (`reaches`), and no run is infinite (`not_diverges`, `extends`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.StraightLine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core.StraightLine

variable {H : Type} {P : Profile}

/-! ## Inversion of steps -/

/-- A step of a one-instruction code (not a value, not a trap) is a head step. -/
theorem step_single {s : Store H} {f : Frame} {e : Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, [e]⟩ c) (hv : e.val? = none) (ht : e ≠ .trap) :
    Head P s f [] e c := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e', rest, c₀, hf, -, hh, rfl⟩ := fnv_headDec hd
    simp only [fnv_cons_of_none hv, Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨h1, rfl, rfl⟩ := hf
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h1.symm
    rcases c₀ with ⟨s₀, f₀, code₀⟩
    simpa [vals] using hh
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb
    · simp only [fnv_cons_of_none hv, Prod.mk.injEq, List.cons.injEq] at hf
      exact absurd hf.2.1 ht
    · simp only [fnv_cons_of_none hv, Prod.mk.injEq] at hf
      simp at hf

/-- A step of a code whose first non-value `e` is of a family other than control is the
family's step on `e` and some of the values before it. -/
theorem step_seq {s : Store H} {f : Frame} {V : List Val} {e : Admin} {rest : List Admin}
    {c : Config H} (h : Step P noHost ⟨s, f, vals V ++ e :: rest⟩ c) (hv : e.val? = none)
    (hk : famOf e ≠ .control) :
    ∃ vs args c₀, V = vs ++ args ∧ FamRel P (famOf e) s f (vals args ++ [e]) c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  have hf0 : fnv (vals V ++ e :: rest) = (V, e :: rest) := by
    simp [fnv_cons_of_none hv]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e', rest', c₀, hf, -, hh, rfl⟩ := fnv_headDec hd
    simp only at hf
    rw [hf0] at hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    exact ⟨vs, args, c₀, rfl, hh.fam_inv hk, rfl⟩
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb
    · simp only at hf
      rw [hf0] at hf
      simp only [Prod.mk.injEq, List.cons.injEq] at hf
      obtain ⟨-, rfl, -⟩ := hf
      exact absurd rfl hk
    · simp only at hf
      rw [hf0] at hf
      simp only [Prod.mk.injEq, List.cons.injEq] at hf
      obtain ⟨-, rfl, -⟩ := hf
      exact absurd rfl hk

/-- The codes that a frame or label cannot be left from by a head rule other than its context
rule, `*-vals` or `trap-*`: their first non-value is a branch, a `RETURN`, a
`RETURN_CALL_REF` or `THROW_REF`. -/
def Escapes (X : List Admin) : Prop :=
  ∃ W e rest, fnv X = (W, e :: rest) ∧ (Blocked e ∨ e = .plain .throwRef)

theorem escapes_of {X : List Admin} {W : List Val} {e : Admin} {rest : List Admin}
    (hX : X = vals W ++ e :: rest) (he : e.val? = none)
    (h : Blocked e ∨ e = .plain .throwRef) : Escapes X :=
  ⟨W, e, rest, by subst hX; simp [fnv_cons_of_none he], h⟩

/-- The head steps of a frame. -/
theorem head_frame {s : Store H} {f F : Frame} {m : Nat} {X : List Admin} {c : Config H}
    (h : Head P s f [] (.frame m F X) c) :
    (∃ s' F' X', Step P noHost ⟨s, F, X⟩ ⟨s', F', X'⟩ ∧ c = ⟨s', f, [.frame m F' X']⟩) ∨
    (∃ vs, X = vals vs ∧ vs.length = m ∧ c = ⟨s, f, vals vs⟩) ∨
    (X = [.trap] ∧ c = ⟨s, f, [.trap]⟩) ∨ Escapes X := by
  cases h with
  | ctxtFrame h => exact .inl ⟨_, _, _, h, rfl⟩
  | frameVals hb hn => exact .inr (.inl ⟨_, hb, hn, rfl⟩)
  | trapFrame => exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  | returnFrame hb hn =>
    rename_i vs' vs rest
    exact .inr (.inr (.inr (escapes_of (W := vs' ++ vs) (rest := rest) (by rw [hb]; simp) rfl
      (.inl (.inr (.inl rfl))))))
  | returnCallRefFrameNull hb hc =>
    rename_i vs c rest
    exact .inr (.inr (.inr (escapes_of (W := vs ++ [.ref .null]) (rest := rest)
      (by rw [hb]; simp [Val.toAdmin]) (IsReturnCallRef.val_none hc) (.inl (.inr (.inr hc))))))
  | returnCallRefFrameAddr hb hc hf he hn =>
    rename_i vs' vs a c rest fn ps rs
    exact .inr (.inr (.inr (escapes_of (W := vs' ++ vs ++ [.ref (.func a)]) (rest := rest)
      (by rw [hb]; simp [Val.toAdmin]) (IsReturnCallRef.val_none hc) (.inl (.inr (.inr hc))))))
  | throwRefFrame =>
    rename_i a
    exact .inr (.inr (.inr (escapes_of (W := [.ref (.exn a)]) (rest := [])
      (by simp [vals, Val.toAdmin]) rfl (.inr rfl))))
  | parametric h => exact absurd (famOf_of_shape (ParametricStep.shape h)).2 (by simp [famOf])
  | numeric h => exact absurd (famOf_of_shape (NumericStep.shape h)).2 (by simp [famOf])
  | vector h => exact absurd (famOf_of_shape (VectorStep.shape h)).2 (by simp [famOf])
  | «variable» h => exact absurd (famOf_of_shape (VariableStep.shape h)).2 (by simp [famOf])
  | table h => exact absurd (famOf_of_shape (TableStep.shape h)).2 (by simp [famOf])
  | memory h => exact absurd (famOf_of_shape (MemoryStep.shape h)).2 (by simp [famOf])
  | reference h => exact absurd (famOf_of_shape (RefStep.shape h)).2 (by simp [famOf])
  | aggregate h => exact absurd (famOf_of_shape (AggregateStep.shape h)).2 (by simp [famOf])
  | callRefFunc ha hc => exact hc.elim

/-- The head steps of a label. -/
theorem head_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {L : List Admin}
    {c : Config H} (h : Head P s f [] (.label n cont L) c) :
    (∃ s' f' L', Step P noHost ⟨s, f, L⟩ ⟨s', f', L'⟩ ∧ c = ⟨s', f', [.label n cont L']⟩) ∨
    (∃ vs, L = vals vs ∧ c = ⟨s, f, vals vs⟩) ∨
    (L = [.trap] ∧ c = ⟨s, f, [.trap]⟩) ∨ Escapes L := by
  cases h with
  | ctxtLabel h => exact .inl ⟨_, _, _, h, rfl⟩
  | labelVals hb => exact .inr (.inl ⟨_, hb, rfl⟩)
  | trapLabel => exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  | brLabelZero hb hl hn =>
    rename_i vs' vs l rest
    exact .inr (.inr (.inr (escapes_of (W := vs' ++ vs) (rest := rest) (by rw [hb]; simp) rfl
      (.inl (.inl ⟨l, rfl⟩)))))
  | brLabelSucc hb hl =>
    rename_i vs l rest
    exact .inr (.inr (.inr (escapes_of (W := vs) (rest := rest) (by rw [hb]; simp) rfl
      (.inl (.inl ⟨l, rfl⟩)))))
  | returnLabel hb =>
    rename_i vs rest
    exact .inr (.inr (.inr (escapes_of (W := vs) (rest := rest) (by rw [hb]; simp) rfl
      (.inl (.inr (.inl rfl))))))
  | returnCallRefLabel hb hc =>
    rename_i vs c rest
    exact .inr (.inr (.inr (escapes_of (W := vs) (rest := rest) (by rw [hb]; simp)
      (IsReturnCallRef.val_none hc) (.inl (.inr (.inr hc))))))
  | throwRefLabel =>
    rename_i a
    exact .inr (.inr (.inr (escapes_of (W := [.ref (.exn a)]) (rest := [])
      (by simp [vals, Val.toAdmin]) rfl (.inr rfl))))
  | parametric h => exact absurd (famOf_of_shape (ParametricStep.shape h)).2 (by simp [famOf])
  | numeric h => exact absurd (famOf_of_shape (NumericStep.shape h)).2 (by simp [famOf])
  | vector h => exact absurd (famOf_of_shape (VectorStep.shape h)).2 (by simp [famOf])
  | «variable» h => exact absurd (famOf_of_shape (VariableStep.shape h)).2 (by simp [famOf])
  | table h => exact absurd (famOf_of_shape (TableStep.shape h)).2 (by simp [famOf])
  | memory h => exact absurd (famOf_of_shape (MemoryStep.shape h)).2 (by simp [famOf])
  | reference h => exact absurd (famOf_of_shape (RefStep.shape h)).2 (by simp [famOf])
  | aggregate h => exact absurd (famOf_of_shape (AggregateStep.shape h)).2 (by simp [famOf])
  | callRefFunc ha hc => exact hc.elim

/-- A code whose first non-value is not blocked and not `THROW_REF` does not escape. -/
theorem not_escapes {X : List Admin} {W : List Val} {e : Admin} {rest : List Admin}
    (hX : fnv X = (W, e :: rest)) (hb : ¬ Blocked e) (ht : e ≠ .plain .throwRef) :
    ¬ Escapes X := by
  rintro ⟨W', e', rest', hX', h⟩
  rw [hX] at hX'
  simp only [Prod.mk.injEq, List.cons.injEq] at hX'
  obtain ⟨-, rfl, -⟩ := hX'
  exact h.elim hb ht

theorem not_escapes_vals {vs : List Val} : ¬ Escapes (vals vs) := by
  rintro ⟨W, e, rest, h, -⟩
  simp at h

theorem not_escapes_trap : ¬ Escapes [.trap] :=
  not_escapes (W := []) (rest := []) (fnv_cons_of_none rfl []) (by
    rintro (⟨l, h⟩ | h | h) <;> cases h) (by simp)

theorem not_escapes_label {n : Nat} {cont : List Instr} {L : List Admin} :
    ¬ Escapes [.label n cont L] :=
  not_escapes (W := []) (rest := []) (fnv_cons_of_none rfl []) (by
    rintro (⟨l, h⟩ | h | h) <;> cases h) (by simp)

/-! ## Families -/

/-- `local.get` reads a local and nothing else. -/
theorem variableStep_localGet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx}
    {c : Config H} (h : VariableStep ⟨s, f, vals args ++ [.plain (.localGet x)]⟩ c) :
    args = [] ∧ ∃ v, f.local? x = some (some v) ∧ c = ⟨s, f, [v.toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.localGet x)]⟩ : Config H) = c₀ at h
  cases h with
  | localGet hv =>
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, hl⟩ := hc
    have := congrArg List.length hl
    simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at this
    obtain rfl : args = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, Admin.plain.injEq,
      Instr.localGet.injEq, and_true] at hl
    subst hl
    exact ⟨rfl, _, hv, rfl⟩
  | _ =>
    simp only [Config.mk.injEq] at hc
    obtain ⟨-, -, hl⟩ := hc
    have := congrArg List.getLast? hl
    simp at this

/-- `numArity` is the arity of the left-hand sides of `NumericStep`. -/
theorem numericStep_arity {args : List Val} {op : Instr} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain op]) is') : numArity op = some args.length := by
  generalize hl : vals args ++ [.plain op] = l at h
  cases h <;>
  · have h1 := congrArg List.length hl
    have h2 := congrArg List.getLast? hl
    simp at h1 h2
    subst h2
    simp only [numArity, Option.some.injEq]
    omega

/-- A scalar numeric instruction is in the numeric family. -/
theorem famOf_of_numArity {op : Instr} {k : Nat} (h : numArity op = some k) :
    famOf (.plain op) = .numeric := by
  cases op <;> simp_all [numArity, famOf]

theorem val?_of_numArity {op : Instr} {k : Nat} (h : numArity op = some k) :
    (Admin.plain op).val? = none := by
  cases op <;> simp_all [numArity, Admin.val?]

/-- The result of a numeric step is one value or a trap. -/
theorem numericStep_result {l is' : List Admin} (h : NumericStep P l is') :
    (∃ v : Val, is' = [v.toAdmin]) ∨ is' = [.trap] := by
  cases h with
  | intUnOp => exact .inl ⟨.num ⟨.int _, _⟩, rfl⟩
  | floatUnOp => exact .inl ⟨.num ⟨.float _, _⟩, rfl⟩
  | intBinOp => exact .inl ⟨.num ⟨.int _, _⟩, rfl⟩
  | intBinOpTrap => exact .inr rfl
  | floatBinOp => exact .inl ⟨.num ⟨.float _, _⟩, rfl⟩
  | intTestOp => exact .inl ⟨.i32 _, rfl⟩
  | intRelOp => exact .inl ⟨.i32 _, rfl⟩
  | floatRelOp => exact .inl ⟨.i32 _, rfl⟩
  | convert => exact .inl ⟨_, rfl⟩
  | convertTrap => exact .inr rfl

/-- The result of a numeric step does not step. -/
theorem not_step_result {l is' : List Admin} (h : NumericStep P l is') {s : Store H}
    {f : Frame} {c : Config H} : ¬ Step P noHost ⟨s, f, is'⟩ c := by
  rcases numericStep_result h with ⟨v, rfl⟩ | rfl
  · exact fun hs => not_step_vals (W := [v]) hs
  · exact not_step_trap

/-! ## Through a frame and a label -/

theorem vals_ne_label {vs : List Val} {n : Nat} {cont : List Instr} {L : List Admin} :
    vals vs ≠ [.label n cont L] := by
  intro h
  have := congrArg fnv h
  simp [fnv_cons_of_none (a := .label n cont L) rfl] at this

/-- A step inside `FRAME_m{F} (LABEL_n{cont} L)` whose first non-value is of a family other than
control is a step of `L`. -/
theorem step_frame_label {s : Store H} {f F : Frame} {m n : Nat} {cont : List Instr}
    {L : List Admin} {W : List Val} {e : Admin} {rest : List Admin} {c : Config H}
    (hL : fnv L = (W, e :: rest)) (hk : famOf e ≠ .control)
    (h : Step P noHost ⟨s, f, [.frame m F [.label n cont L]]⟩ c) :
    ∃ s' F' L', Step P noHost ⟨s, F, L⟩ ⟨s', F', L'⟩ ∧
      c = ⟨s', f, [.frame m F' [.label n cont L']]⟩ := by
  have hb : ¬ Blocked e := not_blocked_of_fam rfl hk
  have ht : e ≠ .plain .throwRef := by rintro rfl; exact hk rfl
  rcases head_frame (step_single h rfl (by simp)) with ⟨s', F', X', hX, rfl⟩ | ⟨vs, hv, -⟩ |
      ⟨hv, -⟩ | hX
  · rcases head_label (step_single hX rfl (by simp)) with ⟨s'', f'', L', hL', hc⟩ | ⟨vs, hv, -⟩ |
        ⟨hv, -⟩ | hE
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact ⟨_, _, _, hL', rfl⟩
    · subst hv; simp at hL
    · subst hv
      simp only [fnv_trap_cons, Prod.mk.injEq, List.cons.injEq] at hL
      obtain ⟨-, rfl, -⟩ := hL
      exact absurd rfl hk
    · exact absurd hE (not_escapes hL hb ht)
  · exact absurd hv.symm vals_ne_label
  · simp at hv
  · exact absurd hX not_escapes_label

/-! ## The stages of a run -/

section Run

variable {s : Store H} {a : Nat} {fi : FuncInst H} {args : List Val} {op : Instr} {code : Func}
  {ps rs : Ty (.list .val)}

/-- The data of a straight-line numeric function, as the steps use it. -/
structure Data (s : Store H) (a : Nat) (args : List Val) (op : Instr) (fi : FuncInst H)
    (code : Func) (ps rs : Ty (.list .val)) : Prop where
  hf : s.funcs[a]? = some fi
  hcode : fi.code = .wasm code
  hloc : code.locals = []
  hbody : Body args.length op code.body
  he : Expand fi.type (.func ps rs)
  hps : ps.length = args.length
  hrs : rs.length = 1
  har : numArity op = some args.length

/-- The frame of the call. -/
abbrev frm (fi : FuncInst H) (args : List Val) : Frame := Frame.forCall fi.module args []

/-- The label's code after `j` `local.get`s. -/
def lbody (code : Func) (args : List Val) (j : Nat) : List Admin :=
  vals (args.take j) ++ expression (code.body.drop j)

/-- The stages of a run, with a rank that every step decreases. -/
inductive Inv (P : Profile) (s : Store H) (a : Nat) (args : List Val) (op : Instr)
    (F : Frame) (code : Func) : Config H → Nat → Prop
  | start : Inv P s a args op F code (invoke s a args) (args.length + 4)
  | get {j : Nat} (hj : j ≤ args.length) :
      Inv P s a args op F code ⟨s, {}, [.frame 1 F [.label 1 [] (lbody code args j)]]⟩
        (args.length - j + 3)
  | num {is' : List Admin} (h : NumericStep P (vals args ++ [.plain op]) is') :
      Inv P s a args op F code ⟨s, {}, [.frame 1 F [.label 1 [] is']]⟩ 2
  | lab {is' : List Admin} (h : NumericStep P (vals args ++ [.plain op]) is') :
      Inv P s a args op F code ⟨s, {}, [.frame 1 F is']⟩ 1
  | done {is' : List Admin} (h : NumericStep P (vals args ++ [.plain op]) is') :
      Inv P s a args op F code ⟨s, {}, is'⟩ 0

theorem invoke_eq (D : Data s a args op fi code ps rs) :
    invoke s a args = ⟨s, {}, vals (args ++ [.ref (.func a)]) ++ [.callRefType fi.type]⟩ := by
  simp [invoke, D.hf, Val.toAdmin]

theorem lbody_zero : lbody code args 0 = expression code.body := by simp [lbody]

theorem lbody_len (D : Data s a args op fi code ps rs) :
    lbody code args args.length = vals args ++ [.plain op] := by
  simp [lbody, D.hbody.1, expression]

theorem body_drop (D : Data s a args op fi code ps rs) {j : Nat} (hj : j < args.length) :
    ∃ x : LocalIdx, x.toNat = j ∧
      code.body.drop j = .localGet x :: code.body.drop (j + 1) := by
  obtain ⟨x, hx, hxj⟩ := D.hbody.2 j hj
  refine ⟨x, hxj, ?_⟩
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hx
  rw [List.drop_eq_getElem_cons hlt, hget]

theorem body_drop_ne (D : Data s a args op fi code ps rs) {j : Nat} (hj : j ≤ args.length) :
    code.body.drop j ≠ [] := by
  intro h
  have h1 := congrArg List.length D.hbody.1
  have h2 := congrArg List.length h
  simp only [List.length_drop, List.length_cons, List.length_nil] at h1 h2
  omega

theorem local_frm {j : Nat} (hj : j < args.length) {x : LocalIdx} (hx : x.toNat = j) :
    (frm fi args).local? x = some (some args[j]) := by
  simp [Frame.local?, Frame.forCall, hx, hj]

theorem lbody_succ {j : Nat} (hj : j < args.length) :
    vals (args.take j ++ [args[j]]) ++ expression (code.body.drop (j + 1)) =
      lbody code args (j + 1) := by
  rw [lbody, List.take_add_one, List.getElem?_eq_getElem hj]
  rfl

/-- The step from `$invoke`: `call_ref` of the function. -/
theorem step_start (D : Data s a args op fi code ps rs) {c : Config H}
    (h : Step P noHost (invoke s a args) c) :
    c = ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] (lbody code args 0)]]⟩ := by
  rw [invoke_eq D] at h
  have hf0 : fnv (vals (args ++ [.ref (.func a)]) ++ [.callRefType fi.type]) =
      (args ++ [.ref (.func a)], [.callRefType fi.type]) := by
    simp [fnv_cons_of_none (a := .callRefType fi.type) rfl]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args', e, rest, c₀, hf, -, hh, rfl⟩ := fnv_headDec hd
    simp only at hf
    rw [hf0] at hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨hva, rfl, rfl⟩ := hf
    cases hh with
    | callRefNull hc =>
      have := (append_singleton_inj.mp hva).2
      simp at this
    | callRefFunc ha hc hf he hn hcode =>
      rename_i vs' a' fi' ps' rs' code'
      subst ha
      rw [← List.append_assoc] at hva
      obtain ⟨hargs, hr⟩ := append_singleton_inj.mp hva
      simp only [Val.ref.injEq, Ref.func.injEq] at hr
      subst hr
      rw [D.hf] at hf
      cases hf
      rw [D.hcode] at hcode
      cases hcode
      have hpr := Expand.det he D.he
      injection hpr with hp hr'
      subst hp hr'
      have hl := congrArg List.length hargs
      simp only [List.length_append] at hl
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by have := D.hps; omega)
      simp only [List.nil_append] at hargs
      subst hargs
      simp [lbody_zero, D.hloc, D.hrs, frm]
    | parametric hp => exact absurd (famOf_of_shape (ParametricStep.shape hp)).2 (by simp [famOf])
    | numeric hp => exact absurd (famOf_of_shape (NumericStep.shape hp)).2 (by simp [famOf])
    | vector hp => exact absurd (famOf_of_shape (VectorStep.shape hp)).2 (by simp [famOf])
    | «variable» hp => exact absurd (famOf_of_shape (VariableStep.shape hp)).2 (by simp [famOf])
    | table hp => exact absurd (famOf_of_shape (TableStep.shape hp)).2 (by simp [famOf])
    | memory hp => exact absurd (famOf_of_shape (MemoryStep.shape hp)).2 (by simp [famOf])
    | reference hp => exact absurd (famOf_of_shape (RefStep.shape hp)).2 (by simp [famOf])
    | aggregate hp => exact absurd (famOf_of_shape (AggregateStep.shape hp)).2 (by simp [famOf])
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb <;> simp only at hf <;>
      rw [hf0] at hf <;> simp at hf

/-- A step after `j < k` `local.get`s: the next `local.get`. -/
theorem step_get_lt (D : Data s a args op fi code ps rs) {f : Frame} {j : Nat}
    (hj : j < args.length) {c : Config H}
    (h : Step P noHost ⟨s, f, [.frame 1 (frm fi args) [.label 1 [] (lbody code args j)]]⟩ c) :
    c = ⟨s, f, [.frame 1 (frm fi args) [.label 1 [] (lbody code args (j + 1))]]⟩ := by
  obtain ⟨x, hx, hd⟩ := body_drop D hj
  have hL : lbody code args j =
      vals (args.take j) ++ .plain (.localGet x) :: expression (code.body.drop (j + 1)) := by
    simp [lbody, hd, expression]
  rw [hL] at h
  obtain ⟨s', F', L', hs, rfl⟩ := step_frame_label (W := args.take j) (e := .plain (.localGet x))
    (rest := expression (code.body.drop (j + 1))) (by rw [fnv_vals_append, fnv_cons_of_none rfl]; simp) (by simp [famOf]) h
  obtain ⟨vs, args', c₀, hv, hfam, hc⟩ := step_seq hs rfl (by simp [famOf])
  obtain ⟨rfl, v, hloc, rfl⟩ := variableStep_localGet (show VariableStep _ c₀ from hfam)
  simp only [Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  rw [local_frm hj hx] at hloc
  simp only [Option.some.injEq] at hloc
  subst hloc
  simp only [List.append_nil] at hv
  subst hv
  rw [← lbody_succ hj, vals_append]
  rfl

/-- The step after all `local.get`s: the numeric step. -/
theorem step_get_len (D : Data s a args op fi code ps rs) {f : Frame} {c : Config H}
    (h : Step P noHost
      ⟨s, f, [.frame 1 (frm fi args) [.label 1 [] (lbody code args args.length)]]⟩ c) :
    ∃ is', NumericStep P (vals args ++ [.plain op]) is' ∧
      c = ⟨s, f, [.frame 1 (frm fi args) [.label 1 [] is']]⟩ := by
  rw [lbody_len D] at h
  have hk := famOf_of_numArity D.har
  obtain ⟨s', F', L', hs, rfl⟩ := step_frame_label (W := args) (e := .plain op) (rest := [])
    (by rw [fnv_vals_append, fnv_cons_of_none (val?_of_numArity D.har)]; simp) (by rw [hk]; simp) h
  obtain ⟨vs, args', c₀, hv, hfam, hc⟩ := step_seq hs (val?_of_numArity D.har) (by rw [hk]; simp)
  rw [hk] at hfam
  obtain ⟨is', hn, rfl⟩ := hfam
  have ha := numericStep_arity hn
  rw [D.har, Option.some.injEq] at ha
  have hl := congrArg List.length hv
  simp only [List.length_append] at hl
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.nil_append] at hv
  subst hv
  simp only [Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨is', hn, by simp⟩

/-- After the numeric step: leaving the label. -/
theorem step_num {f F : Frame} {is' : List Admin}
    (hn : NumericStep P (vals args ++ [.plain op]) is') {c : Config H}
    (h : Step P noHost ⟨s, f, [.frame 1 F [.label 1 [] is']]⟩ c) :
    c = ⟨s, f, [.frame 1 F is']⟩ := by
  rcases head_frame (step_single h rfl (by simp)) with ⟨s', F', X', hX, rfl⟩ | ⟨vs, hv, -⟩ |
      ⟨hv, -⟩ | hX
  · rcases head_label (step_single hX rfl (by simp)) with ⟨s'', f'', L', hL', -⟩ | ⟨vs, hv, hc⟩ |
        ⟨hv, hc⟩ | hE
    · exact absurd hL' (not_step_result hn)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [hv]
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [hv]
    · rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
      · exact absurd hE (not_escapes_vals (vs := [v]))
      · exact absurd hE not_escapes_trap
  · exact absurd hv.symm vals_ne_label
  · simp at hv
  · exact absurd hX not_escapes_label

/-- After leaving the label: leaving the frame. -/
theorem step_lab {f F : Frame} {is' : List Admin}
    (hn : NumericStep P (vals args ++ [.plain op]) is') {c : Config H}
    (h : Step P noHost ⟨s, f, [.frame 1 F is']⟩ c) : c = ⟨s, f, is'⟩ := by
  rcases head_frame (step_single h rfl (by simp)) with ⟨s', F', X', hX, -⟩ | ⟨vs, hv, -, hc⟩ |
      ⟨hv, hc⟩ | hX
  · exact absurd hX (not_step_result hn)
  · rw [hc, hv]
  · rw [hc, hv]
  · rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
    · exact absurd hX (not_escapes_vals (vs := [v]))
    · exact absurd hX not_escapes_trap

/-- Every step from a stage goes to a stage of smaller rank. -/
theorem inv_step (D : Data s a args op fi code ps rs) {c c' : Config H} {r : Nat}
    (hi : Inv P s a args op (frm fi args) code c r) (h : Step P noHost c c') :
    ∃ r', Inv P s a args op (frm fi args) code c' r' ∧ r' < r := by
  cases hi with
  | start =>
    rw [step_start D h]
    exact ⟨_, .get (Nat.zero_le _), by omega⟩
  | get hj =>
    rename_i j
    rcases Nat.lt_or_ge j args.length with hlt | hge
    · rw [step_get_lt D hlt h]
      exact ⟨_, .get hlt, by omega⟩
    · obtain rfl : j = args.length := by omega
      obtain ⟨is', hn, rfl⟩ := step_get_len D h
      exact ⟨_, .num hn, by omega⟩
  | num hn =>
    rw [step_num hn h]
    exact ⟨_, .lab hn, by omega⟩
  | lab hn =>
    rw [step_lab hn h]
    exact ⟨_, .done hn, by omega⟩
  | done hn => exact absurd h (not_step_result hn)

/-! ## Progress -/

theorem step_start_ex (D : Data s a args op fi code ps rs) :
    Step P noHost (invoke s a args)
      ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] (lbody code args 0)]]⟩ := by
  rw [invoke_eq D, lbody_zero, show vals (args ++ [.ref (.func a)]) ++ [.callRefType fi.type] =
    vals args ++ [.ref (.func a), .callRefType fi.type] by simp [Val.toAdmin]]
  have := Step.callRefFunc (P := P) (host := noHost) (s := s) (f := {}) (vs := args)
    (c := .callRefType fi.type) trivial D.hf D.he (D.hps.symm) D.hcode
  simpa [D.hloc, D.hrs, frm] using this

theorem steps_get (D : Data s a args op fi code ps rs) :
    ∀ j ≤ args.length, Steps P noHost (invoke s a args)
      ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] (lbody code args j)]]⟩
  | 0, _ => .single (step_start_ex D)
  | j + 1, hj => by
    refine (steps_get D j (by omega)).tail ?_
    obtain ⟨x, hx, hd⟩ := body_drop D (j := j) (by omega)
    have hL : lbody code args j =
        vals (args.take j) ++ [.plain (.localGet x)] ++ expression (code.body.drop (j + 1)) := by
      simp [lbody, hd, expression]
    rw [hL, ← lbody_succ (by omega)]
    refine .ctxtFrame (.ctxtLabel ?_)
    have := Step.ctxtInstrs (P := P) (host := noHost) (s := s) (vs := args.take j)
      (rest := expression (code.body.drop (j + 1)))
      (.variable (VariableStep.localGet (local_frm (fi := fi) (args := args) (j := j) (by omega) hx)))
      (.inr (by simpa [expression] using body_drop_ne D (j := j + 1) hj))
    rw [vals_append]
    exact this

/-- Every result of the numeric step is reached. -/
theorem steps_done (D : Data s a args op fi code ps rs) {is' : List Admin}
    (hn : NumericStep P (vals args ++ [.plain op]) is') :
    Steps P noHost (invoke s a args) ⟨s, {}, is'⟩ := by
  have h1 : Step P noHost
      ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] (lbody code args args.length)]]⟩
      ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] is']]⟩ := by
    rw [lbody_len D]
    exact .ctxtFrame (.ctxtLabel (.numeric hn))
  have h2 : Step P noHost ⟨s, {}, [.frame 1 (frm fi args) [.label 1 [] is']]⟩
      ⟨s, {}, [.frame 1 (frm fi args) is']⟩ := by
    rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
    · exact .ctxtFrame (.labelVals (vs := [v]))
    · exact .ctxtFrame .trapLabel
  have h3 : Step P noHost ⟨s, {}, [.frame 1 (frm fi args) is']⟩ ⟨s, {}, is'⟩ := by
    rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
    · exact .frameVals (vs := [v]) rfl
    · exact .trapFrame
  exact (((steps_get D args.length le_rfl).tail h1).tail h2).tail h3

/-- A stage other than the last steps, if the numeric step has a result. -/
theorem inv_progress (D : Data s a args op fi code ps rs) {c : Config H} {r : Nat}
    (hi : Inv P s a args op (frm fi args) code c r) (hr : r ≠ 0)
    (hex : ∃ is', NumericStep P (vals args ++ [.plain op]) is') :
    ∃ c', Step P noHost c c' := by
  cases hi with
  | start => exact ⟨_, step_start_ex D⟩
  | get hj =>
    rename_i j
    rcases Nat.lt_or_ge j args.length with hlt | hge
    · obtain ⟨x, hx, hd⟩ := body_drop D hlt
      have hL : lbody code args j =
          vals (args.take j) ++ [.plain (.localGet x)] ++ expression (code.body.drop (j + 1)) := by
        simp [lbody, hd, expression]
      rw [hL]
      exact ⟨_, .ctxtFrame (.ctxtLabel (.ctxtInstrs (s := s)
        (.variable (VariableStep.localGet (local_frm (fi := fi) (args := args) hlt hx)))
        (.inr (by simpa [expression] using body_drop_ne D (j := j + 1) hlt))))⟩
    · obtain rfl : j = args.length := by omega
      obtain ⟨is', hn⟩ := hex
      rw [lbody_len D]
      exact ⟨_, .ctxtFrame (.ctxtLabel (.numeric hn))⟩
  | num hn =>
    rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
    · exact ⟨_, .ctxtFrame (.labelVals (vs := [v]))⟩
    · exact ⟨_, .ctxtFrame .trapLabel⟩
  | lab hn =>
    rcases numericStep_result hn with ⟨v, rfl⟩ | rfl
    · exact ⟨_, .frameVals (vs := [v]) rfl⟩
    · exact ⟨_, .trapFrame⟩
  | done => exact absurd rfl hr

/-! ## Every run -/

theorem inv_of_steps (D : Data s a args op fi code ps rs) {c : Config H}
    (h : Steps P noHost (invoke s a args) c) : ∃ r, Inv P s a args op (frm fi args) code c r := by
  induction h with
  | refl => exact ⟨_, .start⟩
  | tail _ hs ih =>
    obtain ⟨r, hi⟩ := ih
    obtain ⟨r', hi', -⟩ := inv_step D hi hs
    exact ⟨r', hi'⟩

/-- **Every normal form** is the result of a numeric step, in the empty frame and the same
store. -/
theorem nf (D : Data s a args op fi code ps rs)
    (hex : ∃ is', NumericStep P (vals args ++ [.plain op]) is') {c : Config H}
    (h : Steps P noHost (invoke s a args) c) (hnf : ∀ x, ¬ Step P noHost c x) :
    ∃ is', NumericStep P (vals args ++ [.plain op]) is' ∧ c = ⟨s, {}, is'⟩ := by
  obtain ⟨r, hi⟩ := inv_of_steps D h
  by_cases hr : r = 0
  · subst hr
    cases hi with
    | done hn => exact ⟨_, hn, rfl⟩
  · obtain ⟨c', hc'⟩ := inv_progress D hi hr hex
    exact absurd hc' (hnf c')

/-- **No run is infinite.** -/
theorem not_diverges (D : Data s a args op fi code ps rs) :
    ¬ Diverges P noHost (invoke s a args) := by
  rintro ⟨g, hg0, hg⟩
  have key : ∀ n, ∃ r, Inv P s a args op (frm fi args) code (g n) r ∧ r + n ≤ args.length + 4 := by
    intro n
    induction n with
    | zero => exact ⟨args.length + 4, by rw [hg0]; exact .start, by omega⟩
    | succ n ih =>
      obtain ⟨r, hi, hr⟩ := ih
      obtain ⟨r', hi', hr'⟩ := inv_step D hi (hg n)
      exact ⟨r', hi', by omega⟩
  obtain ⟨r, hi, hr⟩ := key (args.length + 5)
  omega

/-- **Every finite run extends to a normal form.** -/
theorem extends_nf (D : Data s a args op fi code ps rs) {c : Config H}
    (h : Steps P noHost (invoke s a args) c) :
    ∃ c', Steps P noHost c c' ∧ ∀ x, ¬ Step P noHost c' x := by
  obtain ⟨r, hi⟩ := inv_of_steps D h
  clear h
  induction r using Nat.strong_induction_on generalizing c with
  | _ r ih =>
    by_cases hs : ∃ x, Step P noHost c x
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨r', hi', hr'⟩ := inv_step D hi hx
      obtain ⟨c', hc', hnf⟩ := ih r' hr' hi'
      exact ⟨c', .head hx hc', hnf⟩
    · exact ⟨c, .refl, fun x hx => hs ⟨x, hx⟩⟩

end Run

/-! ## From `Fn` -/

theorem expand_of_funcType? {d : DefType} {pl rl : List CValType}
    (h : d.funcType? = some (pl, rl)) :
    ∃ ps rs : Ty (.list .val), Expand d (.func ps rs) ∧ ps.length = pl.length ∧
      rs.length = rl.length := by
  unfold DefType.funcType? at h
  split at h
  · rename_i ps rs hex
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ps, rs, Expand.iff.mpr hex, rfl, rfl⟩
  · cases h

theorem data_of_fn {s : Store H} {a : Nat} {fi : FuncInst H} {args : List Val} {op : Instr}
    (hf : s.funcs[a]? = some fi) (hfn : Fn fi args.length op) :
    ∃ code ps rs, Data s a args op fi code ps rs := by
  obtain ⟨code, hcode, hloc, hbody⟩ := hfn.code
  obtain ⟨pl, rl, hft, hpl, hrl⟩ := hfn.type
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hft
  exact ⟨code, ps, rs, hf, hcode, hloc, hbody, he, hps.trans hpl, hrs.trans hrl, hfn.arity⟩

theorem isLocalGet_sound {j : Nat} {i : Instr} (h : isLocalGet j i = true) :
    ∃ x : LocalIdx, i = .localGet x ∧ x.toNat = j := by
  unfold isLocalGet at h
  split at h
  · exact ⟨_, rfl, by simpa using h⟩
  · cases h

theorem localGetsB_sound : ∀ {j n : Nat} {body : Expr}, localGetsB j n body = true →
    ∀ i < n, ∃ x : LocalIdx, body[i]? = some (.localGet x) ∧ x.toNat = j + i
  | _, 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _, _ + 1, [], h, _, _ => by simp [localGetsB] at h
  | j, n + 1, ins :: rest, h, i, hi => by
    simp only [localGetsB, Bool.and_eq_true] at h
    obtain ⟨hx, h⟩ := h
    obtain ⟨x, rfl, hx⟩ := isLocalGet_sound hx
    cases i with
    | zero => exact ⟨x, rfl, by omega⟩
    | succ i =>
      obtain ⟨y, hy, hyj⟩ := localGetsB_sound h i (by omega)
      exact ⟨y, by simpa using hy, by omega⟩

theorem fn?_sound {fi : FuncInst H} {k : Nat} {op : Instr} (h : fn? fi k = some op) :
    Fn fi k op := by
  unfold fn? at h
  split at h
  · rename_i c hc
    split at h
    · rename_i op' ps rs hd hft
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hb
        obtain ⟨⟨⟨⟨hloc, hlg⟩, har⟩, hps⟩, hrs⟩ := hb
        exact ⟨⟨c, hc, hloc, hd, fun j hj => by simpa using localGetsB_sound hlg j hj⟩,
          ⟨ps, rs, hft, hps, hrs⟩, har⟩
      · cases h
    · cases h
  · cases h

end Silmaril.Proofs.Wasm.Execution.StraightLine

end
