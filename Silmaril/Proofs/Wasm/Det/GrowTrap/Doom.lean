module

public import Silmaril.Proofs.Wasm.Det.GrowTrap.Basic
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# Subset 2 (allocation failure traps): a failed `memory.grow` is doomed

`Dm code`: the code is at a stage of a guarded `memory.grow` failure, possibly inside labels and
frames. The stages follow the guard `(local.tee k)? t.const -1 t.eq if bt (unreachable …) …`
after `-1` (all ones, at any integer type `a`) was pushed:

* `tee`, `set`: the optional `local.tee k` (it duplicates the value, then `local.set` stores it);
* `rel`: `-1` at type `a` and `-1` at type `t` below `t.eq` (the comparison is stuck unless
  `a = t`, and then yields a nonzero `i32`);
* `ift`: a nonzero `i32` below the `if` (the `then` branch is taken);
* `blk`: the `block` of the `then` branch, `unreachable` first;
* `unr`: `unreachable`; `trap`: a trap, which bubbles out;
* `label`, `frame`: a `Dm` body inside a label or a frame.

**`dm_step`**: every host-free step from `Dm` code, at every profile, leads to `Dm` code (the
steps are inverted with silmaril-lean's `hostFree_head_inv`, `Det.Step.decomp` and head
inversions). **`dm_not_stop`**: `Dm` code is not a non-trapping stop (not a result other than a
trap, and not a host-call redex). Hence **`dm_doomed`**: from `Dm` code no host-free run reaches a
non-trapping stop, at every profile. A stuck comparison (a mismatched type) is covered: stuck
code has no further step.

The head-inversion lemmas follow silmaril-lean's
`Silmaril.Wasm.Binaryen.GuardSim.head_localGet`/`head_if` (`RemoveUnusedBrsGuardSim.lean`),
restated for the instructions of the guard. New proofs otherwise.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.GrowTrap Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-- All ones at an integer type, as a value. -/
def m1 (t : IntType) : Val := .num ⟨.int t, BitVec.allOnes _⟩

/-- The tail of the guard after its constant: `t.eq; if bt (unreachable th) el`. -/
abbrev relIf (t : IntType) (bt : BlockType) (th el : List Instr) (rest : List Admin) :
    List Admin :=
  .plain (.intRelOp t .eq) :: .plain (.if_ bt (.unreachable :: th) el) :: rest

/-- **The stages of a guarded `memory.grow` failure.** -/
inductive Dm : List Admin → Prop
  | trap (ws : List Val) (rest : List Admin) : Dm (vals ws ++ .trap :: rest)
  | unr (ws : List Val) (rest : List Admin) : Dm (vals ws ++ .plain .unreachable :: rest)
  | blk (ws : List Val) (bt : BlockType) (th : List Instr) (rest : List Admin) :
      Dm (vals ws ++ .plain (.block bt (.unreachable :: th)) :: rest)
  | ift (ws : List Val) (c : BitVec 32) (hc : c ≠ 0) (bt : BlockType) (th el : List Instr)
      (rest : List Admin) :
      Dm (vals (ws ++ [.i32 c]) ++ .plain (.if_ bt (.unreachable :: th) el) :: rest)
  | rel (ws : List Val) (a t : IntType) (bt : BlockType) (th el : List Instr) (rest : List Admin) :
      Dm (vals (ws ++ [m1 a, m1 t]) ++ relIf t bt th el rest)
  | set (ws : List Val) (a t : IntType) (k : LocalIdx) (bt : BlockType) (th el : List Instr)
      (rest : List Admin) :
      Dm (vals (ws ++ [m1 a, m1 a]) ++ .plain (.localSet k) :: (m1 t).toAdmin :: relIf t bt th el rest)
  | tee (ws : List Val) (a t : IntType) (k : LocalIdx) (bt : BlockType) (th el : List Instr)
      (rest : List Admin) :
      Dm (vals (ws ++ [m1 a]) ++ .plain (.localTee k) :: (m1 t).toAdmin :: relIf t bt th el rest)
  | label (ws : List Val) (n : Nat) (k : List Instr) (body rest : List Admin) (h : Dm body) :
      Dm (vals ws ++ .label n k body :: rest)
  | frame (ws : List Val) (n : Nat) (fr : Frame) (body rest : List Admin) (h : Dm body) :
      Dm (vals ws ++ .frame n fr body :: rest)

/-! ## The first non-value of `Dm` code -/

/-- The first non-values of the stages. -/
def DmHead : Admin → Prop
  | .trap => True
  | .plain .unreachable => True
  | .plain (.block _ _) => True
  | .plain (.if_ _ _ _) => True
  | .plain (.intRelOp _ _) => True
  | .plain (.localSet _) => True
  | .plain (.localTee _) => True
  | .label _ _ _ => True
  | .frame _ _ _ => True
  | _ => False

theorem vals_cons_eq (ws : List Val) (v : Val) (e : Admin) (rest : List Admin) :
    vals (ws ++ [v]) ++ e :: rest = vals ws ++ v.toAdmin :: e :: rest := by
  simp

/-- `Dm` code has a first non-value, of the stage kinds. -/
theorem Dm.first {l : List Admin} (h : Dm l) :
    ∃ W e rest, l = vals W ++ e :: rest ∧ e.val? = none ∧ DmHead e := by
  cases h with
  | trap ws rest => exact ⟨ws, _, rest, rfl, rfl, trivial⟩
  | unr ws rest => exact ⟨ws, _, rest, rfl, rfl, trivial⟩
  | blk ws bt th rest => exact ⟨ws, _, rest, rfl, rfl, trivial⟩
  | ift ws c _ bt th el rest => exact ⟨_, _, rest, rfl, rfl, trivial⟩
  | rel ws a t bt th el rest => exact ⟨_, _, _, rfl, rfl, trivial⟩
  | set ws a t k bt th el rest => exact ⟨_, _, _, rfl, rfl, trivial⟩
  | tee ws a t k bt th el rest => exact ⟨_, _, _, rfl, rfl, trivial⟩
  | label ws n k body rest _ => exact ⟨ws, _, rest, rfl, rfl, trivial⟩
  | frame ws n fr body rest _ => exact ⟨ws, _, rest, rfl, rfl, trivial⟩

/-- `Dm` code has no first non-value `e` outside the stage kinds. -/
theorem Dm.not_head {l : List Admin} (h : Dm l) {W : List Val} {e : Admin} {R : List Admin}
    (hl : l = vals W ++ e :: R) (he : e.val? = none) (hk : ¬ DmHead e) : False := by
  obtain ⟨W', e', R', hl', he', hk'⟩ := h.first
  rw [hl] at hl'
  have := (Det.vals_append_cons_inj hl' he he').2.1
  exact hk (this ▸ hk')

theorem Dm.not_vals {vs : List Val} (h : Dm (vals vs)) : False := by
  obtain ⟨W, e, R, hl, he, -⟩ := h.first
  exact Det.vals_ne_append_cons he hl

/-! ## `Dm` code is not a non-trapping stop -/

theorem toAdmin_eq_trap {r : Result} (h : r.toAdmin = [.trap]) : r = .trap := by
  rcases r with vs | a | _
  · rcases vs with _ | ⟨v, _ | _⟩ <;> simp [Result.toAdmin, vals] at h
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h
  · simp [Result.toAdmin] at h
  · rfl

theorem dm_not_result {l : List Admin} (h : Dm l) {r : Result} (hr : l = r.toAdmin) :
    r = .trap := by
  rcases r with vs | a | _
  · have hv : l = vals vs := by simpa [Result.toAdmin] using hr
    exact (Dm.not_vals (hv ▸ h)).elim
  · exact (h.not_head (W := [.ref (.exn a)]) (e := .plain .throwRef) (R := [])
      (by simpa [Result.toAdmin, vals, Val.toAdmin] using hr) rfl (by simp [DmHead])).elim
  · rfl

theorem dm_decompose {s : Store Nat} {l : List Admin} (h : Dm l) : decompose? s l = none := by
  induction h with
  | label ws n k body rest _ ih =>
    exact decompose?_vals_cons_none rfl fun vs r => by rw [decompHead_label, ih]; rfl
  | frame ws n fr body rest _ ih =>
    exact decompose?_vals_cons_none rfl fun vs r => by rw [decompHead_frame, ih]; rfl
  | trap ws rest => exact decompose?_vals_cons_none rfl fun _ _ => decompHead_trap
  | unr ws rest => exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | blk ws bt th rest => exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | ift ws c _ bt th el rest => exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | rel ws a t bt th el rest => exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | set ws a t k bt th el rest =>
    exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | tee ws a t k bt th el rest =>
    exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl

/-- **`Dm` code is not a non-trapping stop.** -/
theorem dm_not_stop {c : Config Nat} (h : Dm c.code) : ¬ Stop c := by
  rintro ⟨o, ho⟩
  cases ho with
  | ret hr hc => exact hr (dm_not_result h hc)
  | call hd =>
    rw [dm_decompose h] at hd
    cases hd

/-! ## Head inversions for the guard -/

set_option hygiene false in
/-- A family rule at a control instruction is impossible. -/
local macro "fam_no" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

variable {P : Profile} {s : Store Nat} {f : Frame} {args : List Val} {c₀ : Config Nat}

theorem vals_eq_nil {vs : List Val} (h : vals vs = []) : vs = [] := by
  cases vs <;> simp_all [vals]

/-- `unreachable` traps. -/
theorem head_unreachable (h : Det.Head P s f args (.plain .unreachable) c₀) :
    args = [] ∧ c₀.code = [.trap] := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize hc : vals args ++ [Admin.plain .unreachable] = l at hv
  cases hv with
  | unreachable =>
    exact ⟨vals_eq_nil ((Det.append_singleton_inj (l₂ := [])).mp hc).1, rfl⟩
  | _ =>
    have := congrArg List.getLast? hc
    simp at this

/-- `if` selects a branch. -/
theorem head_if {bt : BlockType} {b₁ b₂ : List Instr}
    (h : Det.Head P s f args (.plain (.if_ bt b₁ b₂)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [.plain (.block bt (if c = 0 then b₂ else b₁))]⟩ := by
  cases h with
  | ifTrue hc => exact ⟨_, rfl, by simp only [hc, ↓reduceIte]⟩
  | ifFalse hc => exact ⟨_, rfl, by simp only [hc, ↓reduceIte]⟩
  | _ => fam_no

theorem vals_two {args : List Val} {A B : Admin} (h : vals args = [A, B]) :
    ∃ w₁ w₂, args = [w₁, w₂] ∧ w₁.toAdmin = A ∧ w₂.toAdmin = B := by
  rcases args with _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, t⟩⟩⟩ <;> simp [vals] at h
  exact ⟨w₁, w₂, rfl, h⟩

theorem vals_one {args : List Val} {A : Admin} (h : vals args = [A]) :
    ∃ w, args = [w] ∧ w.toAdmin = A := by
  rcases args with _ | ⟨w, _ | ⟨w₂, t⟩⟩ <;> simp [vals] at h
  exact ⟨w, rfl, h⟩

/-- The numeric rule of `t.eq`. -/
theorem numeric_relEq {t : IntType} {l' : List Admin}
    (hv : NumericStep P (vals args ++ [.plain (.intRelOp t .eq)]) l') :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      l' = [constI32 (Numerics.intRelOp t .eq x y)] := by
  generalize hc : vals args ++ [Admin.plain (.intRelOp t .eq)] = l at hv
  cases hv with
  | @intRelOp t' op x y =>
    obtain ⟨h1, h2⟩ :=
      (Det.append_singleton_inj (l₂ := [Admin.plain (.intConst t' x), .plain (.intConst t' y)])).mp hc
    have ht : t = t' ∧ IntRelOp.eq = op := by simpa using h2
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨w₁, w₂, rfl, hw₁, hw₂⟩ := vals_two h1
    have e₁ : w₁ = .num ⟨.int t, x⟩ := Det.toAdmin_inj.mp hw₁
    have e₂ : w₂ = .num ⟨.int t, y⟩ := Det.toAdmin_inj.mp hw₂
    exact ⟨x, y, by rw [e₁, e₂], rfl⟩
  | _ => exact absurd (congrArg List.getLast? hc) (by simp)

/-- `t.eq` compares two integers of type `t`. -/
theorem head_relEq {t : IntType} (h : Det.Head P s f args (.plain (.intRelOp t .eq)) c₀) :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      c₀.code = [constI32 (Numerics.intRelOp t .eq x y)] := by
  have hv : ∃ is', NumericStep P (vals args ++ [.plain (.intRelOp t .eq)]) is' ∧
      c₀ = ⟨s, f, is'⟩ := by
    simpa [Det.famOf, Det.FamRel] using h.fam_inv (by simp [Det.famOf])
  obtain ⟨is', hstep, rfl⟩ := hv
  exact numeric_relEq hstep

/-- The variable rule of `local.tee`. -/
theorem variable_tee {k : LocalIdx} {c : Config Nat}
    (hv : VariableStep ⟨s, f, vals args ++ [.plain (.localTee k)]⟩ c) :
    ∃ v, args = [v] ∧ c = ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet k)]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.localTee k)]⟩ : Config Nat) = c₁ at hv
  cases hv with
  | @localTee s' f' x v =>
    have hc' : s = s' ∧ f = f' ∧ vals args ++ [.plain (.localTee k)] = [v.toAdmin] ++
        [.plain (.localTee x)] := by simpa using hc
    obtain ⟨rfl, rfl, h⟩ := hc'
    obtain ⟨h1, h2⟩ := Det.append_singleton_inj.mp h
    have hk : k = x := by simpa using h2
    obtain ⟨w, rfl, hw⟩ := vals_one h1
    have e : w = v := Det.toAdmin_inj.mp hw
    rw [hk, e]
    exact ⟨v, rfl, rfl⟩
  | _ =>
    have hc' := congrArg (fun c : Config Nat => c.code.getLast?) hc
    simp at hc'

/-- `local.tee` duplicates its operand. -/
theorem head_localTee {k : LocalIdx} (h : Det.Head P s f args (.plain (.localTee k)) c₀) :
    ∃ v, args = [v] ∧ c₀ = ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet k)]⟩ :=
  variable_tee (by simpa [Det.famOf, Det.FamRel] using h.fam_inv (by simp [Det.famOf]))

/-- `local.set` stores its operand. -/
theorem head_localSet {k : LocalIdx} (h : Det.Head P s f args (.plain (.localSet k)) c₀) :
    ∃ v, args = [v] ∧ c₀.code = [] ∧ c₀.store = s := by
  have hv := h.fam_inv (by simp [Det.famOf])
  simp only [Det.famOf, Det.FamRel] at hv
  generalize hc : (⟨s, f, vals args ++ [.plain (.localSet k)]⟩ : Config Nat) = c at hv
  cases hv with
  | @localSet s' f' x v _ =>
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, hc⟩ := hc
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj (l₂ := [v.toAdmin])).mp hc
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      have hl := congrArg List.length h1
      simp only [vals, List.length_map, List.length_cons, List.length_nil] at hl
      match args, hl with
      | [w], _ => exact ⟨w, rfl⟩
    exact ⟨w, rfl, rfl, rfl⟩
  | _ =>
    simp only [Config.mk.injEq] at hc
    have := congrArg List.getLast? hc.2.2
    simp at this

theorem returnCallRef_not_head {c : Admin} (hc : c.IsReturnCallRef) : ¬ DmHead c := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsReturnCallRef, DmHead]
  cases i <;> simp_all

/-- The steps of a label around `Dm` code (no argument values). -/
theorem head_label_dm {n : Nat} {k : List Instr} {body : List Admin}
    (hh : Det.Head P s f args (.label n k body) c₀) (hD : Dm body)
    (ih : ∀ {s : Store Nat} {f : Frame} {c' : Config Nat}, Step P Det.noHost ⟨s, f, body⟩ c' →
      Dm c'.code) (vs : List Val)
    (rest : List Admin) : Dm (vals vs ++ c₀.code ++ rest) := by
  cases hh with
  | ctxtLabel h => simpa using Dm.label vs n k _ rest (ih h)
  | labelVals hb => exact (Dm.not_vals (hb ▸ hD)).elim
  | @brLabelZero _ _ _ _ vs' vs₂ l r hb _ _ =>
    exact (hD.not_head (W := vs' ++ vs₂) (e := .plain (.br l)) (R := r) (by rw [hb]; simp) rfl
      (by simp [DmHead])).elim
  | @brLabelSucc _ _ _ _ vs₂ l r hb _ =>
    exact (hD.not_head (W := vs₂) (e := .plain (.br l)) (R := r) (by rw [hb]; simp) rfl
      (by simp [DmHead])).elim
  | @returnLabel _ _ _ _ vs₂ r hb =>
    exact (hD.not_head (W := vs₂) (e := .plain .return_) (R := r) (by rw [hb]; simp) rfl
      (by simp [DmHead])).elim
  | @returnCallRefLabel _ _ _ _ vs₂ c r hb hc =>
    exact (hD.not_head (W := vs₂) (e := c) (R := r) (by rw [hb]; simp) (val?_returnCallRef hc)
      (returnCallRef_not_head hc)).elim
  | trapLabel => simpa using Dm.trap vs rest
  | @throwRefLabel _ _ _ a =>
    exact (hD.not_head (W := [.ref (.exn a)]) (e := .plain .throwRef) (R := [])
      (by simp [vals, Val.toAdmin]) rfl
      (by simp [DmHead])).elim
  | _ => fam_no

/-- The steps of a frame around `Dm` code. -/
theorem head_frame_dm {n : Nat} {fr : Frame} {body : List Admin}
    (hh : Det.Head P s f args (.frame n fr body) c₀) (hD : Dm body)
    (ih : ∀ {s : Store Nat} {f : Frame} {c' : Config Nat}, Step P Det.noHost ⟨s, f, body⟩ c' →
      Dm c'.code) (vs : List Val)
    (rest : List Admin) : Dm (vals vs ++ c₀.code ++ rest) := by
  cases hh with
  | ctxtFrame h => simpa using Dm.frame vs n _ _ rest (ih h)
  | frameVals hb _ => exact (Dm.not_vals (hb ▸ hD)).elim
  | @returnFrame _ _ _ _ vs' vs₂ r hb _ =>
    exact (hD.not_head (W := vs' ++ vs₂) (e := .plain .return_) (R := r) (by rw [hb]; simp) rfl
      (by simp [DmHead])).elim
  | @returnCallRefFrameNull _ _ _ _ vs₂ c r hb hc =>
    exact (hD.not_head (W := vs₂ ++ [.ref .null]) (e := c) (R := r)
      (by rw [hb]; simp [Val.toAdmin]) (val?_returnCallRef hc) (returnCallRef_not_head hc)).elim
  | @returnCallRefFrameAddr _ _ _ _ vs' vs₂ a c r _ _ _ hb hc =>
    exact (hD.not_head (W := vs' ++ vs₂ ++ [.ref (.func a)]) (e := c) (R := r)
      (by rw [hb]; simp [Val.toAdmin]) (val?_returnCallRef hc) (returnCallRef_not_head hc)).elim
  | trapFrame => simpa using Dm.trap vs rest
  | @throwRefFrame _ _ _ a =>
    exact (hD.not_head (W := [.ref (.exn a)]) (e := .plain .throwRef) (R := [])
      (by simp [vals, Val.toAdmin]) rfl
      (by simp [DmHead])).elim
  | _ => fam_no

/-- A trap only bubbles. -/
theorem step_trap_dm {ws : List Val} {rest : List Admin} {c' : Config Nat}
    (h : Step P Det.noHost ⟨s, f, vals ws ++ .trap :: rest⟩ c') : Dm c'.code := by
  have hf : Det.fnv (vals ws ++ .trap :: rest) = (ws, .trap :: rest) := by simp
  rcases Det.Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest', c₀, hf', -, hh, -⟩ := Det.fnv_headDec hd
    have he : e = .trap := by
      rw [hf] at hf'
      simp only [Prod.mk.injEq, List.cons.injEq] at hf'
      exact hf'.2.1.symm
    exact (hh.good.ne_trap he).elim
  · obtain ⟨p, q, u, r, -, ⟨-, -, hc⟩ | ⟨a, hf', -, -⟩⟩ := Det.fnv_bubble hb
    · rw [hc]
      simpa using Dm.trap p r
    · rw [hf] at hf'
      simp at hf'

/-- Splitting a value stack below known arguments. -/
theorem split_args {ws vs args L : List Val} (h : ws ++ L = vs ++ args)
    (hl : L.length = args.length) : ws = vs ∧ L = args :=
  List.append_inj' h hl

theorem m1_eq {a t : IntType} {x : BitVec t.width} (h : m1 a = .num ⟨.int t, x⟩) :
    a = t ∧ x.toNat = (BitVec.allOnes t.width).toNat := by
  simp only [m1, Val.num.injEq] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem dm_step_unr {ws : List Val} {rest : List Admin} {c' : Config Nat}
    (hs : Step P Det.noHost ⟨s, f, vals ws ++ .plain .unreachable :: rest⟩ c') : Dm c'.code := by
  obtain ⟨vs, args, c₀, -, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) hs
  obtain ⟨-, hc⟩ := head_unreachable hh
  rw [hc]
  simpa using Dm.trap vs rest

theorem dm_step_blk {ws : List Val} {bt : BlockType} {th : List Instr} {rest : List Admin}
    {c' : Config Nat}
    (hs : Step P Det.noHost ⟨s, f, vals ws ++ .plain (.block bt (.unreachable :: th)) :: rest⟩ c') :
    Dm c'.code := by
  obtain ⟨vs, args, c₀, -, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) hs
  obtain ⟨t₁, t₂, -, -, rfl⟩ := head_block hh
  have hb : Dm (vals args ++ expression (.unreachable :: th)) := by
    simpa [expression] using Dm.unr args (expression th)
  simpa using Dm.label vs t₂.length [] _ rest hb

theorem dm_step_ift {ws : List Val} {c : BitVec 32} (hc : c ≠ 0) {bt : BlockType}
    {th el : List Instr} {rest : List Admin} {c' : Config Nat}
    (hs : Step P Det.noHost
      ⟨s, f, vals (ws ++ [.i32 c]) ++ .plain (.if_ bt (.unreachable :: th) el) :: rest⟩ c') :
    Dm c'.code := by
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv (W := ws ++ [.i32 c]) rfl
    (by simp) (by simp) hs
  obtain ⟨c₁, rfl, rfl⟩ := head_if hh
  obtain ⟨hws, hcc⟩ := split_args hW rfl
  have hcc₁ : (Val.i32 c : Val) = .num ⟨.int .i32, c₁⟩ := (List.cons.inj hcc).1
  have hcc' : c = c₁ := by
    simp only [Val.i32, Val.num.injEq] at hcc₁
    cases hcc₁
    rfl
  have hb : (if c₁ = 0 then el else Instr.unreachable :: th) = .unreachable :: th := by
    rw [← hcc']
    split <;> simp_all
  show Dm (vals vs ++ [.plain (.block bt (if c₁ = 0 then el else .unreachable :: th))] ++ rest)
  rw [hb]
  simpa using Dm.blk vs bt th rest

theorem dm_step_rel {ws : List Val} {a t : IntType} {bt : BlockType} {th el : List Instr}
    {rest : List Admin} {c' : Config Nat}
    (hs : Step P Det.noHost ⟨s, f, vals (ws ++ [m1 a, m1 t]) ++ relIf t bt th el rest⟩ c') :
    Dm c'.code := by
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv (W := ws ++ [m1 a, m1 t]) rfl
    (by simp) (by simp) hs
  obtain ⟨x, y, rfl, hc⟩ := head_relEq hh
  obtain ⟨hws, hxy⟩ := split_args hW rfl
  have hx : a = t ∧ x.toNat = (BitVec.allOnes t.width).toNat := m1_eq (List.cons.inj hxy).1
  have hy : t = t ∧ y.toNat = (BitVec.allOnes t.width).toNat :=
    m1_eq (List.cons.inj (List.cons.inj hxy).2).1
  have hxy' : x = y := BitVec.eq_of_toNat_eq (hx.2.trans hy.2.symm)
  have h1 : Numerics.intRelOp t .eq x y ≠ 0 := by simp [Numerics.intRelOp, hxy', Numerics.bool32]
  rw [hc, ← hws]
  simpa [relIf, constI32] using Dm.ift ws _ h1 bt th el rest

theorem dm_step_set {ws : List Val} {a t : IntType} {k : LocalIdx} {bt : BlockType}
    {th el : List Instr} {rest : List Admin} {c' : Config Nat}
    (hs : Step P Det.noHost ⟨s, f, vals (ws ++ [m1 a, m1 a]) ++ .plain (.localSet k) ::
      (m1 t).toAdmin :: relIf t bt th el rest⟩ c') : Dm c'.code := by
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv (W := ws ++ [m1 a, m1 a]) rfl
    (by simp) (by simp) hs
  obtain ⟨v, rfl, hc, -⟩ := head_localSet hh
  have hvs : vs = ws ++ [m1 a] :=
    (split_args (ws := ws ++ [m1 a]) (L := [m1 a]) (args := [v]) (by simpa using hW) rfl).1.symm
  rw [hc, hvs]
  simpa [relIf] using Dm.rel ws a t bt th el rest

theorem dm_step_tee {ws : List Val} {a t : IntType} {k : LocalIdx} {bt : BlockType}
    {th el : List Instr} {rest : List Admin} {c' : Config Nat}
    (hs : Step P Det.noHost ⟨s, f, vals (ws ++ [m1 a]) ++ .plain (.localTee k) ::
      (m1 t).toAdmin :: relIf t bt th el rest⟩ c') : Dm c'.code := by
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv (W := ws ++ [m1 a]) rfl
    (by simp) (by simp) hs
  obtain ⟨v, rfl, rfl⟩ := head_localTee hh
  obtain ⟨hws, hv⟩ := split_args hW rfl
  have hv' : v = m1 a := by simpa using hv.symm
  rw [hv', ← hws]
  simpa [relIf] using Dm.set ws a t k bt th el rest

/-- **Every host-free step from `Dm` code, at every profile, leads to `Dm` code.** -/
theorem dm_step {l : List Admin} (h : Dm l) :
    ∀ {s : Store Nat} {f : Frame} {c' : Config Nat}, Step P Det.noHost ⟨s, f, l⟩ c' →
      Dm c'.code := by
  induction h with
  | trap ws rest => exact fun hs => step_trap_dm hs
  | unr ws rest => exact fun hs => dm_step_unr hs
  | blk ws bt th rest => exact fun hs => dm_step_blk hs
  | ift ws c hc bt th el rest => exact fun hs => dm_step_ift hc hs
  | rel ws a t bt th el rest => exact fun hs => dm_step_rel hs
  | set ws a t k bt th el rest => exact fun hs => dm_step_set hs
  | tee ws a t k bt th el rest => exact fun hs => dm_step_tee hs
  | label ws n k body rest hD ih =>
    intro s f c' hs
    obtain ⟨vs, args, c₀, -, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) hs
    exact head_label_dm hh hD ih vs rest
  | frame ws n fr body rest hD ih =>
    intro s f c' hs
    obtain ⟨vs, args, c₀, -, hh, rfl⟩ := hostFree_head_inv rfl (by simp) (by simp) hs
    exact head_frame_dm hh hD ih vs rest

/-- **From `Dm` code no host-free run reaches a non-trapping stop**, at every profile. -/
theorem dm_doomed {c : Config Nat} (h : Dm c.code) : Doomed P c := by
  intro d hd
  suffices hD : Dm d.code from dm_not_stop hD
  induction hd with
  | refl => exact h
  | tail _ hs ih =>
    rename_i x y _
    exact dm_step ih (s := x.store) (f := x.frame) hs

end Silmaril.Proofs.Wasm.Det.GrowTrap
