module

public import Silmaril.Wasm.FnInst.Ground.Opt.Defs
public import Silmaril.Proofs.Wasm.FnInst.Ground.Rules

@[expose] public section

/-! # Opt equivalences of stack-only segments are grounded equal runs

* `stepS_tr`, `run_trStk`: on `i32` stacks, the grounded interpreter computes the opt
  fragment's deterministic execution `execStk`; `opt_run_eq`: the opt semantics `Opt.run` of
  call-free code is the singleton of `execStk`;
* `run_split`: stack-only code typed at height `n` touches only the top `n` operands;
* `runRef_of_runEq`: an opt equivalence `Opt.RunEq ft n E a b` of two typed stack-only
  segments, whose left side forces its `n` inputs to be `i32`, is `RunRef` of the
  translations, hence (with a non-constant on the left) a `Good` pair.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-! ## The opt semantics of stack-only code is deterministic -/

theorem bind_ok (st : Opt.St) (k : Opt.St → Set Opt.Out) :
    Opt.Out.bind {.ok st} k = k st := by
  ext x
  simp only [Opt.Out.bind, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨st', h, hx⟩ | ⟨h, hx⟩)
    · cases h
      exact hx
    · subst h
      cases hx
  · intro hx
    exact Or.inl ⟨st, rfl, hx⟩

theorem bind_notOk {o : Opt.Out} (ho : o.isOk = false) (k : Opt.St → Set Opt.Out) :
    Opt.Out.bind {o} k = {o} := by
  ext x
  simp only [Opt.Out.bind, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨st, h, -⟩ | ⟨h, -⟩)
    · subst h
      cases ho
    · exact h
  · intro hx
    exact Or.inr ⟨hx, hx ▸ ho⟩

theorem execStk_cons (i : Opt.Instr) (c : Opt.Code) (st : Opt.St) :
    execStk (i :: c) st = match Opt.exec1 i st with
      | .ok st' => execStk c st'
      | o => o := rfl

theorem ofOptStk_stk : ∀ {i : Opt.Instr} {g : GInstr}, ofOptStk i = some g → g.stk = true
  | .const _, _, rfl | .add, _, rfl | .sub, _, rfl | .mul, _, rfl | .and, _, rfl
  | .or, _, rfl | .xor, _, rfl | .eqz, _, rfl | .drop, _, rfl => rfl
  | .localGet _, _, h | .localSet _, _, h | .localTee _, _, h | .globalGet _, _, h
  | .globalSet _, _, h | .call _, _, h => by cases h

theorem ofOptStk_ne_call {i : Opt.Instr} {g : GInstr} (h : ofOptStk i = some g) (f : ℕ) :
    i ≠ .call f := by
  rintro rfl
  cases h

theorem opt_step {i : Opt.Instr} {g : GInstr} (h : ofOptStk i = some g) (ft : Opt.FTypes)
    (E : Opt.Env) (st : Opt.St) : Opt.step ft E i st = {Opt.exec1 i st} := by
  cases i <;> first | rfl | cases h

theorem trStk_cons {i : Opt.Instr} {c : Opt.Code} {g : List GInstr}
    (h : trStk (i :: c) = some g) :
    ∃ gi gs, ofOptStk i = some gi ∧ trStk c = some gs ∧ g = gi :: gs := by
  simp only [trStk, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨gi, hi, gs, hs, rfl⟩ := h
  exact ⟨gi, gs, hi, hs, rfl⟩

/-- **The opt semantics of translatable code is the singleton of `execStk`.** -/
theorem opt_run_eq {c : Opt.Code} {g : List GInstr} (h : trStk c = some g) (ft : Opt.FTypes)
    (E : Opt.Env) (st : Opt.St) : Opt.run ft E c st = {execStk c st} := by
  induction c generalizing g st with
  | nil => rfl
  | cons i c ih =>
    obtain ⟨gi, gs, hi, hs, rfl⟩ := trStk_cons h
    show Opt.Out.bind (Opt.step ft E i st) (Opt.run ft E c) = _
    rw [opt_step hi]
    cases he : Opt.exec1 i st with
    | ok st' =>
      rw [bind_ok, execStk_cons, he]
      exact ih hs st'
    | trap => rw [bind_notOk rfl, execStk_cons, he]
    | div => rw [bind_notOk rfl, execStk_cons, he]

/-! ## The grounded interpreter computes `execStk` on `i32` stacks -/

theorem eqzV_eq (a : BitVec 32) : Opt.eqzV a = intTestOp .i32 .eqz a := by
  by_cases h : a = 0
  · subst h
    rfl
  · have hb : (a == 0) = false := by simpa using h
    show (if a = 0 then 1 else 0) = bool32 (a == 0)
    rw [hb]
    simp only [h, ↓reduceIte, bool32, Bool.false_eq_true]

theorem stepS_bin_tr (b : Bin) (st : Opt.St) :
    stepS (.bin b) (st.stack.map Val.i32) = outS (Opt.binop b.eval st) := by
  obtain ⟨L, G, S⟩ := st
  rcases S with _ | ⟨y, _ | ⟨x, r⟩⟩ <;> rfl

theorem stepS_tr : ∀ {i : Opt.Instr} {g : GInstr}, ofOptStk i = some g → ∀ st : Opt.St,
    stepS g (st.stack.map Val.i32) = outS (Opt.exec1 i st)
  | .const _, _, rfl, _ => rfl
  | .add, _, rfl, st => stepS_bin_tr .add st
  | .sub, _, rfl, st => stepS_bin_tr .sub st
  | .mul, _, rfl, st => stepS_bin_tr .mul st
  | .and, _, rfl, st => stepS_bin_tr .and st
  | .or, _, rfl, st => stepS_bin_tr .or st
  | .xor, _, rfl, st => stepS_bin_tr .xor st
  | .eqz, _, rfl, ⟨_, _, []⟩ => rfl
  | .eqz, _, rfl, ⟨_, _, a :: _⟩ => by
    show some (Val.i32 (intTestOp .i32 .eqz a) :: _) = some (Val.i32 (Opt.eqzV a) :: _)
    rw [eqzV_eq]
  | .drop, _, rfl, ⟨_, _, []⟩ => rfl
  | .drop, _, rfl, ⟨_, _, _ :: _⟩ => rfl
  | .localGet _, _, h, _ | .localSet _, _, h, _ | .localTee _, _, h, _ | .globalGet _, _, h, _
  | .globalSet _, _, h, _ | .call _, _, h, _ => by cases h

/-- **On `i32` stacks the grounded interpreter runs the opt execution.** -/
theorem run_trStk {c : Opt.Code} {g : List GInstr} (h : trStk c = some g) (f : Frame)
    (st : Opt.St) : run g f (st.stack.map Val.i32) = (outS (execStk c st)).map (f, ·) := by
  induction c generalizing g st with
  | nil =>
    obtain rfl : g = [] := by simpa [trStk] using h.symm
    rfl
  | cons i c ih =>
    obtain ⟨gi, gs, hi, hs, rfl⟩ := trStk_cons h
    rw [run_cons, step1_of_stk (ofOptStk_stk hi), stepS_tr hi]
    cases he : Opt.exec1 i st with
    | ok st' =>
      simp only [outS, Option.map_some, Option.bind_some, execStk_cons, he]
      exact ih hs st'
    | trap => simp only [outS, Option.map_none, Option.bind_none, execStk_cons, he]
    | div => simp only [outS, Option.map_none, Option.bind_none, execStk_cons, he]

/-! ## Typed stack-only code touches only the top of the stack -/

theorem stepS_split {g : GInstr} (hg : g.stk = true) {X : List Val} (hX : popS g ≤ X.length)
    (S : List Val) : stepS g (X ++ S) = (stepS g X).map (· ++ S) := by
  cases g with
  | localGet _ | localSet _ | localTee _ => cases hg
  | const _ | nop => rfl
  | drop =>
    rcases X with _ | ⟨v, X⟩
    · simp [popS] at hX
    · rfl
  | eqz =>
    rcases X with _ | ⟨v, X⟩
    · simp [popS] at hX
    · show (asI32 v).map _ = ((asI32 v).map _).map _
      cases asI32 v <;> rfl
  | bin b =>
    rcases X with _ | ⟨y, _ | ⟨x, X⟩⟩
    · simp [popS] at hX
    · simp [popS] at hX
    · show ((asI32 x).bind _) = ((asI32 x).bind _).map _
      cases asI32 x <;> cases asI32 y <;> rfl

theorem stepS_length {g : GInstr} {X Y : List Val} (h : stepS g X = some Y) :
    Y.length + popS g = X.length + pushS g := by
  cases g with
  | localGet _ | localSet _ | localTee _ => cases h
  | const _ => obtain rfl := Option.some.inj h; rfl
  | nop => obtain rfl := Option.some.inj h; rfl
  | drop => obtain ⟨v, rfl⟩ := stepS_drop_inv h; rfl
  | eqz => obtain ⟨x, X', rfl, rfl⟩ := stepS_eqz_inv h; rfl
  | bin b => obtain ⟨x, y, X', rfl, rfl⟩ := stepS_bin_inv h; rfl

/-- **Typed stack-only code touches only the top `n` operands.** -/
theorem run_split {g : List GInstr} (hg : ∀ i ∈ g, i.stk = true) {n m : ℕ}
    (hc : chkS g n = some m) {X : List Val} (hX : X.length = n) (f : Frame) (S : List Val) :
    run g f (X ++ S) = (run g f X).map fun r => (r.1, r.2 ++ S) := by
  induction g generalizing n X with
  | nil => rfl
  | cons i g ih =>
    have hi : i.stk = true := hg i (by simp)
    have hc' : popS i ≤ n ∧ chkS g (n - popS i + pushS i) = some m := by
      unfold chkS at hc
      split at hc
      · exact ⟨by assumption, hc⟩
      · cases hc
    rw [run_cons, run_cons, step1_of_stk hi, step1_of_stk hi, stepS_split hi (by omega) S]
    cases hY : stepS i X with
    | none => rfl
    | some Y =>
      have hl := stepS_length hY
      exact ih (fun j hj => hg j (by simp [hj])) hc'.2 (by omega)

theorem hgt_tr : ∀ {i : Opt.Instr} {g : GInstr}, ofOptStk i = some g →
    ∀ (ft : Opt.FTypes) (n : ℕ),
      Opt.hgt ft i n = if popS g ≤ n then some (n - popS g + pushS g) else none
  | .const _, _, rfl, _, _ | .add, _, rfl, _, _ | .sub, _, rfl, _, _ | .mul, _, rfl, _, _
  | .and, _, rfl, _, _ | .or, _, rfl, _, _ | .xor, _, rfl, _, _ | .eqz, _, rfl, _, _
  | .drop, _, rfl, _, _ => rfl
  | .localGet _, _, h, _, _ | .localSet _, _, h, _, _ | .localTee _, _, h, _, _
  | .globalGet _, _, h, _, _ | .globalSet _, _, h, _, _ | .call _, _, h, _, _ => by cases h

theorem chk_tr {c : Opt.Code} {g : List GInstr} (h : trStk c = some g) (ft : Opt.FTypes)
    (n : ℕ) : Opt.chk ft c n = chkS g n := by
  induction c generalizing g n with
  | nil =>
    obtain rfl : g = [] := by simpa [trStk] using h.symm
    rfl
  | cons i c ih =>
    obtain ⟨gi, gs, hi, hs, rfl⟩ := trStk_cons h
    have e : Opt.hgt ft i n = if popS gi ≤ n then some (n - popS gi + pushS gi) else none :=
      hgt_tr hi ft n
    show (Opt.hgt ft i n).bind (Opt.chk ft c) = chkS (gi :: gs) n
    rw [e]
    unfold chkS
    split
    · exact ih hs _
    · rfl

theorem trStk_stk {c : Opt.Code} {g : List GInstr} (h : trStk c = some g) :
    ∀ i ∈ g, i.stk = true := by
  induction c generalizing g with
  | nil =>
    obtain rfl : g = [] := by simpa [trStk] using h.symm
    simp
  | cons i c ih =>
    obtain ⟨gi, gs, hi, hs, rfl⟩ := trStk_cons h
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ofOptStk_stk hi
    · exact ih hs j hj

/-! ## The transfer -/

/-- Opt equal runs give equal grounded runs on `i32` stacks deep enough for the hole. -/
theorem run_eq_of_runEq {ft : Opt.FTypes} {n : ℕ} {E : Opt.Env} {a b : Opt.Code}
    {ga gb : List GInstr} (hrun : Opt.RunEq ft n E a b) (ha : trStk a = some ga)
    (hb : trStk b = some gb) (f : Frame) (vs : List (BitVec 32)) (hn : n ≤ vs.length) :
    run ga f (vs.map Val.i32) = run gb f (vs.map Val.i32) := by
  let st : Opt.St := ⟨fun _ => 0, fun _ => 0, vs⟩
  have h₁ : ({execStk a st} : Set Opt.Out) = {execStk b st} := by
    rw [← opt_run_eq ha ft E, ← opt_run_eq hb ft E]
    exact hrun st hn
  have h₂ : execStk a st = execStk b st := Set.singleton_eq_singleton_iff.mp h₁
  rw [run_trStk ha f st, run_trStk hb f st, h₂]

/-- **The transfer**: an opt equivalence of typed stack-only segments whose left side forces
its inputs to be `i32` is a grounded equal-run pair. -/
theorem runRef_of_runEq {ft : Opt.FTypes} {n m m' : ℕ} {E : Opt.Env} {a b : Opt.Code}
    {ga gb : List GInstr} (hrun : Opt.RunEq ft n E a b) (ha : trStk a = some ga)
    (hb : trStk b = some gb) (hca : Opt.chk ft a n = some m) (hcb : Opt.chk ft b n = some m')
    (hforce : Forces n ga) : RunRef ga gb := by
  intro f st r h
  obtain ⟨vs, S, rfl, hlen⟩ := hforce f st r h
  have hlen' : (vs.map Val.i32).length = n := by simpa using hlen
  have hsa := run_split (trStk_stk ha) ((chk_tr ha ft n).symm.trans hca) hlen' f S
  have hsb := run_split (trStk_stk hb) ((chk_tr hb ft n).symm.trans hcb) hlen' f S
  have heq := run_eq_of_runEq hrun ha hb f vs (by omega)
  rw [hsb, ← heq, ← hsa]
  exact h

/-! ## Forcing lemmas -/

/-- A binary operator after a constant forces its other operand to be `i32`. -/
theorem forces_constBin (k : BitVec 32) (b : Bin) : Forces 1 [.const k, .bin b] := by
  intro f st r h
  have h₀ : run [.bin b] f (Val.i32 k :: st) = some r := h
  obtain ⟨⟨f₁, X₁⟩, h₁, -⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨-, h₁'⟩ := step1_stk_inv rfl h₁
  obtain ⟨x, y, X', hX, -⟩ := stepS_bin_inv h₁'
  obtain ⟨-, rfl⟩ := List.cons.inj hX
  exact ⟨[x], X', rfl, rfl⟩

/-- `i32.eqz` first forces its operand to be `i32`. -/
theorem forces_eqz (c : List GInstr) : Forces 1 (.eqz :: c) := by
  intro f st r h
  obtain ⟨⟨f₁, X₁⟩, h₁, -⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, h₁'⟩ := step1_stk_inv rfl h₁
  obtain ⟨x, X, rfl, -⟩ := stepS_eqz_inv h₁'
  exact ⟨[x], X, rfl, rfl⟩

end Silmaril.Wasm.FnInst.Ground
