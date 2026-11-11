module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Macro

/-!
# Pure instructions: shapes, extra locals, stack effects, depths

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Pure.lean`; the length facts are one
statement, `pexec_lenSpec`, proved by shape).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- The pure instructions, by shape. -/
inductive PureShape (S : Nat) : Instr → Prop
  | nop : PureShape S .nop
  | drop : PureShape S .drop
  | get (x : LocalIdx) : x.value.val < S → PureShape S (.localGet x)
  | set (x : LocalIdx) : x.value.val < S → PureShape S (.localSet x)
  | tee (x : LocalIdx) : x.value.val < S → PureShape S (.localTee x)
  | const (b : BitVec 32) : PureShape S (.intConst .i32 b)
  | un (op : IntUnOp) : PureShape S (.intUnOp .i32 op)
  | bin (op : IntBinOp) : PureShape S (.intBinOp .i32 op)
  | test (op : IntTestOp) : PureShape S (.intTestOp .i32 op)
  | rel (op : IntRelOp) : PureShape S (.intRelOp .i32 op)

theorem i32_const {S : Nat} {t : IntType} {b : BitVec t.width}
    (h : pureIns S (.intConst t b) = true) : t = .i32 := by
  cases t
  · rfl
  · simp [pureIns] at h

theorem i32_un {S : Nat} {t : IntType} {op : IntUnOp} (h : pureIns S (.intUnOp t op) = true) :
    t = .i32 := by
  cases t
  · rfl
  · simp [pureIns] at h

theorem i32_bin {S : Nat} {t : IntType} {op : IntBinOp} (h : pureIns S (.intBinOp t op) = true) :
    t = .i32 := by
  cases t
  · rfl
  · simp [pureIns] at h

theorem i32_test {S : Nat} {t : IntType} {op : IntTestOp}
    (h : pureIns S (.intTestOp t op) = true) : t = .i32 := by
  cases t
  · rfl
  · simp [pureIns] at h

theorem i32_rel {S : Nat} {t : IntType} {op : IntRelOp} (h : pureIns S (.intRelOp t op) = true) :
    t = .i32 := by
  cases t
  · rfl
  · simp [pureIns] at h

/-- A pure instruction has one of the shapes (the `i32` facts above for the numeric ones). -/
theorem pureShape {S : Nat} {i : Instr} (h : pureIns S i = true) : PureShape S i := by
  cases i
  all_goals try (simp [pureIns] at h; done)
  case nop => exact .nop
  case drop => exact .drop
  case localGet x => exact .get x (by simpa [pureIns] using h)
  case localSet x => exact .set x (by simpa [pureIns] using h)
  case localTee x => exact .tee x (by simpa [pureIns] using h)
  case intConst t b => cases i32_const h; exact .const b
  case intUnOp t op => cases i32_un h; exact .un op
  case intBinOp t op => cases i32_bin h; exact .bin op
  case intTestOp t op => cases i32_test h; exact .test op
  case intRelOp t op => cases i32_rel h; exact .rel op

theorem pexec_ext {S : Nat} {i : Instr} (hi : PureShape S i) {ls ex ops : List W}
    (hl : ls.length = S) :
    pexec i (ls ++ ex) ops = (pexec i ls ops).map fun r => (r.1 ++ ex, r.2) := by
  cases hi with
  | nop => simp [pexec]
  | drop => cases ops <;> simp [pexec]
  | get x hx =>
    simp only [pexec, List.getElem?_append_left (show x.value.val < ls.length by omega)]
    cases ls[x.value.val]? <;> rfl
  | set x hx =>
    cases ops <;> simp [pexec, List.set_append_left _ _ (show x.value.val < ls.length by omega)]
    simp only [show x.value.val < ls.length + ex.length by omega, show x.value.val < ls.length by omega,
      ite_true]
  | tee x hx =>
    cases ops <;> simp [pexec, List.set_append_left _ _ (show x.value.val < ls.length by omega)]
    simp only [show x.value.val < ls.length + ex.length by omega, show x.value.val < ls.length by omega,
      ite_true]
  | const b => simp [pexec]
  | un op => cases ops <;> simp [pexec]
  | bin op =>
    rcases ops with _ | ⟨y, _ | ⟨x, ops⟩⟩ <;> simp [pexec]
    cases Numerics.intBinOp .i32 op x y <;> simp
  | test op => cases ops <;> simp [pexec]
  | rel op => rcases ops with _ | ⟨y, _ | ⟨x, ops⟩⟩ <;> simp [pexec]

theorem segStep_pure {S : Nat} {i : Instr} (hi : PureShape S i) (s : LS) :
    segStep i s = (pexec i s.locals s.ops).map fun r => { s with locals := r.1, ops := r.2 } := by
  cases hi <;> simp only [segStep, ctlOf, segCore] <;> cases pexec _ _ _ <;> rfl

/-- What a pure step does to the lengths: the locals keep theirs, the operands change by
`eff i`. -/
def LenSpec (i : Instr) (ls ops ls' ops' : List W) : Prop :=
  ls'.length = ls.length ∧ (eff i).1 ≤ ops.length ∧ ops'.length = ops.length - (eff i).1 + (eff i).2

/-- The locals are unchanged and the operands are `o' ++ ops` after popping `k`. -/
theorem lenSpec_of {i : Instr} {ls ops o' rest : List W} {k : Nat} (hk : (eff i).1 = k)
    (ho : (eff i).2 = o'.length) (hops : ops.length = k + rest.length) :
    LenSpec i ls ops ls (o' ++ rest) := by
  refine ⟨rfl, by omega, ?_⟩
  rw [List.length_append]
  omega

theorem lenSpec_setTee {i : Instr} {x : LocalIdx} {ls ops ls' ops' : List W}
    (hi : i = .localSet x ∨ i = .localTee x) (h : pexec i ls ops = some (ls', ops')) :
    LenSpec i ls ops ls' ops' := by
  rcases ops with _ | ⟨v, o⟩
  · rcases hi with rfl | rfl <;> simp [pexec] at h
  · rcases hi with rfl | rfl <;> simp only [pexec] at h <;> split at h <;> cases h <;>
      exact ⟨List.length_set .., by simp [eff], by simp [eff]⟩

theorem lenSpec_bin {op : IntBinOp} {ls ops ls' ops' : List W}
    (h : pexec (.intBinOp .i32 op) ls ops = some (ls', ops')) :
    LenSpec (.intBinOp .i32 op) ls ops ls' ops' := by
  rcases ops with _ | ⟨y, _ | ⟨x, ops⟩⟩ <;> simp only [pexec] at h
  · cases h
  · cases h
  · split at h <;> cases h
    exact lenSpec_of (k := 2) (o' := [_]) rfl rfl (by simp only [List.length_cons]; omega)

theorem lenSpec_get {x : LocalIdx} {ls ops ls' ops' : List W}
    (h : pexec (.localGet x) ls ops = some (ls', ops')) :
    LenSpec (.localGet x) ls ops ls' ops' := by
  simp only [pexec, Option.map_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  cases h
  exact lenSpec_of (k := 0) (o' := [_]) rfl rfl (Nat.zero_add _).symm

theorem lenSpec_one {i : Instr} {f : W → W} {ls ops ls' ops' : List W}
    (hi : ∀ v o, pexec i ls (v :: o) = some (ls, f v :: o)) (hnil : pexec i ls [] = none)
    (he : eff i = (1, 1)) (h : pexec i ls ops = some (ls', ops')) : LenSpec i ls ops ls' ops' := by
  rcases ops with _ | ⟨v, o⟩
  · cases hnil.symm.trans h
  · have hv : (ls, f v :: o) = (ls', ops') := Option.some.inj ((hi v o).symm.trans h)
    cases hv
    exact lenSpec_of (k := 1) (o' := [_]) (by rw [he]) (by rw [he]; rfl) (by simp only [List.length_cons]; omega)

theorem lenSpec_rel {op : IntRelOp} {ls ops ls' ops' : List W}
    (h : pexec (.intRelOp .i32 op) ls ops = some (ls', ops')) :
    LenSpec (.intRelOp .i32 op) ls ops ls' ops' := by
  rcases ops with _ | ⟨y, _ | ⟨x, ops⟩⟩ <;>
    simp only [pexec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lenSpec_of (k := 2) (o' := [_]) rfl rfl (by simp only [List.length_cons]; omega)

/-- **The length effect of a pure step.** -/
theorem pexec_lenSpec {S : Nat} {i : Instr} (hi : PureShape S i) {ls ops ls' ops' : List W}
    (h : pexec i ls ops = some (ls', ops')) : LenSpec i ls ops ls' ops' := by
  cases hi with
  | set x _ => exact lenSpec_setTee (.inl rfl) h
  | tee x _ => exact lenSpec_setTee (.inr rfl) h
  | bin op => exact lenSpec_bin h
  | get x _ => exact lenSpec_get h
  | rel op => exact lenSpec_rel h
  | un op => exact lenSpec_one (fun _ _ => rfl) rfl rfl h
  | test op => exact lenSpec_one (fun _ _ => rfl) rfl rfl h
  | nop =>
    have hv : (ls, ops) = (ls', ops') := Option.some.inj h
    cases hv
    exact lenSpec_of (k := 0) (o' := []) rfl rfl (Nat.zero_add _).symm
  | const b =>
    have hv : (ls, b :: ops) = (ls', ops') := Option.some.inj h
    cases hv
    exact lenSpec_of (k := 0) (o' := [b]) rfl rfl (Nat.zero_add _).symm
  | drop =>
    rcases ops with _ | ⟨v, o⟩
    · cases h
    · have hv : (ls, o) = (ls', ops') := Option.some.inj h
      cases hv
      exact lenSpec_of (k := 1) (o' := []) rfl rfl (by simp only [List.length_cons]; omega)

theorem pexec_len {S : Nat} {i : Instr} (hi : PureShape S i) {ls ops ls' ops' : List W}
    (h : pexec i ls ops = some (ls', ops')) : ls'.length = ls.length :=
  (pexec_lenSpec hi h).1

theorem pexec_depth {S : Nat} {i : Instr} (hi : PureShape S i) {ls ops ls' ops' : List W}
    (h : pexec i ls ops = some (ls', ops')) :
    (eff i).1 ≤ ops.length ∧ ops'.length = ops.length - (eff i).1 + (eff i).2 :=
  (pexec_lenSpec hi h).2

theorem depthAfter_cons {S : Nat} {i : Instr} (hi : PureShape S i) {p : List Instr}
    {ls ops ls' ops' : List W} {d : Nat}
    (hd : depthAfter (i :: p) ops.length = some d) (h : pexec i ls ops = some (ls', ops')) :
    depthAfter p ops'.length = some d := by
  obtain ⟨h1, h2⟩ := pexec_depth hi h
  simp only [depthAfter, show (eff i).1 ≤ ops.length from h1, ite_true] at hd
  rw [h2]; exact hd

theorem depthAfter_append : ∀ (p q : List Instr) (d : Nat),
    depthAfter (p ++ q) d = (depthAfter p d).bind (depthAfter q)
  | [], q, d => by simp [depthAfter]
  | i :: p, q, d => by
    simp only [List.cons_append, depthAfter]
    split
    · exact depthAfter_append p q _
    · rfl

end Silmaril.Wasm.FX.Asyncify.Tool
