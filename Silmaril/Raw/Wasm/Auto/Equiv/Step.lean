module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Norm
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# One symbolic step (unrefined)

`sstep_exec1`: one step of the symbolic executor of `Silmaril.Wasm.Auto.Equiv.Defs` is one
step of the straight-line interpreter `Silmaril.Wasm.Logic.Core.exec1` on every concrete
state the symbolic state denotes. `wp_sstep`: the forward rule for one symbolic step in
both readings of the every-run logic, from the instruction rules of
`Silmaril.Wasm.Logic.Instr.Thms`. Both proofs are a case analysis on the instruction and the
shape of the symbolic stack, kept here, unrefined, rather than in Isar style; they are used
by `Silmaril.Proofs.Wasm.Auto.Equiv.Sexec`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 popInt popV localVal? Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {ρ : Env}

/-! ## Agreement with `exec` -/

@[simp] theorem stackAt_cons (p : IntType × Term) (st : List (IntType × Term))
    (ls : List (IntType × Term)) : stackAt ρ ⟨ls, p :: st⟩ = den ρ p :: stackAt ρ ⟨ls, st⟩ := rfl

theorem popInt_den (t : IntType) (e : Term) (rs : List Val) :
    popInt t (den ρ (t, e) :: rs) = some (ev ρ t e, rs) := by
  cases t <;> rfl

theorem frameAt_set (f : Frame) (S : SState) (x : LocalIdx) (p : IntType × Term) (st) :
    frameAt f ρ ⟨S.locals.set x.toNat p, st⟩ = (frameAt f ρ S).setLocal x (den ρ p) := by
  simp [frameAt, Frame.setLocal, List.map_set]

theorem frameAt_local? (f : Frame) (S : SState) (x : LocalIdx) :
    (frameAt f ρ S).local? x = (S.locals[x.toNat]?).map fun p => some (den ρ p) := by
  simp [frameAt, Frame.local?]

theorem den_const (t : IntType) (c : BitVec t.width) : den ρ (t, .const c.toNat) = .num ⟨.int t, c⟩ := by
  simp [den, ev]

theorem den_eqz (t : IntType) (a : Term) :
    den ρ (.i32, .rel t .eq a (.const 0)) = Val.i32 (intTestOp t .eqz (ev ρ t a)) := by
  simp only [den, ev, Val.i32, intTestOp, intRelOp]
  rfl

theorem den_rel (t : IntType) (op : IntRelOp) (a b : Term) :
    den ρ (.i32, .rel t op a b) = Val.i32 (intRelOp t op (ev ρ t a) (ev ρ t b)) := by
  simp only [den, ev, Val.i32]
  rfl

theorem binV_of_ok {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
    (hz : intBinOp t op x y = .ok z) : binV t op x y = z := by
  simp [binV, hz]

@[simp] theorem frameAt_mk (f : Frame) (ls st : List (IntType × Term)) :
    frameAt f ρ ⟨ls, st⟩ = { f with locals := ls.map fun p => some (den ρ p) } := rfl

theorem frameAt_stack (f : Frame) (ls st st' : List (IntType × Term)) :
    frameAt f ρ ⟨ls, st⟩ = frameAt f ρ ⟨ls, st'⟩ := rfl

/-- **One symbolic step is one step of `exec`.** -/
theorem sstep_exec1 {S S' : SState} {i : Instr} (h : sstep S i = some S') (s : Store H) (f : Frame)
    (extra : List Val) :
    exec1 s (frameAt f ρ S) (stackAt ρ S ++ extra) i =
      some (s, frameAt f ρ S', stackAt ρ S' ++ extra) := by
  rcases S with ⟨ls, st⟩
  cases i <;> simp only [sstep] at h <;> try cases h
  case nop => rfl
  case drop =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  case intConst t c =>
    simp only [exec1, stackAt, den_const, List.map_cons, List.cons_append]
    rfl
  case localGet x =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [exec1, localVal?, frameAt_local?, hp, Option.map_some, stackAt, List.map_cons,
      List.cons_append]
    rfl
  case localSet x =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i hx
      cases h
      simp [exec1, popV, hx, Frame.setLocal, stackAt, List.map_set]
    · cases h
  case localTee x =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i hx
      cases h
      simp [exec1, popV, hx, Frame.setLocal, stackAt, List.map_set]
    · cases h
  case intUnOp t op =>
    rcases st with _ | ⟨⟨t₁, a⟩, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      subst ht
      cases h
      simp only [exec1, stackAt, List.map_cons, List.cons_append, popInt_den, Option.map_some]
      rfl
    · cases h
  case intBinOp t op =>
    rcases st with _ | ⟨⟨t₂, b⟩, _ | ⟨⟨t₁, a⟩, st'⟩⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      obtain ⟨rfl, rfl, hs⟩ := ht
      cases h
      obtain ⟨z, hz⟩ := safeBin_ok (ρ := ρ) t₂ op b hs (ev ρ t₂ a)
      simp only [exec1, stackAt, List.map_cons, List.cons_append, popInt_den, Option.bind_some, hz]
      simp only [den, ev, binV_of_ok hz]
      rfl
    · cases h
  case intTestOp t op =>
    rcases st with _ | ⟨⟨t₁, a⟩, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      subst ht
      cases h
      cases op
      simp only [exec1, stackAt, List.map_cons, List.cons_append, popInt_den, Option.map_some,
        den_eqz]
      rfl
    · cases h
  case intRelOp t op =>
    rcases st with _ | ⟨⟨t₂, b⟩, _ | ⟨⟨t₁, a⟩, st'⟩⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      simp only [exec1, stackAt, List.map_cons, List.cons_append, popInt_den, Option.bind_some,
        Option.map_some, den_rel]
      rfl
    · cases h

/-- **Forward rule** for one symbolic step. -/
theorem wp_sstep {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {S S' : SState} {i : Instr} (h : sstep S i = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin)
    (hw : Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    Wp m P host s (frameAt f ρ S) (vals (us ++ (stackAt ρ S).reverse) ++ .plain i :: rest) Q := by
  rcases S with ⟨ls, st⟩
  cases i <;> simp only [sstep] at h <;> try cases h
  case nop => exact Wp.nop hw
  case drop =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    have := Wp.drop (v := den ρ p) (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse) (rest := rest) hw
    simpa [stackAt, frameAt_mk] using this
  case intConst t c =>
    simpa [stackAt, den_const, vals, Val.toAdmin, frameAt_mk] using hw
  case localGet x =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    refine Wp.localGet (v := den ρ p) ?_ ?_
    · rw [frameAt_local?, hp]
      rfl
    · simpa [stackAt, frameAt_mk] using hw
  case localSet x =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i hx
      cases h
      have hx' : x.toNat < (frameAt f ρ ⟨ls, p :: st'⟩).locals.length := by simpa [frameAt] using hx
      have := Wp.localSet (v := den ρ p) (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse) (rest := rest)
        hx' (by rw [frameAt_stack f ls (p :: st') st', ← frameAt_set]; exact hw)
      simpa [stackAt, frameAt_mk] using this
    · cases h
  case localTee x =>
    rcases st with _ | ⟨p, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i hx
      cases h
      have hx' : x.toNat < (frameAt f ρ ⟨ls, p :: st'⟩).locals.length := by simpa [frameAt] using hx
      have h₁ := Wp.localSet (v := den ρ p) (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse ++ [den ρ p])
        (rest := rest) hx' (by
          rw [← frameAt_set f ⟨ls, p :: st'⟩ x p (p :: st')]
          simpa [stackAt] using hw)
      have := Wp.localTee (x := x) (v := den ρ p) (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse)
        (rest := rest) (by simpa using h₁)
      simpa [stackAt, frameAt_mk] using this
    · cases h
  case intUnOp t op =>
    rcases st with _ | ⟨⟨t₁, a⟩, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      subst ht
      cases h
      have := Wp.intUnOp (op := op) (x := ev ρ t₁ a) (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse)
        (rest := rest) (by simpa [stackAt, den, ev] using hw)
      simpa [stackAt, den, frameAt_mk] using this
    · cases h
  case intBinOp t op =>
    rcases st with _ | ⟨⟨t₂, b⟩, _ | ⟨⟨t₁, a⟩, st'⟩⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      obtain ⟨rfl, rfl, hs⟩ := ht
      cases h
      obtain ⟨z, hz⟩ := safeBin_ok (ρ := ρ) t₂ op b hs (ev ρ t₂ a)
      have := Wp.intBinOp (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse) (rest := rest) hz
        (by simpa [stackAt, den, ev, binV_of_ok hz] using hw)
      simpa [stackAt, den, frameAt_mk] using this
    · cases h
  case intTestOp t op =>
    rcases st with _ | ⟨⟨t₁, a⟩, st'⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      subst ht
      cases h
      cases op
      have := Wp.intTestOp (op := .eqz) (x := ev ρ t₁ a)
        (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse) (rest := rest)
        (by simpa [stackAt, den_eqz] using hw)
      simpa [stackAt, den, frameAt_mk] using this
    · cases h
  case intRelOp t op =>
    rcases st with _ | ⟨⟨t₂, b⟩, _ | ⟨⟨t₁, a⟩, st'⟩⟩ <;> simp only [reduceCtorEq] at h
    split at h
    · rename_i ht
      obtain ⟨rfl, rfl⟩ := ht
      cases h
      have := Wp.intRelOp (op := op) (x := ev ρ t₂ a) (y := ev ρ t₂ b)
        (us := us ++ (stackAt ρ ⟨ls, st'⟩).reverse) (rest := rest)
        (by simpa [stackAt, den_rel] using hw)
      simpa [stackAt, den, frameAt_mk] using this
    · cases h

end Silmaril.Proofs.Wasm.Auto.Equiv