module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Wait

/-!
# `hello` under `den`: every step of the driver keeps the invariant

`resume_inv` (answers of the world), `tau_inv` (silent steps: `task.return`, the packed codes
`helloK` returns, traps).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

theorem DInv.trapped {o : Obs} {d : DConf helloK} (h : DInv o d) : DInv o d.trapped :=
  dinv_trapped h.1 h.prefix

theorem internal_ret {S : Spaces} (hw : HelloWiring S) {d : DConf helloK} {v : Nat}
    (hr : d.result = none) :
    internal (builtin S 22) [v] d =
      some (some { d with core := helloK.resume d.core [], result := some [v] }) := by
  rw [hw.taskReturn]; simp only [internal, hr]

/-- A forwarded built-in at a program point that calls the world. -/
theorem fwd_inv {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hp : PcInv o d.core)
    (hco : callOf d.core = some (k', args)) (hi : internal (builtin S k') args d = none)
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  cases hpc : d.core.pc <;> simp only [PcInv, hpc] at hp
  case new => exact resume_new hw hm hok hr hpc hp hco hf n
  case wvs => exact resume_wvs hw hm hok hr hpc hp hco hf n
  case wsNew => exact resume_wsNew hw hm hok hr hpc hp hco hf n
  case write => exact resume_write hw hm hok hr hpc hp hco hf n
  case joinW => exact resume_joinW hw hm hok hr hpc hp hco hf n
  case dropW => exact resume_dropW hw hm hok hr hpc hp hco hf n
  case fread => exact resume_fread hw hm hok hr hpc hp hco hf n
  case joinF => exact resume_joinF hw hm hok hr hpc hp hco hf n
  case ret v =>
    obtain ⟨rfl, rfl⟩ := call_eq (k0 := 22) (a0 := [v]) (by simp only [callOf, hpc]) hco
    rw [internal_ret hw hr] at hi; cases hi
  case waitW => simp only [callOf, hpc, reduceCtorEq] at hco
  case waitF => simp only [callOf, hpc, reduceCtorEq] at hco

/-- **Answers keep the invariant.** -/
theorem resume_inv {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {m : P3Op}
    {k : Option (List Val) → DConf helloK} (hc : DCall helloK S 30 d m k) (hd : DInv o d)
    (n : Option (List Val)) (hacc : (obsStep o (.imp m.1.1 m.2 n)).wp.isSome) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (k n) := by
  cases hc with
  | @fwd k' args _ kont hm hco hi hf =>
    obtain ⟨hok, hd⟩ := hd
    simp only [hm] at hd
    change callOf d.core = some _ at hco
    show DInv _ (contOf d kont n)
    rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact fwd_inv hw hm hok hr hp hco hi hf n
    · simp only [callOf, hx, reduceCtorEq] at hco
    · simp only [callOf, hx, reduceCtorEq] at hco
  | wait hm =>
    obtain ⟨hok, hd⟩ := hd
    simp only [hm] at hd
    obtain ⟨hr, rfl, (⟨hpc, hp⟩ | ⟨hpc, hp⟩)⟩ := hd
    · exact resume_waitW hok hr hpc hp n hacc
    · exact resume_waitF hok hr hpc hp n hacc

theorem retOf_some {c : HConf} {vs : List Nat} (h : helloK.ret c vs) :
    (c.pc = .waitW ∨ c.pc = .waitF) ∧ vs = [2 + 16 * c.s] ∨ c.pc = .exit ∧ vs = [0] := by
  obtain ⟨p, hp, rfl⟩ := h
  unfold retOf at hp
  split at hp <;> simp_all

/-- `task.return` at `ret v`. -/
theorem internal_ret_inv {S : Spaces} (hw : HelloWiring S) {o : Obs} {d d' : DConf helloK}
    {v : Nat} (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none)
    (hpc : d.core.pc = .ret v) (hp : Live o d.core ∧ (v = 0 → d.core.off = len) ∧ o.wp = some [])
    (hi : internal (builtin S 22) [v] d = some (some d')) : DInv o d' := by
  rw [internal_ret hw hr, Option.some.injEq, Option.some.injEq] at hi
  subst hi
  refine ⟨hok, ?_⟩
  simp only [hm]
  refine .inr (.inl ⟨by simp only [helloK, afterCall, hpc], hp.1.prefix, ?_⟩)
  rintro v' ⟨⟩ rfl
  rw [hp.1.2.2.1, hp.2.1 rfl, take_len]

/-- `task.return` (the only built-in local to the task that `helloK` calls). -/
theorem internal_inv {S : Spaces} (hw : HelloWiring S) {o : Obs} {d d' : DConf helloK} {k : Nat}
    {args : List Nat} (hm : d.mode = .run) (hco : helloK.callOut d.core k args)
    (hi : internal (builtin S k) args d = some (some d')) (hd : DInv o d) : DInv o d' := by
  change callOf d.core = some (k, args) at hco
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · cases hpc : d.core.pc <;> simp only [PcInv, hpc] at hp
    case ret v =>
      obtain ⟨rfl, rfl⟩ := call_eq (k0 := 22) (a0 := [v]) (by simp only [callOf, hpc]) hco
      exact internal_ret_inv hw hm hok hr hpc hp hi
    all_goals simp only [callOf, hpc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hco
    all_goals obtain ⟨rfl, rfl⟩ := hco; simp only [hw.streamNew, hw.wvs, hw.wsNew, hw.write,
      hw.join, hw.dropW, hw.fread, internal, reduceCtorEq] at hi
  all_goals simp only [callOf, hx, reduceCtorEq] at hco

theorem wait_inv {o : Obs} {d : DConf helloK} {p s : Nat} (hm : d.mode = .run)
    (hret : helloK.ret d.core [p])
    (hun : Silmaril.Wasm.Component.Async.Cabi.unpackCallback p = .ok (.wait, s)) (hd : DInv o d) :
    DInv o { d with mode := .wait s } := by
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  rcases retOf_some hret with ⟨hpc, e⟩ | ⟨hpc, e⟩ <;> cases e
  · rw [unpack_wait, Except.ok.injEq, Prod.mk.injEq] at hun
    obtain ⟨-, rfl⟩ := hun
    rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
    · refine ⟨hok, hr, rfl, ?_⟩
      rcases hpc with hpc | hpc <;> simp only [PcInv, hpc] at hp
      · exact .inl ⟨hpc, hp⟩
      · exact .inr ⟨hpc, hp⟩
    · rcases hpc with hpc | hpc <;> rw [hpc] at hx <;> cases hx
    · rcases hpc with hpc | hpc <;> rw [hpc] at hx <;> cases hx
  · rw [unpack_exit] at hun; cases hun

theorem exit_inv {o : Obs} {d : DConf helloK} {p s : Nat} (hm : d.mode = .run)
    (hret : helloK.ret d.core [p])
    (hun : Silmaril.Wasm.Component.Async.Cabi.unpackCallback p = .ok (.exit, s)) (hd : DInv o d) :
    DInv o { d with mode := .exit } := by
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  rcases retOf_some hret with ⟨hpc, e⟩ | ⟨hpc, e⟩ <;> cases e
  · rw [unpack_wait] at hun; cases hun
  · rcases hd with ⟨hr, hp⟩ | ⟨-, hx⟩ | ⟨hx, -⟩
    · simp only [PcInv, hpc] at hp
    · exact ⟨hok, hx⟩
    · rw [hpc] at hx; cases hx

/-- **Silent steps keep the invariant.** -/
theorem tau_inv {S : Spaces} (hw : HelloWiring S) {o : Obs} {d d' : DConf helloK}
    (hs : DStep helloK S 30 d d') (hd : DInv o d) : DInv o d' := by
  cases hs with
  | core _ h => exact absurd h id
  | @internal _ k args hm hco hi => exact internal_inv hw hm hco hi hd
  | bad _ _ _ => exact DInv.trapped hd
  | yield hm hret hun =>
    rcases retOf_some hret with ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
    · rw [unpack_wait] at hun; cases hun
    · rw [unpack_exit] at hun; cases hun
  | wait hm hret hun => exact wait_inv hm hret hun hd
  | exit hm hret hun => exact exit_inv hm hret hun hd
  | badRet _ _ _ => exact DInv.trapped hd
  | trap _ _ => exact DInv.trapped hd

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
