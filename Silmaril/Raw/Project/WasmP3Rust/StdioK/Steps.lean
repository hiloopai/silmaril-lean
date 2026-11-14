module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.WaitRes

/-!
# `cat` and `echo` under `DenX.den`: every step of the driver keeps the invariant

`resume_inv` (answers of the world, by program point), `tau_inv` (silent steps: `task.return`,
the packed codes the model returns, traps).
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

theorem DInv.trapped {o : Obs} {d : DConf (stdioK P)} (h : DInv P o d) : DInv P o d.trapped :=
  dinv_trapped h.1 h.prefOk

theorem internal_ret (hw : Wiring P S) {d : DConf (stdioK P)} {v : Nat} (hr : d.result = none) :
    internal (builtinX S P.taskReturn) [v] d = some (some { d.resume [] with result := some [v] }) := by
  rw [hw.taskReturn]; simp only [internal, hr]

/-- A forwarded built-in at a program point that calls the world. -/
theorem fwd_inv (hw : Wiring P S) {o : Obs} {d : DConf (stdioK P)} {k' : Nat} {args : List Nat}
    {m : XOp} {kont : Option (List Val) → Option (DConf (stdioK P))} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hp : PcInv P o d)
    (hco : callOf P d.core = some (k', args)) (hi : internal (builtinX S k') args d = none)
    (hf : forward (builtinX S k') args d = some (m, kont)) (n : Option (List Val)) :
    DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  cases hpc : d.core.pc
  case src =>
    rcases hk : P.kind with _ | _
    · exact src_cat hw hk hm hok hr hpc hp hco hf n
    · exact src_echo hw hk hm hok hr hpc hp hco hf n
  case new => exact resume_new hw hm hok hr hpc hp hco hf n
  case wvs => exact resume_wvs hw hm hok hr hpc hp hco hf n
  case wsNew => exact resume_wsNew hw hm hok hr hpc hp hco hf n
  case read => exact resume_read hw hm hok hr hpc hp hco hf n
  case joinR => exact resume_join hw hm hok hr (.inl hpc) hp hco hf n
  case write => exact resume_write hw hm hok hr hpc hp hco hf n
  case joinW => exact resume_join hw hm hok hr (.inr (.inl hpc)) hp hco hf n
  case dropW => exact resume_dropW hw hm hok hr hpc hp hco hf n
  case fread b => exact resume_fread hw hm hok hr hpc hp hco hf n
  case joinF b => exact resume_join hw hm hok hr (.inr (.inr ⟨b, hpc⟩)) hp hco hf n
  case ret v =>
    obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.taskReturn) (a0 := [v]) (by simp only [callOf, hpc]) hco
    rw [internal_ret hw hr] at hi; cases hi
  all_goals simp only [callOf, hpc, reduceCtorEq] at hco

theorem retOf_some {c : SConf} {p : Nat} (h : retOf c = some p) :
    (waiting c.pc = true ∧ p = 2 + 16 * c.s) ∨ (c.pc = .exit ∧ p = 0) := by
  unfold retOf at h
  split at h
  · rename_i hw; exact .inl ⟨hw, (Option.some.inj h).symm⟩
  · split at h
    · rename_i he; exact .inr ⟨he, (Option.some.inj h).symm⟩
    · cases h

/-- **Answers keep the invariant.** -/
theorem resume_inv (hw : Wiring P S) {o : Obs} {d : DConf (stdioK P)} {m : XOp}
    {k : Option (List Val) → DConf (stdioK P)} (hc : DCall (stdioK P) S P.cb d m k)
    (hd : DInv P o d) (n : Option (List Val)) (hacc : (obsStep o (.imp m.1.1 m.2 n)).wp.isSome) :
    DInv P (obsStep o (.imp m.1.1 m.2 n)) (k n) := by
  cases hc with
  | @fwd k' args _ kont hm hco hi hf =>
    obtain ⟨hok, hd⟩ := hd
    simp only [hm] at hd
    change callOf P d.core = some _ at hco
    rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact fwd_inv hw hm hok hr hp hco hi hf n
    · simp only [callOf, hx, reduceCtorEq] at hco
    · simp only [callOf, hx, reduceCtorEq] at hco
  | @wait s hm =>
    obtain ⟨hok, hd⟩ := hd
    simp only [hm] at hd
    obtain ⟨hr, rfl, hwt, hp⟩ := hd
    show DInv P (obsStep o (.imp cWait [natV d.core.s] n)) _
    cases hpc : d.core.pc
    case waitR => exact resume_waitR hok hr hpc hp n hacc
    case waitW =>
      simp only [PcInv, hpc] at hp
      exact resume_waitW hok hr hpc hp.1 hp.2 n hacc
    case waitF b => exact resume_waitF hok hr hpc hp n hacc
    all_goals rw [hpc] at hwt; cases hwt

/-- `task.return` at `ret v`. -/
theorem internal_inv (hw : Wiring P S) {o : Obs} {d d' : DConf (stdioK P)} {k : Nat}
    {args : List Nat} (hm : d.mode = .run) (hco : (stdioK P).callOut d.core k args)
    (hi : internal (builtinX S k) args d = some (some d')) (hd : DInv P o d) : DInv P o d' := by
  change callOf P d.core = some (k, args) at hco
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · cases hpc : d.core.pc
    case ret v =>
      obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.taskReturn) (a0 := [v]) (by simp only [callOf, hpc]) hco
      rw [internal_ret hw hr, Option.some.injEq, Option.some.injEq] at hi
      subst hi
      simp only [PcInv, hpc] at hp
      obtain ⟨hl, hv, -, -⟩ := hp
      refine ⟨hok, ?_⟩
      simp only [dresume, hm]
      refine .inr (.inl ⟨by simp only [afterCall, hpc], hl.prefOk, ?_⟩)
      rintro v' ⟨⟩ rfl
      obtain ⟨-, -, ⟨⟨m, hm', he⟩, -⟩, -⟩ := hl
      refine ⟨m, hm', ?_⟩
      rw [← he, hv rfl, List.drop_length, List.append_nil]
    case src =>
      obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.src) (a0 := [retA]) (by simp only [callOf, hpc]) hco
      rw [hw.src] at hi
      rcases hk : P.kind with _ | _ <;> simp only [hk, srcB, internal, reduceCtorEq] at hi
    all_goals simp only [callOf, hpc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hco
    all_goals obtain ⟨rfl, rfl⟩ := hco
    all_goals simp only [hw.streamNew, hw.wvs, hw.wsNew, hw.read, hw.write, hw.join, hw.dropW,
      hw.fread, internal, reduceCtorEq] at hi
  · simp only [callOf, hx, reduceCtorEq] at hco
  · simp only [callOf, hx, reduceCtorEq] at hco

theorem wait_inv {o : Obs} {d : DConf (stdioK P)} {p s : Nat} (hm : d.mode = .run)
    (hret : (stdioK P).ret d.core [p])
    (hun : Silmaril.Wasm.Component.Async.Cabi.unpackCallback p = .ok (.wait, s)) (hd : DInv P o d) :
    DInv P o { d with mode := .wait s } := by
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  obtain ⟨p', hp', e⟩ := hret
  cases e
  rcases retOf_some hp' with ⟨hwt, rfl⟩ | ⟨hpc, rfl⟩
  · rw [unpack_wait, Except.ok.injEq, Prod.mk.injEq] at hun
    obtain ⟨-, rfl⟩ := hun
    rcases hd with ⟨hr, hp⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact ⟨hok, hr, rfl, hwt, hp⟩
    · rw [hx] at hwt; cases hwt
    · rw [hx] at hwt; cases hwt
  · rw [unpack_exit] at hun; cases hun

theorem exit_inv {o : Obs} {d : DConf (stdioK P)} {p s : Nat} (hm : d.mode = .run)
    (hret : (stdioK P).ret d.core [p])
    (hun : Silmaril.Wasm.Component.Async.Cabi.unpackCallback p = .ok (.exit, s)) (hd : DInv P o d) :
    DInv P o { d with mode := .exit } := by
  obtain ⟨hok, hd⟩ := hd
  simp only [hm] at hd
  obtain ⟨p', hp', e⟩ := hret
  cases e
  rcases retOf_some hp' with ⟨hwt, rfl⟩ | ⟨hpc, rfl⟩
  · rw [unpack_wait] at hun; cases hun
  · rcases hd with ⟨hr, hp⟩ | ⟨-, hx⟩ | ⟨hx, -⟩
    · simp only [PcInv, hpc] at hp
    · exact ⟨hok, hx⟩
    · rw [hpc] at hx; cases hx

/-- **Silent steps keep the invariant.** -/
theorem tau_inv (hw : Wiring P S) {o : Obs} {d d' : DConf (stdioK P)}
    (hs : DStep (stdioK P) S P.cb d d') (hd : DInv P o d) : DInv P o d' := by
  cases hs with
  | core _ h => exact absurd h id
  | @internal _ k args hm hco hi => exact internal_inv hw hm hco hi hd
  | bad _ _ _ => exact hd.trapped
  | yield hm hret hun =>
    obtain ⟨p', hp', e⟩ := hret
    cases e
    rcases retOf_some hp' with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [unpack_wait] at hun; cases hun
    · rw [unpack_exit] at hun; cases hun
  | wait hm hret hun => exact wait_inv hm hret hun hd
  | exit hm hret hun => exact exit_inv hm hret hun hd
  | badRet _ _ _ => exact hd.trapped
  | trap _ _ => exact hd.trapped

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
