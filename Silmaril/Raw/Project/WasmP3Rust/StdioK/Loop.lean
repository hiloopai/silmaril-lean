module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Resume

/-!
# `cat` and `echo` under `DenX.den`: answers keep the invariant (the loop and after it)

`stream.read` of stdin (the chunk is what the read delivered, and stdin's bytes grow by
exactly it), `stream.write` of the rest of the chunk (stdout grows by what the write
accepted), the `waitable.join`s, `stream.drop-writable` and the `future.read`s.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

/-! ## `waitable.join` and `stream.drop-writable` -/

theorem resume_join_of {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpre : PrefOk P o) {x y : Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hf : forward (builtinX S P.join) [x, y] d = some (m, kont))
    (hnext : PcInv P o (d.resume [])) (n : Option (List Val)) :
    DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  rw [hw.join] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  refine resume_quiet quiet_join hok hpre fun d' hkn => ?_
  rw [← hk'] at hkn
  dsimp only at hkn
  split at hkn
  · rw [Option.some.injEq] at hkn; subst hkn; exact ⟨hm, hr, hnext⟩
  · cases hkn

theorem resume_join {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none)
    (hpc : d.core.pc = .joinR ∨ d.core.pc = .joinW ∨ ∃ b, d.core.pc = .joinF b)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  rcases hpc with hpc | hpc | ⟨b, hpc⟩
  · obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.join) (a0 := [d.core.rin, d.core.s])
      (by simp only [callOf, hpc]) hco
    simp only [PcInv, hpc] at hp
    refine resume_join_of hw hm hok hr hp.1.prefOk hf ?_ n
    simp only [PcInv, dresume, afterCall, hpc]
    exact hp
  · obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.join) (a0 := [d.core.w, d.core.s])
      (by simp only [callOf, hpc]) hco
    simp only [PcInv, hpc] at hp
    refine resume_join_of hw hm hok hr hp.1.1.prefOk hf ?_ n
    simp only [PcInv, dresume, afterCall, hpc]
    exact hp
  · obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.join) (a0 := [d.core.fut b, d.core.s])
      (by simp only [callOf, hpc]) hco
    simp only [PcInv, hpc] at hp
    refine resume_join_of hw hm hok hr hp.1.1.prefOk hf ?_ n
    simp only [PcInv, dresume, afterCall, hpc]
    exact hp

theorem resume_dropW {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .dropW)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.dropW) (a0 := [d.core.w]) (by simp only [callOf, hpc]) hco
  simp only [PcInv, hpc] at hp
  rw [hw.dropW] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  refine resume_quiet quiet_dropW hok hp.1.1.prefOk fun d' hkn => ?_
  rw [← hk'] at hkn
  dsimp only at hkn
  split at hkn
  · rw [Option.some.injEq] at hkn
    subst hkn
    refine ⟨hm, hr, ?_⟩
    rcases hkind : P.kind with _ | _ <;>
      simp only [PcInv, dresume, afterCall, hpc, hkind, ↓reduceIte, reduceCtorEq] <;> exact hp
  · cases hkn

/-! ## `future.read` -/

theorem gotFuture_inv {o : Obs} {d : DConf (stdioK P)} {c : SConf} {b : Bool} {v : Nat}
    {pend : List (Nat × Nat × Nat)} (hd : Done P o c) (hpf : PendF pend) :
    PcInv P o { d with core := gotFuture c b v, pend := pend } := by
  unfold gotFuture
  cases b
  · simp only [Bool.false_eq_true, ite_false, PcInv]
    exact ⟨hd.1, fun _ => hd.2.1, hd.2.2, hpf⟩
  · simp only [ite_true, PcInv]
    exact ⟨hd, hpf⟩

theorem afterFut_inv {o : Obs} {d : DConf (stdioK P)} {c : SConf} {b : Bool} (code : Nat)
    {pend : List (Nat × Nat × Nat)} (hd : Done P o c) (hpf : PendF pend) :
    PcInv P o { d with core := afterFut c b code, pend := pend } := by
  unfold afterFut
  split
  · simp only [PcInv]; exact ⟨hd, hpf⟩
  · exact gotFuture_inv hd hpf
  · exact gotFuture_inv hd hpf

theorem resume_fread {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) {b : Bool} (hpc : d.core.pc = .fread b)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.fread) (a0 := [d.core.fut b, futA])
    (by simp only [callOf, hpc]) hco
  simp only [PcInv, hpc] at hp
  obtain ⟨hd, hpf⟩ := hp
  rw [hw.fread] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  refine resume_quiet quiet_fread hok hd.1.prefOk fun d' hkn => ?_
  rw [← hk'] at hkn
  dsimp only at hkn
  split at hkn
  · rename_i pv
    cases hc : natOf pv with
    | none => rw [hc] at hkn; cases hkn
    | some code =>
      rw [hc, Option.map_some, Option.some.injEq] at hkn
      subst hkn
      refine ⟨by split <;> exact hm, by split <;> exact hr, ?_⟩
      have hpf' : PendF (if code = blocked then (evFutureRead, d.core.fut b, futA) :: d.pend
          else d.pend) := by
        split
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨rfl, rfl⟩
          · exact hpf e he
        · exact hpf
      have e : (if code = blocked then d.block evFutureRead (d.core.fut b) futA else d).resume [code] =
          { d with
            core := afterFut d.core b code
            pend := if code = blocked then (evFutureRead, d.core.fut b, futA) :: d.pend
              else d.pend } := by
        split <;> simp [dresume, DConf.block, afterCall, hpc]
      rw [e]
      exact afterFut_inv code hd hpf'
  · rename_i pv v
    cases hc : natOf pv with
    | none => rw [hc] at hkn; cases hkn
    | some code =>
      simp only [hc, dstore, Option.map_some, Option.some.injEq] at hkn
      subst hkn
      refine ⟨hm, hr, ?_⟩
      have hst : store d.core futA [discByte v] = { d.core with res := (discByte v).toNat } := by
        simp [store, futA, retA]
      simp only [dresume, hst, afterCall, hpc]
      exact afterFut_inv (d := d) code (c := { d.core with res := _ }) hd hpf
  · cases hkn

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
